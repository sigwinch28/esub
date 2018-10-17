-module(esub_otp).
-export([analyse/1]).
-import(esub_log, [debug/1,debug/2,info/1,info/2,warn/1,warn/2,err/1,err/2,
		   fatal/1,fatal/2,print/1,print/2]).

-define(COMPILER_OPTIONS, [verbose]).

-define(BEHAVIOUR_ATTR, behaviour).
-define(SERVER_CALL_NAME, {'handle_call',3}).
-define(SERVER_CALL_MSG_PAT, 1).
-define(SERVER_CAST_NAME, {'handle_cast',2}).
-define(SERVER_CAST_MSG_PAT, 1).
-define(SERVER_INFO_NAME, {'handle_info',2}).
-define(SERVER_INFO_MSG_PAT, 1).
-define(SERVER_START_NAME, {'start_link',0}).
-define(EXCLUDED_DEFS, [{'module_info',0},{'module_info',1}]).

-define(START_FUNS_ATTR, 'esub_start_funs').
-define(API_FUNS_ATTR, 'esub_api_funs').

-type fun_name() :: {atom(), integer()}.

%% @doc Determines the callback function name (and arity) for a given OTP module
%% and request name.
-spec call_to_callback(atom(), atom()) -> fun_name().
call_to_callback('gen_server', 'call') -> {'handle_call',3};
call_to_callback('gen_server', 'cast') -> {'handle_cast',2}.

%% @doc Returns a list of known OTP calls for a specific behaviour
-spec known_calls(atom()) -> [atom()].
known_calls('gen_server') -> ['call', 'cast'].

%% @doc Returns the known callback functions for the given OTP behaviour name
-spec known_callbacks(atom()) -> [fun_name()].
known_callbacks('gen_server') -> [{'handle_call',3},{'handle_cast',2}].

start_funs('gen_server') -> [{'start_link',4,1},{'start',4,1}].
    

analyse(Filename) ->
    {ok, _Pid} = esub_log:start(),
    info("Analysing Erlang module '~s'", [Filename]),
    CompileRes = compile:file(Filename, [to_core, binary] ++ ?COMPILER_OPTIONS),
    Cerl = case CompileRes of
	       {ok, _Name, Bin} ->
		   debug("Compiled module to Core Erlang"),
		   Bin;
	       error ->
		   fatal("Compilation error");
	       {error,Errors,_Warnings} ->
		   fatal("Compilation errors:~n~p~n", [Errors])
	   end,

    Behaviour = case get_otp_behaviour(Cerl) of
		    {ok, B} ->
			info("Detected the '~p' behaviour", [B]),
			B;
		    _ ->
			fatal("Couldn't find an OTP behaviour"),
			none  
		end,

    debug("Finding start functions under the ~p attribute", [?START_FUNS_ATTR]),
    {ok, StartFuns} = get_attr(?START_FUNS_ATTR, Cerl),
    info("Known start functions: ~p", [StartFuns]),

    BehaviourStartFuns = start_funs(Behaviour),
    ServerNames = lists:flatmap(fun(StartFun) ->
					case get_def(StartFun, Cerl) of
					    {ok, Body} ->
						debug("Getting server names from '~p'", [StartFun]),
						Names = process_names(Body, Behaviour, BehaviourStartFuns),
						debug("Discovered names '~p' in '~p'", [Names, StartFun]),
						Names;
					    {error, undefined} ->
						error("Start function '~p' is undefined", [StartFun]),
						[]
					end
				end, StartFuns),
    info("Known server names are '~p'", [ServerNames]),

    debug("Finding API functions under the ~p attribute", [?API_FUNS_ATTR]),
    {ok, APIFuns} = get_attr(?API_FUNS_ATTR, Cerl),
    info("Known API functions: ~p", [APIFuns]),
    
    APIDefs = lists:filtermap(fun(Name) ->
				case get_def(Name, Cerl) of
				    {ok, Def} ->
					debug("Retrieved definition of API function ~p", [Name]),
					{true, {Name, Def}};
				    {error, undefined} ->
					err("API function ~p is undefined", [Name]),
					false
				end
			end, APIFuns),
    
    debug("Finding requests in known API functions"),
    Reqs = lists:flatmap(
	     fun({Name, Fun}) ->
		     Reqs = find_requests(Behaviour, Fun),
		     debug("Found ~p requests in ~p", [length(Reqs), Name]),
		     Reqs
	     end, APIDefs),
    info("Discovered ~p requests in the '~p' behaviour", [length(Reqs), Behaviour]),

    lists:foreach(fun({_Behaviour, Type, {Ref, _Msg, Src}}) ->
			  Known = case lists:member(Ref, ServerNames) of
				      true -> "known";
				      false -> "unknown"
				  end,
			  debug("'~p' request on line ~p to '~p' (~s destination)", [Type, cerl_line(Src), Ref, Known])
		  end, Reqs),

    BehaviourCallbacks = known_callbacks(Behaviour),
    debug("Finding callback functions"),
    CallbackDefs = lists:filtermap(fun(Name) ->
					   case get_def(Name, Cerl) of
					       {ok, Def} ->
						   debug("Retrieved definition of callback function ~p", [Name]),
						   {true, {Name, Def}};
					       {error, undefined} ->
						   err("Callback function ~p is undefined", [Name]),
						   false
					   end
				   end, BehaviourCallbacks),
    info("Discovered ~p callback functions in the '~p' behaviour", [length(CallbackDefs), Behaviour]),

    Clauses = lists:filtermap(fun({{_Name, Arity} = Fun, Def}) ->
				      Body = cerl:fun_body(Def),
				      case cerl:type(Body) of
					  'case' ->
					      Arg = cerl:case_arg(Body),
					      case cerl:type(Arg) of
						  values ->
						      Es = cerl:values_es(Arg),
						      case length(Es) of
							  Arity ->
							      {true, {Fun,cerl:case_clauses(Body)}};
							  _ ->
							      err("Malformed callback ~p (wrong number of exprs in case)", [Fun]),
							      false
						      end;
						  _ ->
						      err("Malformed callback ~p (case arg is not values)", [Fun]),
						      false
					      end;
					  _ ->
					      err("Malformed callback (no top-level case) ~p", [Fun]),
					      false
				      end
			      end, CallbackDefs),

    print("~p~n", [Clauses]),
    esub_log:stop().

find_requests(Behaviour, Cerl) ->
    lists:flatmap(fun(CallName) ->
			  Calls = find_call(Behaviour, CallName, Cerl),
			  lists:map(fun(Call) ->
					    {Behaviour, CallName, call_to_request(Call)}
				    end, Calls)
	      end, known_calls(Behaviour)).

call_to_request(Call) ->
    Args = cerl:call_args(Call),
    Ref0 = lists:nth(1, Args),
    Ref = case cerl:is_literal(Ref0) of
	      true -> 
		  case cerl:concrete(Ref0) of
		      Ref1 when is_atom(Ref1) -> {local, Ref1};
		      Ref1 -> Ref1
		  end;
	      false -> Ref0
	  end,
    Msg = lists:nth(2, Args),
    {Ref, Msg, Call}.

process_names(Cerl, Behaviour, FNames) ->
    lists:flatmap(fun({FName,Arity,ArgN}) ->
			  Calls = find_call(Behaviour, FName, Cerl),
			  lists:filtermap(fun(Call) ->
						  Args = cerl:call_args(Call),
						  case length(Args) of
						      Arity ->
							  Name = lists:nth(ArgN, Args),
							  cerl:is_literal(Name) andalso {true, cerl:concrete(Name)};
						      _ ->
							  false
						  end
					  end, Calls)
		  end, FNames).

concrete_defs(Module) ->
    Defs = cerl:module_defs(Module),
    lists:map(fun({Name,Def}) ->
		      {cerl:var_name(Name),Def}
	      end, Defs).

find_call1(Module, Name, Cerl, Acc) ->
    case cerl:type(Cerl) of
	'call' ->
	    CallModule0 = cerl:call_module(Cerl),
	    CallName0 = cerl:call_name(Cerl),
	    
	    case cerl:is_literal(CallModule0) andalso
		cerl:is_literal(CallName0) of
		true ->
		    CallModule = cerl:concrete(CallModule0),
		    CallName = cerl:concrete(CallName0),
		    case CallModule =:= Module andalso
			CallName =:= Name of
			true ->
			    [Cerl|Acc];
			false ->
			    Acc
		    end;
		false ->
		    Acc
	    end;
	_ -> Acc
    end.

find_call(Module, Name, Cerl0) ->
    cerl_trees:fold(fun(Cerl, Acc) ->
			    find_call1(Module, Name, Cerl, Acc)
		    end, [], Cerl0).
    
    
    
compile(Filename) ->
    %%{ok, ModuleName} = compile:file(Filename, [report|?COMPILER_OPTIONS]),
    {ok, ModuleName, Cerl} = compile:file(Filename, [to_core, binary] ++ ?COMPILER_OPTIONS),
    {ModuleName, Cerl}.

get_attr(Name, Module) ->
    Attrs = concrete_attrs(cerl:module_attrs(Module)),
    case proplists:is_defined(Name, Attrs) of
	true ->
	    {ok, proplists:get_value(Name, Attrs)};
	false ->
	    {error, undefined}
    end.
    
    
concrete_attrs(Attrs) ->
    lists:map(fun({K,V}) ->
		      {cerl:concrete(K), cerl:concrete(V)}
	      end, Attrs).

is_behaviour(Behaviour, Module) ->
    case get_attr(?BEHAVIOUR_ATTR, Module) of
	{ok, Behaviours} ->
	    lists:member(Behaviour, Behaviours);
	_ ->
	    false
    end.

get_otp_behaviour(Module) ->
    case is_behaviour('gen_server', Module) of
	true ->
	    {ok, 'gen_server'};
	false ->
	    {error, no_behaviour}
    end.

get_def(Name, Module) ->
    Defs = concrete_defs(Module),
    case proplists:is_defined(Name, Defs) of
	true ->
	    {ok, proplists:get_value(Name, Defs)};
	false ->
	    {error, undefined}
    end.

cerl_line(Cerl) ->
    Ann = cerl:get_ann(Cerl),
    case Ann of
	[Line|_] when is_integer(Line) ->
	    Line;
	_ ->
	    unknown
    end.
