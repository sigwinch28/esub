-module(esub_otp).
-export([main/1]).
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

%%==============================================================================
%% Entry point
%%==============================================================================

main(Args) ->
    [Filename] = Args,
    info("Analysing file '~s'", [Filename]),
    
    debug("Compiling module to Core Erlang"),
    CompileRes = compile:file(Filename, [to_core, binary] ++ ?COMPILER_OPTIONS),
    {_Name, Module} = case CompileRes of
	       {ok, Name, Bin} ->
		   info("Compiled module '~s' to Core Erlang", [Name]),
		   {Name, Bin};
	       error ->
		   fatal("Compilation error");
	       {error,Errors,_Warnings} ->
		   fatal("Compilation errors: ~p", [Errors])
	   end,

    debug("Finding module behaviours"),
    AllBehaviours = c_module_behaviours(Module),
    debug("Module behaviours: ~p", [AllBehaviours]),

    Behaviours = lists:filter(fun is_supported/1, AllBehaviours),
    info("Supported module behaviours: ~p", [Behaviours]),

    lists:foreach(fun(Behaviour) ->
			  info("Checking behaviour '~p'", [Behaviour]),
			  check_behaviour(Behaviour, Module)
		  end, Behaviours).

   
		

%%==============================================================================
%% Behaviour Information
%%==============================================================================
is_supported(gen_server) -> true;
is_supported(_) -> false.

known_callbacks(gen_server) ->
    [{{handle_call,3},1},
     {{handle_cast,2},1},
     {{handle_info,2},1}].

known_requests(gen_server) ->
    %% {{name, arity}, refArg, payloadArg}
    [{{call,2},1,2},
     {{call,3},1,2},
     {{cast,2},1,2}].

request_to_callback(gen_server, call) -> {handle_call,3};
request_to_callback(gen_server, cast) -> {handle_cast,2}.

known_starts(gen_server) -> [{{start_link,4},1}, {{start,4},1}].

%%==============================================================================
%% Behaviour Checking
%%==============================================================================

check_behaviour(Behaviour, Module) ->
    debug("Collecting function clauses for behaviour callbacks"),
    {Callbacks, Undefined, Invalid} = get_callback_clauses(Behaviour, Module),
    lists:foreach(fun(Name) ->
			  warn("Callback '~p' for behaviour '~p' UNDEFINED", [Name, Behaviour])
		  end, Undefined),
    lists:foreach(fun(Name) ->
			  err("Callback '~p' for behaviour '~p' MALFORMED", [Name, Behaviour])
		  end, Invalid),
    lists:foreach(fun({Name,_Arg,_Body}) ->
			  debug("Callback '~p' for behaviour '~p' OK", [Name, Behaviour])
		  end, Callbacks),
    info("Collected function clauses for behaviour callbacks"),

    KnownRequests = known_requests(Behaviour),
    info("Known request functions: ~p", [KnownRequests]),

    debug("Finding calls to known request functions"),
    Requests = lists:flatmap(fun({{ReqName,Arity}=Name,RefArg,PayloadArg}) ->
				     debug("Finding calls to ~p", [Name]),
				     Calls = find_calls(Behaviour, ReqName, Arity, Module),
				     lists:map(fun(Call) ->
						       Args = cerl:call_args(Call),
						       Ref = lists:nth(RefArg, Args),
						       Payload = lists:nth(PayloadArg, Args),
						       Line = c_line(Call),
						       info("Found call to ~p on line ~p", [Name, Line]),
						       {{ReqName,Arity},Ref,Payload,Call}
					       end, Calls)
			     end, KnownRequests),
    info("Found ~p calls to known request functions", [Requests]),
    Requests.

%%==============================================================================
%% Callback Helpers
%%==============================================================================

-spec get_callback_clauses(atom(), cerl:c_module()) -> {[{fun_name(), [cerl:c_clause()]}], [fun_name()], [fun_name()]}.
get_callback_clauses(Behaviour, Module) ->
    Defs = c_module_defs(Module),
    lists:foldl(fun({Name,Arg},{Ok,Undefined,Malformed}) ->
		      case proplists:lookup(Name, Defs) of
			  {Name, Body} ->
			      case callback_to_clauses(Body) of
				  {ok, Clauses} ->
				      {[{Name,Arg,Clauses}|Ok],Undefined,Malformed};
				  {error, _} ->
				      {Ok, Undefined, [Name|Malformed]}
			      end;
			  none ->
			      {Ok,[Name|Undefined],Malformed}
		      end
		end, {[],[],[]}, known_callbacks(Behaviour)).
    

-spec callback_to_clauses(cerl:c_fun()) -> {ok, [cerl:c_clause()]} | {error, term()}.
callback_to_clauses(Fun) ->
    Body = cerl:fun_body(Fun),
    case cerl:type(Body) of
	'case' ->
	    {ok, cerl:case_clauses(Body)};
	_ ->
	    {error, top_level_not_case}
    end.	

%%==============================================================================
%% Core Erlang Helpers
%%==============================================================================

c_module_defs(Module) ->
    lists:map(fun({Name,Def}) ->
		      {cerl:var_name(Name),Def}
	      end, cerl:module_defs(Module)).

c_module_behaviours(Module) ->
    Attrs = c_module_attrs(Module),
    proplists:get_value(behaviour, Attrs, []).

c_module_attrs(Module) ->
    Attrs = cerl:module_attrs(Module),
    lists:map(fun({K,V}) ->
		      {cerl:concrete(K), cerl:concrete(V)}
	      end, Attrs).

c_line(Cerl) ->
    Ann = cerl:get_ann(Cerl),
    case Ann of
	[Line|_] when is_integer(Line) ->
	    Line;
	_ ->
	    unknown
    end.


find_call1(Module, Name, Arity, Cerl, Acc) ->
    case cerl:type(Cerl) of
	'call' ->
	    CallModule0 = cerl:call_module(Cerl),
	    CallName0 = cerl:call_name(Cerl),
	    
	    case cerl:is_literal(CallModule0) andalso
		cerl:is_literal(CallName0) of
		true ->
		    CallModule = cerl:concrete(CallModule0),
		    CallName = cerl:concrete(CallName0),
		    CallArgs = cerl:call_args(Cerl),
		    case CallModule =:= Module andalso
			CallName =:= Name andalso
			length(CallArgs) =:= Arity of
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

find_calls(Module, Name, Arity, Cerl0) ->
    cerl_trees:fold(fun(Cerl, Acc) ->
			    find_call1(Module, Name, Arity, Cerl, Acc)
		    end, [], Cerl0).
