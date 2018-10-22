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
-type errorable(Ty) :: {ok, Ty} | {error, term()}.

-record(request, {callback :: fun_name(),
		  ref :: cerl:cerl(),
		  payload :: cerl:cerl(),
		  src :: cerl:cerl()}).

-record(request_type, {callback :: fun_name(),
		       ref :: cerl:cerl(),
		       type :: esub_type:type(),
		       src :: cerl:cerl()}).

%%==============================================================================
%% Entry point
%%==============================================================================

main(Args) ->
    [Filename] = Args,
    analyse_file(Filename).

analyse_file(Filename) ->
    info("Analysing file '~s'", [Filename]),
    
    debug("Compiling module to Core Erlang"),
    CompileRes = compile:file(Filename, [to_core, binary] ++ ?COMPILER_OPTIONS),
    case CompileRes of
	{ok, Name, Bin} ->
	    info("Compiled module '~s' to Core Erlang", [Name]),
	    analyse_c_module(Bin);
	error ->
	    fatal("Compilation error");
	{error,Errors,_Warnings} ->
	    fatal("Compilation errors: ~p", [Errors])
    end.
    
analyse_c_module(Module) ->
    debug("Finding module behaviours"),
    AllBehaviours = c_module_behaviours(Module),
    debug("Module behaviours: ~p", [AllBehaviours]),

    Behaviours = lists:filter(fun is_supported/1, AllBehaviours),
    info("Supported module behaviours: ~p", [Behaviours]),

    lists:foreach(fun(Behaviour) ->
			  info("Checking behaviour '~p'", [Behaviour]),
			  ok = check_behaviour(Behaviour, Module)
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

request_to_callback(gen_server, {call,2}) -> {handle_call,3};
request_to_callback(gen_server, {cast,2}) -> {handle_cast,2}.

known_starts(gen_server) -> [{{start_link,4},1}, {{start,4},1}].

%%==============================================================================
%% Behaviour Checking
%%==============================================================================
pat_guard_to_type(Pat, CGuard) ->
    Guard = esub_core:c_guard_to_guard(CGuard),
    {Envs, _} = esub:guard_to_envs(Guard),
    debug("Envs: ~p", [Envs]),
    Types = lists:map(fun(Env) -> esub:c_pat_to_type(Pat, Env) end, Envs),
    lists:foldl(fun(Type,Acc) ->
			esub_type:t_or(Type,Acc)
		end, esub_type:t_not(esub_type:t_any()), Types).

check_behaviour(Behaviour, Module) ->
    debug("Finding calls to known request functions"),
    Requests = get_requests(Behaviour, Module),
    info("Found ~p calls to known request functions", [length(Requests)]),
    RequestTypes = lists:map(fun({Fun,Ref,Payload,Src}) ->
				     {Fun,esub:c_pat_to_type(Payload)}
			     end, Requests),

    debug("Finding known callback functions"),
    {Callbacks, Undefined, Invalid} = get_callbacks(Behaviour, Module),
    lists:foreach(fun(Name) ->
			  warn("Callback '~p' for behaviour '~p' UNDEFINED", [Name, Behaviour])
		  end, Undefined),
    lists:foreach(fun(Name) ->
			  err("Callback '~p' for behaviour '~p' MALFORMED", [Name, Behaviour])
		  end, Invalid),
    lists:foreach(fun({Name,_Body}) ->
			  debug("Callback '~p' for behaviour '~p' OK", [Name, Behaviour])
		  end, Callbacks),
    info("Found ~p callback functions", [length(Callbacks)]),
    CallbackTypes = lists:map(fun({Name,Cases}) ->
				      Types = lists:map(fun({Pat, Guard}) ->
								pat_guard_to_type(Pat, Guard)
							end, Cases),
				      {Name, Types}
			      end, Callbacks),

    Res = lists:map(fun({Req,Type}) ->
			    CallbackName = request_to_callback(Behaviour, Req),
			    CallbackType = proplists:get_value(CallbackName, CallbackTypes),
			    debug("Request:~n~p", [Type]),
			    debug("Callback:~n~p", [CallbackType]),
			    {Req,Type,CallbackType}
		    end, RequestTypes),
    Res.

%%    {Requests, CallbackTypes, Res}.

get_requests(Behaviour, Cerl) ->
    KnownRequests = known_requests(Behaviour),
    lists:flatmap(fun({{Name,Arity}=Fun,RefN,PayloadN}) ->
			  Calls = find_calls(Behaviour, Name, Arity, Cerl),
			  lists:map(fun(Src) ->
					    Args = cerl:call_args(Src),
					    Ref = lists:nth(RefN, Args),
					    Payload = lists:nth(PayloadN, Args),
					    {Fun,Ref,Payload,Src}
				    end, Calls)
		  end, KnownRequests).
	
    

%%==============================================================================
%% Callback Helpers
%%==============================================================================

-spec get_callbacks(atom(), cerl:c_module()) -> {[{fun_name(), [cerl:c_clause()]}], [fun_name()], [fun_name()]}.
get_callbacks(Behaviour, Module) ->
    Defs = c_module_defs(Module),
    lists:foldl(fun({Name,Arg},{Ok,Undefined,Malformed}) ->
		      case proplists:lookup(Name, Defs) of
			  {Name, Body} ->
			      case get_nth_fun_arg(Arg, Body) of
				  {ok, Clauses} ->
				      {[{Name,Clauses}|Ok],Undefined,Malformed};
				  {error, _} ->
				      {Ok, Undefined, [Name|Malformed]}
			      end;
			  none ->
			      {Ok,[Name|Undefined],Malformed}
		      end
		end, {[],[],[]}, known_callbacks(Behaviour)).

-spec get_nth_fun_arg(cerl:c_fun(), integer()) -> errorable([{cerl:cerl(), cerl:cerl()}]).
get_nth_fun_arg(N, Fun) ->
    Body = cerl:fun_body(Fun),
    case cerl:type(Body) of
	'case' ->
	    Clauses = cerl:case_clauses(Body),
	    Args = lists:map(fun(Clause) ->
				     get_nth_clause_arg(N, Clause)
			     end, Clauses),
	    lift_error(Args);
	_ ->
	    {error, top_level_not_case}
    end.

-spec get_nth_clause_arg(cerl:c_clause(), integer()) -> errorable({cerl:cerl(), cerl:cerl()}).
get_nth_clause_arg(N, Clause) ->
    Pats = cerl:clause_pats(Clause),
    case length(Pats) > N of
	true ->
	    {ok, {lists:nth(N, Pats), cerl:clause_guard(Clause)}};
	false ->
	    {error, not_enough_pats}
    end.

lift_error(Xs) ->
    lists:foldl(fun(X0,Acc0) ->
			case Acc0 of
			    {ok, Acc} ->
				case X0 of
				    {ok, X} ->
					{ok, [X|Acc]};
				    {error, _} ->
					X0
				end;
			    {error, _} ->
				Acc0
			end
		end, {ok, []}, lists:reverse(Xs)).
    

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
