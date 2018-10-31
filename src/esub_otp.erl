-module(esub_otp).
-define(debug, true).
-include("esub_debug.hrl").
-export([main/1]).

-define(COMPILER_OPTIONS, [verbose]).

-define(BEHAVIOUR_ATTR, behaviour).
-define(EXCLUDED_DEFS, [{'module_info',0},{'module_info',1}]).

-type fun_name() :: {atom(), integer()}.


-record(request, {name :: fun_name(),
		  used = false :: false | {true, integer()},
		  type :: esub_type:type(),
		  line = undefined :: integer()}).

-record(callback, {name :: fun_name(),
		   payload_arg :: integer(),
		   clauses :: [callback_clause()]}).

-record(callback_clause, {types :: [esub_type:type()],
			  used = false :: boolean(),
			  line = undefined :: integer()}).

-type request() :: #request{}.
-type callback() :: #callback{}.
-type callback_clause() :: #callback_clause{}.

%%==============================================================================
%% Entry point
%%==============================================================================

main(Args) ->
    [Filename] = Args,
    {ok, ModuleName, Behaviours} = analyse_file(Filename),
    io:format("module ~p~n", [ModuleName]),
    lists:foreach(
      fun({BehaviourName, {Reqs, Cbs}}) ->
	      io:format("  behaviour ~p~n", [BehaviourName]),
	      io:format("    requests~n"),
	      lists:foreach(
		fun(Req) ->
			{Name, Arity} = Req#request.name,
			Line = Req#request.line,
			io:format("      request on line ~p via ~p:~p/~B~n",
				  [Line, BehaviourName, Name, Arity]),
			io:format("        used: "),
			case Req#request.used of
			    {true, N} ->
				io:format("true, using clauses ~p~n", [N]);
			    false ->
				io:format("false~n")
			end
		end, Reqs),
	      io:format("    callbacks~n"),
	      lists:foreach(
		fun({_, Cb}) ->
			{Name, Arity} = Cb#callback.name,
			io:format("      callback ~p/~B~n", [Name, Arity]),
			lists:foreach(
			  fun(Cl) ->
				  io:format("        clause on line ~p~n",
					    [Cl#callback_clause.line]),
				  io:format("          used: ~p~n",
					    [Cl#callback_clause.used])
			  end, Cb#callback.clauses)
		end, maps:to_list(Cbs))
	      end, Behaviours).



analyse_file(Filename) ->
    ?debug("Analysing source file '~s'", [Filename]),

    ?debug("Compiling module to Core Erlang"),
    CompileRes = compile:file(Filename, [to_core, binary] ++ ?COMPILER_OPTIONS),
    case CompileRes of
	{ok, Name, Bin} ->
	    ?debug("Successfully compiled ~p to Core Erlang", [Name]),
	    {ok, Name,  analyse_c_module(Bin)};
	error ->
	    ?debug("Unspecified compiler error"),
	    {error, unspecified_compiler_error};
	{error,Errors,_Warnings} ->
	    ?debug("Compilation errors:"),
	    ?debug("~p", [Errors]),
	    {error, {compiler_errors, Errors}}
    end.

analyse_c_module(Module) ->
    ?debug("Searching for known module behaviours"),
    AllBehaviours = c_module_behaviours(Module),
    ?debug("Module has behaviours: ~p", [AllBehaviours]),

    Behaviours = lists:filter(fun is_supported/1, AllBehaviours),
    ?debug("Supported module behaviours: ~p", [Behaviours]),

    lists:map(fun(BehaviourName) ->
		      ?debug("Checking behaviour ~p", [BehaviourName]),
		      {BehaviourName, check_behaviour(BehaviourName, Module)}
	      end, Behaviours).

%%==============================================================================
%% Behaviour Information
%%==============================================================================
-spec is_supported(atom()) -> boolean().
is_supported(gen_server) -> true;
is_supported(_) -> false.

-spec known_callbacks(atom()) -> [{fun_name(), integer()}].
known_callbacks(gen_server) ->
    [{{handle_call,3},1},
     {{handle_cast,2},1},
     {{handle_info,2},1}].

-spec known_requests(atom()) -> [{fun_name(), integer(), integer()}].
known_requests(gen_server) ->
    %% {{name, arity}, refArg, payloadArg}
    [{{call,2},1,2},
     {{call,3},1,2},
     {{cast,2},1,2}].

-spec request_name_to_callback_name(atom(), fun_name()) -> fun_name().
request_name_to_callback_name(gen_server, {call,2}) -> {handle_call,3};
request_name_to_callback_name(gen_server, {cast,2}) -> {handle_cast,2}.

%%==============================================================================
%% Behaviour Checking
%%==============================================================================


-spec find_requests(atom(), cerl:cerl()) -> [request()].
find_requests(BehaviourName, Cerl) ->
    KnownRequests = known_requests(BehaviourName),
    lists:flatmap(fun({{Name,Arity}=Fun,RefN,PayloadN}) ->
			  Calls = find_calls(BehaviourName, Name, Arity, Cerl),
			  lists:map(fun(Src) ->
					    Args = cerl:call_args(Src),
					    _Ref = lists:nth(RefN, Args),
					    Payload = lists:nth(PayloadN, Args),
					    Type = esub:c_pat_to_type(Payload),
					    #request{
					       name = Fun,
					       used = false,
					       type = Type,
					       line = c_line(Src)
					      }
				    end, Calls)
		  end, KnownRequests).

-spec ternary_mapfilter1(fun((A) -> {ok, B} | warn | error), [A], {[B], [A], [A]}) -> {[B],[A],[A]}.
ternary_mapfilter1(_F, [], {Ok, Warn, Error}) ->
    {lists:reverse(Ok), lists:reverse(Warn), lists:reverse(Error)};
ternary_mapfilter1(F, [X|Xs], {Ok,Warn,Error}) ->
    Acc = case F(X) of
	      {ok, Y} ->
		  {[Y|Ok], Warn, Error};
	      warn ->
		  {Ok, [X|Warn], Error};
	      error ->
		  {Ok, Warn, [X|Error]}
	  end,
    ternary_mapfilter1(F, Xs, Acc).

-spec ternary_mapfilter(fun((A) -> {ok, B} | warn | error), [A]) -> {[B], [A], [A]}.
ternary_mapfilter(F, Xs) ->
    ternary_mapfilter1(F, Xs, {[], [], []}).

c_clause_to_types(CClause) ->
    CPats = cerl:clause_pats(CClause),
    CGuard = cerl:clause_guard(CClause),

    Guard = esub_core:c_guard_to_guard(CGuard),
    {Envs, _} = esub:guard_to_envs(Guard),
    lists:map(fun(Pat) ->
		      Types = lists:map(fun(Env) ->
						esub:c_pat_to_type(Pat, Env)
					end, Envs),
		      lists:foldl(fun esub_type:t_or/2, esub_type:t_void(), Types)
	      end, CPats).


c_clause_to_callback_clause(CClause) ->
    Line = c_line(CClause),
    Types = c_clause_to_types(CClause),
    #callback_clause{
       types = Types,
       used = false,
       line = Line
      }.

c_def_to_callback({Name, Fun}) ->
    Case = cerl:fun_body(Fun),
    CClauses = cerl:case_clauses(Case),
    Clauses0 = lists:map(fun c_clause_to_callback_clause/1, CClauses),
    %% TODO: more robust check for auto-generated final clause.
    Clauses = lists:reverse(tl(lists:reverse(Clauses0))),
    #callback{
       name = Name,
       clauses = Clauses
      }.


find_callbacks(BehaviourName, Module) ->
    KnownCallbacks = known_callbacks(BehaviourName),
    Defs = c_module_defs(Module),
    ternary_mapfilter(fun({Name, PayloadArg}) ->
			      case proplists:lookup(Name, Defs) of
				  {Name, Def} ->
				      Callback0 = c_def_to_callback({Name, Def}),
				      Callback = Callback0#callback{ payload_arg = PayloadArg },
				      {ok, Callback};
				  none ->
				      warn
			      end
		      end, KnownCallbacks).


check_behaviour(BehaviourName, Module) ->
    Requests = find_requests(BehaviourName, Module),

    {Callbacks0, UndefinedCbs, InvalidCbs} = find_callbacks(BehaviourName, Module),

    lists:foreach(fun({Name, Arity}) ->
			  ?debug("Callback ~p/~B undefined", [Name, Arity])
		  end, UndefinedCbs),
    lists:foreach(fun({Name, Arity}) ->
			  ?debug("Callback ~p/~B is malformed", [Name, Arity])
		  end, InvalidCbs),

    CallbacksPropList = lists:map(fun(Cb) ->
					  {Cb#callback.name, Cb}
				  end, Callbacks0),
    Callbacks = maps:from_list(CallbacksPropList),

    {Reqs, Cbs} = lists:mapfoldl(
		    fun(Req, Cbs) ->
			    CbName = request_name_to_callback_name(BehaviourName, Req#request.name),
			    case maps:find(CbName, Cbs) of
				error ->
				    %% unchanged
				    {Req, Cbs};
				{ok, Cb} ->
				    ReqType = Req#request.type,

				    case callback_count_subtype(Cb, ReqType) of
					[] ->
					    %% unchanged
					    {Req, Cbs};
					 ClauseIDXs ->
					    ?debug("Line ~p:~p: ~p",
						   [Req#request.line,
						    Req#request.name,
						    ClauseIDXs]),
					    Req1 = request_mark_used(Req, ClauseIDXs),
					    Cb1 = callback_mark_used(Cb, ClauseIDXs),
					    Cbs1 = maps:update(CbName, Cb1, Cbs),
					    {Req1, Cbs1}
				    end
			    end
		    end, Callbacks, Requests),
    ?debug("Finished checking behaviour:~n~p", [{Reqs, Cbs}]),

    Reqs1 = lists:sort(fun(A, B) ->
			       A#request.line =< B#request.line
		       end, Reqs),
    {Reqs1, Cbs}.

-spec callback_count_subtype(callback(), esub_type:type()) -> [integer()].
callback_count_subtype(Cb, ReqTy) ->
    ?debug("Finding clauses used to match type ~s", [esub_type:format(ReqTy)]),
    Clauses = Cb#callback.clauses,
    PayloadArg = Cb#callback.payload_arg,
    callback_count_subtype1(Clauses, PayloadArg, ReqTy, {1, [], esub_type:t_void()}).

callback_count_subtype1([], _ArgN, _Ty, {_N, Used, _AccTy}) ->
    Used;
callback_count_subtype1([Cl|Clauses], ArgN, ReqTy, {N, Used, AccTy}) ->
    %% check for overlap between clause and request type
    %% if there is no overlap between the type of the request and the type of
    %% the clause, then it is not possible for the clause to match the request
    ClauseType = lists:nth(ArgN, Cl#callback_clause.types),
    ?debug("Type of clause ~p on L~p is ~s", [N, Cl#callback_clause.line, esub_type:format(ClauseType)]),
    Intersects = esub_type:dnf_plus(esub_type:t_and(ReqTy, ClauseType)),
    ?debug("Intersections: ~s", [esub_type:format(Intersects)]),
    case esub_type:is_void(Intersects) of
	true ->
	    ?debug("No intersections"),
	    %% no overlap, so move on
	    callback_count_subtype1(Clauses, ArgN, ReqTy, {N+1, Used, AccTy});
	false ->
	    Type = esub_type:t_or(ClauseType, AccTy),
	    case esub_type:subtype(ReqTy, Type) of
		true ->
		    Res = [N|Used],
		    ?debug("Found! ~p", [Res]),
		    Res;
		false ->
		    ?debug("~s not a subtype of ~s",
			   [esub_type:format(ReqTy), esub_type:format(Type)]),
		    callback_count_subtype1(Clauses, ArgN, ReqTy, {N+1, [N|Used], Type})
	    end
    end.

-spec callback_mark_used(callback(), [integer()]) -> callback().
callback_mark_used(Cb, Ns) ->
    Clauses = callback_mark_used1(Cb#callback.clauses, 1, Ns, []),
    Cb#callback { clauses = Clauses }.

-spec callback_mark_used1([callback_clause()], integer(), [integer()], [callback_clause()]) -> [callback_clause()].
callback_mark_used1([], _Count, _Ns, Acc) ->
    lists:reverse(Acc);
callback_mark_used1([Cl|Cls], Count, Ns, Acc) ->
    Cl1 = case lists:member(Count, Ns) of
	      true ->
		  callback_clause_mark_used(Cl);
	      false ->
		  Cl
	  end,
    callback_mark_used1(Cls, Count+1, Ns, [Cl1|Acc]).

callback_clause_mark_used(Clause) ->
    Clause#callback_clause{ used = true }.

request_mark_used(Request, N) ->
    Request#request{ used = {true, N} }.


%%==============================================================================
%% Callback Helpers
%%==============================================================================

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
