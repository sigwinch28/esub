-module(esub).

-import(esub_log, [print/1,print/2,debug/1,debug/2,fatal/2]).

%% API exports
-export([main/1]).
-export([c_pat_to_type/1,c_pat_to_type/2,c_guard_to_guard/1,guard_to_envs/1]).

%% Types
-type var() :: term().
-type env() :: [#{var() => esub_type:type()}].

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    esub_log:start(),
    print("Esub v0.0.1~n"),
    debug("Args: ~p", [Args]),
    [RawCmd|Args1] = Args,
    case parse_command(RawCmd) of
	{ok, otp} ->
	    debug("Running command 'otp' with args ~p", [Args1]),
	    esub_otp:main(Args1);
	unknown ->
	    fatal("Unknown command '~s'", [RawCmd])
    end,
    esub_log:stop(),
    erlang:halt(0).

-spec c_pat_to_type(cerl:c_pat()) -> esub_type:type().
c_pat_to_type(Pattern) ->
    c_pat_to_type(Pattern, #{}).

-spec c_pat_to_type(cerl:c_pat(), env()) -> esub_type:type().
c_pat_to_type(Pattern, Gamma) ->
    case cerl:type(Pattern) of
	'var' ->
	    esub_env:get(cerl:var_name(Pattern), Gamma);
	'tuple' ->
	    Types = lists:map(fun(E) -> c_pat_to_type(E, Gamma) end,
			      cerl:tuple_es(Pattern)),
	    esub_type:update_ann(src, Pattern, esub_type:t_tuple(Types));
	'literal' ->
	    Value = cerl:concrete(Pattern),
	    esub_type:update_ann(src,Pattern, esub_type:t_singleton(Value))
    end.

-spec c_guard_to_guard(cerl:cerl()) -> esub_guard:guard().
c_guard_to_guard(_Guard) ->
    not_implemented.

-spec guard_to_envs(esub_guard:guard()) -> {[env()], [env()]}.
guard_to_envs(Guard) ->
    case esub_guard:type(Guard) of
       'true' ->
	    {[any],#{}};
	'false' ->
	    {#{},[none]};
	'eq' ->
	    Var = esub_guard:eq_var(Guard),
	    Lit = esub_guard:eq_lit(Guard),
	    Ty = esub_type:singleton(Lit),
	    {[#{Var => Ty}],[#{Var => esub_type:t_not(Ty)}]};
	'test' ->
	    Var = esub_guard:test_var(Guard),
	    Ty = esub_guard:test_type(Guard),
	    {[#{Var => Ty}],[#{Var => esub_type:t_not(Ty)}]};
	'if' ->
	    {TestEnvs, NegTestEnvs} = guard_to_envs(esub_guard:if_test(Guard)),
	    {ThenEnvs, NegThenEnvs} = guard_to_envs(esub_guard:if_then(Guard)),
	    {ElseEnvs, NegElseEnvs} = guard_to_envs(esub_guard:if_else(Guard)),
	    Success = join_env_lists(TestEnvs, ThenEnvs) ++
		join_env_lists(NegTestEnvs, ElseEnvs),
	    Failure = join_env_lists(TestEnvs, NegThenEnvs) ++
		join_env_lists(NegTestEnvs, NegElseEnvs),
	    {Success, Failure};
	'not' ->
	    {Success, Failure} = guard_to_envs(esub_guard:not_guard(Guard)),
	    {Failure, Success}
    end.

join_env_lists(Es1, Es2) ->
    lists:flatmap(fun(E1) ->
			  lists:map(fun(E2) ->
					    esub_env:join(E1, E2)
				    end, Es2)
		  end, Es1).




%%====================================================================
%% Internal functions
%%====================================================================

parse_command("otp") -> {ok, otp}.
