-module(esub_env).

-export([get/2,join/2,negate/1]).

-type var() :: atom().
-type env() :: #{ var => esub_type:type() } | any | none.

-spec get(var(), env()) -> esub_type:type().
get(_Var, any) ->
    esub_type:t_any();
get(_Var, none) ->
    esub_type:t_not(esub_type:t_any());
get(Var, Map) ->
    case maps:find(Var, Map) of
	{ok, Ty} ->
	    Ty;
	error ->
	    esub_type:t_any()
    end.

negate(any) ->
    none;
negate(none) ->
    any;
negate(Env) ->
    maps:map(fun(_Key,Val) ->
		     esub_type:t_not(Val)
	     end, Env).

join(any, E2) ->
    E2;
join(E1, any) ->
    E1;
join(none, E2) ->
    none;
join(E1, none) ->
    none;
join(E1, E2) ->
    Keys1 = lists:usort(maps:keys(E1)),
    Keys2 = lists:usort(maps:keys(E2)),
    Keys = lists:umerge(Keys1, Keys2),
    
    Res = lists:map(fun(Key) ->
			    case {maps:get(Key, E1), maps:get(Key, E2)} of
				{{ok, T1}, {ok, T2}} ->
				    {Key, esub_type:t_and(T1, T2)};
				{{ok, T1}, error} ->
				    {Key, T1};
				{error, {ok, T2}} ->
				    {Key, T2}
			    end
		    end, Keys),
    maps:from_list(Res).




