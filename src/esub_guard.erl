-module(esub_guard).
-export([get_ann/1,set_ann/2,update_ann/3]).

-export([g_true/0,g_false/0,g_test/2,test_type/1,test_var/1,g_eq/2,eq_lit/1,
	 eq_var/1,g_if/3,if_test/1,if_then/1,if_else/1]).

-export([type/1,format/1]).

-export_type([g_true/0,g_false/0,g_test/0,g_eq/0,g_if/0,guard/0]).

-define(ANN_ELEM, 2).

-type var() :: atom().

-record(g_true, {ann = #{}}).
-record(g_false, {ann = #{}}).
-record(g_test, {ann = #{}, type :: esub_type:name() , var :: var()}).
-record(g_eq, {ann = #{}, lit :: any(), var :: var()}).
-record(g_if, {ann = #{}, test :: guard(), then :: guard(), else :: guard()}).

-type g_true() :: #g_true{}.
-type g_false() :: #g_false{}.
-type g_eq() :: #g_eq{}.
-type g_test() :: #g_test{}.
-type g_if() :: #g_if{}.

-type guard() :: g_true() | g_false() | g_eq() | g_test() | g_if().

-type type() :: 'true' | 'false' | 'eq' | 'test' | 'if'.

-spec get_ann(guard()) -> any() | 'undefined'.
get_ann(Guard) ->
    element(?ANN_ELEM, Guard).

-spec set_ann(guard(), any()) -> guard().
set_ann(Guard, Ann) ->
    setelement(?ANN_ELEM, Guard, Ann).

-spec update_ann(any(), any(), guard()) -> guard().
update_ann(Key, Value, Guard) ->
    Ann = get_ann(Guard),
    NewAnn = maps:put(Key, Value, Ann),
    set_ann(Guard, NewAnn).

-spec g_true() -> g_true().
g_true() ->
    #g_true{}.

-spec g_false() -> g_false().
g_false() ->
    #g_false{}.

-spec g_test(atom(), var()) -> g_test().
g_test(Type, Var) ->
    #g_test{type=Type,var=Var}.

-spec test_type(g_test()) -> esub_type:name().
test_type(Test) ->
    Test#g_test.type.

-spec test_var(g_test()) -> var().
test_var(Test) ->
    Test#g_test.var.

-spec g_eq(any(), var()) -> g_eq().
g_eq(Lit, Var) ->
    #g_eq{lit=Lit, var=Var}.

-spec eq_lit(g_eq()) -> any().
eq_lit(Eq) ->
    Eq#g_eq.lit.

-spec eq_var(g_eq()) -> var().
eq_var(Eq) ->
    Eq#g_eq.var.

-spec g_if(guard(), guard(), guard()) -> g_if().
g_if(Test, Then, Else) ->
    #g_if{test=Test, then=Then, else=Else}.

-spec if_test(g_if()) -> guard().
if_test(If) ->
    If#g_if.test.

-spec if_then(g_if()) -> guard().
if_then(If) ->
    If#g_if.then.

-spec if_else(g_if()) -> guard().
if_else(If) ->
    If#g_if.else.

-spec type(guard()) -> type().
type(#g_true{}) -> true;
type(#g_false{}) -> false;
type(#g_test{}) -> test;
type(#g_eq{}) -> eq;
type(#g_if{}) -> 'if'.

-spec format(guard()) -> list().
format(Guard) ->
    case type(Guard) of
	'true' -> "true";
	'false' -> "false";
	'test' ->
	    Type = atom_to_list(test_type(Guard)),
	    Var = atom_to_list(test_var(Guard)),
	    ["is_", Type, "(", Var, ")"];
	'eq' ->
	    Lit = io_lib:format("~w", [eq_lit(Guard)]),
	    Var = atom_to_list(eq_var(Guard)),
	    [Var, " =:= ", Lit];
	'if' ->
	    Test = format(if_test(Guard)),
	    Then = format(if_then(Guard)),
	    Else = format(if_else(Guard)),
	    ["if ", Test, " then ", Then, " else ", Else]
	end.
