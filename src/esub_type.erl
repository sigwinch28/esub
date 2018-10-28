-module(esub_type).
-export([get_ann/1,set_ann/2,update_ann/3]).

-export([t_any/0,t_atom/0,t_boolean/0,t_number/0,t_integer/0,t_tuple/0,
	 t_tuple/1,t_singleton/1,t_singleton/2,t_not/1,t_or/2,t_and/2]).
-export([tuple_types/1,singleton_type/1,singleton_value/1,
	 not_type/1,set_not_type/2,or_left/1,set_or_left/2,or_right/1,
	 set_or_right/2,and_left/1,set_and_left/2,and_right/1,set_and_right/2]).

-export([format/1,name/1,atom_to_type/1,strip/1,eq/2]).
-export([dnf_plus/1,dnf_to_canonical/1,dnf/1,intersect/2,subtype/2,is_dnf/1,atomic_subtype/2]).

-export_type([t_any/0,t_atom/0,t_boolean/0,t_number/0,t_integer/0,
	      t_tuple/1,t_singleton/0,t_not/0,t_or/0,t_and/0,atomic/0,
	      type/0]).


-define(ANN_ELEM, 2).

-type etype() :: atom() | boolean() | number() | integer().

-record(t_any, {ann = #{}}).
-record(t_atom, {ann = #{}}).
-record(t_boolean, {ann = #{}}).
-record(t_number, {ann = #{}}).
-record(t_integer, {ann = #{}}).
-record(t_tuple, {ann = #{}, types}).
-record(t_singleton, {ann = #{}, type :: atomic(), value :: etype()}).
-record(t_not, {ann = #{}, type :: type()}).
-record(t_or, {ann = #{}, left :: type(), right :: type()}).
-record(t_and, {ann = #{}, left :: type(), right :: type()}).

-type t_any() :: #t_any{}.
-type t_atom() :: #t_atom{}.
-type t_boolean() :: #t_boolean{}.
-type t_number() :: #t_number{}.
-type t_integer() :: #t_integer{}.
-type t_tuple(A) :: #t_tuple{ types :: [A]}.
-type t_singleton() :: #t_singleton{type :: atomic()}.
-type t_not() :: #t_not{type :: type()}.
-type t_or() :: #t_or{left :: type(), right :: type()}.
-type t_and() :: #t_and{left :: type(), right :: type()}.

-type atomic() :: t_any() | t_atom() | t_boolean() | t_number() | t_integer()
		  | t_tuple(atomic()).

-type type() :: t_any() | t_atom() | t_boolean() | t_number() | t_integer() |
	       t_tuple(type()) | t_singleton() | t_not() | t_or() | t_and().

-type type_name() :: 'any' | 'atom' | 'boolean' | 'number' | 'integer' | 'tuple'
		  | 'singleton' | 'not' | 'or' | 'and'.


%%==============================================================================
%% Type definitions
%%==============================================================================

%%
%% annotation helpers
%%

-spec get_ann(type()) -> any() | 'undefined'.
get_ann(Ty) ->
    element(?ANN_ELEM, Ty).

-spec set_ann(type(), any()) -> type().
set_ann(Ty, Ann) ->
    setelement(?ANN_ELEM, Ty, Ann).

-spec update_ann(any(), any(), type()) -> type().
update_ann(Key, Value, Ty) ->
    Ann = get_ann(Ty),
    NewAnn = maps:put(Key, Value, Ann),
    set_ann(Ty, NewAnn).

%% wildcard type
-spec t_any() -> t_any().
t_any() ->
    #t_any{}.

%% erlang atoms
-spec t_atom() -> t_atom().
t_atom() ->
    #t_atom{}.

%% erlang atoms of value `true` and `false`
-spec t_boolean() -> t_boolean().
t_boolean() ->
    #t_boolean{}.

%% erlang numbers
-spec t_number() -> t_number().
t_number() ->
    #t_number{}.

%% erlang integers
-spec t_integer() -> t_integer().
t_integer() ->
    #t_integer{}.

%% erlang tuple of unknown size
-spec t_tuple() -> t_tuple(any()).
t_tuple() ->
    #t_tuple{}.

%% erlang tuple of known size and element types
-spec t_tuple([A]) -> t_tuple(A).
t_tuple(Types) ->
    #t_tuple{types=Types}.

%% a type, with a specific erlang value
-spec t_singleton(type(), any()) -> t_singleton().
t_singleton(Type, Value) ->
    #t_singleton{type=Type, value=Value}.

%% a specific erlang value
-spec t_singleton(any()) -> t_singleton().
t_singleton(Value) ->
    TypeName = type_of(Value),
    Type = atom_to_type(TypeName),
    t_singleton(Type, Value).

%% negation of a type
-spec t_not(type()) -> t_not().
t_not(Type) ->
    #t_not{type=Type}.

%% option between two types
-spec t_or(type(), type()) -> t_or().
t_or(Left, Right) ->
    #t_or{left=Left, right=Right}.

%% overlap of two types
-spec t_and(type(), type()) -> t_and().
t_and(Left, Right) ->
    #t_and{left=Left, right=Right}.

%% get the element types of a tuple
-spec tuple_types(t_tuple(A)) -> list(A) | 'undefined'.
tuple_types(Tuple) ->
    Tuple#t_tuple.types.

%% update the types of a tuple
-spec set_tuple_types(t_tuple(A), list(type()) | 'undefined') -> t_tuple(A).
set_tuple_types(Tuple, Types)  ->
    Tuple#t_tuple{types=Types}.

%% get the type of a singleton
-spec singleton_type(t_singleton()) -> type().
singleton_type(Singleton) ->
    Singleton#t_singleton.type.

%% get the value of a singleton
-spec singleton_value(t_singleton()) -> any().
singleton_value(Singleton) ->
    Singleton#t_singleton.value.

%% get the negated type
-spec not_type(t_not()) -> type().
not_type(Not) ->
    Not#t_not.type.

%% set the negated type
-spec set_not_type(t_not(), type()) -> t_not().
set_not_type(Not, Type) ->
    Not#t_not{type=Type}.

%% get the left of an or type
-spec or_left(t_or()) -> type().
or_left(Or) ->
    Or#t_or.left.

-spec set_or_left(t_or(), type()) -> t_or().
set_or_left(Or, Left) ->
    Or#t_or{left=Left}.

-spec or_right(t_or()) -> type().
or_right(Or) ->
    Or#t_or.right.

-spec set_or_right(t_or(), type()) -> t_or().
set_or_right(Or, Right) ->
    Or#t_or{right=Right}.

-spec and_left(t_and()) -> type().
and_left(And) ->
    And#t_and.left.

-spec set_and_left(t_and(), type()) -> t_and().
set_and_left(And, Left) ->
    And#t_and{left=Left}.

-spec and_right(t_and()) -> type().
and_right(And) ->
    And#t_and.right.

-spec set_and_right(t_and(), type()) -> t_and().
set_and_right(And, Right) ->
    And#t_and{right=Right}.

%% get the name of a type, instead of a record.
-spec name(type()) -> type_name().
name(#t_any{}) -> any;
name(#t_atom{}) -> atom;
name(#t_boolean{}) -> boolean;
name(#t_number{}) -> number;
name(#t_integer{}) -> integer;
name(#t_tuple{}) -> tuple;
name(#t_singleton{}) -> singleton;
name(#t_not{}) -> 'not';
name(#t_or{}) -> 'or';
name(#t_and{}) -> 'and'.

-spec atom_to_type(atom()) -> type().
atom_to_type(any) -> t_any();
atom_to_type(atom) -> t_atom();
atom_to_type(boolean) -> t_boolean();
atom_to_type(number) -> t_number();
atom_to_type(integer) -> t_integer().

-spec type_of(term()) -> atom().
type_of(X) when is_boolean(X) -> boolean;
type_of(X) when is_atom(X) -> atom.

%%
%% pretty printing of types
%%

-spec format(atom()) -> list().
format(Ety) ->
    case name(Ety) of
	any -> "any";
	atom -> "atom";
	boolean -> "boolean";
	number -> "number";
	integer -> "integer";
	tuple ->
	    Elems = case tuple_types(Ety) of
			undefined ->
			    [];
			Types ->
			    lists:map(fun format/1, Types)
		    end,
	    ["{", lists:join(", ", Elems), "}"];
	singleton ->
	    io:format("~w~n", [singleton_type(Ety)]),
	    Type = format(singleton_type(Ety)),
	    Val = io_lib:format("~w", [singleton_value(Ety)]),
	    ["<", Val, ",", Type, ">"];
	'not' ->
	    ["~", format(not_type(Ety))];
	'or' ->
	    Left = format(or_left(Ety)),
	    Right = format(or_right(Ety)),
	    ["(", Left, " \\/ ", Right, ")"];
	'and' ->
	    Left = format(and_left(Ety)),
	    Right = format(and_right(Ety)),
	    ["(", Left, " /\\ ", Right, ")"]
    end.

%%==============================================================================
%% Main API
%%==============================================================================

%%
%% Returns true when the first argument is a subtype of the second. returns
%% false otherwise.
%%
-spec subtype(type(), type()) -> boolean().
subtype(S, T) ->
    Void = t_not(t_any()),
    eq(Void, dnf_plus(t_and(S, t_not(T)))).

%%==============================================================================
%% Type helpers
%%==============================================================================

%% fold a function over a type, bottom-up.
-spec fold(fun((type()) -> type()), type()) -> type().
fold(F, Type) ->
    case name(Type) of
	any -> F(Type);
	atom -> F(Type);
	boolean -> F(Type);
	number -> F(Type);
	integer -> F(Type);
	singleton ->
	    NewType = fold(F, singleton_type(Type)),
	    F(t_singleton(NewType, singleton_value(Type)));
	tuple ->
	    NewTypes = case tuple_types(Type) of
			   undefined -> undefined;
			   Types -> lists:map(fun(T) -> fold(F, T) end, Types)
		       end,
	    F(t_tuple(NewTypes));
	'not' ->
	    Not = fold(F, not_type(Type)),
	    F(t_not(Not));
	'and' ->
	    Left = fold(F, and_left(Type)),
	    Right = fold(F, and_right(Type)),
	    F(t_and(Left, Right));
	'or' ->
	    Left = fold(F, or_left(Type)),
	    Right = fold(F, or_right(Type)),
	    F(t_or(Left, Right))
    end.

%% strip all annotations from a type
-spec strip(type()) -> type().
strip(Type) ->
    fold(fun(T) -> set_ann(T, #{}) end, Type).

%% check whether two stripped types are equal according to `=:=`
%% this is not some idea of "type equivalence"
-spec eq(type(), type()) -> type().
eq(Type1, Type2) ->
    strip(Type1) =:= strip(Type2).

%%
%% Type rewriting
%%

%% repeatedly folds the provided function over a type until no more changes
%% occur.
-spec rewrite(fun((type()) -> type()), type()) -> type().
rewrite(F, Step0) ->
    Step1 = fold(F, Step0),
    case eq(Step0,Step1) of
	true ->
	    Step1;
	false ->
	    rewrite(F, Step1)
    end.

%% applies the provided function to the second argument and the
%% head of the list. if the function returns ok, return the associated
%% term and all elements of the second and third arguments (i.e. those
%% which were not used in the rewrite). If the application yields none,
%% then move the head of the list to 'Unused', and recurse.
-spec rewrite_list1(fun((A,A) -> {ok, A} | none), A, [A], [A]) -> [A].
rewrite_list1(_F, _Term, [], _Unused) ->
    none;
rewrite_list1(F, Term, [H|T], Unused) ->
    case F(Term,H) of
	{ok, NewTerm} ->
	    %% return the new term, and the unprocessed/unused elements
	    {ok, NewTerm, T++Unused};
	none ->
	    rewrite_list1(F, Term, T, [H|Unused])
    end.

%% takes a rewrite function, which takes two arguments and either
%% returns ok and a result, or none. The function is recursively
%% applied to pairs of elements in the list until no more
%% rewrites occur.
-spec rewrite_list(fun((A,A) -> {ok, A} | none), [A]) -> [A].
rewrite_list(_F, []) ->
    [];
rewrite_list(_F, [Term]) ->
    [Term];
rewrite_list(F, [Term|Terms]) ->
    case rewrite_list1(F, Term, Terms, []) of
	{ok, NewTerm, Unused} ->
	    rewrite_list(F, [NewTerm|Unused]);
	none ->
	    [Term|Terms]
    end.

%%
%% Type identification helpers
%%

-spec is_primitive(type()) -> boolean().
is_primitive(Ty) ->
    case name(Ty) of
	any ->
	    true;
	atom ->
	    true;
	boolean ->
	    true;
	number ->
	    true;
	integer ->
	    true;
	tuple ->
	    case tuple_types(Ty) of
		undefined -> true;
		Tys -> lists:all(fun is_primitive/1, Tys)
	    end;
	singleton ->
	    is_primitive(singleton_type(Ty));
	'not' ->
	    false;
	'or' ->
	    false;
	'and' ->
	    false
    end.

is_void(Type) ->
    case name(Type) of
	'not' ->
	    name(not_type(Type)) =:= any;
	'or' ->
	    is_void(or_left(Type)) andalso is_void(or_right(Type));
	_ ->
	    false
    end.

%%==============================================================================
%% Positive atomic type operators
%%==============================================================================

%% intersection of positive types

-spec intersect(type(), type()) -> {ok, type()} | none.
intersect(T1, T2) ->
    case {name(T1),name(T2)} of
	{_, any} -> {ok, T1};
	{any, _} -> {ok, T2};
	{boolean, atom} -> {ok, T1};
	{atom, boolean} -> {ok, T2};
	{integer, number} -> {ok, T1};
	{number, integer} -> {ok, T2};
	{tuple, tuple} ->
	    case elems_intersect(tuple_types(T1), tuple_types(T2)) of
		{ok, Ts} ->
		    {ok, t_tuple(Ts)};
		none ->
		    none
	    end;
	{singleton, singleton} ->
	    case singleton_value(T1) =:= singleton_value(T2) of
		true ->
		    case intersect(singleton_type(T1), singleton_type(T2)) of
			{ok, T} ->
			    {ok, t_singleton(T, singleton_value(T1))};
			none ->
			    none
		    end;
		false ->
		    none
	    end;
	{singleton, _} ->
	    case intersect(singleton_type(T1), T2) of
		{ok, T} ->
		    {ok, t_singleton(T, singleton_value(T1))};
		none ->
		    none
	    end;
	{_, singleton} ->
	    case intersect(T1, singleton_type(T2)) of
		{ok, T} ->
		    {ok, t_singleton(T, singleton_value(T2))};
		none ->
		    none
	    end;
	_ ->
	    case eq(T1, T2) of
		true ->
		    {ok, T1};
		false ->
		    none
	    end
    end.

elems_intersect(undefined, undefined) ->
    {ok, undefined};
elems_intersect(Xs, undefined) ->
    {ok, Xs};
elems_intersect(undefined, Ys) ->
    {ok, Ys};
elems_intersect(Xs, Ys) ->
    case length(Xs) =:= length(Ys) of
	true ->
	    lift_option_list(lists:zipwith(fun intersect/2, Xs, Ys));
	false ->
	    none
    end.

%%
%% subtyping of positive types
%%

-spec atomic_subtype(type(), type()) -> {ok, type()} | none.
atomic_subtype(T, #t_any{}) -> {ok, T};
atomic_subtype(#t_boolean{} = T, #t_atom{}) -> {ok, T};
atomic_subtype(#t_integer{} = T, #t_number{}) -> {ok, T};
atomic_subtype(#t_singleton{} = S, #t_singleton{} = T) ->
    case atomic_subtype(singleton_type(S), singleton_type(T)) of
	none -> none;
	{ok, Type} ->
	    Res = S#t_singleton{type=Type},
	    case singleton_value(S) =:= singleton_value(T) of
		true ->
		    {ok, Res};
		false ->
		    none
	    end
    end;
atomic_subtype(#t_tuple{} = S, #t_tuple{} = T) ->
    case elems_subtype(tuple_types(S), tuple_types(T)) of
	{ok, Types} -> {ok, set_tuple_types(S, Types)};
	none -> none
    end;
atomic_subtype(S, T) ->
    case eq(S, T) of
	true -> {ok, S};
	false -> none
    end.

elems_subtype(undefined, undefined) ->
    {ok, undefined};
elems_subtype(Xs, undefined) ->
    {ok, Xs};
elems_subtype(undefined, Ys) ->
    {ok, Ys};
elems_subtype(Xs, Ys) ->
    case length(Xs) =:= length(Ys) of
	true ->
	    lift_option_list(lists:zipwith(fun atomic_subtype/2, Xs, Ys));
	false ->
	    none
    end.

%%==============================================================================
%% General type functions (i.e. including negation, intersection, and union)
%%==============================================================================

%%
%% DNF+ form
%%
%% i.e. canonical(dnf(T))

%% convert a type into DNF form, then canonicalise.
-spec dnf_plus(type()) -> type().
dnf_plus(T) ->
    dnf_to_canonical(dnf(T)).

%%
%% Disjunctive normal form
%%
%% (can cause exponential explosion in size)
%%
-spec dnf(type()) -> type().
dnf(Type) ->
    rewrite(fun dnf1/1, Type).


-spec dnf1(type()) -> type().
dnf1(Type) ->
    case name(Type) of
	'not' ->
	    Not = not_type(Type),
	    case name(Not) of
		'not' ->
		    not_type(Not);
		'and' ->
		    Left = and_left(Not),
		    Right = and_right(Not),
		    t_or(t_not(Left), t_not(Right));
		'or' ->
		    Left = or_left(Not),
		    Right = or_right(Not),
		    t_and(t_not(Left), t_not(Right));
		_ ->
		    Type
	    end;
	'and' ->
	    Left = and_left(Type),
	    Right = and_right(Type),
	    case name(Left) of
		'or' ->
		    t_or(t_and(or_left(Left), Right),
			 t_and(or_right(Left), Right));
		_ ->
		    case name(Right) of
			'or' ->
			    t_or(t_and(Left, or_left(Right)),
				 t_and(Left, or_right(Right)));
			_ ->
			    Type
		    end
	    end;
	'tuple' ->
	    case tuple_types(Type) of
		undefined ->
		    Type;
		Types ->
		    Res = dnf1_tuple(Types, []),
		    %io:format("Rewritten tuple: ~n~p~n~p~n", [Type, Res]),
		    Res
	    end;
	_ ->
	    Type
    end.

dnf1_tuple([], Acc) ->
    t_tuple(lists:reverse(Acc));
dnf1_tuple([Type|Types], Acc) ->
    case name(Type) of
	'or' ->
	    Left = or_left(Type),
	    Right = or_right(Type),
	    LeftElems = lists:append(lists:reverse([Left|Acc]), Types),
	    RightElems = lists:append(lists:reverse([Right|Acc]), Types),
	    t_or(t_tuple(LeftElems), t_tuple(RightElems));
	'and' ->
	    Left = and_left(Type),
	    Right = and_right(Type),
	    LeftElems = lists:append(lists:reverse([Left|Acc]), Types),
	    RightElems = lists:append(lists:reverse([Right|Acc]), Types),
	    t_and(t_tuple(LeftElems), t_tuple(RightElems));
	'not' ->
	    Not = not_type(Type),
	    LeftElems = lists:append(lists:reverse([t_any()|Acc]), Types),
	    RightElems = lists:append(lists:reverse([Not|Acc]), Types),
	    t_and(t_tuple(LeftElems), t_not(t_tuple(RightElems)));
	_ ->
	    dnf1_tuple(Types, [Type|Acc])
    end.

%%
%% Conjunct canonicalisation (of DNF types)
%%

%% canonicalise the provided DNF.
%% As this is in DNF, we know that:
%%  - the top level connectives are all `or`
%%  - all other connectives will be `and`.
%%  - negation will only be applied to atomic types.
%%
%% The result is a type which has been entirely canonicalised.
%%
-spec dnf_to_canonical(type()) -> type().
dnf_to_canonical(Type) ->
    Disjs = disj_to_list(Type),
    Res = lists:map(fun(Disj) ->
			    Conjs = conj_to_list(Disj),
			    ConjRes = rewrite_list(fun canon1/2, Conjs),
			    list_to_conj(ConjRes)
		    end, Disjs),
    list_to_disj(Res).

%% canonicalises a type of form T1 /\ T2, where the arguments to this
%% function are T1 and T2.
%%
%% Assuming T1 and T2 are of the form LHS => rewrite to RHS.
%%
%% Rewrite rules:
%%  void /\ _ => void -- (symmetric)
%%  t1 /\ t2 when is_atomic(t1) /\ is_atomic(t2) => t1 `intersect` t2 -- ditto
%%  t1 /\ ¬ t2 => ... -- See canon1_neg/1 for rewrite rules
%%  ¬ t1 /\ ¬ t2 when t1 > t2 => ¬ t1 -- "absorb" the "smaller" type (which is a proper subset)

-spec canon1(type(), type()) -> {ok, type()} | type().
canon1(Left, Right) ->
    case is_void(Left) or is_void(Right) of
	true -> {ok, t_not(t_any())};
	false ->
	    case {name(Left),name(Right)} of
		{'not', 'not'} ->
		    case intersect(not_type(Left), not_type(Right)) of
			{ok, NewType} -> {ok, t_not(NewType)};
			_ -> none
		    end;
		{'not', _} ->
		    canon1_neg(Right, not_type(Left));
		{_, 'not'} ->
		    canon1_neg(Left, not_type(Right));
		_ ->
		    case is_primitive(Left) andalso is_primitive(Right) of
			true ->
			    case intersect(Left, Right) of
				{ok, NewType} -> NewType;
				none -> {ok, t_not(t_any())}
			    end;
			false ->
			    none
		    end
	    end
    end.

%% Performs canonicalisation of a type of form T1 /\ ¬ T2, where the arguments
%% to this function are T1 and T2.
%%
%% Rewrite rules:
%%  T1 /\ ¬ T2 when T1 < T2 => void() -- cannot have t1 without t2, so uninhabited
%%  T1 /\ ¬ T2 when !(T1 `intersect` T2) => T1 -- no overlap, so ¬T2 has no effect on T1
%%  T1 /\ ¬ T2 when !(T1 > T2) => T1 /\ ¬(T1 `intersect` T2) -- for partial overlap of a negative component. removes the component which is out of the domain of T1.
%%
%% example of partial overlap:
%%  {any, int} /\ ¬ {int, any}
%% rewrites to:
%%  {any, int} /\ ¬ ({any, int} `intersect` {int, any})
%%  {any, int} /\ ¬ ({int, int})

-spec canon1_neg(type(), type()) -> {ok, type()} | none.
canon1_neg(Type1, Type2) ->
    case atomic_subtype(Type1, Type2) of
	{ok, _} ->
	    {ok, t_not(t_any())};
	none ->
	    case intersect(Type1, Type2) of
		none ->
		    {ok, Type1};
		{ok, _} ->
		    case atomic_subtype(Type2, Type1) of
			none ->
			    IntersectType = case intersect(Type1, Type2) of
						none -> t_not(t_any());
						{ok, T} -> T
					    end,
			    {ok, t_and(Type1, t_not(IntersectType))};
			_ -> none
		    end
	    end
    end.










has_ors(Type) ->
    case name(Type) of
	any -> false;
	atom -> false;
	boolean -> false;
	number -> false;
	integer -> false;
	tuple ->
	    case tuple_types(Type) of
		undefined -> false;
		Types -> lists:any(fun has_ors/1, Types)
	    end;
	singleton ->
	    has_ors(singleton_type(Type));
	'not' ->
	    has_ors(not_type(Type));
	'and' ->
	    has_ors(and_left(Type)) orelse has_ors(and_right(Type));
	'or' ->
	    true
    end.

-spec is_dnf(type()) -> boolean().
is_dnf(Type) ->
    case name(Type) of
	any -> true;
	atom -> true;
	boolean -> true;
	number -> true;
	integer -> true;
	tuple ->
	    case tuple_types(Type) of
		undefined -> true;
		Types -> lists:all(fun is_primitive/1, Types)
	    end;
	singleton ->
	    is_primitive(singleton_type(Type));
	'not' ->
	    is_dnf(not_type(Type)) andalso (is_primitive(not_type(Type)));
	'and' ->
	    Left = and_left(Type),
	    Right = and_right(Type),
	    is_dnf(Left) andalso (not has_ors(Left)) andalso
		is_dnf(Right) andalso (not has_ors(Right));
	'or' ->
	    is_dnf(or_left(Type)) andalso is_dnf(or_right(Type))
    end.







-spec lift_option_list([{ok, A} | none]) -> {ok, [A]} | none.
lift_option_list([]) ->
    {ok, []};
lift_option_list([{ok, X}|Xs]) ->
    case lift_option_list(Xs) of
	none -> none;
	{ok, Xs2} -> {ok, [X|Xs2]}
    end;
lift_option_list([none|_]) ->
    none.



%% splits types of the form t_and(T1, T2) into conj_list(T1) ++ conj_list(T2).
-spec conj_to_list(type()) -> [type()].
conj_to_list(T) ->
    case name(T) of
	'and' ->
	    conj_to_list(and_left(T)) ++ conj_to_list(and_right(T));
	_ ->
	    [T]
    end.

%% takes a list of types and folds them into a single unbalanced
%% right-"heavy" `and` type, without adding any additional elements.
-spec list_to_conj([type()]) -> t_and().
list_to_conj([T]) ->
    T;
list_to_conj([T|Ts]) ->
    t_and(T, list_to_conj(Ts)).

%% splits types of the form t_or(T1, T2) into disj_to_list(T1) ++ disj_to_list(T2).
-spec disj_to_list(type()) -> [type()].
disj_to_list(T) ->
    case name(T) of
	'or' ->
	    conj_to_list(or_left(T)) ++ conj_to_list(or_right(T));
	_ ->
	    [T]
    end.

list_to_disj([T]) ->
    T;
list_to_disj([T|Ts]) ->
    t_or(T, list_to_disj(Ts)).
