-module(esub_core).

-export([c_guard_to_guard/1]).

-spec c_guard_to_guard(cerl:cerl()) -> esub_guard:guard().
c_guard_to_guard(Guard) ->
    case cerl:type(Guard) of
	call ->
	    c_call_to_guard(Guard);
	'try' ->
	    % all guards are of the form `try e of var -> var catch var -> false
	    c_guard_to_guard(cerl:try_arg(Guard));
	'let' ->
	    Subst = cerl_subst(
	      cerl:let_vars(Guard),
	      cerl:let_arg(Guard),
	      cerl:let_body(Guard)
	     ),
	    c_guard_to_guard(Subst);
	'case' ->
	    case is_c_compiler_generated(Guard) of
		true ->
		    % short-circuiting boolean operation
		    Test = c_guard_to_guard(cerl:case_arg(Guard)),
		    % These take the form of a true/false branch,
		    % another true/false branch, and a catch-all for
		    % internal bollocks of "this function which is
		    % "known to return true/false might not do so",
		    % and we discard it.
		    [A,B,_Catchall] = cerl:case_clauses(Guard),
		    AGuard = c_guard_to_guard(cerl:clause_body(A)),
		    BGuard = c_guard_to_guard(cerl:clause_body(B)),
		    % the compiler-generated clauses only have one
		    % pattern, and the pattern is either the literal
		    % true or false
		    {ABool,BBool} =
			{cerl:concrete(hd(cerl:clause_pats(A))),
			 cerl:concrete(hd(cerl:clause_pats(B)))},
		    % create an if statement, considering the ordering
		    % of the true/false branches
		    case {ABool, BBool} of
			{true, false} ->
			    esub_type:update_ann(src, Guard,
						 esub_guard:g_if(Test, AGuard, BGuard));
			{false, true} ->
			    esub_type:update_ann(src, Guard,
						 esub_guard:g_if(Test, BGuard, AGuard))
		    end
	    end;
	'literal' ->
	    case cerl:concrete(Guard) of
		true -> esub_guard:update_ann(src, Guard, esub_guard:g_true());
		false -> esub_guard:update_ann(src, Guard, esub_guard:g_false())
	    end
    end.

-spec cerl_subst([cerl:cerl()], cerl:cerl(), cerl:cerl()) -> cerl:cerl().
cerl_subst(Vars, Value, Node) ->
    lists:foldl(fun(V,Acc) ->
			cerl_subst1(cerl:car_name(V),Value,Acc)
		end, Node, Vars).

-spec cerl_subst1(cerl:cerl(), cerl:cerl(), cerl:cerl()) -> cerl:cerl().
cerl_subst1(Var, Value, Tree) ->
    cerl_trees:map(fun(Node) ->
			   case cerl:type(Node) of
			       'var' ->
				   case cerl:var_name(Node) of
				       Var -> Value;
				       _ -> Node
				   end;
			       _ -> Node
			   end
		   end, Tree).

-spec is_c_call_concrete(cerl:c_call()) -> {true, atom(), atom()} | false.
is_c_call_concrete(Call) ->
    Module = cerl:call_module(Call),
    case cerl:is_literal(Module) of
	true ->
	    Name = cerl:call_name(Call),
	    case cerl:is_literal(Name) of
		true ->
		    {true, cerl:concrete(Module), cerl:concrete(Name)};
		false ->
		    false
	    end;
	false ->
	    false
    end.

c_erlang_call_to_test(Type, Call) ->
    case cerl:call_args(Call) of
	[Arg] ->
	    case cerl:type(Arg) of
		var ->
		    Var = cerl:var_name(Arg),
		    Ty = esub_type:atom_to_type(Type),
		    esub_guard:update_ann(src, Call, esub_guard:g_test(Ty, Var))
	    end
    end.

c_erlang_call_to_guard(Call) ->
    Name = cerl:concrete(cerl:call_name(Call)),
    Args = cerl:call_args(Call),
    case Name of
	% simple type tests
	'is_atom' ->
	    c_erlang_call_to_test(atom, Call);
	'is_boolean' ->
	    c_erlang_call_to_test(boolean, Call);
	'is_number' ->
	    c_erlang_call_to_test(number, Call);
	'is_integer' ->
	    c_erlang_call_to_test(integer, Call);
	'=:=' ->
	    [L, R] = Args,
	    % equalities should either be boolean
	    % coercions, or they should be value
	    % checks on individual variables
	    case is_c_compiler_generated(Call) of
		true ->
		    % this is a boolean coercion
		    c_guard_to_guard(L);
		false ->
		    case {cerl:type(L),cerl:type(R)} of
			{literal, var} ->
			    ety:g_test(cerl:concrete(L),
				       cerl:var_name(R));
			{var, literal} ->
			    ety:g_test(cerl:concrete(R),
				       cerl:var_name(L))

		    end
	    end;
	'or' ->
	    [L, R] = Args,
	    LeftGuard = c_guard_to_guard(L),
	    RightGuard = c_guard_to_guard(R),
	    ety:g_if(LeftGuard, ety:g_true(), RightGuard);
	'and' ->
	    [L, R] = Args,
	    LeftGuard = c_guard_to_guard(L),
	    RightGuard = c_guard_to_guard(R),
	    ety:g_if(LeftGuard, RightGuard, ety:g_false())
    end.

-spec is_c_compiler_generated(cerl:cerl()) -> boolean().
is_c_compiler_generated(Node) ->
    lists:member(compiler_generated, cerl:get_ann(Node)).

c_call_to_guard(Call) ->
    case is_c_call_concrete(Call) of
	{true, Module, _Name} ->
	    case Module of
		erlang ->
		    c_erlang_call_to_guard(Call);
		_Other ->
		    {error, {unknown_module, Module}}
	    end;
	false ->
	    {error, {abstract_call, Call}}
    end.    

c_pat_to_ety(Pattern, Gamma) ->
    case cerl:type(Pattern) of
	'var' ->
	    maps:get(cerl:var_name(Pattern), Gamma,
		     ety:update_ann(src, Pattern, ety:t_any()));
	'tuple' ->
	    Types = lists:map(fun(E) -> c_pat_to_ety(E, Gamma) end,
			      cerl:tuple_es(Pattern)),
	    ety:update_ann(src, Pattern, ety:t_tuple(Types))
    end.
