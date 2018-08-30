-module(prop_type).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-export([prop_dnf_is_dnf/1,prop_dnf_nf/1,prop_sub_impl_intersect/1]).

-import(esub_type, [is_dnf/1,dnf/1,strip/1,subtype/2,intersect/2]).

option_to_bool({ok, _}) -> true;
option_to_bool(none) -> false.
    

prop_dnf_is_dnf(doc) ->
    "All types are in DNF after being rewritten with DNF rules";
prop_dnf_is_dnf(opts) ->
    [{max_size,13},{spec_timeout,10000}].

prop_dnf_nf(doc) ->
    "All types in DNF are not changed by DNF rewriting";
prop_dnf_nf(opts) ->
    [{max_size,13},{spec_timeout,10000}].

prop_sub_impl_intersect(doc) ->
    "Subtyping implies intersection";
prop_sub_impl_intersect(opts) ->
    [{max_size,10}].



prop_dnf_is_dnf() ->
    ?FORALL(T, esub_type:type(), is_dnf(dnf(strip(T)))).

prop_dnf_nf() ->
    ?FORALL(T, esub_type:type(), equals(dnf(strip(T)), dnf(dnf(strip(T))))).

prop_sub_impl_intersect() ->
    ?FORALL({S, T}, {esub_type:atomic(), esub_type:atomic()},
	    ?IMPLIES(option_to_bool(subtype(S, T)),
		     option_to_bool(intersect(S, T)))).
