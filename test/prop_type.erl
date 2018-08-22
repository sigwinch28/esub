-module(prop_type).

-include_lib("proper/include/proper.hrl").
-include_lib("eunit/include/eunit.hrl").

-export([prop_dnf/1]).

-import(esub_type, [is_dnf/1,dnf/1,strip/1]).

prop_dnf(doc) ->
    "All types are in DNF after being rewritten with DNF rules";
prop_dnf(opts) ->
    [{max_size,13},{spec_timeout,10000}].

prop_dnf() ->
    ?FORALL(T, esub_type:type(), is_dnf(dnf(strip(T)))).
