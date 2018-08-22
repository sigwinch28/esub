-module(foo).
-export([f/1]).

f(_) ->
    receive
	{A, B} when is_atom(A), is_integer(B); is_atom(B) ->
	    ok
    end.
