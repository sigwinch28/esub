-module(esub_debug).
-export([print/3]).
-export([use_unused/2]).

-spec use_unused(any(), any()) -> 'ok'.
use_unused(_, _) ->
    ok.

print({File,Line,{Fun,Arity}}, Fmt, Args) ->
    Res = io_lib:format(Fmt, Args),
    lists:foreach(fun(Ln) ->
			  io:format("~s:~B(~w/~B): ~s~n", [File, Line, Fun, Arity, Ln])
		  end, string:split(Res, "\n", all)).
