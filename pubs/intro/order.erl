-module(order).
-export([start/0]).

client(Server) ->
    Server ! 'end',
    Server ! 'begin'.

server() ->
    receive
	'begin' -> ok
    end,
    receive
	'end' -> ok
    end,
    io:format("done!~n").

start() ->
    Server = spawn(fun server/0),
    client(Server).
