-module(test_server).
-behaviour(gen_server).

-export([ok_call/1,ok_cast/1,mismatch_call/1,mismatch_cast/1]).
-export([start/0]).
-export([init/1,handle_call/3,handle_cast/2]).

start() ->
    gen_server:start({local, ?MODULE}, ?MODULE, [], []).

ok_call(Arg) ->
    gen_server:call(?MODULE, {call, Arg}).

mismatch_call(Arg) ->
    gen_server:call(?MODULE, {call_invalid, Arg}).

ok_cast(Arg) ->
    gen_server:cast(?MODULE, {cast, Arg}).

mismatch_cast(Arg) ->
    gen_server:cast(?MODULE, {cast_invalid, Arg}).

init(_Args) ->
    {ok, []}.

handle_call({call, Arg}, _From, State) when is_atom(Arg) ->
    {reply, ok, State};
handle_call({call, Arg}, _From, State) when not is_atom(Arg) ->
    {reply, ok, State};
handle_call({call_unused, _Arg}, _From, State) ->
    {reply, ok, State}.


handle_cast({cast, _Arg}, State) ->
    {noreply, State};
handle_cast({cast_unused, _Arg}, State) ->
    {noreply, State}.
