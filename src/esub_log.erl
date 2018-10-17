-module(esub_log).
-behaviour(gen_server).

-export([start/0,stop/0]).
-export([init/1,handle_call/3,handle_cast/2]).
-export([debug/1,debug/2,info/1,info/2,warn/1,warn/2,err/1,err/2,fatal/1,fatal/2]).
-export([print/1,print/2,indent/0,unindent/0,indent/1,unindent/1,set_level/1]).

-esub_start_funs([start/0]).
-esub_api_funs([fatal/2,log/3,print/2]).

debug(Str) ->
    debug(Str, []).

debug(Fmt, Args) ->
    log(debug, Fmt, Args).

info(Str) ->
    info(Str, []).

info(Fmt, Args) ->
    log(info, Fmt, Args).

warn(Str) ->
    warn(Str, []).

warn(Fmt, Args) ->
    log(warn, Fmt, Args).

err(Str) ->
    err(Str, []).

err(Fmt, Args) ->
    log(error, Fmt, Args).

fatal(Str) ->
    fatal(Str, []).

fatal(Fmt, Args) ->
    log(error, Fmt, Args),
    gen_server:call(?MODULE, shutdown),
    exit(fatal_error).

log(Level, Fmt, Args) ->
    Str = io_lib:format(Fmt, Args),
    gen_server:cast(?MODULE, {log, Level, Str}).

print(Str) ->
    print(Str, []).

print(Fmt, Args) ->
    Str = io_lib:format(Fmt, Args),
    gen_server:cast(?MODULE, {print, Str}).

indent() ->
    indent(1).

indent(N) ->
    gen_server:call(?MODULE, {indent, N}).

unindent() ->
    unindent(1).

unindent(N) ->
    gen_server:call(?MODULE, {unindent, N}).

set_level(Level) ->
    level_to_integer(Level),
    gen_server:call(?MODULE, {level, Level}).
    

start() ->
    gen_server:start({local, ?MODULE}, ?MODULE, [], []).

stop() ->
    gen_server:stop(?MODULE).

init(_) ->
    {ok, {debug, 0}}.

handle_call(shutdown, _From, State) ->
    {stop, normal, ok, State};
handle_call({indent, N}, _From, {Level, Indent}) ->
    {reply, ok, {Level, Indent + N}};
handle_call({unindent, N}, _From, {Level, Indent}) ->
    {reply, ok, {Level, max(Indent - N, 0)}};
handle_call({level, NewLevel}, _From, {_Level, Indent}) ->
    {reply, ok, {NewLevel, Indent}}.


handle_cast({print, Str}, {_Level, Indent} = State) ->
    print_indent(Indent),
    io:format("~s", [Str]),
    {noreply, State};
handle_cast({log, MsgLevel, Str}, {Level, _Indent} = State) ->
    case level_to_integer(MsgLevel) >= level_to_integer(Level) of
	true ->
	    io:format("[~s] ", [level_to_list(Level)]),
	    io:format("~s", [Str]),
	    io:format("~n");
	false ->
	    ok
    end,
    {noreply, State}.

level_to_list(debug) -> "DEBUG";
level_to_list(info)  -> "INFO ";
level_to_list(warn)  -> "WARN ";
level_to_list(error) -> "ERROR";
level_to_list(fatal) -> "FATAL".

level_to_integer(debug) -> 1;
level_to_integer(info) -> 2;
level_to_integer(warn) -> 3;
level_to_integer(error) -> 4;
level_to_integer(fatal) -> 5.
    

print_indent(0) ->
    ok;
print_indent(N) when N > 0 ->
    io:format(" "),
    print_indent(N-1).
