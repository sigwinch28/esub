-module(esub).

-import(esub_log, [print/1,print/2,debug/1,debug/2,fatal/2]).

%% API exports
-export([main/1]).

%%====================================================================
%% API functions
%%====================================================================

%% escript Entry point
main(Args) ->
    esub_log:start(),
    print("Esub v0.0.1~n"),
    debug("Args: ~p", [Args]),
    [RawCmd|Args1] = Args,
    case parse_command(RawCmd) of
	{ok, otp} ->
	    debug("Running command 'otp' with args ~p", [Args1]),
	    esub_otp:main(Args1);
	unknown ->
	    fatal("Unknown command '~s'", [RawCmd])
    end,
    esub_log:stop(),
    erlang:halt(0).

%%====================================================================
%% Internal functions
%%====================================================================

parse_command("otp") -> {ok, otp}.
    
