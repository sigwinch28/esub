-module(test_all).
-include_lib("eunit/include/eunit.hrl").

setup() ->
    ?debugFmt("~p~n", [file:get_cwd()]),
    esub_log:start().

teardown(_) ->
    esub_log:stop().

test_all_test_() ->
    {setup, fun setup/0, fun teardown/1,
     [
      fun test_otp/0
      ]
    }.

test_otp() ->
    esub_otp:main(["./test/test_server"]).

