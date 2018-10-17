-module(esub_otp).
-export([analyse/1]).

-define(COMPILER_OPTIONS, [verbose]).

-define(BEHAVIOUR_ATTR, behaviour).
-define(SERVER_CALL_NAME, {'handle_call',3}).
-define(SERVER_CALL_MSG_PAT, 1).
-define(SERVER_CAST_NAME, {'handle_cast',2}).
-define(SERVER_CAST_MSG_PAT, 1).
-define(SERVER_INFO_NAME, {'handle_info',2}).
-define(SERVER_INFO_MSG_PAT, 1).
-define(SERVER_START_NAME, {'start_link',0}).
-define(EXCLUDED_DEFS, [{'module_info',0},{'module_info',1}]).

-define(START_FUNS_ATTR, 'esub_start_funs').
-define(API_FUNS_ATTR, 'esub_api_funs').

-type fun_name() :: {atom(), integer()}.

call_to_callback('gen_server', 'call') -> {'handle_call',3};
call_to_callback('gen_server', 'cast') -> {'handle_cast',2}.

known_calls('gen_server') -> ['call', 'cast'].

known_callbacks('gen_server') -> [{'handle_call',3},{'handle_cast',2}].
    
			     
    
    

info(Str) ->
    info(Str, []).

info(Fmt, Args) ->
    io:format(Fmt, Args).

err(Str) ->
    err(Str, []).

err(Fmt, Args) ->
    io:format(Fmt, Args).

analyse(Filename) ->
    info("Analysing '~s'~n", [Filename]),
    {_ModuleName, Cerl} = compile(Filename),
    info("Compiled module to Core Erlang.~n"),

    {ok, Behaviour} = get_otp_behaviour(Cerl),
    info("Module is a '~p'. Continuing.~n", [Behaviour]),

    {ok, StartFuns} = get_attr(?START_FUNS_ATTR, Cerl),
    info("Known start functions: ~p~n", [StartFuns]),

    AllServerNames = module_to_start_link_names(Cerl),
    ServerNames = lists:flatmap(fun(Name) ->
					case proplists:get_value(Name, AllServerNames) of
					    undefined ->
						[];
					    Names ->
						Names
					end
				end, StartFuns),
    info("Known server names are '~p'~n", [ServerNames]),

    {ok, APIFuns} = get_attr(?API_FUNS_ATTR, Cerl),
    info("Known API functions: ~p~n", [APIFuns]),
    
    APIDefs = lists:map(fun(Name) ->
				{ok, Def} = get_def(Name, Cerl),
				{Name, Def}
			end, APIFuns),
    
    Reqs = lists:flatmap(
	     fun({_Name, Fun}) ->
		     find_requests(Behaviour, Fun)
	     end, APIDefs),
    info("Discovered '~s' requests:~n", [Behaviour]),
    lists:foreach(fun({_Behaviour, Type, {Ref, _Msg, Src}}) ->
			  io:format("  ~p on line ~p to ~p", [Type, cerl_line(Src), Ref]),
			  lists:member(Ref, ServerNames) andalso io:format(" (known destination)"),
			  io:format("~n")
		  end, Reqs).

find_requests(Behaviour, Cerl) ->
    lists:flatmap(fun(CallName) ->
			  Calls = find_call(Behaviour, CallName, Cerl),
			  lists:map(fun(Call) ->
					    {Behaviour, CallName, call_to_request(Call)}
				    end, Calls)
	      end, known_calls(Behaviour)).

call_to_request(Call) ->
    Args = cerl:call_args(Call),
    Ref0 = lists:nth(1, Args),
    Ref = case cerl:is_literal(Ref0) of
	      true -> cerl:concrete(Ref0);
	      false -> Ref0
	  end,
    Msg = lists:nth(2, Args),
    {Ref, Msg, Call}.
    
    

%% @doc Determines the name of the <code>gen_server</code> that a call to
%% <code>start_link</code> names.
-spec call_to_start_link_names(cerl:c_call(), atom()) -> [term()].
call_to_start_link_names(Call, ModuleName) ->
    Args = cerl:call_args(Call),
    case length(Args) of
	4 ->
	    Name0 = hd(Args),
	    case cerl:is_literal(Name0) of
		true ->
		    Name = cerl:concrete(Name0),
		    [Name];
		false ->
		    []
	    end;
	3 -> [ModuleName]
    end.

%% @doc Determines the referenced <code>gen_server:start_link</code> server
%% names. The module name is returned for calls to <code>start_link/3</code>,
%% while calls to <code>start_link/4</code> return the concrete form of the
%% name if it is a literal, and nothing otherwise.
-spec module_to_start_link_names(cerl:c_module()) -> [{fun_name(), [term()]}].
module_to_start_link_names(Module) ->
    Defs = concrete_defs(Module),
    lists:map(fun({Name,Def}) ->
		      Body = cerl:fun_body(Def),
		      Calls = find_call('gen_server', 'start_link', Body),
		      ModuleName = cerl:concrete(cerl:module_name(Module)),
		      Names = lists:flatmap(fun(Call) ->
						    call_to_start_link_names(Call, ModuleName)
					    end, Calls),
		      {Name, Names}
	      end, Defs).

concrete_defs(Module) ->
    Defs = cerl:module_defs(Module),
    lists:map(fun({Name,Def}) ->
		      {cerl:var_name(Name),Def}
	      end, Defs).

find_call1(Module, Name, Cerl, Acc) ->
    case cerl:type(Cerl) of
	'call' ->
	    CallModule0 = cerl:call_module(Cerl),
	    CallName0 = cerl:call_name(Cerl),
	    
	    case cerl:is_literal(CallModule0) andalso
		cerl:is_literal(CallName0) of
		true ->
		    CallModule = cerl:concrete(CallModule0),
		    CallName = cerl:concrete(CallName0),
		    case CallModule =:= Module andalso
			CallName =:= Name of
			true ->
			    [Cerl|Acc];
			false ->
			    Acc
		    end;
		false ->
		    Acc
	    end;
	_ -> Acc
    end.

find_call(Module, Name, Cerl0) ->
    cerl_trees:fold(fun(Cerl, Acc) ->
			    find_call1(Module, Name, Cerl, Acc)
		    end, [], Cerl0).
    
    
    
compile(Filename) ->
    {ok, ModuleName} = compile:file(Filename, [report|?COMPILER_OPTIONS]),
    {ok, ModuleName, Cerl} = compile:file(Filename, [to_core, binary] ++ ?COMPILER_OPTIONS),
    {ModuleName, Cerl}.

load(Filename, ModuleName) ->
    {module, ModuleName} = code:load_abs(Filename),
    ok.

get_attr(Name, Module) ->
    Attrs = concrete_attrs(cerl:module_attrs(Module)),
    case proplists:is_defined(Name, Attrs) of
	true ->
	    {ok, proplists:get_value(Name, Attrs)};
	false ->
	    {error, undefined}
    end.
    
    
concrete_attrs(Attrs) ->
    lists:map(fun({K,V}) ->
		      {cerl:concrete(K), cerl:concrete(V)}
	      end, Attrs).

is_behaviour(Behaviour, Module) ->
    case get_attr(?BEHAVIOUR_ATTR, Module) of
	{ok, Behaviours} ->
	    lists:member(Behaviour, Behaviours);
	_ ->
	    false
    end.

get_otp_behaviour(Module) ->
    case is_behaviour('gen_server', Module) of
	true ->
	    {ok, 'gen_server'};
	false ->
	    {error, no_behaviour}
    end.

get_def(Name, Module) ->
    Defs = concrete_defs(Module),
    case proplists:is_defined(Name, Defs) of
	true ->
	    {ok, proplists:get_value(Name, Defs)};
	false ->
	    {error, undefined}
    end.

cerl_line(Cerl) ->
    Ann = cerl:get_ann(Cerl),
    case Ann of
	[Line|_] when is_integer(Line) ->
	    Line;
	_ ->
	    unknown
    end.
