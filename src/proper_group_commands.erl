-module(proper_group_commands).
-export([parse_transform/2]).

-include("proper_internal.hrl").

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% definitions & macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-define(EMPTY_GUARD, []).
-define(CALL(F, V), call(F, V)).

-define(ADD_PREFIX(A, L), list_to_atom(atom_to_list(A) ++ "_" ++ atom_to_list(L))).

-define(ARGS, args).
-define(NEXT, next).
-define(POST, post).
-define(PRE, pre).

-define(KEY(F), ?ADD_PREFIX(?KEY, F)).
-define(KEY, ?ADD_PREFIX(?MODULE, key)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% API functions & first level internal functions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-spec parse_transform([abs_form()], [compile:option()]) -> [abs_form()].
parse_transform(Forms, _Options) ->
  case [F || F <- Forms, is_legacy_function(F)] of
    [] ->
      generate_legacy_functions(Forms);
    _FNs ->
      %io:format("~n~p~n", [_FNs]),
      Forms
  end.

is_legacy_function({function, _, Fun, Arity, _}) ->
  LegacyFunctions = [
    {command, 1},
    {precondition, 2},
    {postcondition, 3},
    {next_state, 3}],
    LegacyFunctions -- [{Fun, Arity}] =/= LegacyFunctions;
is_legacy_function(_) -> false.

generate_legacy_functions(Forms) ->
  [Module] = [M || {attribute, _, module, M} <- Forms],
  add_flag(module, Module),
  Functions = [{Fun, Arity} || {function, _, Fun, Arity, _} <- Forms],
  Commands = get_list_of_commands(Functions),
  HasWeightFn = (Functions -- [{weight, 2}] =/= Functions),
  add_flag(has_weight_fn, HasWeightFn),
  Forms ++ [
    generate__command__1(Commands),
    generate__precondition_2(Commands),
    generate__postcondition_3(Commands),
    generate__next_state_3(Commands)
  ].

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% functions to manage process dictionary
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
add_flag(Flag, Val) -> put(?KEY(Flag), Val).
get_flag(Flag) -> get(?KEY(Flag)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% functions to parse commands
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_list_of_commands(Functions) ->
  Commands = [{CmdName, [{args, ArgsFun}]} ||
    {CmdName, _} <- Functions,
    {ArgsFunName, 1} = ArgsFun <- Functions,
    ?ADD_PREFIX(CmdName, ?ARGS) =:= ArgsFunName],
  get_list_of_commands(Commands, Functions, [
    fun add_pre1_functions/2,
    fun add_pre2_functions/2,
    fun add_post_functions/2,
    fun add_next_functions/2]).

get_list_of_commands(Commands, _, []) -> Commands;
get_list_of_commands(Commands, Functions, [Action | T]) ->
  get_list_of_commands(Action(Commands, Functions), Functions, T).

add_pre1_functions(Commands, Functions) -> add_function(Commands, pre1, ?PRE, 1, Functions).
add_pre2_functions(Commands, Functions) -> add_function(Commands, pre2, ?PRE, 2, Functions).
add_post_functions(Commands, Functions) -> add_function(Commands, post, ?POST, 3, Functions).
add_next_functions(Commands, Functions) -> add_function(Commands, next, ?NEXT, 3, Functions).

add_function(Commands, Key, Prefix, Arity, Functions) ->
  CommandsWithFN = [{CmdName, [{Key, Fun} | L]} ||
    {CmdName, L} <- Commands,
    {FunName, A} = Fun <- Functions,
    ?ADD_PREFIX(CmdName, Prefix) =:= FunName,
    A =:= Arity],
  merge(1, Commands, CommandsWithFN).

merge(KeyPos, L1, L2) ->
  merge(KeyPos, [], lists:keysort(KeyPos, L1), lists:keysort(KeyPos, L2)).

merge(_, ML, L1, []) -> ML ++ L1;
merge(_, ML, [], L2) -> ML ++ L2;
merge(KP, ML, [H1 | T1] = L1, [H2 | T2] = L2) ->
  K1 = element(KP, H1), K2 = element(KP, H2),
  if
    K1 < K2 -> merge(KP, ML ++ [H1], T1, L2);
    K1 > K2 -> merge(KP, ML ++ [H2], L1, T2);
    K1 =:= K2 -> merge(KP, ML ++ [H2], T1, T2)
  end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% helper functions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
get_function(FnType, FnList) ->
  case lists:keyfind(FnType, 1, FnList) of
    false -> undefined;
    {FnType, Fn} -> Fn
  end.

call({FnName, Arity}, Variables) when length(Variables) =:= Arity ->
  Parameters = [if
                  is_atom(V) -> {var, 0, V};
                  true -> V
                end || V <- Variables],
  {call, 0, {atom, 0, FnName}, Parameters}.

commands_with_function(FnType, Commands) when is_atom(FnType) ->
  commands_with_functions([FnType], Commands).

commands_with_functions([], Commands) -> Commands;
commands_with_functions([FnType | T], Commands) ->
  commands_with_functions(T, [C || {_, L} = C <- Commands, lists:keymember(FnType, 1, L)]).

commands_with_one_of_the_functions(FnTypeList, Commands) ->
  commands_with_one_of_the_functions(FnTypeList, [], Commands).

commands_with_one_of_the_functions([], FilteredCommands, _) -> FilteredCommands;
commands_with_one_of_the_functions([FnType | T], FC1, Commands) ->
  FC2 = [C || {_, L} = C <- Commands, lists:keymember(FnType, 1, L)],
  commands_with_one_of_the_functions(T, merge(1, FC1, FC2), Commands).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% generations functions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
generate__command__1(Commands) ->
  {function, 0, command, 1,
    [{clause, 0,
      [{var, 0, 'S'}],
      [],
      [%actions
        {match, 0,
          {var, 0, 'CommandList'},
          command_list(Commands)},
        case get_flag(has_weight_fn) of
          true -> ?CALL({frequency, 1}, ['CommandList']);
          _ -> ?CALL({oneof, 1}, ['CommandList'])
        end]}]}.

command_list([Command]) -> single_command(Command);
command_list([Command | T]) ->
  {op, 0, '++', single_command(Command), command_list(T)}.

single_command({CmdName, L}) ->
  Pre1 = get_function(pre1, L),
  Args = get_function(args, L),
  Cmd = {tuple, 0, [
    {atom, 0, call},
    {atom, 0, get_flag(module)},
    {atom, 0, CmdName},
    ?CALL(Args, ['S'])]},
  Head = if
           Pre1 =:= undefined -> cons;
           true -> lc
         end,
  Body = case get_flag(has_weight_fn) of
           true -> {tuple, 0, [?CALL({weight, 2}, ['S', {atom, 0, CmdName}]), Cmd]};
           _ -> Cmd
         end,
  Tail = if
           Pre1 =:= undefined -> {nil, 0};
           true -> [?CALL(Pre1, ['S'])]
         end,
  {Head, 0, Body, Tail}.

generate__precondition_2(Commands) ->
  PreFunctions = [{CmdName, get_function(pre1, L), get_function(pre2, L)} ||
    {CmdName, L} <- commands_with_one_of_the_functions([pre1, pre2], Commands)],
  {function, 0, precondition, 2,
      [precondition_clause(C, F1, F2) || {C, F1, F2} <- PreFunctions] ++
      [%default clause
        {clause, 0,
          [{var, 0, '_'}, {var, 0, '_'}],
          ?EMPTY_GUARD,
          [{atom, 0, true}]}]}.

precondition_clause(Cmd, Pre1, Pre2) ->
  {clause, 0,
    [%params
      {var, 0, 'S'},
      {tuple, 0,
        [{atom, 0, call},
          {var, 0, '_'},
          {atom, 0, Cmd},
          {var, 0, if
                     Pre2 =:= undefined -> '_Args';
                     true -> 'Args'
                   end}]}],
    ?EMPTY_GUARD,
    [%actions
      if
        Pre1 =/= undefined, Pre2 =/= undefined ->
          {op, 0, 'andalso', ?CALL(Pre1, ['S']), ?CALL(Pre2, ['S', 'Args'])};
        Pre2 =/= undefined -> ?CALL(Pre2, ['S', 'Args']);
        Pre1 =/= undefined -> ?CALL(Pre1, ['S'])
      end]}.

generate__postcondition_3(Commands) ->
  PostFunctions = [{CmdName, get_function(post, L)} ||
    {CmdName, L} <- commands_with_function(post, Commands)],
  {function, 0, postcondition, 3,
      [postcondition_clause(C, F) || {C, F} <- PostFunctions] ++
      [%default clause
        {clause, 0,
          [{var, 0, '_'}, {var, 0, '_'}, {var, 0, '_'}],
          ?EMPTY_GUARD,
          [{atom, 0, true}]}]}.

postcondition_clause(Cmd, PostFN) ->
  {clause, 0,
    [%params
      {var, 0, 'S'},
      {tuple, 0, [
        {atom, 0, call},
        {var, 0, '_'},
        {atom, 0, Cmd},
        {var, 0, 'Args'}]},
      {var, 0, 'Res'}],
    ?EMPTY_GUARD,
    [%actions
      ?CALL(PostFN, ['S', 'Args', 'Res'])]}.

generate__next_state_3(Commands) ->
  NextFunctions = [{CmdName, get_function(next, L)} ||
    {CmdName, L} <- commands_with_function(next, Commands)],
  {function, 0, next_state, 3,
      [next_state_clause(C, F) || {C, F} <- NextFunctions] ++
      [%default clause
        {clause, 0,
          [{var, 0, 'S'}, {var, 0, '_'}, {var, 0, '_'}],
          ?EMPTY_GUARD,
          [{var, 0, 'S'}]}]}.

next_state_clause(Cmd, NextFn) ->
  {clause, 0,
    [%params
      {var, 0, 'S'},
      {var, 0, 'V'},
      {tuple, 0, [
        {atom, 0, call},
        {var, 0, '_'},
        {atom, 0, Cmd},
        {var, 0, 'Args'}]}],
    ?EMPTY_GUARD,
    [%actions
      ?CALL(NextFn, ['S', 'V', 'Args'])]}.
