%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2012-2020. All Rights Reserved.
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.
%%
%% %CopyrightEnd%
%%
%% This patch adds a pass which first analyzes the first few basic
%% blocks of a function to determine if its result can be expressed as
%% a simple condition on its input parameters. The result of the
%% analysis is then used to, together with the results from the
%% ssa_opt_type_continue pass, elide calls to local functions while
%% preserving the behavior of the original program.

-module(beam_ssa_guard_chains).

-export([module/2]).

-import(lists, [foldl/3]).

-include("beam_ssa_opt.hrl").
-include("beam_types.hrl").

%-define(DEBUG, true).

-ifdef(DEBUG).
-define(dp(__String), io:format(__String)).
-define(dp(__String, __Args), io:format(__String, __Args)).
-else.
-define(dp(__String), ok).
-define(dp(__String, __Args), ok).
-endif.

-spec module(beam_ssa:b_module(), [compile:option()]) ->
          {'ok',beam_ssa:b_module()}.

module(#b_module{body=Fs0,attributes=As}=Module, Opts) ->
    Info = [function(F, Opts) || F <- Fs0],
    Guards = [ G || {_,G} <- Info],
    Fs = [ F || {F,_} <- Info],
    {ok,Module#b_module{body=Fs,attributes=[{guard_chains,Guards}|As]}}.

function(F=#b_function{bs=Bs0,args=Args,anno=Anno,cnt=Cnt0}, _Opts) ->
    MFA = maps:get(func_info, Anno),
    R = analyze_head(Bs0, Args),
    case lists:reverse(R) of % Check that the format is what we expect
        [{true,_}|_] -> ok;
        [] -> ok
    end,
    case {only_tag_tests(R), length(R) - 1} of
        {true, Len} when Len =:= 2 ->
            {Bs, Cnt} = insert_select_tag(R, Bs0, Cnt0),
            {F#b_function{bs=Bs,cnt=Cnt},{MFA,R}};
        _ ->
            {F,{MFA,[]}}
    end.

%%%
%%% Figure out if the result if this function is simply one of its
%%% arguments for a particular value and/or type of its arguments.
%%%
analyze_head(Blocks, Args) ->
    Defs = beam_ssa:definitions(Blocks),
    Uses = maps:map(fun(_, Ls) ->
                            [L || {L,_} <- Ls]
                    end, beam_ssa:uses(Blocks)),
    {_,Args2Idx} = foldl(fun(Arg, {Idx,Acc}) ->
                                 {Idx+1,[{Arg,Idx}|Acc]}
                         end, {0,[]}, Args),
    R = analyze_block(0, Blocks, maps:from_list(Args2Idx), Defs, Uses),
    add_useful_heads(R).

add_useful_heads(Result) ->
    case has_useful_heads(Result) of
        true ->
            Result;
        false -> []
    end.

has_useful_heads([_,_|_]) ->
    true;
has_useful_heads(_) ->
    false.


%%%
%%% Starting from a block, investigate if we, from known arguments,
%%% can statically determine the return value of the function by just
%%% looking at the initial argument pattern matching guards.
%%%
%%% We assume a code structure looking like this:
%%%
%%% entry:
%%%   ...
%%%   br <cond0> <cond0-true> <cond0-false>
%%%
%%% <cond0-true>:
%%%   ...
%%%   ret
%%% <cond0-false>:
%%%   ...
%%%   br <cond1> <cond1-true> <cond1-false>
%%%   ...
%%%
%%% We will follow the <condX-false>-edges and look into the
%%% <condX-true> blocks for return instructions.
%%%
analyze_block(Block, Blocks, Args, Defs, Uses) ->
    analyze_entry_bb(maps:get(Block, Blocks), Blocks, Args, Defs, Uses).

analyze_entry_bb(#b_blk{last=#b_ret{}}, _Blocks, _Args, _Defs, _Uses) ->
    %% Can't do anything useful with this one
    [];
analyze_entry_bb(#b_blk{last=#b_switch{}}, _Blocks, _Args, _Defs, _Uses) ->
    %% TODO: Support switches
    [];
analyze_entry_bb(#b_blk{last=#b_br{succ=D,fail=D}},
                 _Blocks, _Args, _Defs, _Uses) ->
    [];
analyze_entry_bb(Block=#b_blk{is=Is, last=#b_br{bool=B,succ=S,fail=F}},
                 Blocks, Args, Defs, Uses) ->
    case has_side_effects(Block) orelse has_escaping_defs(Is, 0, Uses) of
        true -> [];
        false ->
            analyze_guarded_bb(0, analyze_bool(B, Args, Defs), S,  F,
                               Blocks, Args, Defs, Uses)
    end.

analyze_guarded_bb(Lbl, false, _, _, _, _, _, _)->
    %% We cannot statically determine the result of the guard, so give
    %% up.
    [{true,Lbl}];
analyze_guarded_bb(Lbl, Condition, GuardedBlock,
                   FallthroughBlock, Blocks, Args, Defs, Uses) ->
    [{Lbl,Condition,GuardedBlock}|analyze_bb(FallthroughBlock, Blocks, Args, Defs, Uses)].

analyze_bb(Lbl, Blocks, Args, Defs, Uses) ->
    Block = #b_blk{is=Is} = maps:get(Lbl, Blocks),
    case has_side_effects(Block) orelse has_escaping_defs(Is, Lbl, Uses) of
        true -> [{true,Lbl}];
        false -> analyze_side_effect_free_bb(Lbl, Block, Blocks,
                                             Args, Defs, Uses)
    end.

analyze_side_effect_free_bb(Lbl,#b_blk{last=Last}, Blocks, Args, Defs, Uses) ->
    case Last of
        #b_ret{} -> [{true,Lbl}];
        #b_br{succ=D,fail=D} -> [{true,Lbl}];
        #b_br{bool=Guard,succ=S,fail=F} ->
            analyze_guarded_bb(Lbl, analyze_bool(Guard, Args, Defs), S,  F,
                               Blocks, Args, Defs, Uses);
        #b_switch{} ->
            %% TODO: Support switches
            [{true,Lbl}]
    end.

%%%
%%% Return true if the block has side effects
%%%
has_side_effects(#b_blk{is=Is}) ->
    has_side_effects1(Is).
has_side_effects1([]) ->
    false;
has_side_effects1([I|Is]) ->
    (not beam_ssa:no_side_effect(I)) orelse has_side_effects1(Is).

%%%
%%% Return true if the block has defs which live outside the block
%%%
has_escaping_defs([], _Lbl, _Uses) ->
    false;
has_escaping_defs([#b_set{dst=Dst}|Is], Lbl, Uses) ->
    case Uses of
        #{ Dst := [Lbl] } -> has_escaping_defs(Is, Lbl, Uses);
        #{ Dst := _ } -> true
    end.

%%% Analyze a boolean expression to tell if can be expressed as a
%%% simple operation on one or more of the function arguments.
analyze_bool(B, Args, Defs) ->
    case Defs of
        #{ B := #b_set{op=is_nonempty_list,args=[Var]} }
          when is_map_key(Var, Args) ->
            {Var, is_nonempty_list};
        #{ B := #b_set{op={bif,Bif},args=[Var]} }
          when is_map_key(Var, Args) ->
            {Var, Bif};
        #{ B := #b_set{op={bif,'=:='},args=[Var,#b_literal{val=[]}]} }
          when is_map_key(Var, Args) ->
            {Var, is_nil};
        _ ->
            false
    end.

%%%
%%% Check if the tests in the list of guards all use the same argument
%%% and are tag tests. As the future optimization is only useful for
%%% sequences of at least two tag tests and a fallthrough, we consider
%%% shorter sequences as not valid.
%%%
only_tag_tests(Gs=[{_,{Arg,_},_},_,_|_]) ->
    only_tag_tests(Arg, Gs);
only_tag_tests(_) ->
    false.

only_tag_tests(_, [{true,_}]) ->
    true;
only_tag_tests(Arg, [{_,{Arg,is_nonempty_list},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_atom},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_bitstring},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_float},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_function,#b_literal{}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_function},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_integer},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_list},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_map},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_nil},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_number},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_pid},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_port},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_reference},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{_,{Arg,is_tuple},_}|Rest]) ->
    only_tag_tests(Arg, Rest);

%%
only_tag_tests(Arg, [{_,{Arg,{is_tagged_tuple,_,_}},_}|_]) ->
    false;
%% only_tag_tests(Arg, [{_,{Arg,{bif,O,_}},_}|_])
%%   when O =:= '>=' ; O =:= '=<' ; O =:= '==' ; O =:= '=:=' ;
%%        O == '<' ; O =:= '>' ->
%%     false;
only_tag_tests(Arg, [{_,{Arg,is_binary},_}|_Rest]) ->
    false;
only_tag_tests(Arg, [{_,{Other,_},_}|_]) when Arg =/= Other ->
    false;
only_tag_tests(_Arg, _Guards) ->
    io:format("!!! arg:~p, ~p~n", [_Arg, _Guards]),
    false.

insert_select_tag([{Parent,{Var=#b_var{},TagTest0},Lbl0},
                   {_,{Var,TagTest1},Lbl1},
                   {true,FailLbl}], Bs0, Cnt0) ->
    %% Replace the chain of branches with a switch using a magic operand
    Blk0 = #b_blk{is=Is0} = maps:get(Parent, Bs0),
    SwitchArg = #b_var{name={magic_switch_arg,Cnt0}},
    Is = Is0 ++ [#b_set{op=tag_select,dst=SwitchArg,
                        args=[#b_literal{val=TagTest0},
                              #b_literal{val=TagTest1},Var]}],
    Last=#b_switch{arg=SwitchArg,fail=FailLbl,
                   list=[{#b_literal{val=0},Lbl0},
                         {#b_literal{val=1},Lbl1}]},
    Blk = Blk0#b_blk{is=Is,last=Last},
    Bs1 = Bs0#{ Parent => Blk },
    Bs2 = maps:from_list(beam_ssa_dead:opt(beam_ssa:linearize(Bs1))),
    %% beam_ssa_dead:opt/1 does not remove dead defs unless they are
    %% in one of the blocks which are touched by the optimization. So
    %% do that manually here.
    {drop_dead_defs(Bs2),Cnt0 + 1}.

drop_dead_defs(Blocks0) ->
    Uses = beam_ssa:uses(Blocks0),
    Defs = beam_ssa:definitions(Blocks0),
    ToDrop = maps:fold(fun(Var, Def, Acc) when not is_map_key(Var, Uses) ->
                               case beam_ssa:no_side_effect(Def) of
                                   true ->
                                       cerl_sets:add_element(Def, Acc);
                                   false ->
                                       Acc
                               end;
                          (_, _, Acc) ->
                               Acc
                       end, cerl_sets:new(), Defs),
    maps:fold(fun(Lbl, Blk, Acc) -> Acc#{ Lbl => drop_defs(Blk, ToDrop) } end,
              #{}, Blocks0).

drop_defs(Blk=#b_blk{is=Is}, ToDrop) ->
    Blk#b_blk{is=lists:filter(fun(I) ->
                                      not cerl_sets:is_element(I, ToDrop)
                              end, Is)}.
