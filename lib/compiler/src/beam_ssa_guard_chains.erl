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
    case only_tag_tests(R) of
        true ->
            {Bs, Cnt} = insert_markers(R, 0, length(R) - 1, Bs0, Cnt0),
            {F#b_function{bs=Bs,cnt=Cnt},{MFA,R}};
        false ->
            {F,{MFA,[]}}
    end.

%%%
%%% Figure out if the result if this function is simply one of its
%%% arguments for a particular value and/or type of its arguments.
%%%
analyze_head(Blocks, Args) ->
    Defs = beam_ssa:definitions(Blocks),
    {_,Args2Idx} = foldl(fun(Arg, {Idx,Acc}) ->
                                 {Idx+1,[{Arg,Idx}|Acc]}
                         end, {0,[]}, Args),
    R = analyze_block(0, Blocks, maps:from_list(Args2Idx), Defs),
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
analyze_block(Block, Blocks, Args, Defs) ->
    analyze_entry_bb(maps:get(Block, Blocks), Blocks, Args, Defs).

analyze_entry_bb(#b_blk{last=#b_ret{}}, _Blocks, _Args, _Defs) ->
    %% Can't do anything useful with this one
    [];
analyze_entry_bb(#b_blk{last=#b_switch{}}, _Blocks, _Args, _Defs) ->
    %% TODO: Support switches
    [];
analyze_entry_bb(#b_blk{last=#b_br{succ=D,fail=D}}, _Blocks, _Args, _Defs) ->
    [];
analyze_entry_bb(Block=#b_blk{last=#b_br{bool=B,succ=S,fail=F}},
                 Blocks, Args, Defs) ->
    case has_side_effects(Block) of
        true -> [];
        false ->
            analyze_guarded_bb(0, analyze_bool(B, Args, Defs), S,  F,
                               Blocks, Args, Defs)
    end.

analyze_guarded_bb(Lbl, false, _, _, _, _, _)->
    %% We cannot statically determine the result of the guard, so give
    %% up.
    [{true,Lbl}];
analyze_guarded_bb(_, Condition, GuardedBlock,
                   FallthroughBlock, Blocks, Args, Defs) ->
    [{Condition,GuardedBlock}|analyze_bb(FallthroughBlock, Blocks, Args, Defs)].

analyze_bb(Lbl, Blocks, Args, Defs) ->
    Block = maps:get(Lbl, Blocks),
    case has_side_effects(Block) of
        true -> [{true,Lbl}];
        false -> analyze_side_effect_free_bb(Lbl, Block, Blocks, Args, Defs)
    end.

analyze_side_effect_free_bb(Lbl,#b_blk{last=Last}, Blocks, Args, Defs) ->
    case Last of
        #b_ret{} -> [{true,Lbl}];
        #b_br{succ=D,fail=D} -> [{true,Lbl}];
        #b_br{bool=Guard,succ=S,fail=F} ->
            analyze_guarded_bb(Lbl, analyze_bool(Guard, Args, Defs), S,  F,
                               Blocks, Args, Defs);
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

%%% Analyze a boolean expression to tell if can be expressed as a
%%% simple operation on one or more of the function arguments.
analyze_bool(B, Args, Defs) ->
    case Defs of
        #{ B := #b_set{op=is_nonempty_list,args=[Var]} } ->
            case Args of
                #{ Var := Idx } ->
                    {Idx, is_nonempty_list};
                _ ->
                    false
            end;
        #{ B := #b_set{op={bif,Bif},args=[Var]} } ->
            case Args of
                #{ Var := Idx } ->
                    {Idx, {bif, Bif}};
                _ ->
                    false
            end;
        #{ B := #b_set{op={bif,Bif},args=[Var,V=#b_literal{}]} } ->
            case Args of
                #{ Var := Idx } ->
                    {Idx, {bif, Bif, V}};
                _ ->
                    false
            end;
        #{ B := #b_set{op=is_tagged_tuple,
                       args=[Var,#b_literal{val=A},#b_literal{val=T}]}
         } when is_integer(A), is_atom(T) ->
            case Args of
                #{ Var := Idx } ->
                    {Idx, {is_tagged_tuple,A,T}};
                _ ->
                    false
            end;
        _ ->
            false
    end.

%%%
%%% Check if the tests in the list of guards all use the same argument
%%% and are tag tests. As the future optimization is only useful for
%%% sequences of at least two tag tests and a fallthrough, we consider
%%% shorter sequences as not valid.
%%%
only_tag_tests(Gs=[{{Arg,_},_},_,_|_]) ->
    only_tag_tests(Arg, Gs);
only_tag_tests(_) ->
    false.

only_tag_tests(_, [{true,_}]) ->
    true;
only_tag_tests(Arg, [{{Arg,is_nonempty_list},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,'=:=',{b_literal,[]}}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_atom}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_bitstring}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_binary}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_float}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_function,{b_literal,_}}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_function}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_integer}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_list}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_map}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_number}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_pid}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_port}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_reference}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);
only_tag_tests(Arg, [{{Arg,{bif,is_tuple}},_}|Rest]) ->
    only_tag_tests(Arg, Rest);

%%
only_tag_tests(Arg, [{{Arg,{bif,'=:=',{b_literal,_}}},_}|_]) ->
    false;
only_tag_tests(Arg, [{{Arg,{is_tagged_tuple,_,_}},_}|_]) ->
    false;
only_tag_tests(Arg, [{{Arg,{bif,O,_}},_}|_])
  when O =:= '>=' ; O =:= '=<' ; O =:= '==' ; O =:= '=:=' ;
       O == '<' ; O =:= '>' ->
    false;

only_tag_tests(Arg, [{{Other,_},_}|_]) when Arg =/= Other ->
    false;
only_tag_tests(_Arg, Guards) ->
    io:format("!!~p~n", [Guards]),
    false.

insert_markers([], _Idx, _Order, Bs, Cnt0) ->
    {Bs,Cnt0};
insert_markers([{_,BB}|Guards], Idx, Order, Bs, Cnt0) ->
    Blk0 = #b_blk{is=Is0} = maps:get(BB, Bs),
    Is = [#b_set{op=gchain,
                 dst=#b_var{name={ignored,Cnt0}},
                 args=[#b_literal{val=Order},
                       #b_literal{val=Idx}]}|Is0],
    Blk = Blk0#b_blk{is=Is},
    insert_markers(Guards, Idx + 1, Order, Bs#{ BB => Blk }, Cnt0 + 1).
