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
%% Purpose: Run right after beam_z to do calculate various quality
%% metrics for the compiled module. Writes quality metrics to the
%% io-device given to module/2.

-module(beam_ssa_callsites).

-export([module/2]).

-import(lists, [foldl/3, reverse/1,nth/2]).

-include("erl_compile.hrl").
-include("beam_ssa.hrl").

-spec module(#b_module{}, any()) -> 'ok'.

module(Mod=#b_module{name=_Name,body=Body,attributes=As}, _Opts) ->
    Funs = foldl(fun add_function/2, #{}, Body),
    %% io:format("**FUNS~n~p~n", [Funs]),
    Calls = maps:fold(fun analyze_calls/3, [], Funs),
    %% io:format("** CALLS~n~p~n", [Calls]),
    Called = [ Cs || {_,_,Cs,_} <- Calls],
    Targets = cerl_sets:to_list(cerl_sets:from_list(Called)),
    Heads = analyze_heads(Funs, Targets),
    %% io:format("** ~p ** HEADS~n~p~n", [_Name, Heads]),
    io:format("~p calls~n", [length(Calls)]),
    {Elide, ShortCircuit,WElide,WShortCircuit} =
        count_optimizable_calls(Calls, Heads, Funs),
    io:format("~p are possible to elide~n", [Elide]),
    io:format("~p are possible to short circuit~n", [ShortCircuit]),
    io:format("~p weighted elides~n", [WElide]),
    io:format("~p weighted short circuit~n", [WShortCircuit]),
    Info = {callsites,#{total => length(Calls),
                        elide => Elide,
                        sc => ShortCircuit,
                        welide => WElide,
                        wsc => WShortCircuit}},
    {ok,Mod#b_module{attributes=[Info|As]}}.

count_optimizable_calls(Calls, Heads, Funs) ->
    count_optimizable_calls(Calls, 0, 0, 0, 0, Heads, Funs).

count_optimizable_calls([Call|Calls], Elide, ShortCircuit,
                        WElide, WShortCircuit, Heads, Funs) ->
    case analyze_call_arguments(Call, Heads, Funs) of
        X when is_integer(X), X > 0 ->
            count_optimizable_calls(Calls, Elide, ShortCircuit + 1,
                                    WElide, WShortCircuit + X,
                                    Heads, Funs);
        X when is_integer(X), X < 0 ->
            count_optimizable_calls(Calls, Elide + 1, ShortCircuit,
                                    WElide - X, WShortCircuit,
                                    Heads, Funs);
        false ->
            count_optimizable_calls(Calls, Elide, ShortCircuit,
                                    WElide, WShortCircuit, Heads, Funs)
    end;
count_optimizable_calls([], Elide, ShortCircuit, WElide, WShortCircuit, _, _) ->
    {Elide, ShortCircuit, WElide, WShortCircuit}.

add_function(F, Map) ->
    {_,Fun,Arity} = beam_ssa:get_anno(func_info, F),
    Key = {Fun,Arity},
    Map#{ Key => F}.

analyze_calls({F,A}, #b_function{bs=Blocks}, Calls0) ->
    IFun = fun(#b_set{op=call,
                      dst=D,
                      args=[#b_local{name=#b_literal{val=Name},
                                     arity=Arity}|Args]}, Calls2) ->
                   [{{F,A},D,{Name,Arity},Args}|Calls2];
              (_I, Calls2) ->
                   Calls2
           end,
    BFun = fun(_Lbl, #b_blk{is=Is}, Calls1) ->
                   foldl(IFun, Calls1, Is)
           end,
    maps:fold(BFun, Calls0, Blocks).

analyze_heads(Funs, Targets) ->
    foldl(fun(Target, Acc) ->
                  analyze_head(Target, maps:get(Target, Funs), Acc)
          end, #{}, Targets).

analyze_head(FA={_F,_A}, #b_function{args=Args,bs=Bs}, Heads) ->
%    io:format("Analyzing heads of ~p/~p~n", [F, A]),
%    io:format("  args: ~p~n", [Args]),
%    io:format("  bs: ~p~n", [Bs]),
    Defs = beam_ssa:definitions(Bs),
    {_,Args2Idx} = foldl(fun(Arg, {Idx,Acc}) ->
                                 {Idx+1,[{Arg,Idx}|Acc]}
                         end, {0,[]}, Args),
    R = reverse(analyze_block(FA, 0, Bs, maps:from_list(Args2Idx), Defs, [])),
    case R of
        [] -> Heads;
        R -> Heads#{FA => R}
    end.

analyze_block(FA, Block, Blocks, Args, Defs, Heads) ->
    analyze_branch(FA, maps:get(Block, Blocks), Blocks, Args, Defs, Heads).

analyze_branch(_, #b_blk{last=#b_ret{arg=R}}, _Blocks, Args, _Defs, Acc) ->
    case Args of
        #{ R := Idx } ->
            [{true,{returns,Idx}}|Acc];
        _ ->
            Acc
    end;
analyze_branch(_, #b_blk{last=#b_ret{}}, _Blocks, _Args, _Defs, Acc) ->
    Acc;
analyze_branch(_, #b_blk{last=#b_br{succ=D,fail=D}}, _Blocks, _Args, _Defs, Acc) ->
    Acc;
analyze_branch(FA, #b_blk{last=#b_br{bool=B,succ=S,fail=F}},
               Blocks, Args, Defs, Acc) ->
    case analyze_bool(B, Args, Defs) of
        false ->
            Acc;
        Guard ->
            analyze_block(FA, F, Blocks, Args, Defs, [{Guard,S}|Acc])
    end;
analyze_branch(_, #b_blk{last=#b_switch{}}, _Blocks, _Args, _Defs, Acc) ->
    %% XXXX
    Acc.

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
        _ ->
            false
    end.

analyze_call_arguments({Caller, D, Callee, Args}, Heads, Funs) ->
    case Heads of
        #{ Callee := Hs } ->
            #b_function{bs=Bs,args=CallerArgs} = maps:get(Caller, Funs),
            % Extend the args with the caller's arguments
            Defs = foldl(fun(Arg, Map) ->
                                 Map#{ Arg => {caller_arg,Arg} }
                         end, beam_ssa:definitions(Bs), CallerArgs),

            %% io:format("Looking at call to ~p at ~p, args: ~p~n",
            %%           [Callee, D, Args]),
            analyze_call_arguments(1, D, Args, Hs, Defs);
        _ ->
            false
    end.

analyze_call_arguments(_Depth, _Loc, _Args, [], _Defs) ->
    %% io:format("  No matching heads found~n~n"),
    false;
analyze_call_arguments(Depth, Loc, Args, [{Cond,_Lbl}=_Head|Heads], Defs) ->
    %% io:format("  Looking at head ~p~n", [_Head]),
    case Cond of
        true ->
            %% The call could be elided.
            -Depth;
        {{caller_arg,_},_} ->
            false;
        {ArgI,Op} ->
            Arg = nth(ArgI + 1, Args),
            case analyze_cond(Op, Arg, Defs) of
                true ->
                    %% io:format("  ==> can call ~p directly~n", [Lbl]),
                    Depth;
                false ->
                    analyze_call_arguments(Depth + 1, Loc, Args, Heads, Defs)
            end
    end.

analyze_cond(Op, ArgVar, Defs) ->
    Arg = case ArgVar of
            #b_literal{}=Lit -> Lit;
            _ -> maps:get(ArgVar, Defs)
        end,
    case {Op,Arg} of
        {_,{caller_arg,_}} ->
            false;
        {is_nonempty_list,#b_set{op=put_list}} ->
            true;
        {{bif,is_atom},#b_literal{val=V}} when is_atom(V) ->
            true;
        {{bif,is_boolean},#b_literal{val=true}} ->
            true;
        {{bif,is_boolean},#b_literal{val=false}} ->
            true;
        {{bif,is_integer},#b_literal{val=V}} when is_integer(V) ->
            true;
        {{bif,is_list},#b_set{op=put_list}} ->
            true;
        {{bif,is_map},#b_set{op=put_map}} ->
            true;
        {{bif,is_tuple},#b_set{op=put_tuple}} ->
            true;
        {{bif,is_list},#b_literal{val=V}} when is_list(V) ->
            true;
        {{bif,'=:=',#b_literal{val=A}},#b_literal{val=B}} when A =:= B ->
            true;
        _ ->
            %% io:format("  ?? ~p ~p~n", [Op, Arg]),
            false
    end.
