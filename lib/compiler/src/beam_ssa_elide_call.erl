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

-module(beam_ssa_elide_call).

-export([module/2,function/4]).

-import(lists, [foldl/3,map/2,reverse/1]).

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

-spec module(st_map(), func_info_db()) -> term().
module(StMap, FuncDb0) when FuncDb0 =/= #{} ->
    FuncDb = maps:fold(fun analyze_head/3, FuncDb0, StMap),
    {StMap, FuncDb};
module(StMap, FuncDb) ->
    %% Module-level analysis is disabled.
    {StMap, FuncDb}.

-spec function(Linear, Args, Anno, FuncDb) -> {Linear, FuncDb} when
      Linear :: [{non_neg_integer(), beam_ssa:b_blk()}],
      Args :: [beam_ssa:b_var()],
      Anno :: beam_ssa:anno(),
      FuncDb :: func_info_db().
function(Linear0, _Args, Anno, FuncDb) when FuncDb =/= #{} ->
    MFA={_M,_F,_A} = maps:get(func_info, Anno),
    ?dp("function:~p:~p/~p~n  ~p~n  args: ~p~n~n",
        [_M, _F, _A, Linear0, _Args]),
    Replacements =
        maps:from_list(foldl(fun({_Lbl,#b_blk{is=Is}}, Acc) ->
                                     elide_calls(Is, MFA, FuncDb, Acc)
                             end, [], Linear0)),
    N = maps:size(Replacements),

    Linear =
        if N =:= 0 ->
                Linear0;
           true ->
                ?dp("replacements: ~p~n", [Replacements]),
                Replacements1 = flatten_replacements(Replacements),
                ?dp("replacements1: ~p~n", [Replacements1]),
                ?dp("IN: ~p~n", [Linear0]),
                Replaced = replace_all_uses(Linear0, Replacements1),
                ?dp("OUT: ~p~n", [Replaced]),
                Replaced
        end,
    {Linear, FuncDb};
function(Linear0, _Args, _Anno, FuncDb) ->
    %% Module-level optimization is disabled, pass an empty function database
    %% so we only perform local optimizations.
    {Linear0, FuncDb}.

elide_calls([], _Caller, _FuncDb, Acc) ->
    Acc;
elide_calls([#b_set{op=call,
                    dst=D,
                    args=[Callee=#b_local{name=#b_literal{val=_Name},
                                          arity=_Arity}|Args]}|Is],
            Caller={_M,F,A}, FuncDb, Acc0) ->
    ?dp("Call from ~p to ~p/~p~n", [Caller,_Name,_Arity]),
    #func_info{heads=Heads,arg_types=ArgTypes} =
        get_function_info(Callee, FuncDb),
    ?dp("  heads: ~p~n", [Heads]),
    ?dp("  arg-types: ~p~n", [ArgTypes]),
    Callsite = {#b_local{name=#b_literal{val=F},arity=A},D},
    TypedArgs = type_args(ArgTypes, Callsite),
    ?dp("  typed-args: ~p~n", [TypedArgs]),
    Acc = case attempt_fold(TypedArgs, Heads) of
              false -> Acc0;
              {elide,#b_literal{}=R} ->
                  io:format("Elide!~n"),
                  [{D,R}|Acc0];
              {elide,{argument,Idx}} ->
                  io:format("Elide!~n"),
                  [{D,lists:nth(Idx + 1, Args)}|Acc0]
          end,
    elide_calls(Is, Caller, FuncDb, Acc);
elide_calls([_|Is], Caller, FuncDb, Acc) ->
    elide_calls(Is, Caller, FuncDb, Acc).

get_function_info(Callee=#b_local{}, FuncDb) ->
    maps:get(Callee, FuncDb).

type_args([], _Callsite) ->
    [];
type_args([ArgTypeMap|ArgTypes], Callsite) ->
    [maps:get(Callsite, ArgTypeMap,any)|type_args(ArgTypes, Callsite)].

attempt_fold(_TypedArgs, []) ->
    false;
attempt_fold(TypedArgs, [{Cond,Result}=_Head|Heads]) ->
    ?dp("Attempt fold~n  ~p~n  ~p~n~n", [TypedArgs, _Head]),
    Verdict = eval_cond(Cond, TypedArgs),
    case {Verdict,Result} of
        {undetermined,_} ->
            %% We cannot determine if this condition will evaluate to
            %% true or false. We will have to call the function.
            false;
        {true,false} ->
            %% We cannot determine the result, but we know this guard
            %% will be true, so there is no point in looking at the
            %% next head.
            false;
        {true,_} ->
            %% This can be elided as we can determine the result.
            {elide,Result};
        {false,_} ->
            %% We know that this is not a result that will be produced
            %% from these arguments. So try with the next head.
            attempt_fold(TypedArgs, Heads)
    end.

%%%
%%% Try to determine if the condition, with the given arguments,
%%% evaluates to true, false, or if it cannot be determined.
%%%
eval_cond(true, _Args) ->
    true;
eval_cond({ArgI,Cond}, Args) ->
    Arg = lists:nth(ArgI + 1, Args),
    eval_guard(Cond, Arg).

eval_guard({bif,is_atom}, #t_atom{}) ->
    true;
eval_guard({bif,is_atom}, #t_union{atom=none}) ->
    false;
eval_guard({bif,is_atom}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_atom}, any) ->
    undetermined;
eval_guard({bif,is_atom}, _) ->
    false;

eval_guard({bif,is_float}, #t_float{}) ->
    true;
eval_guard({bif,is_float}, #t_union{number=none}) ->
    false;
eval_guard({bif,is_float}, #t_union{number=#t_integer{}}) ->
    false;
eval_guard({bif,is_float}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_float}, number) ->
    undetermined;
eval_guard({bif,is_float}, any) ->
    undetermined;
eval_guard({bif,is_float}, _) ->
    false;

eval_guard({bif,is_function}, #t_fun{}) ->
    true;
eval_guard({bif,is_function}, #t_union{other=none}) ->
    false;
eval_guard({bif,is_function}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_function}, any) ->
    undetermined;
eval_guard({bif,is_function}, _) ->
    false;

eval_guard({bif,is_integer}, #t_integer{}) ->
    true;
eval_guard({bif,is_integer}, #t_union{number=none}) ->
    false;
eval_guard({bif,is_integer}, #t_union{number=#t_float{}}) ->
    false;
eval_guard({bif,is_integer}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_integer}, number) ->
    undetermined;
eval_guard({bif,is_integer}, any) ->
    undetermined;
eval_guard({bif,is_integer}, _) ->
    false;

eval_guard({bif,is_number}, #t_float{}) ->
    true;
eval_guard({bif,is_number}, #t_integer{}) ->
    true;
eval_guard({bif,is_number}, #t_union{number=none}) ->
    false;
eval_guard({bif,is_number}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_number}, number) ->
    true;
eval_guard({bif,is_number}, any) ->
    undetermined;
eval_guard({bif,is_number}, _) ->
    false;

eval_guard({bif,is_tuple}, #t_tuple{}) ->
    true;
eval_guard({bif,is_tuple}, #t_union{tuple_set=none}) ->
    false;
eval_guard({bif,is_tuple}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_tuple}, any) ->
    undetermined;
eval_guard({bif,is_tuple}, _) ->
    false;

eval_guard({bif,'=:=',#b_literal{val=[]}}, nil) ->
    true;
eval_guard({bif,'=:=',#b_literal{val=V}}, number) when not is_number(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_integer{})
  when not is_integer(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_float{}) when not is_float(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_integer{elements={E,E}})
  when is_integer(V) ->
    V =:= E;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_integer{elements={L,H}})
  when is_integer(V), (V < L) orelse (H < V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_integer{}) when is_integer(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_float{elements={E,E}})
  when is_float(V) ->
    V =:= E;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_float{elements={L,H}})
  when is_float(V), (V < L) orelse (H < V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_float{}) when is_float(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, number) when is_number(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{number=none})
  when is_number(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{}) when is_number(V) ->
    undetermined;
eval_guard({bif,'==',#b_literal{val=V}}, number) when is_number(V) ->
    undetermined;

eval_guard({bif,is_list}, #t_list{}) ->
    true;
eval_guard({bif,is_list}, #t_cons{}) ->
    true;
eval_guard({bif,is_list}, nil) ->
    true;
eval_guard({bif,is_list}, any) ->
    undetermined;
eval_guard({bif,is_list}, #t_union{list=none}) ->
    false;
eval_guard({bif,is_list}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_list}, _) ->
    false;

eval_guard(is_nonempty_list, #t_list{}) ->
    undetermined;
eval_guard(is_nonempty_list, #t_cons{}) ->
    true;
eval_guard(is_nonempty_list, nil) ->
    false;
eval_guard(is_nonempty_list, #t_union{list=none}) ->
    false;
eval_guard(is_nonempty_list, _) ->
    undetermined;

eval_guard({bif,is_map}, #t_map{}) ->
    true;
eval_guard({bif,is_map}, #t_union{other=none}) ->
    false;
eval_guard({bif,is_map}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_map}, any) ->
    undetermined;
eval_guard({bif,is_map}, _) ->
    false;

eval_guard({bif,'>',#b_literal{val=V}}, #t_integer{elements={L,_}})
  when is_integer(V), L > V ->
    true;
eval_guard({bif,'>',#b_literal{val=V}}, #t_integer{elements={_,H}})
  when is_integer(V), H =< V ->
    false;
eval_guard({bif,'>',#b_literal{val=V}}, #t_integer{}) when is_integer(V) ->
    undetermined;

eval_guard({bif,'>',#b_literal{val=V}}, #t_float{elements={L,_}})
  when is_float(V), L > V ->
    true;
eval_guard({bif,'>',#b_literal{val=V}}, #t_float{elements={_,H}})
  when is_float(V), H =< V ->
    false;
eval_guard({bif,'>',#b_literal{val=V}}, #t_float{}) when is_float(V) ->
    undetermined;

eval_guard({bif,'<',#b_literal{val=V}}, #t_integer{elements={_,H}})
  when is_integer(V), H < V ->
    true;
eval_guard({bif,'<',#b_literal{val=V}}, #t_integer{elements={L,_}})
  when is_integer(V), L >= V ->
    false;
eval_guard({bif,'<',#b_literal{val=V}}, #t_integer{}) when is_integer(V) ->
    undetermined;

eval_guard({bif,'<',#b_literal{val=V}}, #t_float{elements={_,H}})
  when is_float(V), H < V ->
    true;
eval_guard({bif,'<',#b_literal{val=V}}, #t_float{elements={L,_}})
  when is_float(V), L >= V ->
    false;
eval_guard({bif,'<',#b_literal{val=V}}, #t_float{}) when is_float(V) ->
    undetermined;

eval_guard({bif,'>=',#b_literal{val=V}}, #t_integer{elements={L,_}})
  when is_integer(V), L >= V ->
    true;
eval_guard({bif,'>=',#b_literal{val=V}}, #t_integer{elements={_,H}})
  when is_integer(V), H < V ->
    false;
eval_guard({bif,'>=',#b_literal{val=V}}, #t_integer{}) when is_integer(V) ->
    undetermined;

eval_guard({bif,'>=',#b_literal{val=V}}, #t_float{elements={L,_}})
  when is_float(V), L >= V ->
    true;
eval_guard({bif,'>=',#b_literal{val=V}}, #t_float{elements={_,H}})
  when is_float(V), H < V ->
    false;
eval_guard({bif,'>=',#b_literal{val=V}}, #t_float{}) when is_float(V) ->
    undetermined;

eval_guard({bif,'=<',#b_literal{val=V}}, #t_integer{elements={_,H}})
  when is_integer(V), H =< V ->
    true;
eval_guard({bif,'=<',#b_literal{val=V}}, #t_integer{elements={L,_}})
  when is_integer(V), L > V ->
    false;
eval_guard({bif,'=<',#b_literal{val=V}}, #t_integer{}) when is_integer(V) ->
    undetermined;

eval_guard({bif,'=<',#b_literal{val=V}}, #t_float{elements={_,H}})
  when is_float(V), H =< V ->
    true;
eval_guard({bif,'=<',#b_literal{val=V}}, #t_float{elements={L,_}})
  when is_float(V), L > V ->
    false;
eval_guard({bif,'=<',#b_literal{val=V}}, #t_float{}) when is_float(V) ->
    undetermined;

eval_guard({bif,'=:=',#b_literal{}}, #t_integer{elements=any}) ->
    undetermined;

eval_guard({bif,'=:=',#b_literal{}}, #t_float{elements=any}) ->
    undetermined;

eval_guard({bif,'=:=',#b_literal{val=V}}, #t_atom{elements=any})
  when is_atom(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_atom{elements=[E]}) ->
    V =:= E;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_atom{}) when is_atom(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{atom=none})
  when is_atom(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{}) when is_atom(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, any) when is_atom(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, _) when is_atom(V) ->
    false;

eval_guard({bif,'=:=',#b_literal{val=V}}, #t_bitstring{})
  when is_bitstring(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_bitstring{})
  when is_bitstring(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{other=none})
  when is_bitstring(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{})
  when is_bitstring(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, any) when is_bitstring(V) ->
    undetermined;

eval_guard({bif,is_binary}, #t_bitstring{size_unit=Len}) ->
    (Len rem 8) =:= 0;
eval_guard({bif,is_binary}, #t_bs_matchable{}) ->
    undetermined;
eval_guard({bif,is_binary}, #t_bs_context{}) ->
    undetermined;
eval_guard({bif,is_binary}, #t_union{other=none}) ->
    false;
eval_guard({bif,is_binary}, #t_union{}) ->
    undetermined;
eval_guard({bif,is_binary}, any) ->
    undetermined;
eval_guard({bif,is_binary}, _) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_cons{}) when not is_list(V) ->
    false;

eval_guard({bif,'=:=',#b_literal{val=V}}, #t_cons{}) when is_list(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_list{}) when is_list(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=[]}}, nil) ->
    true;
eval_guard({bif,'=:=',#b_literal{val=V}}, nil) when is_list(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{list=none})
  when is_list(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{}) when is_list(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, any) when is_list(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, _) when is_list(V) ->
    false;

eval_guard({bif,'=:=',#b_literal{val=V}}, #t_tuple{size=S,exact=true})
  when is_tuple(V), erlang:tuple_size(V) =/= S ->
    %% TODO: consider elements too
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_tuple{}) when is_tuple(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{tuple_set=none})
  when is_tuple(V) ->
    false;
eval_guard({bif,'=:=',#b_literal{val=V}}, #t_union{}) when is_tuple(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, any) when is_tuple(V) ->
    undetermined;
eval_guard({bif,'=:=',#b_literal{val=V}}, _) when is_tuple(V) ->
    false;

%% These are clauses we could handle later
eval_guard({bif,is_pid}, _) ->
    undetermined;

eval_guard({is_tagged_tuple,S,Tag}, #t_tuple{size=S,exact=true, elements=Es}) ->
    case Es of
        #{ 1 := #t_atom{elements=any} } ->
            undetermined;
        #{ 1 := #t_atom{elements=Atoms} } ->
            io:format("IS_TAGGED_TUPLE~n"),
            ordsets:is_element(Tag, Atoms);
        _ ->
            undetermined
    end;
eval_guard({is_tagged_tuple,S0,_}, #t_tuple{size=S1,exact=true})
  when S0 =/= S1->
    false;
eval_guard({is_tagged_tuple,_,_}, _) ->
    undetermined;

%% These are to silence things we know about but cannot do anything
%% useful with
eval_guard({bif,'>',#b_literal{val=V}}, number) when is_number(V) ->
    undetermined;
eval_guard({bif,'<',#b_literal{val=V}}, number) when is_number(V) ->
    undetermined;
eval_guard({bif,'>=',#b_literal{val=V}}, number) when is_number(V) ->
    undetermined;
eval_guard({bif,'=<',#b_literal{val=V}}, number) when is_number(V) ->
    undetermined;

eval_guard(_, any) ->
    undetermined;

eval_guard(Cond, Arg) ->
    io:format("Eval guard~n  ~p~n  ~p~n~n", [Cond, Arg]),
    undetermined.

%%%
%%% Figure out if the result if this function is simply one of its
%%% arguments for a particular value and/or type of its arguments.
%%%
analyze_head(F=#b_local{}, #opt_st{ssa=Linear,args=Args}, FuncDb0) ->
    Bs = maps:from_list(Linear),
    Defs = beam_ssa:definitions(Bs),
    {_,Args2Idx} = foldl(fun(Arg, {Idx,Acc}) ->
                                 {Idx+1,[{Arg,Idx}|Acc]}
                         end, {0,[]}, Args),
    R = analyze_block(0, Bs, maps:from_list(Args2Idx), Defs),
    add_useful_heads(R, FuncDb0, F).

add_useful_heads(Result, FuncDb, F) ->
    case has_useful_heads(Result) of
        true ->
            FI0 = #func_info{} = maps:get(F, FuncDb),
            FI = FI0#func_info{heads=Result},
            FuncDb#{F => FI};
        false -> FuncDb
    end.

has_useful_heads([]) ->
    false;
has_useful_heads([{_,false}|Rest]) ->
    has_useful_heads(Rest);
has_useful_heads([_|_]) ->
    true.

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

analyze_entry_bb(Block=#b_blk{last=#b_ret{}}, _Blocks, Args, Defs) ->
    case {has_side_effects(Block),block_result(Block, Args, Defs)} of
        {true,_} ->
            [];
        {_,false} ->
            % Can't do anything useful with this one
            [];
        {_,Value} ->
            [{true,Value}]
    end;
analyze_entry_bb(#b_blk{last=#b_switch{}}, _Blocks, _Args, _Defs) ->
    %% TODO: Support switches
    [];
analyze_entry_bb(Block=#b_blk{last=#b_br{succ=D,fail=D}},
                 Blocks, Args, Defs) ->
    case has_side_effects(Block) of
        true ->
            [];
        false ->
            analyze_entry_bb(maps:get(D, Blocks), Blocks, Args, Defs)
    end;
analyze_entry_bb(Block=#b_blk{last=#b_br{bool=B,succ=S,fail=F}},
                 Blocks, Args, Defs) ->
    case has_side_effects(Block) of
        true -> [];
        false ->
            analyze_guarded_bb(analyze_bool(B, Args, Defs),
                               maps:get(S, Blocks),  maps:get(F, Blocks),
                               Blocks, Args, Defs)
    end.

analyze_guarded_bb(false, _, _, _, _, _)->
    %% We cannot statically determine the result of the guard, so give
    %% up.
    [];
analyze_guarded_bb(Condition, GuardedBlock, FallthroughBlock,
                   Blocks, Args, Defs) ->
    Result = case has_side_effects(GuardedBlock) of
                 true -> false;
                 false -> block_result(GuardedBlock, Args, Defs)
             end,
    [{Condition,Result}|analyze_bb(FallthroughBlock, Blocks, Args, Defs)].

analyze_bb(Block, Blocks, Args, Defs) ->
    case has_side_effects(Block) of
        true -> [];
        false -> analyze_side_effect_free_bb(Block, Blocks, Args, Defs)
    end.

analyze_side_effect_free_bb(Block=#b_blk{last=Last}, Blocks, Args, Defs) ->
    case Last of
        #b_ret{} ->
            case block_result(Block, Args, Defs) of
                false -> [];
                Result -> [{true,Result}]
            end;
        #b_br{succ=D,fail=D} ->
            %% TODO: Consider if this should be allowed, we would need
            %% protection against loops.
            [];
        #b_br{bool=Guard,succ=S,fail=F} ->
            analyze_guarded_bb(analyze_bool(Guard, Args, Defs),
                               maps:get(S, Blocks),  maps:get(F, Blocks),
                               Blocks, Args, Defs);
        #b_switch{} ->
            %% TODO: Support switches
            []
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
%%% Figure out if this block returns a value that only depends on the
%%% function arguments. If it does, return the value, else return
%%% false.
%%%
block_result(#b_blk{last=#b_ret{arg=Lit=#b_literal{}}}, _Args, _Defs) ->
    Lit;
block_result(#b_blk{last=#b_ret{arg=R}}, Args, _Defs) ->
    case Args of
        #{ R := Idx } -> {argument,Idx};
        _ -> false
    end;
block_result(#b_blk{last=#b_ret{}}, _Args, _Defs) ->
    %% TODO: this could potentially be constant folded into the
    %% caller, but for now ignore it
    false;
block_result(#b_blk{last=#b_switch{}}, _Args, _Defs) ->
    %% TODO: Support switches
    false;
block_result(#b_blk{last=#b_br{}}, _Args, _Defs) ->
    %% TODO: Follow unconditional branches?
    false.

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
%%% Traverse the function while removing calls which have been elided
%%% and succeeded checks for the same calls.
%%%
replace_all_uses([], _Replacements) ->
    [];
replace_all_uses([{Lbl,Blk=#b_blk{}}|Linear], Replacements) ->
    [{Lbl,replace_all_uses_blk(Blk, Replacements)}|
     replace_all_uses(Linear, Replacements)].

replace_all_uses_blk(Blk=#b_blk{is=Is}, Replacements) ->
    replace_all_uses_is(Is, [], Blk, Replacements).

replace_all_uses_is([], Acc, Blk, Replacements) ->
    replace_all_uses_term(Blk#b_blk{is=reverse(Acc)}, Replacements);
replace_all_uses_is([C=#b_set{dst=D},
                     I=#b_set{dst=S,op={succeeded,_},args=[D]}],
                    Acc,
                    Blk=#b_blk{last=Br=#b_br{bool=S}},
                    Replacements) ->
    case Replacements of
        #{ D := _Replacement } ->
            Blk#b_blk{is=reverse(Acc),last=Br#b_br{bool=#b_literal{val=true}}};
        _ ->
            replace_all_uses_is([I], [replace_all_uses_i(C, Replacements)|Acc],
                                Blk, Replacements)
    end;
replace_all_uses_is([I=#b_set{dst=D}|Is], Acc0, Blk, Replacements) ->
    Acc = case Replacements of
              #{ D := _Replacement } -> Acc0;
              _ -> [replace_all_uses_i(I, Replacements)|Acc0]
          end,
    replace_all_uses_is(Is, Acc, Blk, Replacements).

replace_all_uses_i(I=#b_set{op=phi,args=Args0}, Replacements) ->
    Args = map(fun({Val,Lbl}) ->
                       {get_replacement(Val, Replacements), Lbl}
               end, Args0),
    I#b_set{args=Args};
replace_all_uses_i(I=#b_set{args=Args0}, Replacements) ->
    Args = map(fun(Val) -> get_replacement(Val, Replacements) end, Args0),
    I#b_set{args=Args};
replace_all_uses_i(I=#b_br{bool=B}, Replacements) ->
    I#b_br{bool=get_replacement(B, Replacements)};
replace_all_uses_i(I=#b_switch{arg=A}, Replacements) ->
    I#b_switch{arg=get_replacement(A, Replacements)};
replace_all_uses_i(I=#b_ret{arg=A}, Replacements) ->
    I#b_ret{arg=get_replacement(A, Replacements)}.

replace_all_uses_term(Blk=#b_blk{last=T}, Replacements) ->
    Blk#b_blk{last=replace_all_uses_i(T, Replacements)}.

%%%
%%% Process the map of replacements so that each key maps to the final
%%% value, ie. if the map is #{ a => b, b => c} we get #{ a => c, b =>
%%% c}.
%%%
flatten_replacements(Replacements) ->
    maps:map(fun(_, R) -> get_replacement_rec(R, Replacements) end,
             Replacements).

get_replacement_rec(Key, Map) ->
    case Map of
        #{ Key := Value } -> get_replacement_rec(Value, Map);
        _ -> Key
    end.

get_replacement(Var=#b_var{}, Replacements) ->
    case Replacements of
        #{ Var := Value } -> Value;
        _ -> Var
    end;
get_replacement(R=#b_remote{mod=M,name=N}, Replacements) ->
    R#b_remote{mod=get_replacement(M, Replacements),
               name=get_replacement(N, Replacements)};
get_replacement(Other, _) ->
    Other.
