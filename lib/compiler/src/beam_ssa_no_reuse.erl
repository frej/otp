%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2018-2024. All Rights Reserved.
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

%%%
%%% Change the `reuse` hint to `copy` when it is highly probable that
%%% reuse will not happen.
%%%

-module(beam_ssa_no_reuse).

-import(lists, [enumerate/2, foldl/3]).

-export([opt/2]).

%% -define(DEBUG, true).

-ifdef(DEBUG).
-define(DP(FMT, ARGS), io:format(FMT, ARGS)).
-define(DP(FMT), io:format(FMT)).
-else.
-define(DP(FMT, ARGS), skip).
-define(DP(FMT), skip).
-endif.

-include("beam_ssa_opt.hrl").

-spec opt(st_map(), func_info_db()) -> {st_map(), func_info_db()}.

opt(StMap0, FuncDb0) ->
    %% Ignore functions which are not in the function db (never
    %% called).
    Funs = [ F || F <- maps:keys(StMap0), is_map_key(F, FuncDb0)],

    GlobalSt1 =
        foldl(fun(F, GlobalSt0) ->
                      #{F:=OptSt0} = StMap0,
                      init_args(F, OptSt0, GlobalSt0, FuncDb0)
              end, #{}, Funs),
    {Updates,GlobalSt2} =
        foldl(fun(F, {UpdatesAcc,GlobalStAcc}) ->
                      #{F:=OptSt0} = StMap0,
                      start(F, OptSt0, UpdatesAcc, GlobalStAcc)
              end, {sets:new(),GlobalSt1}, Funs),
    ?DP("pre-solve:~n~p~n", [GlobalSt2]),
    case sets:size(Updates) of
        0 ->
            {StMap0,FuncDb0};
        _ ->
            GlobalSt = solve_all_vars(Updates, GlobalSt2),
            ?DP("post-solve:~n~p~n", [GlobalSt]),
            StMap =
                foldl(fun(F, StMapAcc) ->
                              #{F:=OptSt0} = StMap0,
                              OptSt = finish(F, OptSt0, GlobalSt),
                              StMapAcc#{F=>OptSt}
                      end, StMap0, Funs),
            {StMap,FuncDb0}
    end.

init_args(F, #opt_st{args=Args, ssa=Linear0}, GlobalSt, FuncDb)
  when is_list(Linear0) ->
    #func_info{exported=Exported} = maps:get(F, FuncDb),
    St1 = #{ Arg => {arg,Idx} || {Idx,Arg} <- enumerate(0, Args)},
    St = case Exported of
             true ->
                 maps:fold(fun(_Arg, {arg,Idx}, Acc) ->
                                   Acc#{Idx => false}
                           end, St1, St1);
             false ->
                 St1
         end,
    GlobalSt#{F=>St}.

start(F, #opt_st{ssa=Linear0}, Updates, GlobalSt0)
  when is_list(Linear0) ->
    St = maps:get(F, GlobalSt0),
    start_blks(F, Linear0, Updates, St, GlobalSt0).

start_blks(F, [{L,#b_blk{is=Is0,last=Last}}|Bs], Updates0, St0, GlobalSt0) ->
    {Updates,St1,GlobalSt} = start_is(F, Is0, Updates0, St0, GlobalSt0),
    St = case handle_terminator(F, Last, St1) of
             ignore ->
                 St1;
             Other when L =/= ?EXCEPTION_BLOCK ->
                 %% In contrast to other instructions, a non-fresh
                 %% result cannot be omitted from the state, as then
                 %% it would be impossible to distinguish between a
                 %% function returning the result of a recursive call
                 %% to itself from when it returns in its base case.
                 ?DP("Setting result of ~p to ~p~n", [F, Other]),
                 St1#{result=>Other};
             _Something when L =:= ?EXCEPTION_BLOCK ->
                 St1
         end,
    start_blks(F, Bs, Updates, St, GlobalSt);
start_blks(F, [], Updates, St, GlobalSt) ->
    {Updates,GlobalSt#{F=>St}}.


start_is(F, [#b_set{dst=Dst,op=call,args=[#b_local{}=Callee|Args]}|Is],
         Updates, St0, GlobalSt0) ->
    %% Store local state into global state as update_call_args will
    %% modify it.
    GlobalSt1 = GlobalSt0#{F=>St0},
    ?DP("Registering call to ~p~n", [F]),
    GlobalSt = update_call_args(F, Callee, Args, GlobalSt1),
    %% Re-fetch local state.
    #{F:=St} = GlobalSt,
    start_is(F, Is, Updates, St#{Dst=>{result_of,Callee}}, GlobalSt);
start_is(F, [#b_set{dst=Dst}=I|Is], Updates0, St0, GlobalSt) ->
    Updates = case I of
                  #b_set{dst=Dst,op=update_record,
                         args=[#b_literal{val=reuse},_,_|Us]} ->
                      add_updates(F, Us, Updates0);
                  _ ->
                      Updates0
              end,
    case inhibits_reuse(F, I, St0) of
        false ->
            start_is(F, Is, Updates, St0, GlobalSt);
        Other ->
            start_is(F, Is, Updates, St0#{Dst=>Other}, GlobalSt)
    end;
start_is(_F, [], Updates, St, GlobalSt) -> %% TODO: drop F?
    {Updates,St,GlobalSt}.

finish(F, #opt_st{ssa=Linear0}=OptSt, GlobalSt) when is_list(Linear0) ->
    Linear = finish_blks(F, Linear0, maps:get(F, GlobalSt), GlobalSt),
    OptSt#opt_st{ssa=Linear}.

finish_blks(F, [{L,#b_blk{is=Is0}=Blk0}|Bs], St, GlobalSt) ->
    Is = finish_is(F, Is0, St, GlobalSt),
    Blk = Blk0#b_blk{is=Is},
    [{L,Blk}|finish_blks(F, Bs, St, GlobalSt)];
finish_blks(_F, [], _St, _GlobalSt) ->
    [].

finish_is(F, [#b_set{dst=_Dst,op=update_record,
                     args=[#b_literal{val=reuse},_,_|Updates]=Args}=I0|Is],
          St, GlobalSt) ->
    case cannot_reuse(Updates, St) of
        true ->
            ?DP("downgrading: ~p ~p~n", [F, _Dst]),
            I = I0#b_set{args=[#b_literal{val=copy}|tl(Args)]},
            [I|finish_is(F, Is, St, GlobalSt)];
        false ->
            [I0|finish_is(F, Is, St, GlobalSt)]
    end;
finish_is(F, [I|Is], St, GlobalSt) ->
    [I|finish_is(F, Is, St, GlobalSt)];
finish_is(_F, [], _St, _GlobalSt) -> %% TODO: drop F?
    [].

inhibits_reuse(F, #b_set{op=phi,args=Args}, St) ->
    make_all([as_arg(Value, F, St) || {Value,_} <- Args]);
inhibits_reuse(F, #b_set{op=put_map,args=Args}, St) ->
    [_,Map|Updates] = Args,
    make_any([as_arg(Map, F, St),
              make_all([as_arg(A, F, St)
                        || A <- get_update_vals(Updates)])]);
inhibits_reuse(_,
               #b_set{op=call,
                      args=[#b_remote{mod=#b_literal{val=erlang},
                                      name=#b_literal{val=Name}}|_]}, _St) ->
    case Name of
        '++' -> true;
        '--' -> true;
        atom_to_list -> true;
        atom_to_binary -> true;
        list_to_tuple -> true;
        make_ref -> true;
        monitor -> true;
        setelement -> true;
        send_after -> true;
        spawn -> true;
        spawn_link -> true;
        spawn_monitor -> true;
        tuple_to_list -> true;
        _ -> false
    end;
inhibits_reuse(_, #b_set{op={bif,Arith},args=[#b_var{},#b_literal{}]}, _St)
  when Arith =:= '+'; Arith =:= '-' ->
    %% This is probably a counter in a record being updated. (Heuristic,
    %% but with a high probability of being correct).
    true;
inhibits_reuse(_, #b_set{op=Op}, _St) ->
    case Op of
        bs_create_bin -> true;
        bs_get_tail -> true;
        make_fun -> true;
        put_list -> true;
        put_tuple -> true;
        _ -> false
    end.

handle_terminator(F, #b_ret{arg=A}, St) when is_map_key(result, St) ->
    %% There is already a registered result.
    #{result:=R} = St,
    make_all([as_arg(A, F, St), R]);
handle_terminator(F, #b_ret{arg=A}, St) ->
    %% There could be that we already have seen a return, we need to
    %% incorporate this value in our result.
    as_arg(A, F, St);
handle_terminator(_, #b_br{}, _St) ->
    ignore;
handle_terminator(_, #b_switch{}, _St) ->
    ignore.

cannot_reuse([_,Value|Updates], St) ->
    maps:get(Value, St, false) orelse cannot_reuse(Updates, St);
cannot_reuse([], _St) ->
    false.

solve_all_vars(Vars, GS) ->
    ?DP("Solving for: ~p~n", [sets:to_list(Vars)]),
    solve_vars(sets:to_list(Vars), GS).

solve_vars([Var|Vars], GS0) ->
    GS = case solve(Var, [], GS0) of
             {pending,Chain} ->
                 %% As solve_all/3 and solve_any/3 skips pending
                 %% values, the only case when a pending result from
                 %% solve/3 will occur is when Var is circularly
                 %% defined and the value never is non-inhibiting.
                 update_chain(Chain, true, GS0);
             {_,GS1} ->
                 GS1
         end,
    solve_vars(Vars, GS);
solve_vars([], GS) ->
    GS.

solve({F,X}=V, Chain, GS) ->
    #b_local{} = F, % Assertion.
    #{F:=StF} = GS,
    ?DP("Solving ~p~n", [V]),
    case StF of
        #{X:=Status} when Status =:= true; Status =:= false ->
            ?DP("determined status: ~p~n", [Status]),
            {Status, update_chain(Chain, Status, GS)};
        #{X:={result_of,Callee}} ->
            ?DP("result_of: ~p~n", [Callee]),
            solve({Callee,result}, [V|Chain], mark_pending(F, X, GS));
        #{X:={arg,Idx}} ->
            ?DP("arg ~p~n", [Idx]),
            solve({F,Idx}, [V|Chain], mark_pending(F, X, GS));
        #{X:=pending} ->
            ?DP("pending~n"),
            {pending,Chain};
        #{X:={all,Vs}} ->
            ?DP("all~n"),
            solve_all(unique(Vs), [V|Chain], mark_pending(F, X, GS));
        #{X:={any,Vs}} ->
            ?DP("any~n"),
            solve_any(unique(Vs), [V|Chain], mark_pending(F, X, GS));
        #{X:={#b_local{},_}=V2} ->
            ?DP("f+v~n"),
            solve(V2, [V|Chain], mark_pending(F, X, GS));
        #{X:=Something} ->
            throw({something,Something});
        #{} ->
            ?DP("default false~n"),
            {false, update_chain(Chain, false, GS)}
    end.

mark_pending(F, X, GS) ->
    #{F:=StF} = GS,
    GS#{F=>StF#{X=>pending}}.


update_chain([{F,X}=_V|Chain], Status, GS0)
  when Status =:= true ; Status =:= false ->
    ?DP("Updating chain for ~p to ~p~n", [_V, Status]),
    #{F:=StF} = GS0,
    case X of
        #b_var{} -> ok;
        {arg,_} -> ok;
        result -> ok;
        I when is_integer(I) -> ok
    end,
    GS = case Status of
             true ->
                 GS0#{F=>StF#{X=>Status}};
             false ->
                 GS0#{F=>maps:remove(X, StF)}
         end,
    update_chain(Chain, Status, GS);
update_chain([], _, GS) ->
    GS.

solve_all([V|Values], Chain, GS0) ->
    Status = case V of
                 {#b_local{},_} ->
                     solve(V, [], GS0);
                 {any,Any} ->
                     solve_any(Any, [], GS0)
             end,
    case Status of
        {true,GS} ->
            solve_all(Values, Chain, GS);
        {false,GS} ->
            {false,update_chain(Chain, false, GS)};
        {pending,_} ->
            solve_all(Values, Chain, GS0)
    end;
solve_all([], Chain, GS) ->
    {true,update_chain(Chain, true, GS)}.

solve_any([V|Values], Chain, GS0) ->
    Status = case V of
                 {#b_local{},_} ->
                     solve(V, [], GS0);
                 {all,All} ->
                     solve_all(All, [], GS0)
             end,
    case Status of
        {false,GS} ->
            solve_any(Values, Chain, GS);
        {true,GS} ->
            {true,update_chain(Chain, true, GS)};
        {pending,_} ->
            solve_any(Values, Chain, GS0)
    end;
solve_any([], Chain, GS) ->
    {false,update_chain(Chain, false, GS)}.

update_call_args(Caller, Callee, Args, GlobalSt0) ->
    #{Caller:=CallerSt0,Callee:=CalleeSt0} = GlobalSt0,
    CalleeSt = update_call_args(
                 0,
                 [as_arg(A, Caller, CallerSt0) || A <- Args],
                 CalleeSt0),
    GlobalSt0#{Callee:=CalleeSt}.

as_arg(Arg, Caller, CallerSt) ->
    ?DP("as_arg(~p)~n", [Arg]),
    ?DP("** ~p~n", [CallerSt]),
    case CallerSt of
        #{Arg:=true} ->
            true;
        #{Arg:=false} ->
            false;
        #{Arg:={arg,Idx}} ->
            {Caller,Idx};
        #{Arg:={all,_}=All} ->
            All;
        #{Arg:={any,_}=Any} ->
            Any;
        #{Arg:={result_of,Callee}} ->
            {Callee,result};
        #{Arg:={#b_local{},_}=V} ->
            V;
        #{Arg:=Something} ->
            throw({as_arg,Something});
        #{} ->
            {Caller,Arg}
    end.

update_call_args(Idx, [Arg|Args], CalleeSt0) ->
    Status = make_all([Arg, maps:get(Idx, CalleeSt0, true)]),
    ?DP("  arg ~p: ~p old: ~p new: ~p~n",
        [Idx, Arg, maps:get(Idx, CalleeSt0, true), Status]),
    CalleeSt = CalleeSt0#{Idx=>Status},
    update_call_args(Idx + 1, Args, CalleeSt);
update_call_args(_, [], CalleeSt) ->
    CalleeSt.

add_updates(F, [_,Var|Rest], Updates) ->
    add_updates(F, Rest, sets:add_element({F,Var}, Updates));
add_updates(_F, [], Updates) ->
    Updates.

get_update_vals([_,Var|Rest]) ->
    [Var|get_update_vals(Rest)];
get_update_vals([]) ->
    [].

make_all(Values) ->
    make_all(Values, []).

make_all([true|Values], Acc) ->
    make_all(Values, Acc);
make_all([false|_], _) ->
    false;
make_all([{all,All}|Values], Acc) ->
    make_all(Values, All++Acc);
make_all([V|Values], Acc) ->
    make_all(Values, [V|Acc]);
make_all([], []) ->
    true;
make_all([], Acc) ->
    singleton_or_tag(Acc, all).

make_any(Values) ->
    make_any(Values, []).

make_any([false|Values], Acc) ->
    make_any(Values, Acc);
make_any([true|_], _) ->
    true;
make_any([{any,Any}|Values], Acc) ->
    make_any(Values, Any++Acc);
make_any([V|Values], Acc) ->
    make_any(Values, [V|Acc]);
make_any([], []) ->
    false;
make_any([], Acc) ->
    singleton_or_tag(Acc, any).

singleton_or_tag([Single], _Tag) ->
    Single;
singleton_or_tag(Multiple, Tag) ->
    {Tag,Multiple}.

unique(Ls) when is_list(Ls) ->
    sets:to_list(sets:from_list(Ls)).
