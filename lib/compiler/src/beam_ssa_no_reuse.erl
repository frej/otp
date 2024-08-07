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

-import(lists, [foldl/3]).

-export([opt/2]).

-include("beam_ssa_opt.hrl").

%% -type freshness() :: 'fresh' | 'old'.

%% -record(st,
%%         freshness = #{} :: #{#b_var{} => freshness()}
%%        ).



-spec opt(st_map(), func_info_db()) -> {st_map(), func_info_db()}.

opt(StMap0, FuncDb0) ->
    %% Ignore functions which are not in the function db (never
    %% called).
    Funs = [ F || F <- maps:keys(StMap0), is_map_key(F, FuncDb0)],

    GlobalSt =
        foldl(fun(F, GlobalSt0) ->
                      #{F:=OptSt0} = StMap0,
                      start(F, OptSt0, GlobalSt0)
              end, #{}, Funs),
    StMap =
        foldl(fun(F, StMapAcc) ->
                      #{F:=OptSt0} = StMap0,
                      OptSt = finish(F, OptSt0, GlobalSt),
                      StMapAcc#{F=>OptSt}
              end, StMap0, Funs),
    {StMap,FuncDb0}.

start(F, #opt_st{ssa=Linear0}, GlobalSt0) when is_list(Linear0) ->
    start_blks(F, Linear0, #{}, GlobalSt0).

start_blks(F, [{_L,#b_blk{is=Is0}}|Bs], St0, GlobalSt0) ->
    {St,GlobalSt} = start_is(F, Is0, St0, GlobalSt0),
    start_blks(F, Bs, St, GlobalSt);
start_blks(F, [], St, GlobalSt) ->
    GlobalSt#{F=>St}.

start_is(F, [#b_set{dst=Dst}=I|Is], St0, GlobalSt) ->
    case inhibits_reuse(I, St0) of
        true ->
            start_is(F, Is, St0#{Dst=>fresh}, GlobalSt);
        false ->
            start_is(F, Is, St0, GlobalSt)
    end;
start_is(_F, [], St, GlobalSt) -> %% TODO: drop F?
    {St,GlobalSt}.

finish(F, #opt_st{ssa=Linear0}=OptSt, GlobalSt) when is_list(Linear0) ->
    Linear = finish_blks(F, Linear0, maps:get(F, GlobalSt), GlobalSt),
    OptSt#opt_st{ssa=Linear}.

finish_blks(F, [{L,#b_blk{is=Is0}=Blk0}|Bs], St, GlobalSt) ->
    Is = finish_is(F, Is0, St, GlobalSt),
    Blk = Blk0#b_blk{is=Is},
    [{L,Blk}|finish_blks(F, Bs, St, GlobalSt)];
finish_blks(_F, [], _St, _GlobalSt) ->
    [].

finish_is(F, [#b_set{op=update_record,args=Args}=I0|Is], St, GlobalSt) ->
    [_,_,_|Updates] = Args,
    case cannot_reuse(Updates, St) of
        true ->
            I = I0#b_set{args=[#b_literal{val=copy}|tl(Args)]},
            [I|finish_is(F, Is, St, GlobalSt)];
        false ->
            [I0|finish_is(F, Is, St, GlobalSt)]
    end;
finish_is(F, [I|Is], St, GlobalSt) ->
    [I|finish_is(F, Is, St, GlobalSt)];
finish_is(_F, [], _St, _GlobalSt) -> %% TODO: drop F?
    [].

inhibits_reuse(#b_set{op=phi,args=Args}, St) ->
    foldl(fun({Value,_}, Bool) ->
                  %% TODO Extend to unknowns.
                  maps:get(Value, St, false) =/= false andalso Bool
          end, true, Args);
inhibits_reuse(#b_set{op=put_map,args=Args}, St) ->
    [_,Map|Updates] = Args,
    maps:get(Map, St, false) =/= false orelse cannot_reuse(Updates, St);
inhibits_reuse(#b_set{op=call,
                      args=[#b_remote{mod=#b_literal{val=erlang},
                                      name=#b_literal{val=Name}}|_]},
               _St) ->
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
inhibits_reuse(#b_set{op={bif,Arith},args=[#b_var{},#b_literal{}]}, _St)
  when Arith =:= '+'; Arith =:= '-' ->
    %% This is probably a counter in a record being updated. (Heuristic,
    %% but with a high probability of being correct).
    true;
inhibits_reuse(#b_set{op=Op}, _St) ->
    case Op of
        bs_create_bin -> true;
        bs_get_tail -> true;
        make_fun -> true;
        put_list -> true;
        put_tuple -> true;
        _ -> false
             %% TODO: Calls
    end.

cannot_reuse([_,Value|Updates], St) ->
    maps:get(Value, St, false) =/= false orelse cannot_reuse(Updates, St);
cannot_reuse([], _St) ->
    false.

