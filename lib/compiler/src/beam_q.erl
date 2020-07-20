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

-module(beam_q).

-export([module/2]).

-include("erl_compile.hrl").

-spec module(beam_utils:module_code(), file:io_device()) -> 'ok'.

module({Mod,_Exp,Attr,Fs,_Lc}, IO) ->
    Guards = {guard_chains, _} = lists:keyfind(guard_chains, 1, Attr),
    Q = fold_funs(Mod, Fs, [Guards]),
    io:format(IO, "~p.\n", [Q]),
    ok.

fold_funs(Mod, [{function,F,A,_,Is}|Fs], Q) ->
    Init = #{
             instructions => 0,
             restores => 0,
             spills => 0,
             stack => 0,
             xx_moves => 0,
             y_accesses => 0,
             y_init => 0,
             y_kill => 0,
             yy_moves => 0
            },
    fold_funs(Mod, Fs, [{{Mod,F,A}, fold_is(Is, Init)}|Q]);
fold_funs(_, [], Q) ->
    Q.

add(V, Key, Q) ->
    #{ Key := N }=Q,
    Q#{ Key := N+V }.

inc(Key, Q) ->
    add(1, Key, Q).

max(V, Key, Q) ->
    #{ Key := Old}=Q,
    case V > Old of
        true -> Q#{ Key := V };
        false -> Q
    end.

i(Q) ->
    inc(instructions, Q).

spill(Q) ->
    inc(spills, Q).

restore(Q) ->
    inc(restores, Q).

fold_is([], Q) ->
    Q;
fold_is([{label,_}|Is], Q) ->
    fold_is(Is, Q);
fold_is([{move,{x,_},{x,_}}|Is], Q) ->
    fold_is(Is, inc(xx_moves, i(Q)));
fold_is([{move,{y,_},{y,_}}|Is], Q) ->
    fold_is(Is, inc(yy_moves, i(Q)));
fold_is([{move,{x,_},{y,_}}|Is], Q) ->
    fold_is(Is, spill(i(Q)));
fold_is([{move,{y,_},{x,_}}|Is], Q) ->
    fold_is(Is, restore(i(Q)));

fold_is([{swap,{x,_},{y,_}}|Is], Q) ->
    fold_is(Is, restore(spill(i(Q))));
fold_is([{swap,{y,_},{x,_}}|Is], Q) ->
    fold_is(Is, spill(restore(i(Q))));
fold_is([{move,{x,_},{x,_}}|Is], Q) ->
    fold_is(Is, inc(xx_moves, inc(xx_moves, i(Q))));
fold_is([{move,{y,_},{y,_}}|Is], Q) ->
    fold_is(Is, inc(yy_moves, inc(yy_moves, i(Q))));

fold_is([{init,{y,_}}|Is], Q) ->
    fold_is(Is, inc(y_init, i(Q)));
fold_is([{kill,{y,_}}|Is], Q) ->
    fold_is(Is, inc(y_kill, i(Q)));
fold_is([{allocate,Stk,_Live}|Is], Q) ->
    fold_is(Is, max(Stk, stack, i(Q)));
fold_is([{allocate_heap,Stk,_Heap,_Live}|Is], Q) ->
    fold_is(Is, max(Stk, stack, i(Q)));
fold_is([{allocate_zero,Stk,_Live}|Is], Q) ->
    fold_is(Is, max(Stk, stack, i(Q)));
fold_is([{allocate_heap_zero,Stk,_Heap,_Live}|Is], Q) ->
    fold_is(Is, max(Stk, stack, i(Q)));
fold_is([I|Is], Q) when is_tuple(I) ->
    [_|Args] = erlang:tuple_to_list(I),
    fold_is(Is, add(sum_ys(Args), y_accesses, i(Q)));
fold_is([_|Is], Q) ->
    fold_is(Is, i(Q)).

sum_ys([]) ->
    0;
sum_ys(X) when is_number(X) ->
    0;
sum_ys([{y,_}|As]) ->
    1 + sum_ys(As);
sum_ys([X|As]) when is_tuple(X) ->
    sum_ys(erlang:tuple_to_list(X)) + sum_ys(As);
sum_ys([X|As]) when is_list(X) ->
    sum_ys(X) + sum_ys(As);
sum_ys([_|As]) ->
    sum_ys(As).
