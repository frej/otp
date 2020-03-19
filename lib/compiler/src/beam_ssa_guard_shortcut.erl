%%
%% %CopyrightBegin%
%%
%% Copyright Ericsson AB 2019. All Rights Reserved.
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
%% Purpose: We look for branches marked with the annotation
%% 'guard_failure' => Label and rewrite them failure branch to go to
%% Label. This operation is safe to do as the annotation is only
%% placed on branches which check the result of {succeed,guard}
%% operations inside guards.

-module(beam_ssa_guard_shortcut).
-export([module/2]).

-include("beam_ssa.hrl").

-spec module(beam_ssa:b_module(), [compile:option()]) ->
                    {'ok',beam_ssa:b_module()}.

module(#b_module{body=Fs0}=Module, _Opts) ->
    Fs = [function(F) || F <- Fs0],
    {ok,Module#b_module{body=Fs}}.

function(#b_function{anno=Anno}=F) ->
    try
        opt_function(F)
    catch
        Class:Error:Stack ->
            #{func_info:={_,Name,Arity}} = Anno,
            io:fwrite("Function: ~w/~w\n", [Name,Arity]),
            erlang:raise(Class, Error, Stack)
    end.

opt_function(#b_function{bs=Blocks0}=F) ->
    Blocks = maps:map(fun(_, #b_blk{last=T}=B) ->
                              B#b_blk{last=opt_terminator(T)}
                      end, Blocks0),
    F#b_function{bs=Blocks}.

%% opt_terminator(#b_br{}=T) ->
%%     case beam_ssa:get_anno(guard_failure, T, false) of
%%         false -> T;
%%         Lbl -> T#b_br{fail=Lbl}
%%     end;
opt_terminator(T) ->
    T.
