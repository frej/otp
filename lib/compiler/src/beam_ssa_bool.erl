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
%% The purpose of this pass is to optimize boolean expressions in
%% guards. Instead of evaluating a boolean expression and finally
%% comparing it to 'true', evaluate the expression using control flow.
%%
%% This pass is run directly after conversion to SSA code because some
%% optimizations in beam_ssa_opt (especially sinking of
%% get_tuple_element instructions) would prevent these optimizations
%% or at least make them much more difficult to perform.
%%
%% As an example, take the guard:
%%
%%     when is_integer(V0), is_atom(V1) ->
%%
%% The unoptimized SSA code translated to pseudo BEAM code would look
%% like:
%%
%%     bif is_integer V0 => Bool0
%%     bif is_atom V1    => Bool1
%%     bif and Bool0 Bool1 => Bool
%%     test Bool =:= true else goto Fail
%%     ...
%%   Fail:
%%     ...
%%
%%  The optimized code would look like:
%%
%%     test is_integer V0 else goto Fail
%%     test is_atom V1    else goto Fail
%%     ...
%%   Fail:
%%     ...
%%
%%  An 'or' operation is only slightly more complicated:
%%
%%     test is_integer V0 else goto NotFailedYet
%%     goto Success
%%
%%   NotFailedYet:
%%     test is_atom V1 else goto Fail
%%
%%   Success:
%%     ...
%%   Fail:
%%     ...
%%
%% The unoptimized SSA code for the first example looks like:
%%
%% 0:
%%   _2 = bif:is_integer _0
%%   _3 = bif:is_atom _1
%%   _7 = bif:'and' _2, _3
%%   @ssa_bool = succeeded _7
%%   br @ssa_bool, label 4, label 3
%%
%% 4:
%%   @ssa_bool:5 = bif:'=:=' _7, literal true
%%   br @ssa_bool:5, label 6, label 3
%%
%% 6:
%%   ret literal ok
%%
%% 3: Error.
%%   ...
%%
%% The optimized SSA code looks like:
%%
%% 0:
%%   _2 = bif:is_integer _0
%%   br _2, label 11, label 3
%%
%% 11:
%%   _3 = bif:is_atom _1
%%   br _3, label 6, label 3
%%
%% 6:
%%   ret literal ok
%%
%% 3: Error.
%%   ...

-module(beam_ssa_bool).
-export([module/2]).
-import(lists, [all/2,foldl/3,keyfind/3,
                reverse/1,sort/1]).

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

opt_function(#b_function{bs=Blocks0,cnt=Count0}=F) ->
    {Blocks1,Count1} = pre_opt(Blocks0, Count0),
    F#b_function{bs=Blocks1,cnt=Count1}.

%%%
%%% Do some optimizations to help the main boolean optimization pass:
%%%
%%%    * Remove `succeeded` instructions that can't fail after `and`,
%%%      `or`, and `not`. The main optimization pass can only optimize
%%%      boolean operators that are known not to fail.
%%%
%%%    * Rewrite a boolean #b_switch{} to a #b_br{} if the fail label
%%%      can't be reached or is not important. (The main optimization
%%%      can't handle #b_switch{}.)
%%%
%%%    * Simplify phi nodes, eliminating them if they only have one
%%%      value. Also annotate phi nodes that are known to evaluate
%%%      to a boolean.
%%%

-type var() :: beam_ssa:b_var().

%% Note: We use the substitution map for both substitutions and type
%% information. If the associated value for a variable is a #b_set{},
%% it means that the value is a boolean.
-type pre_sub_val() ::
        beam_ssa:value() |                      %Value to be substituted.
        beam_ssa:b_set() |                      %This variable is a boolean.
        {'true_or_any',beam_ssa:label()} |
        '=:='.

-type pre_sub_map() :: #{'uses' => {'uses',beam_ssa:block_map() | list()},
                         var() => pre_sub_val()}.

pre_opt(Blocks, Count) ->
    Top = beam_ssa:rpo(Blocks),

    %% Collect information to help the pre_opt pass to optimize
    %% `switch` instructions.
    Sub0 = #{uses => {uses,Blocks}},
    Sub1 = get_phi_info(Top, Blocks, Sub0),
    Sub = maps:remove(uses, Sub1),

    %% Now do the actual optimizations.
    Reached = gb_sets:singleton(hd(Top)),
    pre_opt(Top, Sub, Reached, Count, Blocks).

-spec get_phi_info(Ls, Blocks, Sub0) -> Sub when
      Ls :: [beam_ssa:label()],
      Blocks :: beam_ssa:block_map(),
      Sub0 :: pre_sub_map(),
      Sub :: pre_sub_map().

%% get_phi_info([Label], Blocks, Sub0) -> Sub.
%%  Collect information to help us optimize `switch` instructions
%%  such as:
%%
%%    switch SomeVar, label _, [ {literal false, _ }, {literal true, _ } ]
%%      .
%%      .
%%      .
%%    PhiVar = phi { SomeVar, _ }, { literal fail, _ }, { literal false, _}
%%    EqBool = bif:'=:=' PhiVar, literal true
%%
%%  Here it can be seen that `SomeVar` is compared to `true`. If
%%  `SomeVar` is not `true`, it does not matter whether its value is
%%  `false` or some other value. That means that the `switch` can be
%%  replaced with a two-way `br`:
%%
%%    NewBoolVar = bif:'=:=' SomeVar, literal true
%%    br NewBoolVar, label _, label _
%%
%%  For this example, the value {true_or_any,LabelOfPhiBlock} will be
%%  added for the key `SomeVar` in the substitution map.

get_phi_info([L|Ls], Blocks, Sub0) ->
    Sub = get_phi_info(Ls, Blocks, Sub0),
    #b_blk{is=Is} = map_get(L, Blocks),
    get_phi_info_is(Is, L, Sub);
get_phi_info([], _, Sub) -> Sub.

get_phi_info_is([I|Is], From, Sub0) ->
    Sub = get_phi_info_is(Is, From, Sub0),
    get_phi_info_instr(I, From, Sub);
get_phi_info_is([], _, Sub) -> Sub.

get_phi_info_instr(#b_set{op={bif,'=:='},
                          args=[#b_var{}=Bool,#b_literal{val=true}]},
                   _From, Sub) ->
    Sub#{Bool=>'=:='};
get_phi_info_instr(#b_set{op=phi,dst=Dst,args=Args}, From, Sub0) ->
    {Safe,Sub} =
        case Sub0 of
            #{Dst:='=:='} ->
                get_phi_info_single_use(Dst, Sub0);
            #{Dst:={true_or_any,_}} ->
                {true,Sub0};
            #{} ->
                {false,Sub0}
        end,
    case Safe of
        true ->
            foldl(fun({#b_var{}=V,_}, A) ->
                          A#{V => {true_or_any,From}};
                     (_, A) -> A
                  end, Sub, Args);
        false -> Sub
    end;
get_phi_info_instr(_, _, Sub) -> Sub.

get_phi_info_single_use(Var, Sub) ->
    case map_get(uses, Sub) of
        Uses when is_map(Uses) ->
            {case Uses of
                 #{Var:=[_]} -> true;
                 #{Var:=[_|_]} -> false
             end,Sub};
        {uses,Blocks} ->
            Uses = beam_ssa:uses(Blocks),
            get_phi_info_single_use(Var, Sub#{uses => Uses})
    end.

-spec pre_opt(Ls, Sub, Reached, Count0, Blocks0) -> {Blocks,Count} when
      Ls :: [beam_ssa:label()],
      Reached :: gb_sets:set(beam_ssa:label()),
      Count0 :: beam_ssa:label(),
      Blocks0 :: beam_ssa:block_map(),
      Sub :: pre_sub_map(),
      Count :: beam_ssa:label(),
      Blocks :: beam_ssa:block_map().

pre_opt([L|Ls], Sub0, Reached0, Count0, Blocks) ->
    case gb_sets:is_member(L, Reached0) of
        false ->
            %% This block will never be reached.
            pre_opt(Ls, Sub0, Reached0, Count0, maps:remove(L, Blocks));
        true ->
            #b_blk{is=Is0,last=Last0} = Blk0 = map_get(L, Blocks),
            {Is,Sub} = pre_opt_is(Is0, Reached0, Sub0, []),
            case pre_opt_terminator(Last0, Sub, Blocks) of
                {#b_set{}=Test0,#b_br{}=Br0} ->
                    %% Here is a #b_switch{} that has been reduced to
                    %% a '=:=' followed by a two-way `br`.
                    Bool = #b_var{name={'@ssa_bool',Count0}},
                    Count = Count0 + 1,
                    Test = Test0#b_set{dst=Bool},
                    Br = Br0#b_br{bool=Bool},
                    Blk = Blk0#b_blk{is=Is++[Test],last=Br},
                    Successors = beam_ssa:successors(Blk),
                    Reached = gb_sets:union(Reached0,
                                            gb_sets:from_list(Successors)),
                    pre_opt(Ls, Sub, Reached, Count, Blocks#{L:=Blk});
                Last ->
                    Blk = Blk0#b_blk{is=Is,last=Last},
                    Successors = beam_ssa:successors(Blk),
                    Reached = gb_sets:union(Reached0,
                                            gb_sets:from_list(Successors)),
                    pre_opt(Ls, Sub, Reached, Count0, Blocks#{L:=Blk})
            end
    end;
pre_opt([], _, _, Count, Blocks) ->
    {Blocks,Count}.

pre_opt_is([#b_set{op=phi,dst=Dst,args=Args0}=I0|Is], Reached, Sub0, Acc) ->
    Args1 = [{Val,From} || {Val,From} <- Args0,
                           gb_sets:is_member(From, Reached)],
    Args = sub_args(Args1, Sub0),
    case all_same(Args) of
        true ->
            %% Single value or all values are the same. We can remove
            %% the phi node.
            {Arg,_} = hd(Args),
            Sub = Sub0#{Dst=>Arg},
            pre_opt_is(Is, Reached, Sub, Acc);
        false ->
            case pre_is_phi_bool(Args, Sub0) of
                true ->
                    %% The value of the phi node is always a
                    %% boolean. Update type information in the sub map
                    %% and add an annotation.
                    Anno = I0#b_set.anno,
                    I = I0#b_set{args=Args,anno=Anno#{boolean_phi=>true}},
                    Sub = Sub0#{Dst=>I},
                    pre_opt_is(Is, Reached, Sub, [I|Acc]);
                false ->
                    I = I0#b_set{args=Args},
                    pre_opt_is(Is, Reached, Sub0, [I|Acc])
            end
    end;
pre_opt_is([#b_set{op=succeeded,dst=Dst,args=Args0}=I0|Is], Reached, Sub0, Acc) ->
    [Arg] = Args = sub_args(Args0, Sub0),
    I = I0#b_set{args=Args},
    case pre_is_safe_bool(Arg, Sub0) of
        true ->
            %% The preceding boolean operation can't fail. Get rid
            %% of this `succeeded` instruction.
            Sub = Sub0#{Dst=>#b_literal{val=true}},
            pre_opt_is(Is, Reached, Sub, Acc);
        false ->
            pre_opt_is(Is, Reached, Sub0, [I|Acc])
    end;
pre_opt_is([#b_set{dst=Dst,args=Args0}=I0|Is], Reached, Sub0, Acc) ->
    Args = sub_args(Args0, Sub0),
    I = I0#b_set{args=Args},
    case is_bool_expr(I) of
        true ->
            case pre_eval_op(I, Sub0) of
                none ->
                    Sub = Sub0#{Dst=>I},
                    pre_opt_is(Is, Reached, Sub, [I|Acc]);
                #b_var{}=Var ->
                    %% We must remove the 'succeeded' instruction that
                    %% follows since the variable it checks is gone.
                    [#b_set{op=succeeded,dst=SuccDst,args=[Dst]}] = Is,
                    Sub = Sub0#{Dst=>Var,SuccDst=>#b_literal{val=true}},
                    pre_opt_is([], Reached, Sub, Acc);
                #b_literal{}=Lit ->
                    Sub = Sub0#{Dst=>Lit},
                    pre_opt_is(Is, Reached, Sub, Acc)
            end;
        false ->
            pre_opt_is(Is, Reached, Sub0, [I|Acc])
        end;
pre_opt_is([], _Reached, Sub, Acc) ->
    {reverse(Acc),Sub}.

pre_opt_terminator(#b_br{bool=#b_literal{}}=Br, _Sub, _Blocks) ->
    Br;
pre_opt_terminator(#b_br{bool=Bool}=Br0, Sub, Blocks) ->
    case beam_ssa:normalize(Br0#b_br{bool=sub_arg(Bool, Sub)}) of
        Br0 ->
            Br0;
        #b_br{bool=#b_literal{val=true},succ=Next}=Br ->
            %% See if the terminator from the successor block
            %% can be incorporated into this block to give
            %% more opportunities for optimization.
            #b_blk{is=Is,last=Last} = map_get(Next, Blocks),
            case {Is,Last} of
                {[],#b_switch{}} ->
                    pre_opt_terminator(Last, Sub, Blocks);
                {_,_} ->
                    Br
            end
    end;
pre_opt_terminator(#b_ret{arg=Arg}=Ret, Sub, _Blocks) ->
    Ret#b_ret{arg=sub_arg(Arg, Sub)};
pre_opt_terminator(#b_switch{arg=Arg0,list=List}=Sw0, Sub, Blocks) ->
    Arg = sub_arg(Arg0, Sub),
    Sw = Sw0#b_switch{arg=Arg},
    case sort(List) of
        [{#b_literal{val=false},Fail},
         {#b_literal{val=true},Succ}] ->
            case pre_is_arg_bool(Arg, Sub) of
                false ->
                    pre_opt_sw(Sw, Fail, Succ, Sub, Blocks);
                true ->
                    beam_ssa:normalize(#b_br{bool=Arg,succ=Succ,fail=Fail})
            end;
        _ ->
            Sw
    end.

pre_opt_sw(#b_switch{arg=Arg,fail=Fail}=Sw, False, True, Sub, Blocks) ->
    case Sub of
        #{Arg:={true_or_any,PhiL}} ->
            #{Fail:=FailBlk,False:=FalseBlk,PhiL:=PhiBlk} = Blocks,
            case {FailBlk,FalseBlk,PhiBlk} of
                {#b_blk{is=[],last=#b_br{succ=PhiL,fail=PhiL}},
                 #b_blk{is=[],last=#b_br{succ=PhiL,fail=PhiL}},
                 #b_blk{is=[#b_set{op=phi,args=PhiArgs}|_]}} ->
                    case keyfind(False, 2, PhiArgs) of
                        {#b_literal{val=Bool},False} when Bool =/= true ->
                            %% This is an `andalso` in a guard. The code
                            %% can be simplified to a two-way `br` because
                            %% the actual value of the variable does not
                            %% matter if it is not equal to `true`.
                            DummyDst = #b_var{name=0},
                            {#b_set{op={bif,'=:='},dst=DummyDst,
                                    args=[Arg,#b_literal{val=true}]},
                             #b_br{bool=DummyDst,succ=True,fail=False}};
                        {_,_} ->
                            Sw
                    end;
                {_,_,_} ->
                    Sw
            end;
        #{} ->
            Sw
    end.

pre_eval_op(#b_set{op={bif,Op},args=Args}, Sub) ->
    case pre_are_args_bool(Args, Sub) of
        true ->
            case {Op,Args} of
                {'and',[#b_literal{val=true},#b_var{}=Res]} -> Res;
                {'and',[#b_literal{val=false}=Res,#b_var{}]} -> Res;
                {'and',[#b_var{}=Res,#b_literal{val=true}]} -> Res;
                {'and',[#b_var{},#b_literal{val=false}=Res]} -> Res;
                {'or',[#b_literal{val=true}=Res,#b_var{}]} -> Res;
                {'or',[#b_literal{val=false},#b_var{}=Res]} -> Res;
                {'or',[#b_var{},#b_literal{val=true}=Res]} -> Res;
                {'or',[#b_var{}=Res,#b_literal{val=false}]} -> Res;
                _ -> none
            end;
        false ->
            none
    end.

all_same([{H,_}|T]) ->
    all(fun({E,_}) -> E =:= H end, T).

pre_is_phi_bool([{#b_literal{val=Lit},_}|As], Sub) ->
    is_boolean(Lit) andalso pre_is_phi_bool(As, Sub);
pre_is_phi_bool([{#b_var{}=A,_}|As], Sub) ->
    case Sub of
        #{A:=#b_set{}} ->
            pre_is_phi_bool(As, Sub);
        #{} ->
            false
    end;
pre_is_phi_bool([], _Sub) -> true.

pre_is_safe_bool(#b_literal{}, _Sub) ->
    true;
pre_is_safe_bool(Var, Sub) ->
    case Sub of
        #{Var:=#b_set{op={bif,is_function},
                      args=[_,Arity]}} ->
            case Arity of
                #b_literal{val=Lit} ->
                    is_integer(Lit) andalso Lit >= 0;
                #b_var{} ->
                    false
            end;
        #{Var:=#b_set{op={bif,Op},args=Args}} ->
            Arity = length(Args),
            erl_internal:bool_op(Op, Arity) andalso
                pre_are_args_bool(Args, Sub);
        #{} ->
            false
    end.

pre_are_args_bool([A|As], Sub) ->
    pre_is_arg_bool(A, Sub) andalso pre_are_args_bool(As, Sub);
pre_are_args_bool([], _Sub) -> true.

pre_is_arg_bool(#b_literal{val=Lit}, _Sub) ->
    is_boolean(Lit);
pre_is_arg_bool(#b_var{}=A, Sub) ->
    case Sub of
        #{A:=#b_set{}} ->
            true;
        #{} ->
            false
    end.

sub_args(Args, Sub) ->
    [sub_arg(Arg, Sub) || Arg <- Args].

sub_arg({#b_var{}=Arg,From}, Sub) when is_integer(From) ->
    {do_sub_arg(Arg, Sub),From};
sub_arg(#b_var{}=Arg, Sub) ->
    do_sub_arg(Arg, Sub);
sub_arg(#b_remote{mod=Mod,name=Name}=Rem, Sub) ->
    Rem#b_remote{mod=do_sub_arg(Mod, Sub),
                 name=do_sub_arg(Name, Sub)};
sub_arg(Arg, _Sub) -> Arg.

do_sub_arg(#b_var{}=Old, Sub) ->
    case Sub of
        #{Old:=#b_literal{}=New} -> New;
        #{Old:=#b_var{}=New} -> New;
        #{} -> Old
    end;
do_sub_arg(#b_literal{}=Old, _Sub) -> Old.

is_bool_expr(#b_set{op={bif,Op},args=Args}) ->
    Arity = length(Args),
    erl_internal:comp_op(Op, Arity) orelse
	erl_internal:new_type_test(Op, Arity) orelse
	erl_internal:bool_op(Op, Arity);
is_bool_expr(_) -> false.

