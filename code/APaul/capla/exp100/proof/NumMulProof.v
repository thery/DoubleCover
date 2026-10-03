(** * num_mul_small, num_mulshr: the specs (task T5) *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge Exp100Capla.Specs.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* p = a w on 7 limbs, for w < 2^32 *)
Theorem num_mul_small_spec ps xs w e1 result :
  length ps = 7%nat -> length xs = 6%nat -> limbs xs ->
  (Int64.unsigned w < 2 ^ limb_bits)%Z ->
  eval_funcall ge (Internal num_mul_small43)
    [Varr (map Vint64 ps); Varr (map Vint64 xs); Vint64 w] e1 (Some result) ->
  exists ps', e1!(param 0 num_mul_small43) = Some (Varr (map Vint64 ps')) /\
    length ps' = 7%nat /\ limbs ps' /\
    val32 ps' = (val32 xs * Int64.unsigned w)%Z.
Admitted.

(* r = floor(a b / 2^160), when it fits in 192 bits *)
Theorem num_mulshr_spec rs xs ys e1 result :
  length rs = 6%nat -> length xs = 6%nat -> length ys = 6%nat ->
  limbs xs -> limbs ys ->
  (val32 xs * val32 ys < 2 ^ (ExpConsts.P + ExpModel.num_bits))%Z ->
  eval_funcall ge (Internal num_mulshr59)
    [Varr (map Vint64 rs); Varr (map Vint64 xs); Varr (map Vint64 ys)]
    e1 (Some result) ->
  exists rs', e1!(param 0 num_mulshr59) = Some (Varr (map Vint64 rs')) /\
    length rs' = 6%nat /\ limbs rs' /\
    val32 rs' = ExpModel.mulshr (val32 xs) (val32 ys).
Admitted.
