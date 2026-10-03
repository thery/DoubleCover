(** * mul_ln2, guess_n: the specs (task T7) *)

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

(* q = floor(n LN2 / 2^32), for n < 2^32 *)
Theorem mul_ln2_spec qs n e1 result :
  length qs = 6%nat -> (Int64.unsigned n < 2 ^ limb_bits)%Z ->
  eval_funcall ge (Internal mul_ln2101)
    [Varr (map Vint64 qs); Vint64 n; Varr (map Vint64 LN2w)] e1 (Some result) ->
  exists qs', e1!(param 0 mul_ln2101) = Some (Varr (map Vint64 qs')) /\
    length qs' = 6%nat /\ limbs qs' /\
    val32 qs' = ExpModel.q (Int64.unsigned n).
Admitted.

(* the first guess of n: floor(X INV / 2^185) *)
Theorem guess_n_spec xs e1 result :
  length xs = 6%nat -> limbs xs ->
  eval_funcall ge (Internal guess_n105) [Varr (map Vint64 xs)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.guess (val32 xs))).
Admitted.
