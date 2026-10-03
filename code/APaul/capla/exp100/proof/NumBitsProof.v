(** * num_bitlen, num_scale: the specs (task T6) *)

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

(* the number of bits of a *)
Theorem num_bitlen_spec xs e1 result :
  length xs = 6%nat -> limbs xs ->
  eval_funcall ge (Internal num_bitlen70) [Varr (map Vint64 xs)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.bitlen (val32 xs))).
Admitted.

(* a = floor(v 2^e), for v < 2^53 and e < 128 *)
Theorem num_scale_spec xs v e e1 result :
  length xs = 6%nat -> (Int64.unsigned v < 2 ^ mant53)%Z ->
  (Int64.signed e < scale_emax)%Z ->
  eval_funcall ge (Internal num_scale92)
    [Varr (map Vint64 xs); Vint64 v; Vint64 e] e1 (Some result) ->
  exists xs', e1!(param 0 num_scale92) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\
    val32 xs' = ExpModel.scale (Int64.unsigned v) (Int64.signed e).
Admitted.
