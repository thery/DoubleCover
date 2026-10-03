(** * num_zero, num_copy, num_pow2, num_low: the specs (task T2) *)

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

(* Six zero words: the number 0. *)
Lemma zeros6 : length (repeat Int64.zero 6) = 6%nat /\
  limbs (repeat Int64.zero 6) /\ val32 (repeat Int64.zero 6) = 0%Z.
Proof.
  split => //; split; last by rewrite /= Int64.unsigned_zero.
  move=> p; case: (Nat.lt_ge_cases p 6) => Hp.
  - by rewrite nth_repeat_lt // Int64.unsigned_zero.
  - by rewrite nth_overflow ?repeat_length // Int64.unsigned_zero.
Qed.

(* a = 0 *)
Theorem num_zero_spec xs e1 result :
  length xs = 6%nat ->
  eval_funcall ge (Internal num_zero6) [Varr (map Vint64 xs)] e1 (Some result) ->
  e1!(param 0 num_zero6) = Some (Varr (map Vint64 (repeat Int64.zero 6))).
Admitted.

(* a = b *)
Theorem num_copy_spec xs ys e1 result :
  length xs = 6%nat -> length ys = 6%nat ->
  eval_funcall ge (Internal num_copy12)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  e1!(param 0 num_copy12) = Some (Varr (map Vint64 ys)).
Admitted.

(* a = 2^f, for f < 192 *)
Theorem num_pow2_spec xs f e1 result :
  length xs = 6%nat -> (Int64.unsigned f < ExpModel.num_bits)%Z ->
  eval_funcall ge (Internal num_pow272) [Varr (map Vint64 xs); Vint64 f]
    e1 (Some result) ->
  exists xs', e1!(param 0 num_pow272) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\
    val32 xs' = ExpModel.pow2 (Int64.unsigned f).
Admitted.

(* a = b mod 2^f, for f < 192 *)
Theorem num_low_spec xs ys f e1 result :
  length xs = 6%nat -> length ys = 6%nat -> limbs ys ->
  (Int64.unsigned f < ExpModel.num_bits)%Z ->
  eval_funcall ge (Internal num_low81)
    [Varr (map Vint64 xs); Varr (map Vint64 ys); Vint64 f] e1 (Some result) ->
  exists xs', e1!(param 0 num_low81) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\
    val32 xs' = ExpModel.low (val32 ys) (Int64.unsigned f).
Admitted.
