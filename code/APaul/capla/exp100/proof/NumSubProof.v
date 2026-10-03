(** * num_sub: the spec (task T3) *)

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

(* a = a - b, for a >= b *)
Theorem num_sub_spec xs ys e1 result :
  length xs = 6%nat -> length ys = 6%nat -> limbs xs -> limbs ys ->
  (val32 ys <= val32 xs)%Z ->
  eval_funcall ge (Internal num_sub27)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  exists xs', e1!(param 0 num_sub27) = Some (Varr (map Vint64 xs')) /\
    length xs' = 6%nat /\ limbs xs' /\ val32 xs' = (val32 xs - val32 ys)%Z.
Admitted.
