(** * num_lt: the spec (task T4) *)

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

(* a < b *)
Theorem num_lt_spec xs ys e1 result :
  length xs = 6%nat -> length ys = 6%nat -> limbs xs -> limbs ys ->
  eval_funcall ge (Internal num_lt35)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  result = Vbool (val32 xs <? val32 ys)%Z.
Admitted.
