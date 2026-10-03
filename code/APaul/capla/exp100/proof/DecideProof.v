(** * decide: the spec (task T12) *)

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

(* The decision of decide_Z, on y and hN in the ranges core_Z gives
   (ExpModelBounds.core_bounds). *)
Theorem decide_spec ys hN los his ds ts e1 result :
  length ys = 6%nat -> limbs ys ->
  (2 ^ ExpConsts.P <= val32 ys < 2 ^ ExpModelBounds.y_bits)%Z ->
  (- 2 ^ ExpModelBounds.hN_bits <= Int64.signed hN <=
     2 ^ ExpModelBounds.hN_bits)%Z ->
  length los = 6%nat -> length his = 6%nat -> length ds = 6%nat ->
  length ts = 6%nat ->
  eval_funcall ge (Internal decide176)
    [Varr (map Vint64 ys); Vint64 hN; Varr (map Vint64 los);
     Varr (map Vint64 his); Varr (map Vint64 ds); Varr (map Vint64 ts)]
    e1 (Some result) ->
  result = Vint64 (Int64.repr (ExpModel.decide_Z (val32 ys) (Int64.signed hN))).
Admitted.
