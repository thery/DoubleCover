(** * exp_core: the spec (task T12) *)

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

(* The return code and, on success, y and hN as core_Z gives them; the
   scratch X q q1 r are left as arrays of 6 words. *)
Theorem exp_core_spec xb ys hs Xs qs q1s rs hhs ts Ta Ca L2a RMa e1 result :
  tables_ok Ta Ca L2a RMa ->
  length ys = 6%nat -> length hs = 1%nat ->
  length Xs = 6%nat -> length qs = 6%nat -> length q1s = 6%nat ->
  length rs = 6%nat -> length hhs = 6%nat -> length ts = 6%nat ->
  eval_funcall ge (Internal exp_core138)
    [Vint64 xb; Varr (map Vint64 ys); Varr (map Vint64 hs);
     Varr (map Vint64 Xs); Varr (map Vint64 qs); Varr (map Vint64 q1s);
     Varr (map Vint64 rs); Varr (map Vint64 hhs); Varr (map Vint64 ts);
     Ta; Ca; L2a; RMa] e1 (Some result) ->
  exists rc, result = Vint64 rc /\
    (Int64.unsigned rc <> 0%Z ->
       ExpModel.core_Z (Int64.unsigned xb) = inl (Int64.unsigned rc)) /\
    (Int64.unsigned rc = 0%Z ->
       exists ys' hN,
         e1!(param 1 exp_core138) = Some (Varr (map Vint64 ys')) /\
         length ys' = 6%nat /\ limbs ys' /\
         e1!(param 2 exp_core138) = Some (Varr [Vint64 hN]) /\
         ExpModel.core_Z (Int64.unsigned xb) =
           inr (val32 ys', Int64.signed hN) /\
         arr6 (e1!(param 3 exp_core138)) /\ arr6 (e1!(param 4 exp_core138)) /\
         arr6 (e1!(param 5 exp_core138)) /\ arr6 (e1!(param 6 exp_core138))).
Admitted.
