(** * T1: addw, B_ia <- B_ia + B_ib mod beta^l *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Htr3.HtrBase.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(* The coefficient at ia becomes (B_ia + B_ib) mod beta^l; every other word
   is unchanged.  The two coefficients do not overlap. *)
Theorem addw_spec xs m ia ib l e1 result :
  let IA := nat_of ia in let IB := nat_of ib in let L := nat_of l in
  length xs = nat_of m ->
  (IA + L <= nat_of m)%coq_nat -> (IB + L <= nat_of m)%coq_nat ->
  (IA + L <= IB \/ IB + L <= IA)%coq_nat ->
  eval_funcall ge (Internal addw12)
    [Varr (map Vint64 xs); Vint64 m; Vint64 ia; Vint64 ib; Vint64 l]
    e1 (Some result) ->
  exists xs', e1!(param 0 addw12) = Some (Varr (map Vint64 xs')) /\
    length xs' = length xs /\
    val (firstn L (skipn IA xs')) =
      ((val (firstn L (skipn IA xs)) + val (firstn L (skipn IB xs)))
         mod base L)%Z /\
    (forall p, (p < IA \/ IA + L <= p)%coq_nat ->
       List.nth p xs' Int64.zero = List.nth p xs Int64.zero).
Proof.
Admitted.
