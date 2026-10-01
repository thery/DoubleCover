(** * T4: tstep, one step of the table *)

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

Require Import Htr3.AddwProof.

(* The k coefficients become B_t + B_(t+1) modulo beta^l, the last one
   unchanged (tstepZ); the words after them are unchanged. *)
Theorem tstep_spec xs m k l e1 result :
  let K := nat_of k in let L := nat_of l in
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat -> (1 <= K)%coq_nat ->
  eval_funcall ge (Internal tstep34)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l] e1 (Some result) ->
  exists xs', e1!(param 0 tstep34) = Some (Varr (map Vint64 xs')) /\
    length xs' = length xs /\
    vcoefs xs' L K = map (fun z => z mod base L)%Z (tstepZ (vcoefs xs L K)) /\
    skipn (K * L) xs' = skipn (K * L) xs.
Proof.
Admitted.
