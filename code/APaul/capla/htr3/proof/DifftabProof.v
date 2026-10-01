(** * T3: difftab, the table of differences *)

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

Require Import Htr3.SubwProof.

(* The k coefficients become their forward differences at 0, modulo
   beta^l; the words after them are unchanged. *)
Theorem difftab_spec xs m k l e1 result :
  let K := nat_of k in let L := nat_of l in
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat ->
  eval_funcall ge (Internal difftab29)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l] e1 (Some result) ->
  exists xs', e1!(param 0 difftab29) = Some (Varr (map Vint64 xs')) /\
    length xs' = length xs /\
    vcoefs xs' L K =
      map (fun j => fdiff (vcoefs xs L K) j mod base L)%Z (seq 0 K) /\
    skipn (K * L) xs' = skipn (K * L) xs.
Proof.
Admitted.
