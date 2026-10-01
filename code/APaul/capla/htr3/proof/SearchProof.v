(** * T5: search, the whole search of one line *)

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

Require Import Htr3.DifftabProof Htr3.TstepProof.

(* The result is the number of candidates j = 0 .. n-1 (cands, in HtrDefs),
   and out holds the first cap of them, in increasing order. *)
Theorem search_spec xs m k l n err outs cap e1 result :
  let K := nat_of k in let L := nat_of l in let N := nat_of n in
  length xs = nat_of m -> (K * L <= nat_of m)%coq_nat ->
  (1 <= K)%coq_nat -> (1 <= L)%coq_nat ->
  (2 * Int64.unsigned err <= Int64.max_unsigned)%Z ->
  length outs = nat_of cap ->
  eval_funcall ge (Internal search46)
    [Varr (map Vint64 xs); Vint64 m; Vint64 k; Vint64 l; Vint64 n;
     Vint64 err; Varr (map Vint64 outs); Vint64 cap] e1 (Some result) ->
  let cs := cands (Z.of_nat L) (Int64.unsigned err) (vcoefs xs L K) N in
  exists c outs', result = Vint64 c /\
    e1!(param 6 search46) = Some (Varr (map Vint64 outs')) /\
    Int64.unsigned c = Z.of_nat (length cs) /\
    firstn (Nat.min (length cs) (nat_of cap)) (map nat_of outs') =
      firstn (nat_of cap) cs.
Proof.
Admitted.
