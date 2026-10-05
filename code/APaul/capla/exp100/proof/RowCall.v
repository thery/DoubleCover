(** * A call with a row of a table, on the probe ./rowcall.b

    exp_core passes the rows T[j] and C[i] to num_mulshr, num_add and
    num_copy: in the Rocq term, a [Sletref] on the path T[Scell j].  This
    file checks the mechanism on the smallest such call: row_copy calls
    num_copy(a, T[j]).  The callee is used through its spec only. *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Export Types Ops SyntaxCommon L1.
Require Import Exp100Capla.rowcall.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Definition ge := genv_of_program program.

(* A table as Capla passes it: an array of arrays of words. *)
Definition vtab (t : list (list int64)) : value :=
  Varr (map (fun r => Varr (map Vint64 r)) t).

Section RowCall.

(* The spec of the callee, as NumBasicProof.v states it for exp100. *)
Hypothesis num_copy_spec : forall xs ys e1 result,
  length xs = 6%nat -> length ys = 6%nat ->
  eval_funcall ge (Internal num_copy7)
    [Varr (map Vint64 xs); Varr (map Vint64 ys)] e1 (Some result) ->
  e1!(param 0 num_copy7) = Some (Varr (map Vint64 ys)).

(* a = T[j] *)
Theorem row_copy_spec xs tl j e1 result :
  length xs = 6%nat -> length tl = 64%nat ->
  (forall r, In r tl -> length r = 6%nat) ->
  (Int64.unsigned j < 64)%Z ->
  eval_funcall ge (Internal row_copy10)
    [Varr (map Vint64 xs); vtab tl; Vint64 j] e1 (Some result) ->
  e1!(param 0 row_copy10) =
    Some (Varr (map Vint64 (List.nth (Z.to_nat (Int64.unsigned j)) tl []))).
Proof.
  move=> Hx Ht Hr Hj.
  intro_eval_funcall row_copy10 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "a" A.
  name_var "T" TT.
  repeat prog.
  (* the path T[j] is read as row j of the table *)
  rewrite /vtab; repeat prog.
  set k := Z.to_nat (Int64.unsigned j).
  have Hk : (k < length tl)%coq_nat by rewrite Ht /k; lia.
  have -> : List.nth k (map (fun r => Varr (map Vint64 r)) tl) Vundef =
            Varr (map Vint64 (List.nth k tl [])).
  { rewrite (List.nth_indep _ Vundef (Varr (map Vint64 []))) ?length_map //.
    by rewrite (List.map_nth (fun r : list int64 => Varr (map Vint64 r))). }
  (* the call, through the spec of the callee *)
  move=> _ _ CALL.
  have E1 := num_copy_spec _ _ _ _ Hx (Hr _ (nth_In _ [] Hk)) CALL.
  change (param 0 num_copy7) with A in E1.
  repeat prog.
  by rewrite E1.
Qed.

End RowCall.
