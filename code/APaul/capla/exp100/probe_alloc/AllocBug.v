(** allocz returns 0 in the semantics (alloc fills with zeros); with
    WP_sound we prove that it returns 1. *)

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
Require Import Probe.allocz.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.

Definition ge := genv_of_program program.

Theorem allocz_one e1 result :
  eval_funcall ge (Internal allocz3) [] e1 (Some result) ->
  result = Vint64 Int64.one.
Proof.
  intro_eval_funcall allocz3 out se1 exec.
  match goal with H : Some result = outcome_result_value out |- _ =>
    have := H end.
  apply_WP_stmt exec out e1 se1.
  repeat prog.
  (* the WP reads a[0] as Vundef, which is not a u64: vacuous *)
  move=> R; rewrite R /= in WELLTYPED; inversion WELLTYPED.
Qed.

Print Assumptions allocz_one.
