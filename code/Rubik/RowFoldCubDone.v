(* =========================================================================  *)
(*  RowFoldCubDone.v -- the run and the proof, put together.                  *)
(* =========================================================================  *)

(* RowFoldCubBool says the boolean is true and loaded no proof to say it.     *)
(* RowFoldCubProof says what being true buys and ran nothing to say that.     *)
(* This is the one line that needs both, and it computes nothing either.      *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Rubik333 Ball Diameter Moves Row.
Require Import RowFoldCubDef RowFoldCubBool RowFoldCubProof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Theorem real_superflip_row_fold_run h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof. apply: (row_of_run rowfullE). Qed.

Corollary real_row_superflip_fold_run m : m \in H ->
  superflip * m \in ball Sset 20.
Proof. apply: (row_of_run_superflip rowfullE). Qed.

(* it must name nothing but the int63 and PArray primitives *)
Print Assumptions real_row_superflip_fold_run.
