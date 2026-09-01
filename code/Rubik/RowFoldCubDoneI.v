(* =========================================================================  *)
(*  RowFoldCubDoneI.v -- the folded theorem, run and proof together.          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row.
Require Import RowFoldCubDefI RowFoldCubBoolI RowFoldCubProofI.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Theorem real_superflip_row_fold_runi h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof. apply: (row_of_runi rowfulliE). Qed.

Corollary real_row_superflip_fold_runi m : m \in H ->
  superflip * m \in ball Sset 20.
Proof. apply: (row_of_runi_superflip rowfulliE). Qed.

(* it must name nothing but the int63 and PArray primitives *)
Print Assumptions real_row_superflip_fold_runi.
