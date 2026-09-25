(* =========================================================================  *)
(*  RowCubDoneB.v -- the plain theorem, with the fast leaf.                   *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row.
Require Import RowCubDefB RowCubBoolB RowCubProofB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Theorem real_superflip_row_cub_runB h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof. exact: (row_of_runpiB rowfullpiBE). Qed.

Print Assumptions real_superflip_row_cub_runB.
