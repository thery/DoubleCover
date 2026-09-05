(* =========================================================================  *)
(*  RowCubDoneI48.v -- the plain theorem, run and proof together.               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row.
Require Import FsmChk.
Require Import RowCubDef48 RowCubBoolI48 RowCubProofI48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Theorem real_superflip_row_cub_runi48 h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof. apply: (row_of_runpi48 rowfullpi48E). Qed.

Corollary real_row_superflip_cub_runi48 m : m \in H ->
  superflip * m \in ball Sset 20.
Proof. apply: (row_of_runpi48_superflip rowfullpi48E). Qed.

(* it must name nothing but the int63 and PArray primitives                   *)
Print Assumptions real_row_superflip_cub_runi48.
