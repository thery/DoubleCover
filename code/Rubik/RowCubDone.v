(* =========================================================================  *)
(*  RowCubDone.v -- the plain run and the plain proof, together.              *)
(* =========================================================================  *)

(* RowCubBool says the boolean is true and loaded no proof to say it.         *)
(* RowCubProof says what being true buys and ran nothing to say that.  This   *)
(* is the one line that needs both, and it computes nothing either.           *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Rubik333 Ball Diameter Moves Row.
Require Import FsmChk.
Require Import RowCubDef RowCubBool RowCubProof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Theorem real_superflip_row_cub_run h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof. apply: (row_of_runp rowfullpE). Qed.

Corollary real_row_superflip_cub_run m : m \in H ->
  superflip * m \in ball Sset 20.
Proof. apply: (row_of_runp_superflip rowfullpE). Qed.

(* it must name nothing but the int63 and PArray primitives *)
Print Assumptions real_row_superflip_cub_run.
