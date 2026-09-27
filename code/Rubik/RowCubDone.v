(* =========================================================================  *)
(*  RowCubDone.v -- the plain theorem, the run over the constants.            *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row.
Require Import RowCubDef RowCubBool RowCubProof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Theorem real_superflip_row_cub_runO h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof. exact: (row_of_runpiO rowfullpiOT). Qed.

(* The superflip is its own inverse.                                          *)
Lemma superflipV : superflip^-1 = superflip.
Proof.
by apply/eqP; rewrite eq_invg_mul -{2}[superflip]expg1 -expgS superflip2.
Qed.

(* Every position of the superflip's coset is within 20 moves.                *)
Corollary superflip_row_cub h : h \in H -> superflip * h \in ball Sset 20.
Proof. by rewrite -superflipV; exact: real_superflip_row_cub_runO. Qed.

Print Assumptions superflip_row_cub.
