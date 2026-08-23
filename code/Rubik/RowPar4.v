(* =========================================================================  *)
(*  RowPar4.v -- the parity table of the four.                              *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* And the same for the twenty four bit numbers.                             *)
Lemma par4okwC : par4okw par4i.  Proof. by vm_compute. Qed.
