(* =========================================================================  *)
(*  RowUp4ok.v -- the unranking of the four is a permutation.               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowMemb RowLeaf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* And the four places up4 names are the four places.                        *)
Lemma up4okC : up4ok.  Proof. by vm_compute. Qed.
