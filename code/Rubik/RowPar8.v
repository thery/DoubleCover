(* =========================================================================  *)
(*  RowPar8.v -- the parity table of the eight.                             *)
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

(* At each page number the table's bit is the parity of the permutation the
   page stands for.                                                          *)
Lemma par8okwC : par8okw par8i.  Proof. by vm_compute. Qed.
