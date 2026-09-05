(* =========================================================================  *)
(*  RowTab48.v -- the corner pair tables, and the one check they must pass.   *)
(* =========================================================================  *)

(* RowTabP48.v is the numbers, written by ocaml/rubik_row_nofold.ml dumptab   *)
(* prep48.  This file makes them arrays and CHECKS them.  There is only one   *)
(* check and it is the whole of what the forty eight bit prepass rests on:    *)
(* the class table and the flip ARE the page table, split by n = n / 2 * 2 +  *)
(* odd n.  Nothing about how they were built is trusted.                      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap Row48 RowMap48 RowPrep48.
Require Import RowTabL RowTabP RowTab RowTabP48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Definition ncpgi : int := 201600%uint63.        (* 20160 pairs by ten moves  *)
Definition ncfli : int := 10%uint63.

Definition cpgi : arr := Eval vm_compute in mkarr ncpgi 0%uint63 cpg_data.
Definition cfli : arr := Eval vm_compute in mkarr ncfli 0%uint63 cfl_data.

(* the flip is a parity                                                       *)
Lemma cflokC : cflok cfli.
Proof. by vm_compute. Qed.

(* AND THE ONE CHECK: 20160 pairs by two parities by ten moves, and each says *)
(* that reading the class table and flipping the parity is reading the page   *)
(* table at the corner rank the two name.                                     *)
Lemma cpgok48C : cpgok48 e8invi mpgi cpgi cfli.
Proof. by vm_compute. Qed.
