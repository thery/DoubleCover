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
Require Import RowMemb RowLeaf RowInst RowFinal48 RowWits RowWitsChk.

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

(* ---- the witnesses, at forty eight bits ---------------------------------- *)

(* THE WITNESS LIST IS THE TWENTY FOUR BIT ONE, and a page in it is a corner  *)
(* RANK.  The same member stands at another place here, so the list is read   *)
(* through wconv -- the page number split, exactly as everywhere else -- and  *)
(* the word is not touched, since the member has not changed.                 *)
Definition rowwits48 : seq (int * int * int * seq nat) :=
  [seq wconv e8numi par8i t | t <- rowwits].

(* and it is still a list of witnesses: every place in range, every word at   *)
(* most twenty moves, and every word still solving its member                 *)
Lemma wits48C :
  wgood48 e8invi e4ofi par4i (RowInst.ptab memb2tab) rowwits48.
Proof.
rewrite /rowwits48; have := witsokC; rewrite /RowFinal.witsok.
elim: rowwits => [|t l ih] //=.
case: t => [[[pg gr] bt] w] /andP[/and3P[hi hs hw] hl].
apply/andP; split; last by apply: ih.
apply/and3P; split; first by apply: (inrange48_conv e8okC hi).
  exact: hs.
by rewrite (unplace48_conv e4ofi par4i e8okC hi).
Qed.
