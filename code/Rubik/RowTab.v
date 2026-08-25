(* =========================================================================  *)
(*  RowTab.v -- the row's tables, and the checks they have to pass.           *)
(* =========================================================================  *)

(* RowTabL.v and RowTabP.v are the numbers, written by                        *)
(* ocaml/rubik_row_nofold.ml.  This file makes them arrays and CHECKS them:   *)
(* Row.e8ok and Row.e4ok say the layout is a bijection, and RowInst's srcok   *)
(* and halfok say the bit tables and btmv agree.  Nothing about how they were *)
(* built is trusted.                                                          *)
(*                                                                            *)
(* `Eval vm_compute in' is what makes each body an array VALUE.  Without it   *)
(* the body IS the cons list, and every tactic that unfolds one read has to   *)
(* walk it -- see the note on fsdtab in Farp1.v.                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

(* ---- the layout ---------------------------------------------------------- *)

Definition e8numi : arr := Eval vm_compute in
  mkarr npagei 0%uint63 e8num_data.
Definition e8invi : arr := Eval vm_compute in
  mkarr npagei 0%uint63 e8inv_data.
Definition par8i : arr := Eval vm_compute in
  mkarr npagei 0%uint63 par8_data.
Definition e4biti : arr := Eval vm_compute in
  mkarr nbiti 0%uint63 e4bit_data.
Definition e4ofi : arr := Eval vm_compute in
  mkarr nbiti 0%uint63 e4of_data.
Definition par4i : arr := Eval vm_compute in
  mkarr nbiti 0%uint63 par4_data.

(* the two checks Row.v asks for: a number carries its parity in its last     *)
(* place, and each table undoes the other                                     *)
Lemma e8okC : e8ok e8numi e8invi par8i.
Proof. by vm_compute. Qed.

Lemma e4okC : e4ok e4biti e4ofi par4i.
Proof. by vm_compute. Qed.

(* ---- the prepass --------------------------------------------------------- *)

Definition nmpgi : int := 403200%uint63.        (* 40320 pages by ten moves  *)
Definition nmgri : int := 201600%uint63.        (* 20160 groups by ten       *)
Definition nhalfi : int := 40960%uint63.        (* ten moves by 4096 words   *)
Definition nbtmvi : int := 240%uint63.          (* 24 bits by ten            *)

Definition mpgi : arr := Eval vm_compute in mkarr nmpgi 0%uint63 mpg_data.
Definition mgri : arr := Eval vm_compute in mkarr nmgri 0%uint63 mgr_data.
Definition mswi : arr := Eval vm_compute in mkarr 10%uint63 0%uint63 msw_data.
Definition mloi : arr := Eval vm_compute in mkarr nhalfi 0%uint63 mlo_data.
Definition mhii : arr := Eval vm_compute in mkarr nhalfi 0%uint63 mhi_data.
Definition btmvi : arr := Eval vm_compute in mkarr nbtmvi 0%uint63 btmv_data.

(* and the two about the bits: the source of a place is in the right half,    *)
(* and each half table moves a bit to the place btmv names                    *)
Lemma srcokC : srcok mswi btmvi.
Proof. by vm_compute. Qed.

Lemma halfokC : halfok mswi mloi mhii btmvi.
Proof. by vm_compute. Qed.

(* and the three ranges: a page goes to a page, a group to a group, a bit to  *)
(* a bit                                                                      *)
Lemma pgokC : pgok mpgi.
Proof. by vm_compute. Qed.

Lemma grokC : grok mgri.
Proof. by vm_compute. Qed.

Lemma btokC : btok btmvi.
Proof. by vm_compute. Qed.
