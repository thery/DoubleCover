(* =========================================================================  *)
(*  RowMoveH.v -- a move of H is its three halves.                            *)
(* =========================================================================  *)

(* Undoing a move of H is its corner half, its outer half and its middle half *)
(* composed, and each half is a permutation that leaves the other two sets of *)
(* facelets alone. Ten moves by forty eight facelets.                         *)
(*                                                                            *)
(* One of the eight walks RowMemb.v asks for, in a file of its own so that    *)
(* the eight run side by side and each says on its own whether it passed.     *)
(* RowMembChk.v puts them together.                                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma hmvokC : hmvok.
Proof. by vm_compute. Qed.
