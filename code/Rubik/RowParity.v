(* =========================================================================  *)
(*  RowParity.v -- the parity shifts by a fixed amount.                       *)
(* =========================================================================  *)

(* A move shifts the corner parity by the same amount at every page and the   *)
(* middle parity by the same amount at every bit. That is what lets the outer *)
(* half be a walk over the group alone, because the outer parity shifts by    *)
(* the two together. Ten by 40320 and ten by twenty four, array reads only.   *)
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

Lemma parokC : parok mpgi btmvi e4ofi par8i par4i.
Proof. by vm_compute. Qed.
