(* =========================================================================  *)
(*  RowPartM.v -- the middle four are a permutation.                          *)
(* =========================================================================  *)

(* At each of the twenty four middle ranks: a permutation of the forty eight  *)
(* facelets that leaves everything outside the middle four alone and keeps    *)
(* the middle four.                                                           *)
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

Lemma mpartokC : mpartok.
Proof. by vm_compute. Qed.
