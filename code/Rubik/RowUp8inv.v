(* =========================================================================  *)
(*  RowUp8inv.v -- the unranking of the eight is a section of the ranking.  *)
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

(* Rank what up8 hands back at each of the 40320 page numbers and the page
   number has to come back.  Nothing about the cube: it is a fact about two
   tables.                                                                   *)
Lemma up8invC : up8inv.  Proof. by vm_compute. Qed.
