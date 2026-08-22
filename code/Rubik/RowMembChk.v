(* =========================================================================  *)
(*  RowMembChk.v -- the eight walks the bridge rests on, run.                 *)
(* =========================================================================  *)

(* RowMemb.v proves that a member names a permutation and that moving the     *)
(* place moves the member by that move of H.  Both proofs are conditional:    *)
(* between them they ask for eight facts about the tables, and every one is a *)
(* walk.  This file runs them.                                                *)
(*                                                                            *)
(* THE ORDER IS BY COST, cheapest first, so that a table that disagrees says  *)
(* so in seconds rather than at the end of a quarter of an hour.  The four    *)
(* big ones are last: cpartok and upartok build a permutation of the forty    *)
(* eight facelets at each of 40320 ranks, and cmvok and umvok build two of    *)
(* them at each of 403 200 place and move pairs.                              *)

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

Import GroupScope.

(* ---- the ten moves of H, and they cost nothing --------------------------- *)

(* Undoing a move of H is its corner half, its outer half and its middle      *)
(* half composed, and each half is a permutation that leaves the other two    *)
(* sets of facelets alone.  Ten moves by forty eight facelets.                *)
Lemma hmvokC : hmvok.
Proof. by vm_compute. Qed.

(* the middle four: btmv is the middle permutation moved.  Ten by twenty four *)
Lemma mmvokC : mmvok btmvi e4ofi.
Proof. by vm_compute. Qed.

(* ---- the parity ---------------------------------------------------------- *)

(* A move shifts the corner parity by the same amount at every page and the   *)
(* middle parity by the same amount at every bit.  This is what lets the      *)
(* outer half be a walk over the group alone: the outer parity shifts by the  *)
(* two together.  Ten by 40320 and ten by twenty four, all of it array reads. *)
Lemma parokC : parok mpgi btmvi e4ofi par8i par4i.
Proof. by vm_compute. Qed.

(* ---- the three parts are permutations ------------------------------------ *)

(* Each part is a permutation of the forty eight facelets, leaves every       *)
(* facelet outside its own alone, and keeps its own.  The middle four first,  *)
(* because it is twenty four ranks and the other two are 40320 each.          *)
Lemma mpartokC : mpartok.
Proof. by vm_compute. Qed.

Lemma cpartokC : cpartok.
Proof. by vm_compute. Qed.

Lemma upartokC : upartok.
Proof. by vm_compute. Qed.

(* ---- and the two halves that move ---------------------------------------- *)

(* The page table is the corner permutation moved, and the group table with   *)
(* its parity shift is the outer permutation moved.  These are the two long   *)
(* ones: each builds two parts at every step.                                 *)
Lemma cmvokC : cmvok mpgi.
Proof. by vm_compute. Qed.

Lemma umvokC : umvok mpgi mgri btmvi e8invi e4ofi par8i par4i.
Proof. by vm_compute. Qed.

(* ---- what RowInst asks for, with nothing left open ----------------------- *)

(* The two hypotheses of RowInst that were about the cube, now facts.         *)
Lemma memb2tab_okC x : tab_ok flast (memb2tab x).
Proof. exact: (memb2tab_ok cpartokC upartokC mpartokC). Qed.

Lemma memb2tab_moveC k pg gr bt : (to_nat k < nhn)%N ->
  inrange pg gr bt ->
  pt flast (memb2tab (unplace e8invi e4ofi par8i par4i
                        (pgmv mpgi k pg) (grmv mgri k gr) (btmv btmvi k bt)))
  = pt flast (memb2tab (unplace e8invi e4ofi par8i par4i pg gr bt)) * hmv k.
Proof.
exact: (memb2tab_move e8okC e4okC pgokC grokC btokC cpartokC upartokC
                      mpartokC cmvokC mmvokC umvokC hmvokC parokC).
Qed.
