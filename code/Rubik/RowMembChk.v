(* =========================================================================  *)
(*  RowMembChk.v -- the bridge, with nothing left open.                       *)
(* =========================================================================  *)

(* RowMemb.v proves that a member names a permutation and that moving the     *)
(* place moves the member by that move of H.  Both are conditional on eight   *)
(* facts about the tables, and every one of the eight is a walk.  The eight   *)
(* run in files of their own -- RowMoveH, RowMoveM, RowParity, RowPartM,      *)
(* RowPartC, RowPartU, RowMoveC, RowMoveU -- so that they go side by side and *)
(* each reports on its own.  This file spends them.                           *)
(*                                                                            *)
(* The long ones are RowPartC and RowPartU, a permutation of the forty eight  *)
(* facelets built at each of 40320 ranks, and RowMoveC and RowMoveU, which    *)
(* build two of them at each of 403 200 place and move pairs.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the two hypotheses of RowInst that were about the cube, now facts          *)
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
