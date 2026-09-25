(* =========================================================================  *)
(*  RowCubProofC.v -- the plain run over the four numbers is the run over     *)
(*  the twenty cubies, no run in it.                                          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal FsmChk.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowSrch RowMark RowLvl RowSrchC RowLeafFast.
Require Import RowCubDefB RowCubProofB RowCubDefC.
Require Import RowCoord RowCoordLeaf RowCoordStep RowCoordRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the run over the four numbers leaves the map the run over the cubies does *)
Lemma rowmappiCE n : rowmappiC n = rowmappiB n.
Proof.
rewrite /rowmappiC /rowmappiB.
exact: (@runskic_coord fsmoveCP cmemb cofy_step cmembE).
Qed.

Lemma rowfullpiCEq : rowfullpiC = rowfullpiB.
Proof. by rewrite /rowfullpiC /rowwitspiC rowmappiCE /rowfullpiB /rowwitspiB. Qed.

Theorem row_of_runpiC : rowfullpiC = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof. by rewrite rowfullpiCEq; exact: row_of_runpiB. Qed.
