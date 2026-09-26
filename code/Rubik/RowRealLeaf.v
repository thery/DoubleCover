(* =========================================================================  *)
(*  RowRealLeaf.v -- what the runs ask of the fast leaf, bitleaf.             *)
(* =========================================================================  *)

(* bitleaf is the member of a solved position, the folded runs' place and the *)
(* plain runs' position: the three lemmas both certificates (RowFoldNSim,     *)
(* RowCubProof) put in for the leaf.                                          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Cyc Sym Root Coord Sym16 Sym16Row.
Require Import Row RowMap RowPrep RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowMembi.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart RowTabF RowFoldTab.
Require Import RowFoldSym RowFoldConj RowFoldGath RowFoldSrc RowFoldLvl.
Require Import RowFoldWrite RowFoldTot RowFoldPorb RowFoldSrch RowFoldRun.
Require Import RowFoldEmpty RowFoldFinal.
Require Import RowFoldCubReal RowLeafFast RowFoldRunC RowFoldFinalC.
Require Import RowMark RowSrch RowSrchP RowSrchC RowCubReal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* ---- the two things the run asks of its leaf ----------------------------- *)

Lemma ybitleafE y : ypstok y -> bitleaf y = ytomemb tomembi y.
Proof. exact: bitleafE. Qed.

Lemma yleaf_membB c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> membok par8i par4i (bitleaf y).
Proof. by move=> hc hy hg hs; rewrite (ybitleafE hy); exact: (yleaf_membi hc hy hg hs). Qed.

Lemma yfleaf_posB c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> posC (bitleaf y) = yposp y.
Proof. by move=> hc hy hg hs; rewrite (ybitleafE hy); exact: (yfleaf_posi hc hy hg hs). Qed.

(* ---- the second thing runsk asks of its leaf ----------------------------- *)

(* the first, membok, is yleaf_membB above as it stands                       *)
Lemma yleaf_posPB c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> RowFinal.pos (RowInst.ptab memb2tab) (bitleaf y) = yposp y.
Proof.
move=> hc hy hg hs; rewrite (ybitleafE hy) (ytomembiE hy).
exact: (yleaf_pos memb2tab_okC r_tomemb_tab hc hy hg hs).
Qed.
