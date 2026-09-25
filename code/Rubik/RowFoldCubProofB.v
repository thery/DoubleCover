(* =========================================================================  *)
(*  RowFoldCubProofB.v -- what the run with the fast leaf buys, no run in it. *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Cyc Sym Root Coord Sym16 Sym16Row.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowMembi FsmChk.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart RowTabF RowFoldTab.
Require Import RowFoldSym RowFoldConj RowFoldGath RowFoldSrc RowFoldLvl.
Require Import RowFoldWrite RowFoldTot RowFoldPorb RowFoldSrch RowFoldRun.
Require Import RowFoldEmpty RowFoldFinal RowFoldCubReal.
Require Import RowFoldCubDef.

Require Import RowFoldSrchI RowFoldSrchIP RowFoldRunC RowFoldSrchIC RowFoldFinalC.
Require Import RowFoldCubProof RowFoldCubRealB RowFoldCubDefB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the int search is the nat one, and the names are RowFoldCubDef's copies    *)
Lemma rowmapiBE : rowmapiB 20 =
  yfcmfinoB p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
            forbi fpopi ishmi.
Proof.
rewrite /yfcmfinoB /fmfinoC -okmvvdE -ycsolveddE -srchdE.
by apply: frunskic_eq.
Qed.

Lemma rowfulliBEq : rowfulliB =
  mfullf ffuli (yfcwitsoB p1ftab frepi fsymi twsymi dnlo_data dnhi_data
                          fllo_data flhi_data forbi fpopi ishmi).
Proof. by rewrite /rowfulliB /ycwitsoiB rowmapiBE. Qed.

Theorem row_of_runB : rowfulliB = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite rowfulliBEq => hf.
exact: (@real_superflip_row_foldoB p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data fsmoveCP
          forbi fpopi ishmi hf).
Qed.
