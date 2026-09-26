(* =========================================================================  *)
(*  RowFoldCubProofD.v -- the counting run over the four numbers proves it.   *)
(* =========================================================================  *)

(* rowmapiD is RowFoldNSim's yfwmfinoD, the names being RowFoldCubDef's     *)
(* copies; RowFoldNSim's certificate then gives the row.                    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf RowWits.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowMembi FsmChk.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowFoldTab RowFoldSrch RowFoldCubDef RowFoldCubProof.
Require Import RowFoldSrchI RowFoldSrchIC RowLeafFast.
Require Import RowCoord RowCoordLeaf RowFoldN RowFoldNSim RowFoldCubDefD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the run is RowFoldNSim's, and the names are RowFoldCubDef's copies        *)
Lemma rowmapiDE : rowmapiD 20 =
  yfwmfinoD p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
            forbi fpopi ishmi.
Proof. by rewrite /rowmapiD /yfwmfinoD /crootD -okmvvdE -ycsolveddE -srchdE. Qed.

Lemma rowfulliDEq : rowfulliD =
  mfullf ffuli (yfwwitsoD p1ftab frepi fsymi twsymi dnlo_data dnhi_data
                          fllo_data flhi_data forbi fpopi ishmi).
Proof. by rewrite /rowfulliD /ycwitsoiD rowmapiDE. Qed.

Theorem row_of_runD : rowfulliD = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite rowfulliDEq => hf.
exact: (@real_superflip_row_foldoD p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data fsmoveCP
          forbi fpopi ishmi hf).
Qed.
