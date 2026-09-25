(* =========================================================================  *)
(*  RowFoldCubProofC.v -- the folded run over the four numbers is the run     *)
(*  over the twenty cubies, no run in it.                                     *)
(* =========================================================================  *)

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
Require Import RowFold RowFoldSrch RowFoldCubDef RowFoldCubProof.
Require Import RowFoldSrchI RowFoldSrchIC RowLeafFast.
Require Import RowFoldCubDefB RowFoldCubProofB RowFoldCubDefC.
Require Import RowCoord RowCoordLeaf RowCoordStep RowCoordRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the run over the four numbers leaves the map the run over the cubies does *)
Lemma rowmapiCE n : rowmapiC n = rowmapiB n.
Proof.
rewrite /rowmapiC /rowmapiB /crootC ycsolveddE.
exact: (@frunskic_coord fsmoveCP cmemb cofy_step cmembE).
Qed.

Lemma rowfulliCEq : rowfulliC = rowfulliB.
Proof. by rewrite /rowfulliC /ycwitsoiC rowmapiCE /rowfulliB /ycwitsoiB. Qed.

Theorem row_of_runC : rowfulliC = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof. by rewrite rowfulliCEq; exact: row_of_runB. Qed.
