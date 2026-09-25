(* =========================================================================  *)
(*  RowCubProofB.v -- what the plain run with the fast leaf buys, no run.     *)
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
Require Import RowSrch RowMark RowLvl RowCubReal RowCubDef.
Require Import RowSrchP RowSrchC RowCubRealB RowCubDefB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the int search is the nat one                                              *)
Lemma rowmappiBE : rowmappiB 20 =
  ycmfinspB p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
            ishmi (prepassD cpgi cfli mgri mswi mloi mhii).
Proof. by rewrite /rowmappiB /ycmfinspB; apply: runskic_eq. Qed.

Lemma rowwitspiBE : rowwitspiB =
  ycwitsrB p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           ishmi (prepassD cpgi cfli mgri mswi mloi mhii).
Proof. by rewrite /rowwitspiB rowmappiBE /wmarkof /ycwitsrB. Qed.

Theorem row_of_runpiB : rowfullpiB = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite /rowfullpiB rowwitspiBE => hf.
exact: (real_superflip_row_pB
          (prepassD_eq cfli mswi mloi mhii pgm_rangeC grm_rangeC) fsmoveCP hf).
Qed.
