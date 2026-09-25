(* =========================================================================  *)
(*  RowCubProofD.v -- the plain run with its running count is sound.          *)
(* =========================================================================  *)

(* rowmappiD over the four numbers is the same run over the twenty cubies     *)
(* (RowSrchNSim), which is RowSrchN's nat run, sound by RowCubRealD.  Its    *)
(* map is not RowCubDefB's: the count decides when the cuts come on, and it   *)
(* is counted differently.  Both are sound.                                   *)

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
Require Import RowCubDefB RowCubProofB RowCubDefD RowCubRealD.
Require Import RowCoord RowCoordLeaf RowCoordStep RowCoordRun.
Require Import RowSrchN RowSrchNSim RowCubReal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the run over the four numbers leaves the map the run over the cubies does *)
Lemma rowmappiDE : rowmappiD 20 =
  ycmfinspD p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
            ishmi (prepassD cpgi cfli mgri mswi mloi mhii).
Proof.
rewrite /rowmappiD /ycmfinspD.
rewrite (@runskni_coord fsmoveCP cmemb cofy_step cmembE).
by apply: runskni_eq.
Qed.

Lemma rowwitspiDE : rowwitspiD =
  ycwitsrD p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           ishmi (prepassD cpgi cfli mgri mswi mloi mhii).
Proof. by rewrite /rowwitspiD rowmappiDE /wmarkof /ycwitsrD. Qed.

Theorem row_of_runpiD : rowfullpiD = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite /rowfullpiD rowwitspiDE => hf.
exact: (real_superflip_row_pD
          (prepassD_eq cfli mswi mloi mhii pgm_rangeC grm_rangeC) fsmoveCP hf).
Qed.
