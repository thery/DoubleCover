(* =========================================================================  *)
(*  RowFoldCubProofB.v -- what the run with the fast leaf buys, no run in it. *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row RowMap RowFold RowFoldFinal.
Require Import RowFoldSrch RowFoldSrchI RowFoldSrchIP RowFoldTab FoldTables.
Require Import P1FTable RowMask RowReal RowWits.
Require Import FsmChk RowFoldCubDef RowFoldCubProof RowFoldCubRealB RowFoldCubDefB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the int search is the nat one, and the names are RowFoldCubDef's copies    *)
Lemma rowmapiBE : rowmapiB 20 =
  yfcmfinoB p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
            forbi fpopi ishmi.
Proof.
rewrite /yfcmfinoB /fmfino -okmvvdE -ycsolveddE -srchdE.
by apply: frunski_eq.
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
