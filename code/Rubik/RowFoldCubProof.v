(* =========================================================================  *)
(*  RowFoldCubProof.v -- what the run's answer buys.                          *)
(* =========================================================================  *)

(* rowfull = true -> the row of the superflip is within twenty.  Nothing is   *)
(* computed here; RowFoldCubBool settles the boolean and RowFoldCubDone puts  *)
(* the two together.  See doc/rowfold-bridge.md.                              *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* ---- the four names the run file had to copy ----------------------------- *)

(* RowFoldCubDef loads no proof, so it copies these four bodies under its own *)
(* names.  Each pair is equal by unfolding a short function.                  *)
Lemma ytomembdE : ytomembd = ytomemb tomembi.  Proof. by []. Qed.
Lemma okmvvdE   : okmvvd = okmvv.              Proof. by []. Qed.
Lemma ycsolveddE : ycsolvedd = ycsolved.       Proof. by []. Qed.
Lemma srchdE    : srchd = srch.                Proof. by []. Qed.

(* ---- and they are the same map ------------------------------------------- *)

Lemma ycwitsoE : ycwitso =
  yfcwitso p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           forbi fpopi ishmi.
Proof.
rewrite /ycwitso /rowmap ytomembdE okmvvdE ycsolveddE srchdE.
by rewrite /yfcwitso /yfcmfino /fmfino.
Qed.

(* ---- what the run buys --------------------------------------------------- *)

Theorem row_of_run : rowfull = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite /rowfull ycwitsoE => hf.
exact: (@real_superflip_row_foldo p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data fsmoveCP
          forbi fpopi ishmi hf).
Qed.

Corollary row_of_run_superflip : rowfull = true ->
  forall m, m \in H -> superflip * m \in ball Sset 20.
Proof.
move=> hr m hm.
have hV : superflip^-1 = superflip.
  by apply: (mulgI superflip); rewrite mulgV; move: superflip2;
     rewrite expgS expg1.
rewrite -{1}hV.
apply: row_of_run.
exact: hr.
exact: hm.
Qed.

(* it must name nothing but the int63 and PArray primitives *)
Print Assumptions row_of_run_superflip.
