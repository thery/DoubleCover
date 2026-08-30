(* =========================================================================  *)
(*  RowFoldCubProof.v -- the row on the folded map, asked.                    *)
(* =========================================================================  *)

(* RowFoldCubReal leaves exactly one thing open -- that the folded map twenty *)
(* levels leave, WITH THE THIRTY TWO WITNESSES MARKED INTO IT, has no bit of  *)
(* the row clear -- and this is that question, asked.  It must print true,    *)
(* and then real_superflip_row_fold is no longer conditional.                 *)
(*                                                                            *)
(* IT IS THE FOLDED MAP, 0.45 GB where the plain one is 6.5, and there is no  *)
(* second map for the witnesses: they are marked in, so mfullf reads ONE map  *)
(* where the plain mfull2 reads two.                                          *)
(*                                                                            *)
(* MEASURED, on roquableu, at depth THIRTEEN and not at twenty: the plain row *)
(* is 2 904.8 s and the folded one 751.3 s.  What twenty costs has not been   *)
(* measured and is not scaled here.                                           *)
(*                                                                            *)
(* THIS FILE CANNOT BE BUILT WHERE P1Fdec IS MISSING.  P1Fdec.v is generated  *)
(* by p1gen and is not tracked, so the folded phase one table is only there   *)
(* on the machine that made it.  Everything this file rests on IS built       *)
(* everywhere: RowFoldCubReal proves the theorem for ANY folded table, since  *)
(* no proof reads it -- the distance and the mask are numbers the search      *)
(* tests, and a table that prunes too little only makes the search bigger.    *)
(*                                                                            *)
(* THE RUN IS NOT HERE.  `./mkrowfold.sh bool' runs it, in a process that     *)
(* loads only what the run reads; this file then loads the proof side and     *)
(* takes the answer without computing.  `./mkrowfold.sh cubfoot' measures     *)
(* what this file costs before it does anything at all.                       *)

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
Require Import Lehmer RowCub RowCubi RowCubInst RowReal FsmChk.
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

(* ---- the run is not in this process, and not in this file ---------------- *)

(* THIS FILE NEVER RUNS ANYTHING.  It says what the run's answer buys, as an  *)
(* implication: `rowfull = true ->' and then the row.  RowFoldCubBool settles *)
(* the left side and loads no proof to do it; RowFoldCubDone puts the two     *)
(* together and is four lines.                                                *)
(*                                                                            *)
(* rowfull is mfullf of RowFoldCubDef's map and yfcwitsoi is mfullf of        *)
(* RowFoldCubReal's.  They are the same map, but every name on the way down   *)
(* differs -- ytomembd against ytomemb tomembi, okmvvd against okmvv,         *)
(* ycsolvedd against ycsolved, srchd against srch -- because the run file     *)
(* loads no proof and so cannot use those constants.                          *)
(*                                                                            *)
(* SO THE UNFOLDING IS WRITTEN OUT, ON BOTH SIDES.  Left to itself,           *)
(* unification does not fail when a name will not match: it reduces, and      *)
(* reducing this is the run again, in the kernel, which is far slower than    *)
(* native.  One side alone is not enough -- unfolding ycsolvedd leaves a      *)
(* lambda against ycsolved, which is still a constant.                        *)
Definition yfcwitsoi : rmap :=
  yfcwitso p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           forbi fpopi ishmi.

(* ---- the four names the run file had to copy ----------------------------- *)

(* RowFoldCubDef loads no proof, so it cannot say ytomemb, okmvv, ycsolved    *)
(* or srch; it writes the same four bodies under its own names.  Each pair is *)
(* equal by unfolding a two line function, which costs nothing.  Rewriting    *)
(* these four makes the two maps the SAME TERM, so nothing is left for        *)
(* unification to search for.                                                 *)
Lemma ytomembdE : ytomembd = ytomemb tomembi.  Proof. by []. Qed.
Lemma okmvvdE   : okmvvd = okmvv.              Proof. by []. Qed.
Lemma ycsolveddE : ycsolvedd = ycsolved.       Proof. by []. Qed.
Lemma srchdE    : srchd = srch.                Proof. by []. Qed.

(* ---- and they are the same map ------------------------------------------- *)

(* Said outright, so that the only thing conversion has to do is compare      *)
(* frunsk's arguments one by one.  It never looks inside the fixpoint: the    *)
(* head is the same constant on both sides.                                   *)
Lemma ycwitsoE : ycwitso = yfcwitsoi.
Proof.
rewrite /ycwitso /rowmap ytomembdE okmvvdE ycsolveddE srchdE.
by rewrite /yfcwitsoi /yfcwitso /yfcmfino /fmfino.
Qed.

(* ---- what the run buys --------------------------------------------------- *)

Theorem row_of_run : rowfull = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite /rowfull ycwitsoE => hf.
exact: (real_superflip_row_foldo p1ftab frepi fsymi twsymi
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
by rewrite -hV; exact: row_of_run hr hm.
Qed.

(* IT MUST NAME NOTHING BUT THE int63 AND PArray PRIMITIVES                   *)
Print Assumptions row_of_run_superflip.
