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
(* Run it with `./mkrowfold.sh proof'.  It runs the OPTIMIZED level.  Watch it with `./mkrowfold.sh cubrun' *)
(* first, which is the same run reported level by level and must print the    *)
(* counts 2560, 72832, 1192960, 14731320.                                     *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* ---- which of the eighteen are moves of H, as RowFoldCut computes it ----- *)

(* The solved coordinate is twist nought and the solved flip and slice rank,  *)
(* which is csolvedci itself.  A move of H is one that leaves it alone.       *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition ishmi : int :=
  Eval vm_compute in
  ifold nmvn 0%uint63
    (fun k a =>
       if Uint63.eqb (fstep csolvedci k) csolvedci
       then Uint63.lor a (Uint63.lsl 1%uint63 k) else a)
    0%uint63.

(* ---- the map the folded run leaves, with the witnesses marked into it ---- *)

(* EVERY OPTIMIZATION ON: Rokicki's early stop and hcoset's two cuts, all     *)
(* three proved sound in RowFoldRun.  The unoptimized certificate is still    *)
(* there -- real_superflip_row_fold on yfcwits -- if this one ever has to be  *)
(* compared against it.                                                       *)
Definition yfcwitsoi : rmap :=
  yfcwitso p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           forbi fpopi ishmi.

(* AND THE MAP: the run and the witnesses together leave no bit of the row    *)
(* clear.  This is the long pole and it is only a run.                        *)
Lemma r_full_foldo : mfullf yfcwitsoi.
Proof. Time native_cast_no_check (erefl true). Qed.

(* ---- and the row of the superflip, with nothing left open ---------------- *)

Theorem real_superflip_row_fold_run h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof.
exact: (real_superflip_row_foldo p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data fsmoveCP
          forbi fpopi ishmi r_full_foldo).
Qed.

Corollary real_row_superflip_fold_run m : m \in H ->
  superflip * m \in ball Sset 20.
Proof.
have hV : superflip^-1 = superflip.
  by apply: (mulgI superflip); rewrite mulgV; move: superflip2;
     rewrite expgS expg1.
by rewrite -hV; exact: real_superflip_row_fold_run.
Qed.

(* IT MUST NAME NOTHING BUT THE int63 AND PArray PRIMITIVES *)
Print Assumptions real_row_superflip_fold_run.
