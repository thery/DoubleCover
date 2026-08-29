(* =========================================================================  *)
(*  RowFoldRunT.v -- the PROVED folded run, reported level by level.          *)
(* =========================================================================  *)

(* NOT A CERTIFICATE.  RowFoldCubProof asks the one boolean; this asks the    *)
(* same run for its count after every level, so that a short depth times what *)
(* a long one will cost and a run in progress can be watched.                 *)
(*                                                                            *)
(* IT IS THE PROVED PATH AND NOT RowFoldCubRun'S.  RowFoldCubRun uses flvls,  *)
(* with hcoset's stop on the last searched level; only flvl -- uncut -- is    *)
(* proved sound, and that is what the certificate runs, so that is what is    *)
(* timed here.  THE COUNTS MAY THEREFORE DIFFER from RowFoldCubRun's at the   *)
(* last searched level: the cut loses words, and losing words only makes the  *)
(* row finish later.                                                          *)
(*                                                                            *)
(* Everything else is the certificate's own: the same step, the same leaf     *)
(* test, the same root, the same tables.                                      *)

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
Require Import Lehmer RowCub RowCubi RowCubInst RowReal.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* one level of the folded row, UNCUT: the level RowFoldRun.flvl_sound proves *)
Notation flvlU :=
  (flvl e8numi e4biti
     fpgi fsrci fsgri fsloi fshii fsbti
     mgri mswi mloi mhii
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) zstepi (ytomemb tomemb) okmvv ycsolved
     RowInst.croot yrooti srch).

(* the run, keeping the count after each level.  The two maps swap: what the  *)
(* level wrote is the next level's source, and its source is the next one's   *)
(* destination -- which is RowFoldSrch.frun, with a count added.              *)
Fixpoint frunlU (n : nat) (d : nat) (m dst : rmap) (acc : seq int) : seq int :=
  if n is n1.+1 then
    let m' := flvlU d.+1 m dst in
    frunlU n1 d.+1 m' m (rcons acc (fcount forbi fpopi m'))
  else acc.
