(* =========================================================================  *)
(*  RowFoldCubFoot.v -- what the certificate costs before it does anything.   *)
(* =========================================================================  *)

(* THE CERTIFICATE DIED AT 56 GB WITHOUT RUNNING A LEVEL, and the map it      *)
(* still had to build is fifteen.  So the question is not how fast the run    *)
(* is, it is how much is gone before the run starts.                          *)
(*                                                                            *)
(* This is RowFoldCubProof's Require list, word for word, and NOTHING else:   *)
(* no definition, no proof, no Eval.  Compile it and watch RES.  What it      *)
(* settles at is the floor, and the run needs fifteen gigabytes above it.     *)
(*                                                                            *)
(* Compare it with RowFoldFoot, which is the measuring run's own list and     *)
(* whose run plateaued at 15.5 GB.  The difference between the two floors is  *)
(* the price of the proof side, and it is the number that says whether the    *)
(* certificate can be a single file at all.                                   *)

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
