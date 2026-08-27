(* =========================================================================  *)
(*  RowCubL12.v -- the row stopped at 12 levels.                             *)
(* =========================================================================  *)

(* NOT A PROOF.  RowCubRun asks the same question with twenty levels and      *)
(* takes over an hour to reach the point where the memory has twice run       *)
(* away.  This asks it with fourteen, which reaches that point in minutes.    *)
(* IT PRINTS false: fourteen levels do not fill the row.  What is being       *)
(* watched is the resident size, not the answer.                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import RowReal FsmChk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* the same map, 12 levels instead of twenty *)
Definition ycprobe : rmap :=
  ymfin e8numi e4biti mpgi mgri mswi mloi mhii p1 actfsri tomemb okmvv srch 12.

Time Eval native_compute in mfull2 ycprobe (wmap rowwits).
