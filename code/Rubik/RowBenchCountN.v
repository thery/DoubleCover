(* =========================================================================  *)
(*  RowBenchCountN.v -- the plain run with its running count, to thirteen.    *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowCubDefD's run to thirteen, against the *)
(* 416 s of RowCubDefC's (RowBenchCoordP), of which one walk of the map was   *)
(* 29.6 s and there were thirteen (RowBenchCount).  The count must print      *)
(* 14 731 320.                                                                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask RowSrch.
Require Import RowCoord RowCoordLeaf RowCubDefD.

(* thrown away: the table arriving                                            *)
Time Eval native_compute in PArray.length p1ftab.

(* the plain run to thirteen, the count kept as it goes                       *)
Time Eval native_compute in mcount (rowmappiD 13).
