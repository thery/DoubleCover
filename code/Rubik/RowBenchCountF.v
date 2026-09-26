(* =========================================================================  *)
(*  RowBenchCountF.v -- the folded run with its count kept, timed to 13.      *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowFoldCubDefC's run walks the map after *)
(* every level to count it; RowFoldCubDefD's keeps the count as it marks and *)
(* walks the map only after a prepass.  Both to depth thirteen, the same map; *)
(* the counts must be 14 731 320 both.                                       *)

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
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.
Require Import RowCoord RowCoordLeaf RowFoldCubDefC RowFoldCubDefD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

(* the tables of the four numbers, timed apart from the runs                  *)
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctab 5) (PArray.get etab 5))
    (Uint63.add (PArray.get e8rT 5) (Uint63.add (PArray.get e4rT 5) crootD.1.1.1)).

(* the count walked after every level                                          *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiC 13).

(* the count kept as the marks go                                              *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiD 13).
