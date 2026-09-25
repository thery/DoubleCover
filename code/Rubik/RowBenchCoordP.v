(* =========================================================================  *)
(*  RowBenchCoordP.v -- the proved runs over the four numbers, timed to 13.   *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowFoldCubDefC's folded run and          *)
(* RowCubDefC's plain run, the runs RowFoldCubProofC and RowCubProofC show    *)
(* equal to the runs over the twenty cubies, each to depth thirteen.  The     *)
(* counts must be 14 731 320 both.                                           *)

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
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.
Require Import RowCoord RowCoordLeaf RowFoldCubDefC RowCubDefC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

(* the tables of the four numbers, timed apart from the runs                  *)
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctab 5) (PArray.get etab 5))
    (Uint63.add (PArray.get e8rT 5) (Uint63.add (PArray.get e4rT 5) crootC.1.1.1)).

(* the folded run                                                              *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiC 13).

(* the plain run                                                               *)
Time Eval native_compute in mcount (rowmappiC 13).
