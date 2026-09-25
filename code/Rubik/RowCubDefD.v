(* =========================================================================  *)
(*  RowCubDefD.v -- the plain run over the four numbers, its count kept as it *)
(*  goes.                                                                     *)
(* =========================================================================  *)

(* RowCubDefC's run with RowSrchN's level and run: the map is walked only     *)
(* after a prepass, and the count is otherwise the running total of new bits. *)
(* No proof here.                                                             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf.
Require Import RowWits RowWitsChk.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal.
Require Import Fold FoldTables P1Fdec P1FTable RowMask RowSrch RowMark.
Require Import RowLvl.
Require Import RowLeafFast RowSrchC.
Require Import RowCubDef.                             (* ishmi *)
Require Import RowCoord RowCoordLeaf RowSrchN.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* the level is RowSrchC's: the prepass only when the cuts are on           *)
Definition rowmappiD (n : nat) : rmap :=
  runskni e8numi e4biti (prepassD cpgi cfli mgri mswi mloi mhii)
         p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
         (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
         RowInst.croot (cofy yrooti) srch ishmi
         n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition rowwitspiD : rmap := wmarkof rowwits48 (rowmappiD 20).

Definition rowfullpiD : bool := mfull rowwitspiD.
