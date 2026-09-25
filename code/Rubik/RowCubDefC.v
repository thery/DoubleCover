(* =========================================================================  *)
(*  RowCubDefC.v -- the plain run, int search, over the four numbers.         *)
(* =========================================================================  *)

(* RowCubDefB's run with the position kept as hcoset's four numbers:          *)
(* RowCoord's cstepx moves them and RowCoordLeaf's cmemb reads the member,    *)
(* in the place of zstepi and bitleaf.  Nothing else changed.  No proof here. *)

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
Require Import RowCoord RowCoordLeaf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* the level is RowSrchC's: the prepass only when the cuts are on           *)
Definition rowmappiC (n : nat) : rmap :=
  runskic e8numi e4biti (prepassD cpgi cfli mgri mswi mloi mhii)
         p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
         (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
         RowInst.croot (cofy yrooti) srch ishmi
         n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition rowwitspiC : rmap := wmarkof rowwits48 (rowmappiC 20).

Definition rowfullpiC : bool := mfull rowwitspiC.
