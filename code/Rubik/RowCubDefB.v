(* =========================================================================  *)
(*  RowCubDefB.v -- the plain run, int search, with the fast leaf.            *)
(* =========================================================================  *)

(* RowCubDef's rowmappi with RowLeafFast's bitleaf at the leaf.  rowmappi     *)
(* hands its leaf in at the table level through ymfinski; this one calls      *)
(* runski itself, with ymfinski's arguments in the same order and bitleaf in  *)
(* the place of ytomemb tomembi.  No proof here.                              *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* the level is RowSrchC's: the prepass only when the cuts are on           *)
Definition rowmappiB (n : nat) : rmap :=
  runskic e8numi e4biti (prepassD cpgi cfli mgri mswi mloi mhii)
         p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
         (RowInst.cstep actfsri) zstepi bitleaf okmvv ycsolved
         RowInst.croot yrooti srch ishmi
         n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition rowwitspiB : rmap := wmarkof rowwits48 (rowmappiB 20).

Definition rowfullpiB : bool := mfull rowwitspiB.
