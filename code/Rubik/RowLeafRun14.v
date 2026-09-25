(* =========================================================================  *)
(*  RowLeafRun14.v -- the run to fourteen, with the run's leaf and straight.  *)
(* =========================================================================  *)

(* A BENCH, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* RowLeafBench measured one leaf: 12.0 us for the run's (the twenty turned   *)
(* back into forty eight and inverted, then ranked) against 5.0 us ranked     *)
(* straight from the twenty.  Fourteen has 148 423 860 leaves, so the two     *)
(* runs below should differ by about 1 040 s.                                 *)
(*                                                                            *)
(*   cd code/Rubik && ulimit -s unlimited                                     *)
(*   /usr/bin/time -v coqc -R . Rubik RowLeafRun14.v                          *)
(*                                                                            *)
(* THE TWO COUNTS MUST BE THE SAME.  The first Eval pays for the tables       *)
(* arriving and is thrown away.                                               *)

(* RowFoldCubDef's own list, so every name rowmapi uses is in scope          *)
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
Require Import RowFoldCubDef RowFoldSrchI RowFoldCubDefI.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* RowLeafBench's: straight from the twenty                                   *)
Definition dirleaf (y : arr) : memb :=
  (rank8i (fun p => PArray.get y p / 3),
   rank8i (fun p => PArray.get y (8 + p) / 2),
   rank4i (fun p => PArray.get y (16 + p) / 2 - 8)).

(* rowmapi with dirleaf in the place of ytomembd, and nothing else changed    *)
Definition rowmapd (n : nat) : rmap :=
  frunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepi dirleaf okmvvd ycsolvedd
          RowInst.croot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition dlev : nat := 14.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapi dlev).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapd dlev).
