(* =========================================================================  *)
(*  RowBench13.v -- the Rocq run to thirteen, the search apart from the       *)
(*  prepasses.                                                                *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  The folded run with bitleaf, its search   *)
(* cut off at depth s: rowmapX n s runs n levels and searches only those up   *)
(* to s, the others being prepass alone.                                      *)
(*                                                                            *)
(*   E1  rowmapX 13 0    thirteen prepasses over a map that stays empty       *)
(*   E2  rowmapX 12 12   the reference                                        *)
(*   E3  rowmapX 13 12   E3 - E2 = the prepass of level thirteen              *)
(*   E4  rowmapX 13 13   E4 - E3 = THE SEARCH AT THIRTEEN, alone              *)
(*                                                                            *)
(* Counts: E1 0, E2 1 192 960, E3 the prepass's share, E4 14 731 320.  At     *)
(* the last searched level the run uses the counting search (the early stop's *)
(* one), in E2, E3 and E4 alike.  The first Eval is thrown away.              *)

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
Require Import RowFoldCubDef RowFoldSrchI.

Require Import RowFoldCubDefB RowLeafFast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Definition rowmapX (n s : nat) : rmap :=
  frunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepi bitleaf okmvvd ycsolvedd
          RowInst.croot yrooti s forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

(* the traversal fcount48 adds to every line below *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapX 13 0).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapX 12 12).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapX 13 12).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapX 13 13).
