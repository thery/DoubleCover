(* =========================================================================  *)
(*  RowBench13b.v -- the search at thirteen: plain against counting, and the  *)
(*  cost of ranking and marking.                                              *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowBench13's E4 searched thirteen as the  *)
(* LAST search level, which is the counting search the early stop needs: it   *)
(* carries a (map, count) pair and counts each new bit.  Here the search      *)
(* limit is sixteen, so thirteen is searched by the plain search, as every    *)
(* level but the last is in the real run.                                     *)
(*                                                                            *)
(*   E5  run to 13, search up to 16, bitleaf        count 14 731 320         *)
(*   E6  the same with a leaf that always answers the same member: every     *)
(*       leaf marks one bit, so E5 - E6 is what ranking and marking cost     *)
(*                                                                            *)
(* Compare with RowBench13: E3 (run 13, search 12) = 133.9 s, E4 = 296.2 s.   *)
(* The first Eval is thrown away.                                             *)

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

Definition rowmapY (lf : arr -> memb) (n s : nat) : rmap :=
  frunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepi lf okmvvd ycsolvedd
          RowInst.croot yrooti s forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

(* the member every leaf answers in E6: the root's own, a real member         *)
Definition leaf0 (y : arr) : memb := (0%uint63, 0%uint63, 0%uint63).

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapY bitleaf 13 16).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapY leaf0 13 16).
