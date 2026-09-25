(* =========================================================================  *)
(*  RowFoldCubDefC.v -- the folded run, int search, over the four numbers.    *)
(* =========================================================================  *)

(* RowFoldCubDefB's run with the position kept as hcoset's four numbers:     *)
(* RowCoord's cstepx moves them and RowCoordLeaf's cmemb reads the member,    *)
(* in the place of zstepi and bitleaf.  Nothing else changed.  No proof here. *)

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
Require Import RowLeafFast RowFoldSrchIC.
Require Import RowCoord RowCoordLeaf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* the root, as four numbers                                                  *)
Definition crootC : cpos := cofy yrooti.

Definition rowmapiC (n : nat) : rmap :=
  frunskic e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd
          RowInst.croot crootC srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition ycwitsoiC : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        (rowmapiC 20) rowwits.

Definition rowfulliC : bool := mfullf ffuli ycwitsoiC.
