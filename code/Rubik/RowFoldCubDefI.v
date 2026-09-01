(* =========================================================================  *)
(*  RowFoldCubDefI.v -- the folded run over the search that converts nothing. *)
(* =========================================================================  *)

(* RowFoldCubDef's rowmap, over frunski.  The same map, the same tables, the  *)
(* same cuts and the same stop; the only difference is that no node makes a   *)
(* unary nat of the table's distance.                                         *)
(*                                                                            *)
(* A FILE OF ITS OWN.  RowFoldCubDef is what the eight hour run is banked     *)
(* against, and it must not move until that run is paid for again.            *)

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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* okmvvd's own || is still eager here.  Nesting it would make this run's     *)
(* move test a different function from RowFoldCubDef's, and the equality      *)
(* proof is stated for one okmv; it costs two int tests a move.               *)

(* THE DEPTH IS AN ARGUMENT and the map is not named, for the reason          *)
(* RowFoldCubDef gives: a nullary Definition is a value native_compute keeps. *)
Definition rowmapi (n : nat) : rmap :=
  frunski e8numi e4biti fpgi fsrci fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepi ytomembd okmvvd ycsolvedd
          RowInst.croot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition ycwitsoi : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        (rowmapi 20) rowwits.

Definition rowfulli : bool := mfullf ycwitsoi.
