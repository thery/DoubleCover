From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1FTable.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.
Set Implicit Arguments.
Local Open Scope uint63_scope.

(* THE CONSISTENCY OF THE STEP: the coordinate stepped by a move must be the
   coordinate OF the position stepped by that move.  RowInst proves it; here
   it is asked of the instantiation. *)
Eval native_compute in croot.
Eval native_compute in coordof sroot.
Eval native_compute in cstep actfsri croot 0.
Eval native_compute in coordof (xstep sroot 0).
Eval native_compute in cstep actfsri croot 3.
Eval native_compute in coordof (xstep sroot 3).
(* and the distance the root's eighteen children read: one must be nine *)
Eval native_compute in
  ifold 18 0%uint63
    (fun k a =>
       let d := fp1g p1ftab frepi fsymi twsymi (cstep actfsri croot k) in
       if (d <? a)%uint63 then d else a) 63%uint63.
