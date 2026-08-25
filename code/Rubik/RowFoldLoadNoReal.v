(* =========================================================================  *)
(*  RowFoldLoadNoReal.v -- the same, without RowReal and so without P1Table.  *)
(* =========================================================================  *)

(* The same as RowFoldLoad.v but without RowReal, which is the only file that
   brings in P1Table -- the UNFOLDED phase one table, 2 217 093 120 entries,
   which the folded row never reads.  The difference between the two runs is
   what that table costs to load. *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* nothing is computed: the number below is what LOADING costs, and nothing
   else.  Watch the memory while it runs. *)
Time Eval native_compute in Uint63.add 1 1.
