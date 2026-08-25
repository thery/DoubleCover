(* =========================================================================  *)
(*  RowFoldLoad.v -- what LOADING the row's tables costs, and nothing else.   *)
(* =========================================================================  *)

(* Exactly RowFoldChk.v's requires, and then a sum of two numbers.  Whatever
   memory this takes is what the tables cost before a single level runs. *)

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
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* nothing is computed: the number below is what LOADING costs, and nothing
   else.  Watch the memory while it runs. *)
Time Eval native_compute in Uint63.add 1 1.
