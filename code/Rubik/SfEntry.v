(* =========================================================================  *)
(*  SfEntry.v -- The phase 1 summary of the superflip, and the entry the      *)
(*     search reads at the root.                                              *)
(*                                                                            *)
(*  NOT in _CoqProject: it requires P1FTable, which does not exist until      *)
(*  mkfold.sh has emitted it.  Run it where the tables are:                   *)
(*                                                                            *)
(*     ulimit -s unlimited; rocq compile -R . Rubik SfEntry.v                 *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Fold P1Fold FoldTables P1FTable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* The summary: the corner twist and the flip x slice value.  Measured on the *)
(* desktop, where no table is needed: (0, 15732735), and 15732735 is          *)
(* 0xF00FFF -- twelve flip bits set, and the mask of the four slice slots.    *)
Eval vm_compute in (ctwistt sftab, coordt sftab).

(* The entry the search reads at the root.  This one needs the real table.    *)
(* Measured on roquableu with the folded table: 10.                          *)
Eval vm_compute in Dp1i p1ftab (ctwistt sftab) (coordt sftab).
