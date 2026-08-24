(* =========================================================================  *)
(*  RowFoldRun.v -- the folded level, run.                                    *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  This file runs the folded level on the ball of H   *)
(* itself -- the row of the solved position -- and prints how many members    *)
(* each level holds.  The numbers are the prototype's, and they have to be    *)
(* the same ones:                                                             *)
(*                                                                            *)
(*   1  11  78  534  3613  23561  146635  883485  5068603  27699336           *)
(*                                                                            *)
(* measured by ocaml/rubik_row.ml fball, which agrees in its turn with the    *)
(* same ball worked out one position at a time up to five.  So this is the    *)
(* level checked against the prototype, level by level, and not a plausible   *)
(* number.                                                                    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowTabL RowTabP RowTab RowTabF RowFoldTab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* the solved position, where it stands: the first page, the group of the     *)
(* first outer permutation, and the bit of the first middle one               *)
Definition fseed : PArray.array (PArray.array int) :=
  fmark fpgi fsgri fsbti memptyf 0
    (Uint63.lsr (PArray.get e8numi 0) 1) (PArray.get e4biti 0).

Notation flv n :=
  (flevn fsrci fsgri fsloi fshii mgri mswi mloi mhii n fseed).

Notation fcnt m := (fcount forbi fpopi m).

(* the empty map first: no level in it at all, so its time is what loading    *)
(* and the count cost, and every line after it is that plus the levels        *)
Time Eval native_compute in fcnt fseed.

Time Eval native_compute in fcnt (flv 1).
Time Eval native_compute in fcnt (flv 2).
Time Eval native_compute in fcnt (flv 3).
