(* =========================================================================  *)
(*  RowBenchCountF.v -- the folded run with every optimisation, timed to 13   *)
(*  beside the section run it is proved equal to.                             *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  rowmapiO against rowmapiD, both in        *)
(* RowFoldCubDef, alternated, twice each: the counts must be 14 731 320       *)
(* all four.                                                                  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Row RowMap RowFold RowFoldTab.
Require Import RowRunConst RowFoldCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving                                           *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiO 1).

(* optimised, then as it was, twice                                           *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiO 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiD 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiO 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiD 13).
