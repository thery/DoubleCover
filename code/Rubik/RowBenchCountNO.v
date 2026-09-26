(* =========================================================================  *)
(*  RowBenchCountNO.v -- the plain run with every optimisation, timed to 13   *)
(*  beside the D run it is proved equal to.                                   *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  rowmappiO (RowCubDefO) against          *)
(* rowmappiD (RowCubDefD), alternated, twice each: the counts must be        *)
(* 14 731 320 all four.                                                       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Row RowMap RowSrch P1FTable.
Require Import RowCubDefD RowCubDefO.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving *)
Time Eval native_compute in PArray.length p1ftab.
Time Eval native_compute in mcount (rowmappiO 1).

(* optimised, then as it was, twice                                           *)
Time Eval native_compute in mcount (rowmappiO 13).
Time Eval native_compute in mcount (rowmappiD 13).
Time Eval native_compute in mcount (rowmappiO 13).
Time Eval native_compute in mcount (rowmappiD 13).
