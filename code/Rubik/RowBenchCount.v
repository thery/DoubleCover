(* =========================================================================  *)
(*  RowBenchCount.v -- what one count of the plain map costs.                 *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  The plain run counts its map once a      *)
(* level (mcount), and the plain run to thirteen took 416 s against 58 s for *)
(* the folded one.  The first line only builds the empty map; the second      *)
(* builds it and counts it, so the difference is one count.  At thirteen the  *)
(* map is almost empty, as here.                                              *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import RowMap RowSrch.

(* the empty plain map, built and nothing else                               *)
Time Eval native_compute in PArray.length (RowMap.mkempty tt).

(* built and counted                                                          *)
Time Eval native_compute in mcount (RowMap.mkempty tt).
