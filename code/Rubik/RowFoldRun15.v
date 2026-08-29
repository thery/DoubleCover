(* =========================================================================  *)
(*  RowFoldRun15.v -- the proved folded run to depth 15, timed.                *)
(* =========================================================================  *)

(* One depth, one process, so that ten, thirteen and fifteen can be run side  *)
(* by side and twenty be estimated from them rather than guessed.             *)
(*                                                                            *)
(* THE FIRST Eval IS THROWN AWAY: the first of a file pays for the tables     *)
(* arriving, and that cost does not grow with the depth.                      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldTab RowFoldRunT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

Time Eval native_compute in frunlU 15 0 (mkempty tt) (mkempty tt) [::].
