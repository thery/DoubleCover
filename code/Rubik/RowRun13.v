(* =========================================================================  *)
(*  RowRun13.v -- the folded run to thirteen, fast leaf and old leaf.         *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  To set beside the OCaml prototype and     *)
(* hcoset at depth thirteen: bench13.sh runs the three on one core.  Each     *)
(* time is the WHOLE run to thirteen, the levels before it and their          *)
(* prepasses included; the count must be 14 731 320 both times.  The first    *)
(* Eval pays for the tables arriving and is thrown away.                      *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldTab RowFoldCubDef RowFoldCubDefI RowFoldCubDefB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition dlev : nat := 13.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiB dlev).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapi dlev).
