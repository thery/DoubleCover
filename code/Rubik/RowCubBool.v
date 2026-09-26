(* =========================================================================  *)
(*  RowCubBool.v -- THE PLAIN RUN, the boolean alone.                         *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap RowCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfullpiOT : rowfullpiO = true.
Proof. Time native_cast_no_check (erefl true). Time Qed.
