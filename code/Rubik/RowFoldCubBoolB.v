(* =========================================================================  *)
(*  RowFoldCubBoolB.v -- THE RUN with the fast leaf, the boolean alone.       *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldCubDefB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfulliBE : rowfulliB = true.
Proof. Time native_cast_no_check (erefl true). Qed.
