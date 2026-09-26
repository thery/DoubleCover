(* =========================================================================  *)
(*  RowFoldCubBoolD.v -- THE RUN, count kept, the boolean alone.              *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldCubDefD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfulliDE : rowfulliD = true.
Proof. Time native_cast_no_check (erefl true). Time Qed.
