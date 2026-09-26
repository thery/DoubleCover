(* =========================================================================  *)
(*  RowCubBoolD.v -- THE PLAIN RUN, running count, the boolean alone.         *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap RowCubDefD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfullpiDE : rowfullpiD = true.
Proof. Time native_cast_no_check (erefl true). Time Qed.
