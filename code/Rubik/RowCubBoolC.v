(* =========================================================================  *)
(*  RowCubBoolC.v -- THE PLAIN RUN over the four numbers, the boolean alone.  *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap RowCubDefC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfullpiCE : rowfullpiC = true.
Proof. Time native_cast_no_check (erefl true). Qed.
