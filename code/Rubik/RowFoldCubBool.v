(* =========================================================================  *)
(*  RowFoldCubBool.v -- THE FOLDED RUN, the boolean alone.                    *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfulliOT : rowfulliO = true.
Proof. Time native_cast_no_check (erefl true). Time Qed.
