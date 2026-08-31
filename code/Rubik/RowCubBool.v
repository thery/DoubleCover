(* =========================================================================  *)
(*  RowCubBool.v -- the plain run's boolean.                                  *)
(* =========================================================================  *)

(* One Require, one Lemma.  The long run.  See doc/rowfold-bridge.md.         *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap RowCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfullpE : rowfullp = true.
Proof. Time native_cast_no_check (erefl true). Qed.
