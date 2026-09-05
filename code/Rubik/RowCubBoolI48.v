(* =========================================================================  *)
(*  RowCubBoolI48.v -- the forty eight bit run's boolean, over the int search.*)
(* =========================================================================  *)

(* One Require, one Lemma.  The long run, on a map of 3.25 GB where the       *)
(* twenty four bit one is 6.5 GB.                                            *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap48 RowCubDef48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfullpi48E : rowfullpi48 = true.
Proof. Time native_cast_no_check (erefl true). Qed.
