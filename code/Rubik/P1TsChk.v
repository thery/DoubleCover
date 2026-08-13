(* =========================================================================  *)
(*  P1TsChk.v -- The twist x slice table's step certificate, and nothing      *)
(*     else.                                                                  *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Phase1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* If the native compiler is unavailable, vm_cast_no_check (erefl true) is the
   fallback -- it evaluates once as well, just more slowly.                   *)
Lemma ts_checkStepP : ts_checkStep.
Proof. Time native_cast_no_check (erefl true). Qed.
