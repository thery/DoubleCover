(* =========================================================================  *)
(*  P1TsChk.v                                                                 *)
(*                                                                            *)
(*  The twist x slice table's step certificate, and nothing else.             *)
(*                                                                            *)
(*  2187 twists x 4096 masks x 18 moves = 161 243 136 conditions.  MEASURED   *)
(*  at 25.8 s for 200 twists under vm_compute, so about 4.7 minutes for all   *)
(*  of them -- and vm_compute would pay it TWICE, once in the tactic and once *)
(*  when the kernel rechecks the cast at Qed.  native_cast_no_check evaluates *)
(*  once, natively, which is what the sixteen Fs_??.v and the eighteen        *)
(*  Far_??.v already do.                                                      *)
(*                                                                            *)
(*  It is in its own file for the same reason they are: so that a day to day  *)
(*  build of Phase1.v does not pay for it.                                    *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts Phase1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* If the native compiler is unavailable, vm_cast_no_check (erefl true) is the
   fallback -- it evaluates once as well, just more slowly. *)
Lemma ts_checkStepP : ts_checkStep.
Proof. Time native_cast_no_check (erefl true). Qed.
