(* =========================================================================  *)
(*  P1Chk0.v                                                                 *)
(*                                                                            *)
(*  p1check0 on the real table: one lookup, the cheap half of the phase    *)
(*                                                                            *)
(*  In its own file for the reason P1TsChk.v is: an all_pow over 2 ^ 24       *)
(*  packed values is not something a day to day build should pay for.         *)
(*                                                                            *)
(*  native_cast_no_check, not `by vm_compute': the latter evaluates twice,    *)
(*  once in the tactic and once when the kernel rechecks the cast at Qed.     *)
(*  If the native compiler is unavailable, vm_cast_no_check (erefl true)      *)
(*  is the fallback -- it also evaluates once, just more slowly.              *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        P1Table.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma p1check0P : p1check0 p1tab.
Proof. Time native_cast_no_check (erefl true). Qed.
