(* =========================================================================  *)
(*  Foldcert.v -- the twelve checks Foldinst.v assumes, run.                  *)
(*                                                                            *)
(*  THE ONLY EXPENSIVE FILE OF THE FOLD'S BOOKKEEPING.  Foldinst.v states     *)
(*  each check and proves what it buys against a section hypothesis, so a     *)
(*  name that does not typecheck is caught there in seconds.  Here they are   *)
(*  computed at the emitted tables: the two big ones are ractA at             *)
(*  2 ^ 20 x 256 and msymR at 2 ^ 20 x 18 x 16.                               *)
(*                                                                            *)
(*  native_cast_no_check, not "by vm_compute": the latter evaluates twice,    *)
(*  once in the tactic and once when the kernel rechecks the cast at Qed.     *)
(*  This evaluates once, and natively.  Every table it reads has to be        *)
(*  natively precompiled first, the eight chunks included.  If the native     *)
(*  compiler is not available, vm_cast_no_check (erefl true) is the fallback. *)
(*                                                                            *)
(*  `rocq compile -vos' checks the statements without running any of them.    *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Fold P1Fold Foldtab Sym16 P1RTable Foldinst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the cheap ones ------------------------------------------------------ *)

Lemma fsymLCP : fsymLC fsymi.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma smulCP : smulC.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma acttwiLCP : acttwiLC.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma twsymLCP : twsymLC twsymi.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma twsymACP : twsymAC twsymi.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma msymTCP : msymTC twsymi.
Proof. Time native_cast_no_check (erefl true). Qed.

(* ---- the ones over the 2 ^ 20 ranks -------------------------------------- *)

Lemma fsymECP : fsymEC ractab frepi fsymi repsi.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma ractLCP : ractLC ractab.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma actrLCP : actrLC actfsr.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma frepSCP : frepSC ractab frepi.
Proof. Time native_cast_no_check (erefl true). Qed.

(* ---- and the two big ones ------------------------------------------------ *)

Lemma ractACP : ractAC ractab.
Proof. Time native_cast_no_check (erefl true). Qed.

Lemma msymRCP : msymRC ractab actfsr.
Proof. Time native_cast_no_check (erefl true). Qed.
