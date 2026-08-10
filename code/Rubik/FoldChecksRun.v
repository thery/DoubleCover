(* =========================================================================  *)
(*  FoldChecksRun.v -- The twelve checks, run at the emitted tables.        *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Fold P1Fold FoldTables Sym16 P1RTable FoldChecks.

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
