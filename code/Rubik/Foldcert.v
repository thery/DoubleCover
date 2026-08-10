(* =========================================================================  *)
(*  Foldcert.v -- the twelve checks Foldinst.v assumes, run.                  *)
(*                                                                            *)
(*  THE ONLY EXPENSIVE FILE OF THE FOLD'S BOOKKEEPING.  Foldinst.v states     *)
(*  each check and proves what it buys against a section hypothesis, so a     *)
(*  name that does not typecheck is caught there in seconds.  Here they are   *)
(*  computed at the emitted tables: the two big ones are ractA at             *)
(*  2 ^ 20 x 256 and msymR at 2 ^ 20 x 18 x 16.                               *)
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

Lemma fsymLCP : fsymLC fsymi. Proof. by vm_compute. Qed.

Lemma smulCP : smulC. Proof. by vm_compute. Qed.

Lemma acttwiLCP : acttwiLC. Proof. by vm_compute. Qed.

Lemma twsymLCP : twsymLC twsymi. Proof. by vm_compute. Qed.

Lemma twsymACP : twsymAC twsymi. Proof. by vm_compute. Qed.

Lemma msymTCP : msymTC twsymi. Proof. by vm_compute. Qed.

(* ---- the ones over the 2 ^ 20 ranks -------------------------------------- *)

Lemma fsymECP : fsymEC ractab frepi fsymi repsi. Proof. by vm_compute. Qed.

Lemma ractLCP : ractLC ractab. Proof. by vm_compute. Qed.

Lemma actrLCP : actrLC actfsr. Proof. by vm_compute. Qed.

Lemma frepSCP : frepSC ractab frepi. Proof. by vm_compute. Qed.

(* ---- and the two big ones ------------------------------------------------ *)

Lemma ractACP : ractAC ractab. Proof. by vm_compute. Qed.

Lemma msymRCP : msymRC ractab actfsr. Proof. by vm_compute. Qed.
