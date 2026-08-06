(* =========================================================================  *)
(*  FastBench.v                                                               *)
(*                                                                            *)
(*  One piece at depth 14 -- i.e. what n = 16 runs -- the current searchz3    *)
(*  against Fast.searchz3f, both under native_compute.  Timing only, no       *)
(*  proof: searchz3f is not yet tied to searchz3 by anything.                 *)
(*                                                                            *)
(*  ONLY roquableu can build this: it needs the real p1tab.                   *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Fsparity
        Farp1 P1Table Fast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* piece 0, depth 14 *)
Definition oldrun : bool :=
  all (fun i => ~~ searchz3 p1tab 14 (prefixi i 0)
                            (init3 (prefixi i 0)) nfcube)
      (iota 0 nroot).

Definition newrun : bool :=
  all (fun i => ~~ searchz3f p1tab 14 14%uint63 (prefixi i 0)
                             (init3 (prefixi i 0)) nfcube)
      (iota 0 nroot).

Definition grun : bool :=
  all (fun i => ~~ searchz3g p1tab 14 14%uint63 (prefixi i 0)
                             (init3 (prefixi i 0)) nfcube)
      (iota 0 nroot).

Definition hrun : bool :=
  all (fun i => ~~ searchz3h p1tab 14 14%uint63 (prefixi i 0)
                             (init3 (prefixi i 0)) nfcube)
      (iota 0 nroot).

Definition krun : bool :=
  all (fun i => ~~ searchz3k p1tab 14 14%uint63 (prefixi i 0)
                             (init3 (prefixi i 0)) nfcube)
      (iota 0 nroot).

Definition mrun : bool :=
  all (fun i => ~~ searchz3m p1tab 14 14%uint63 (prefixi i 0)
                             (init3 (prefixi i 0)) nfcube)
      (iota 0 nroot).

(* ALL must print true, or the comparison means nothing *)
Time Eval native_compute in oldrun.
Time Eval native_compute in newrun.
Time Eval native_compute in grun.
Time Eval native_compute in hrun.
Time Eval native_compute in krun.
Time Eval native_compute in mrun.
