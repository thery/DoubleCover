(* =========================================================================  *)
(*  Runp1.v -- running the three view search, exactly as rubik_par runs it.   *)
(*                                                                            *)
(*  bench/p1gen.ml's search mode, line for line:                              *)
(*                                                                            *)
(*      cube.(0) <- sfti;  tw/fs.(0).(k) <- the three views of it             *)
(*      List.iter (fun m -> step 0 m; dfs 1 (t-1) 0) [0; 1]                   *)
(*                                                                            *)
(*  The first move is U or U2 -- the superflip is fixed by all 48 symmetries  *)
(*  and is its own inverse, so every maneuver is equivalent to one starting   *)
(*  with a quarter or half turn of a fixed face.  That is the factor of 9.    *)
(*                                                                            *)
(*  NO PROOF IS INVOLVED: this is the computation, and it needs only the      *)
(*  definitions and the tables.  What makes its ANSWER a theorem is           *)
(*  Farp1.far_of_searchz3, which is still admitted.                          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the superflip with one move applied -- rubik_par's [step 0 m] *)
Definition rootm (m : nat) : PArray.array int :=
  comp_tabi 47 sfti (nth sfti mtis m).

(* depth t: the first move is fixed, so the search below it has t - 1 left *)
Definition runp1 (T : PArray.array (PArray.array int)) (t : nat) : bool :=
  searchz3 T t.-1 (rootm 0) (init3 (rootm 0)) (fcpos 0) ||
  searchz3 T t.-1 (rootm 1) (init3 (rootm 1)) (fcpos 1).

(* a smoke test against the dummy table: it must RUN, and with Dp1 = 0 the
   heuristic is just the two pair tables, so a shallow depth is enough *)
Definition smoke : bool := runp1 p1dummy 6.

Time Eval vm_compute in smoke.
