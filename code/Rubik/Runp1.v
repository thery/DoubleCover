(* =========================================================================  *)
(*  Runp1.v -- Running the three view search, as rubik_par runs it.           *)
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

(* the superflip with one move applied -- rubik_par's [step 0 m]              *)
Definition rootm (m : nat) : PArray.array int :=
  comp_tabi 47 sfti (nth sfti mtis m).

(* the depth, and the root depth Far.v's droot mirrors: two moves are fixed   *)
(* by prefixi, so the search below a root has depth - 2 left                  *)
Definition p1depth := 16.
Definition p1droot := p1depth.-2.

(* depth t: the first move is fixed, so the search below it has t - 1 left    *)
Definition runp1 (T : PArray.array (PArray.array int)) (t : nat) : bool :=
  searchz3 T t.-1 (rootm 0) (init3 (rootm 0)) (fcpos 0) ||
  searchz3 T t.-1 (rootm 1) (init3 (rootm 1)) (fcpos 1).

(* a smoke test against the dummy table: it must RUN, and with Dp1 = 0 the    *)
(* heuristic is just the two pair tables, so a shallow depth is enough        *)
Definition smoke : bool := runp1 p1dummy 6.

Time Eval vm_compute in smoke.
