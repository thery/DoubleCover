(* A PROBE, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* HBench's node counts came out about ten times SMALLER than the prototype's. *)
(* That is what a different way of counting looks like -- the prototype counts *)
(* a node as it enters it, including the children it cuts at once, and         *)
(* hsearchc never sees those.  It is ALSO what a table read too high looks     *)
(* like, which would cut branches holding a solution and still report no       *)
(* maneuver.  These two tell them apart.                                       *)
(*                                                                            *)
(*   /usr/bin/time -v coqc -R . Rubik HBench2.v                                *)
(*                                                                            *)
(* 1. The table at the root of position 0, along each of the three axes.  The  *)
(*    prototype prints the largest of them as "root table value: 10", so the   *)
(*    largest here must be 10.  This is the whole lookup path -- coordinates,  *)
(*    fold, packing -- against a number computed by the other program.         *)
(*                                                                            *)
(* 2. The same three searches as HBench, counted the prototype's way.  These   *)
(*    must be 773, 28 086 and 880 171 exactly.                                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves HRoot HCoord HSearch HTables HFoldAll.

Import GroupScope.

Definition rootv (i : nat) : int :=
  hget h_which h_fam h_sym_cl h_sym_ct hfoldall (htriple (rooti_ax i 0)).

Eval native_compute in (rootv 0, rootv 1, rootv 2).

Definition hcnt2 (d : nat) : bool * int :=
  hrunn h_mt_e h_mt_cl h_mt_ct h_which h_fam h_sym_cl h_sym_ct hfoldall
        0 [::] d.

Eval native_compute in hcnt2 12.
Eval native_compute in hcnt2 14.
Eval native_compute in hcnt2 16.
