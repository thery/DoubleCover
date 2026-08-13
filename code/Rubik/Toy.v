(* =========================================================================  *)
(*  Toy.v -- The lower bound pipeline end to end, with a heuristic that is    *)
(*     0 everywhere.                                                          *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Ball Table Search Tabi Rubik333 Diameter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Require Import Moves.

(* ---- the heuristic: 0 everywhere ----------------------------------------  *)

Definition D0 (_ : seq nat) := 0.
Definition D0i (_ : PArray.array int) := 0.
Definition h0 (_ : {perm facelet}) := 0.

Lemma h0E t : tab_ok 47 t -> h0 (pt 47 t) = D0 t.
Proof. by []. Qed.

Lemma D0iE a : tabi_ok 47 a -> D0i a = D0 (ti2t 47 a).
Proof. by []. Qed.

(* ---- and the theorem ------------------------------------------------------*)

Theorem superflip_far2 : superflip \notin ball Sset 2.
Proof.
apply: (@searchN _ moves Sset_inv h0 (erefl _) _ 2).
  by move=> g m _.
rewrite mtisE sftiE.
apply: (searchiN n47_small n47_len mtis_ok D0iE h0E sfti_ok).
Time by vm_compute.
Qed.

(* Measured, depth 4, 111 151 nodes, vm_compute (Compute, i.e. cbv, took two  *)
(* minutes and is what used to make this file expensive):                     *)
(*                                                                            *)
(*   searcht 47 mtabs D0 4 sftab    12.50 s     8 900 nodes/s                 *)
(*   searchi 47 mtis  D0i 4 sfti     2.73 s    40 700 nodes/s                 *)
(*                                                                            *)
(* so 4.6x, not the 50x a raw array benchmark suggests: a node composes the   *)
(* table with all eighteen moves, and each composition writes a fresh array   *)
(* of 48 entries, so the cost is in the writes rather than in the reads.      *)
(* Depth 5 is 41 s on arrays -- branching 15 per level, as expected.          *)
(*   Time Eval vm_compute in searcht 47 mtabs D0 4 sftab.                     *)
(*   Time Eval vm_compute in searchi 47 mtis D0i 4 sfti.                      *)
