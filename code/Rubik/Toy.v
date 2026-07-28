(* =========================================================================  *)
(*  Toy.v                                                                     *)
(*                                                                            *)
(*  The lower-bound pipeline, run for real, once, at a ridiculous depth.      *)
(*                                                                            *)
(*  Everything the depth 19 proof needs is here except size: the moves as     *)
(*  tables, the position as a table, a heuristic, the search in the kernel,   *)
(*  and the two bridges that turn a false answer into a membership fact.      *)
(*  The heuristic is 0 everywhere -- admissible, useless -- so the search is  *)
(*  brute force and only tiny depths are affordable.  Replacing it by a real  *)
(*  table changes this file in one place.                                     *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Diameter.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the moves, as tables, in the order of Rubik333.moves ---------------- *)

Definition mtabs : seq (seq nat) :=
  flatten [seq [:: t; exp_tab 47 t 2; inv_tab 47 t]
          | t <- [:: cycs_tab 47 Uncyc; cycs_tab 47 Rncyc; cycs_tab 47 Fncyc;
                     cycs_tab 47 Dncyc; cycs_tab 47 Lncyc; cycs_tab 47 Bncyc]].

Lemma mtabs_ok : all (tab_ok 47) mtabs.
Proof. by vm_compute. Qed.

Lemma mtabsE : moves = [seq pt 47 mt | mt <- mtabs].
Proof.
rewrite /moves /faces {1}/map /flatten /foldr /cat.
by rewrite UmoveT RmoveT FmoveT DmoveT LmoveT BmoveT !ptX // !ptV //.
Qed.

(* ---- the superflip, as a table -------------------------------------------*)

Definition sfncyc : seq (seq nat) :=
  [:: [:: 1; 33]; [:: 3; 9]; [:: 4; 25]; [:: 6; 17]; [:: 11; 36];
      [:: 12; 19]; [:: 14; 43]; [:: 20; 27]; [:: 22; 41]; [:: 28; 35];
      [:: 30; 44]; [:: 38; 46]]%N.

Definition sftab : seq nat := cycs_tab 47 sfncyc.

Lemma sftab_ok : tab_ok 47 sftab.
Proof. by vm_compute. Qed.

Lemma sftabE : superflip = pt 47 sftab.
Proof.
rewrite /superflip /Spcyc /sftab.
by have ->// := @cycs_pt 47%N sfncyc.
Qed.

(* ---- the same, on int63 and PArray ---------------------------------------*)
(*                                                                            *)
(*  The Ti copies of the T theorems above.  t2ti is the only conversion, and  *)
(*  ti2t_t2ti reads the list back unchanged, so each Ti lemma is its T lemma  *)
(*  plus one rewrite -- nothing about the cube is proved twice.               *)

(* the two side conditions of Tabi.v, at n = 47.  nwB is 2 ^ 63 and nat is    *)
(* unary, so the first is not a computation but a comparison of exponents.    *)
Lemma n47_small : 47.+1 < nwB.
Proof. by apply: (@ltn_nwB 6). Qed.

Lemma n47_len : (of_nat 47.+1 <=? PArray.max_length)%uint63.
Proof. by vm_compute. Qed.

Definition mtis : seq (PArray.array int) := [seq t2ti 47 mt | mt <- mtabs].
Definition sfti : PArray.array int := t2ti 47 sftab.

Lemma mtis_ok : all (tabi_ok 47) mtis.
Proof.
rewrite /mtis all_map; apply/allP => mt mtM /=.
by apply: (tabi_ok_t2ti n47_small n47_len); apply: (allP mtabs_ok).
Qed.

Lemma sfti_ok : tabi_ok 47 sfti.
Proof. by rewrite /sfti; apply: (tabi_ok_t2ti n47_small n47_len sftab_ok). Qed.

Lemma ti2t_mtis : [seq ti2t 47 mt | mt <- mtis] = mtabs.
Proof.
rewrite /mtis -map_comp -[RHS]map_id; apply/eq_in_map => mt mtM /=.
by apply: (ti2t_t2ti n47_small n47_len); apply: (allP mtabs_ok).
Qed.

Lemma mtisE : moves = [seq pt 47 mt | mt <- [seq ti2t 47 mt | mt <- mtis]].
Proof. by rewrite ti2t_mtis -mtabsE. Qed.

Lemma sftiE : superflip = pt 47 (ti2t 47 sfti).
Proof. by rewrite /sfti (ti2t_t2ti n47_small n47_len sftab_ok) sftabE. Qed.

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
