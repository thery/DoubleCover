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

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Search Tsearch Rubik333 Sym Diameter.

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

(* ---- the heuristic: 0 everywhere ----------------------------------------  *)

Definition D0 (_ : seq nat) := 0.
Definition h0 (_ : {perm facelet}) := 0.

Lemma h0E t : tab_ok 47 t -> h0 (pt 47 t) = D0 t.
Proof. by []. Qed.

(* ---- and the theorem ------------------------------------------------------*)

Theorem superflip_far2 : superflip \notin ball Sset 2.
Proof.
apply: (@searchN _ moves Sset_inv h0 (erefl _) _ 2).
  by move=> g m _.
rewrite mtabsE sftabE.
apply: (searchtN mtabs_ok h0E sftab_ok).
Time by vm_compute.
Qed.


 Time Compute searcht 47 mtabs D0 4 sftab.
