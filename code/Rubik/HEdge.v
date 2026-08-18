(* =========================================================================  *)
(*  HEdge.v -- obligation C for the edges: a turn acts on the datum.          *)
(* =========================================================================  *)

(* The e coordinate is a ranking of where the four slice cubies sit and how   *)
(* they lie.  What C needs is that a turn sends that datum to another datum   *)
(* by a rule that does not look at the position -- then the table is the      *)
(* ranking of the rule and is checked datum by datum, 190080 of them, with no *)
(* unranking anywhere.  See the header of HAgree.v.                           *)
(*                                                                            *)
(* THE TWO FACTS A TURN GIVES, both computed here over the twelve turns:      *)
(* it carries edge facelets to edge facelets, and it carries the two facelets *)
(* of a place to the two of one place, primary to primary or to secondary     *)
(* consistently.  So `which place a cubie came from' and `is it turned over'  *)
(* are read off the turn alone, which is eplc and eflp below.                 *)
(*                                                                            *)
(* pt_tab_inj is used from HSound.  It belongs in Table.v -- two tables that  *)
(* differ present different permutations is about tables and nothing else --  *)
(* and moving it there is a rebuild of the whole chain, so it waits.          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- inverting a composition, on tables ---------------------------------- *)

(* Table.v has neither this nor pt_tab_inj; with the second the first is one  *)
(* step through the permutations.                                            *)
Lemma inv_tab_comp t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  inv_tab flast (comp_tab t1 t2)
    = comp_tab (inv_tab flast t2) (inv_tab flast t1).
Proof.
move=> ok1 ok2.
apply: pt_tab_inj; first by apply: tab_ok_inv; apply: tab_ok_comp.
  by apply: tab_ok_comp; apply: tab_ok_inv.
by rewrite -ptV ?tab_ok_comp // -ptM // -ptM ?tab_ok_inv // -!ptV // invMg.
Qed.

(* ---- what a turn does to a place ----------------------------------------- *)

(* the facelet the sticker at the primary facelet of place j comes from       *)
Definition eidx (m j : nat) : nat :=
  index (nth 0%N (inv_tab flast (mvt m)) (nth 0%N eprim j)) (eprim ++ esec).

(* the place it came from, and whether it is turned over on the way           *)
Definition eplc (m j : nat) : nat := (eidx m j %% nedge)%N.
Definition eflp (m j : nat) : nat := (eidx m j %/ nedge)%N.

(* A TURN KEEPS EDGES EDGES, both ways round.                                 *)
Lemma emv_edge :
  all (fun m => all (fun f =>
         (index (nth 0%N (mvt m) f) (eprim ++ esec) < 24)%N)
                    (eprim ++ esec)) (iota 0 nq)
  &&
  all (fun m => all (fun f =>
         (index (nth 0%N (inv_tab flast (mvt m)) f) (eprim ++ esec) < 24)%N)
                    (eprim ++ esec)) (iota 0 nq).
Proof. by vm_compute. Qed.

(* AND IT KEEPS THE TWO FACELETS OF A PLACE TOGETHER: they land on the two of *)
(* one place, one on the primary and one on the secondary.                    *)
Lemma emv_pair :
  all (fun m => all (fun j =>
    let ip := index (nth 0%N (mvt m) (nth 0%N eprim j)) (eprim ++ esec) in
    let is_ := index (nth 0%N (mvt m) (nth 0%N esec j)) (eprim ++ esec) in
    ((ip %% nedge == is_ %% nedge) && (ip %/ nedge + is_ %/ nedge == 1))%N)
    (iota 0 nedge)) (iota 0 nq).
Proof. by vm_compute. Qed.

(* eplc is a permutation of the twelve places, and eflp is a bit             *)
Lemma eplc_perm :
  all (fun m => (perm_eq [seq eplc m j | j <- iota 0 nedge] (iota 0 nedge)) &&
                all (fun j => (eflp m j < 2)%N) (iota 0 nedge)) (iota 0 nq).
Proof. by vm_compute. Qed.

(* ---- what is left -------------------------------------------------------- *)

(* With those, the step on the datum is: the cubie at place eplc m j in the   *)
(* position is at place j after the turn, and its flip is the old one plus    *)
(* eflp m j.  Writing that out needs the sticker after the turn to be read    *)
(* back through the turn -- inv_tab_comp above -- and the guard cubti, which  *)
(* is what says the sticker at the secondary facelet belongs to the same      *)
(* cubie as the one at the primary.  Then the datum of a position steps by a  *)
(* rule with no position in it, and the sweep over the 190080 data is what    *)
(* ties the rule to the table.                                                *)
