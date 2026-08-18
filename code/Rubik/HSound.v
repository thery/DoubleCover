(* =========================================================================  *)
(*  HSound.v -- obligation E: what the run computed, as a statement about     *)
(*     maneuvers.                                                             *)
(* =========================================================================  *)

(* The seventy two HRun files say the same thing seventy two times: for one of*)
(* Reid's six positions and one of the 120 pairs of turns the search may play *)
(* first, hsearch came back false.  HBound.targ_far asks for something else,  *)
(*                                                                            *)
(*   forall k v, k < size rpfx -> qw v -> okw 0 v ->                          *)
(*     size (nth [::] rpfx k) + size v <= 24 ->                              *)
(*       wp (nth [::] rpfx k ++ v) != targ                                    *)
(*                                                                            *)
(* -- no word the rule accepts finishes the prefix.  Between the two there are*)
(* four steps, and this file holds the first of them, the one that needs no   *)
(* table at all: a word the rule accepts starts with one of the 120 pairs, so *)
(* the 120 jobs between them cover every word.  The other three are           *)
(*                                                                            *)
(*   the state the search carries IS the triple of the position it stands at  *)
(*     -- obligation C, HAgree;                                               *)
(*   the score it cuts on never exceeds the distance -- obligation D, HAdmis, *)
(*     whose h_cut is exactly what a cut needs;                               *)
(*   the fold reads back what the flat table holds.                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the rule along a word ----------------------------------------------  *)

(* the class a word leaves the rule in                                        *)
Definition hclassw (p : nat) (w : seq nat) : nat := foldl hclass p w.

Lemma hclassw_cat p u v : hclassw p (u ++ v) = hclassw (hclassw p u) v.
Proof. by rewrite /hclassw foldl_cat. Qed.

Lemma okw_cat p u v : okw p (u ++ v) = okw p u && okw (hclassw p u) v.
Proof. by elim: u p => [|m u ih] p //=; rewrite -andbA ih. Qed.

(* ---- every accepted word starts with one of the 120 pairs ---------------  *)

(* The first turn is free and the second is whatever the rule allows after it,*)
(* which is how hpres was built, so this is a check over the 144 pairs.       *)
Lemma okw2_hpres :
  all (fun m1 => all (fun m2 => okw 0 [:: m1; m2] ==> ([:: m1; m2] \in hpres))
                     (iota 0 nq))
      (iota 0 nq).
Proof. by vm_compute. Qed.

(* so a word of at least two turns is one of the 120 jobs and a tail the rule *)
(* accepts from where the pair leaves it                                      *)
Lemma okw_hpres (m1 m2 : nat) (v : seq nat) :
  qw [:: m1, m2 & v] -> okw 0 [:: m1, m2 & v] ->
  ([:: m1; m2] \in hpres) /\ okw (hclassw 0 [:: m1; m2]) v.
Proof.
move=> /and3P[m1L m2L _] ow.
have /andP[ot ov] : okw 0 [:: m1; m2] && okw (hclassw 0 [:: m1; m2]) v.
  by rewrite -okw_cat; exact: ow.
split=> //.
have /implyP := allP (allP okw2_hpres _ (mem_iota0 m1L)) _ (mem_iota0 m2L).
by apply.
Qed.

(* ---- and the twelve jobs cover the 120 prefixes -------------------------- *)

(* The run deals the prefixes round robin over twelve jobs, so what has to be  *)
(* true is that every one of them is dealt to somebody.                        *)
Lemma hslice_tab : all (fun w => has (fun j => w \in hslice j 12) (iota 0 12))
                       hpres.
Proof. by vm_compute. Qed.

Lemma hslice_mem (w : seq nat) : w \in hpres ->
  exists2 j, (j < 12)%N & w \in hslice j 12.
Proof.
move=> wp.
have /hasP[j jI wj] := allP hslice_tab _ wp.
by exists j => //; move: jI; rewrite mem_iota.
Qed.
