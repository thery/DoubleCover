(* =========================================================================  *)
(*  Sym16Row.v -- the row of the superflip is stable under the sixteen.       *)
(* =========================================================================  *)

(* Sym16 says the sixteen renamings permute the eighteen moves.  This file    *)
(* says what that is worth for the row: they fix the superflip, they map the  *)
(* ball of radius n to itself, and so a member of the row carries its whole   *)
(* orbit with it.  That is what lets the map be folded and one page of each   *)
(* orbit be kept.                                                             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord.
Require Import Diameter Moves Far Sym16.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma size_moves18 : seq.size moves = 18%N.
Proof. by rewrite mtabsE seq.size_map; vm_compute. Qed.

(* ---- the sixteen fix the superflip --------------------------------------- *)

Definition sfsymC : bool :=
  all (fun i => conjt (nth [::] sym16ts i) sftab == sftab) (iota 0 16).

Lemma sfsymCP : sfsymC. Proof. by vm_compute. Qed.

Lemma sym16_sf i : (i < 16)%N ->
  superflip ^ pt 47 (nth [::] sym16ts i) = superflip.
Proof.
move=> hi.
have hs := sym16_tab_ok hi.
have /allP h := sfsymCP.
have /eqP he : conjt (nth [::] sym16ts i) sftab == sftab.
  by apply: h; rewrite mem_iota add0n leq0n hi.
by rewrite {1}sftabE (ptJ sftab_ok hs) -/(conjt _ _) he -sftabE.
Qed.

(* ---- and they map the ball to itself ------------------------------------- *)

Lemma sym16_Sset i g : (i < 16)%N -> g \in Sset ->
  g ^ pt 47 (nth [::] sym16ts i) \in Sset.
Proof.
move=> hi; rewrite inE => hg; rewrite inE.
have [k hk hge] : exists2 k, (k < 18)%N & nth 1 moves k = g.
  have /(nthP 1)[k hk hge] := hg.
  rewrite size_moves18 in hk.
  by exists k.
by rewrite -hge (sym16_movesJ hi hk) mem_nth // size_moves18 symmove_lt.
Qed.

Lemma sym16_ball i n g : (i < 16)%N -> g \in ball Sset n ->
  g ^ pt 47 (nth [::] sym16ts i) \in ball Sset n.
Proof.
move=> hi; elim: n g => [|n IH] g.
  by rewrite ball0 !inE => /eqP ->; rewrite conj1g.
rewrite /= !inE => /orP[hg|hg]; first by rewrite IH.
apply/orP; right.
have /mulsgP[a b ha hb he] := hg.
rewrite he conjMg; apply: mem_mulg; first by apply: IH.
by apply: sym16_Sset.
Qed.

(* ---- so the row carries its orbit ---------------------------------------- *)

(* THE FACT THE FOLD RESTS ON.  If a position is within twenty of the         *)
(* superflip then so is its image under any of the sixteen, by the same       *)
(* number of moves.  So one member of each orbit is enough to keep.           *)
Lemma sym16_row i h : (i < 16)%N ->
  superflip^-1 * h \in ball Sset 20 ->
  superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i)) \in ball Sset 20.
Proof.
move=> hi hb; have := sym16_ball hi hb.
by rewrite conjMg conjVg (sym16_sf hi).
Qed.
