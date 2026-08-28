(* =========================================================================  *)
(*  RowFoldPart.v -- a part, conjugated by a renaming.                        *)
(* =========================================================================  *)

(* RowMemb cuts a member into three parts -- corners, outer edges, middle --  *)
(* and RowMemb.part_move says what a MOVE does to one of them.  The fold      *)
(* needs what a RENAMING does to one, and a renaming is not a move in two     *)
(* ways.                                                                      *)
(*                                                                            *)
(* IT DOES NOT KEEP THE SLOT.  part_move asks lslot: the table leaves a       *)
(* facelet in the same slot of its place.  Eight of the sixteen renamings     *)
(* REVERSE a corner's three facelets, so that is simply false for them --     *)
(* and RowCub's partt does not cover it either, since a reversal of three is  *)
(* not a rotation.                                                            *)
(*                                                                            *)
(* BUT THE SLOT IT MOVES TO DOES NOT DEPEND ON THE PLACE.  Renaming 1 sends   *)
(* slot 1 to slot 2 at EVERY corner place, and so it goes for all sixteen.    *)
(* So one slot map serves the whole table, which is lslots below -- and in a  *)
(* conjugation that one map appears on both sides and cancels.  That is why   *)
(* no new kind of part is needed here: the statement is about RowMemb's own   *)
(* part, twice.                                                               *)
(*                                                                            *)
(* AND IT ACTS BY CONJUGATION, not on one side.  So what is said is that the  *)
(* renamed part followed by the renaming is the renaming followed by the      *)
(* part -- which is the conjugation with no inverse written down.             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Sym16 Moves Row RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* a walk over the first n numbers answers about any one of them *)
Lemma aiota_lt (P : nat -> bool) n i : all P (iota 0 n) -> (i < n)%N -> P i.
Proof. by move=> hP hi; apply: (allP hP); rewrite mem_iota add0n leq0n hi. Qed.

Section Conj.

Variable lay : seq nat.
Variable nsl npl : nat.
Variable inL : nat -> bool.
Variable plc slt : nat -> nat.

Notation lprm t := (lperm lay nsl npl plc t).
Notation prt u := (part lay nsl inL plc slt u).

(* THE SAME WALK AS lslot, WITH ONE SLOT MAP ADDED.  The table sends the      *)
(* facelet at place p slot s to place lperm t p, slot sw s -- and sw does not *)
(* depend on p, which is what makes the conjugation below work.               *)
Definition lslots (sw : nat -> nat) (t : seq nat) : bool :=
  all (fun i => nth 0%N t (nth 0%N lay i)
                == nth 0%N lay
                     (nth 0%N (lprm t) (i %/ nsl) * nsl + sw (i %% nsl))%N)
      (iota 0 (npl * nsl)).

(* A PART CONJUGATED IS THE PART OF THE CONJUGATED PLACES.  The condition on  *)
(* the places is exactly what the fold tables are checked to say: the renamed *)
(* rank names the conjugated permutation.                                     *)
Lemma part_conj u v sw t :
  layok lay nsl npl inL plc slt -> lslots sw t ->
  all (fun p => nth 0%N (lprm t) (v p) == u (nth 0%N (lprm t) p)) (iota 0 npl) ->
  all (fun p => (v p < npl)%N) (iota 0 npl) ->
  all (fun p => (nth 0%N (lprm t) p < npl)%N) (iota 0 npl) ->
  all (fun s => (sw s < nsl)%N) (iota 0 nsl) ->
  comp_tab (prt v) (restr inL t) = comp_tab (restr inL t) (prt u).
Proof.
move=> hok hsl hcj hv hl hsw.
have h0 : (0 < nsl)%N by case/and4P: hok.
have hsz : seq.size (restr inL t) = 48%N by rewrite /restr size_mkseq.
have hszp : forall w, seq.size (prt w) = 48%N.
  by move=> w; rewrite /part size_mkseq.
have hr : forall g, (g < 48)%N ->
    nth 0%N (restr inL t) g = if inL g then nth 0%N t g else g.
  by move=> g hg; rewrite /restr nth_mkseq.
have hpv : forall g w, (g < 48)%N -> nth 0%N (prt w) g
         = if inL g then nth 0%N lay (w (plc g) * nsl + slt g)%N else g.
  by move=> g w hg; rewrite /part nth_mkseq.
have ht : forall i, (i < npl * nsl)%N ->
    nth 0%N t (nth 0%N lay i)
    = nth 0%N lay (nth 0%N (lprm t) (i %/ nsl) * nsl + sw (i %% nsl))%N.
  by move=> i hi; apply/eqP; apply: (aiota_lt hsl hi).
apply: (@eq_from_nth _ 0%N).
  by rewrite /comp_tab /restr /part !size_map.
move=> f; rewrite /comp_tab size_map hszp => hf.
rewrite -/(comp_tab _ _) -/(comp_tab _ _).
rewrite comp_tabE ?hszp // comp_tabE ?hsz //.
case: (boolP (inL f)) => hL; last first.
  by rewrite (hpv f v hf) (negbTE hL) (hr f hf) (negbTE hL)
             (hpv f u hf) (negbTE hL).
have /andP[hpf hsf] := lay_rng hok hf hL.
have hj1 : (v (plc f) * nsl + slt f < npl * nsl)%N.
  by apply: lidx => //; apply: (aiota_lt hv hpf).
have /and4P[h1a h1b /eqP h1c /eqP h1d] := layP hok hj1.
have hj2 : (nth 0%N (lprm t) (plc f) * nsl + sw (slt f) < npl * nsl)%N.
  by apply: lidx; [apply: (aiota_lt hl hpf) | apply: (aiota_lt hsw hsf)].
have /and4P[h2a h2b /eqP h2c /eqP h2d] := layP hok hj2.
have hjf : (plc f * nsl + slt f < npl * nsl)%N by apply: lidx.
(* where the renaming sends the facelet itself, which the right side needs   *)
have hRt : nth 0%N t f
         = nth 0%N lay (nth 0%N (lprm t) (plc f) * nsl + sw (slt f))%N.
  rewrite -{1}(layK hok hf hL) (ht _ hjf).
  by rewrite divnMDl // divn_small // addn0 modnMDl modn_small.
rewrite (hpv f v hf) hL (hr _ h1a) h1b (ht _ hj1).
rewrite divnMDl // divn_small // addn0 modnMDl modn_small //.
rewrite (hr f hf) hL hRt (hpv _ u h2a) h2b h2c h2d.
have hswf : (sw (slt f) < nsl)%N by apply: (aiota_lt hsw hsf).
by rewrite divnMDl // divn_small // addn0 modnMDl modn_small //
           (eqP (aiota_lt hcj hpf)).
Qed.

End Conj.
