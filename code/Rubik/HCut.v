(* =========================================================================  *)
(*  HCut.v -- stt_cut: a cut throws no maneuver away.                        *)
(* =========================================================================  *)

(* The fourth hypothesis of HRunS.hsearch_complete: if a word of at most n    *)
(* turns solves the position, the table scores the position at most n along   *)
(* every axis, so the search's cut cannot refuse that word.                   *)
(*                                                                            *)
(* It is HAdmis.h_cut read through the coordinates, but the induction is done *)
(* here on the arrays rather than on permutations: what the search reads is   *)
(* the table at the triple of a position, and the sweep of obligation D says  *)
(* precisely that no turn drops that number by more than one.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon
        HSound HEdge HRunS HCorner HSweep HSweepC HGlue HPok.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- int63: the walk, the lookup, and one addition ----------------------- *)

Lemma landC x y : (x land y)%uint63 = (y land x)%uint63.
Proof. by apply: bit_ext => i; rewrite !land_spec andbC. Qed.

(* where n steps of the sweep's walk get to, in nat                          *)
Lemma to_nat_advn k x : to_nat (HSweep.advn k x) = (to_nat x + k) %% nwB.
Proof.
elim: k x => [|k ih] x /=; first by rewrite addn0 modn_small ?to_nat_bounded.
rewrite ih to_nat_addW to_nat_1 modnDml.
by rewrite addn1 addnS.
Qed.

Lemma advn_of_nat k : (k < nwB)%N -> HSweep.advn k 0%uint63 = of_nat k.
Proof.
move=> kL; apply: to_nat_inj.
by rewrite to_nat_advn to_nat_0 add0n modn_small ?of_natK.
Qed.

(* ---- the cut ------------------------------------------------------------ *)

Section Cut.

Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

Local Notation hg v := (hget which fam sym_cl sym_ct hfold v).
Local Notation hn a :=
  (to_nat (hget which fam sym_cl sym_ct hfold (htriple a))).
Local Notation stp := (stepa mt_e mt_cl mt_ct).

(* WHAT IS TAKEN.  The sweep of obligation D, the three sweeps of C as        *)
(* HSweepC.sweeps_agree delivers them, one lookup on the real table, and the  *)
(* range of the coordinates, which HSweepC.ecoord_lt and its two fellows give *)
(* off the same sweeps.  Everything about the axis view comes from HPok.      *)

Hypothesis Hadmis :
  HSweep.admis mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold.

Hypothesis Hagree : forall (a : arr) m, tabi_ok flast a ->
  cubt (ti2t flast a) -> cubct (ti2t flast a) -> ctsum (inv_tabi flast a) ->
  (m < nq)%N ->
  htriple (comp_tabi flast a (mvq m)) = stp (htriple a) (of_nat m).

Hypothesis Hzero : hg h0i = 0%uint63.

Hypothesis Hcoord : forall (a : arr) e c t, tabi_ok flast a ->
  cubt (ti2t flast a) -> cubct (ti2t flast a) -> ctsum (inv_tabi flast a) ->
  htriple a = (e, c, t) ->
  [/\ (to_nat e < n_e)%N, (to_nat c < n_cl)%N & (to_nat t < n_ct)%N].

(* ---- one lookup is four bits -------------------------------------------- *)

Lemma hget_small v : (to_nat (hg v) <= 15)%N.
Proof.
have h : (to_nat (hg v) < 2 ^ 4)%N.
  case: v => [[e c] t]; rewrite /hget landC.
  by apply: to_nat_land_bound; vm_compute.
have e16 : (2 ^ 4 = 16)%N by [].
by rewrite e16 in h; rewrite -ltnS.
Qed.

Lemma hget_add1 v :
  to_nat (Uint63.add (hg v) 1%uint63) = (to_nat (hg v)).+1.
Proof.
have hs := hget_small v.
have h17 : (17 < nwB)%N by apply: small_nwB.
have hb : (to_nat (hg v) + to_nat 1%uint63 < nwB)%N.
  apply: leq_ltn_trans h17.
  by rewrite to_nat_1 addn1 ltnS; apply: leq_trans hs _.
by rewrite (to_nat_add _ _ hb) to_nat_1 addn1.
Qed.

(* ---- the sweep, at the triple of a position ----------------------------- *)

Lemma adm1_htriple a : tabi_ok flast a -> cubt (ti2t flast a) ->
  cubct (ti2t flast a) -> ctsum (inv_tabi flast a) ->
  HSweep.adm1 mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold (htriple a).
Proof.
move=> aok ca cca cta.
case E : (htriple a) => [[x y] z].
have [he hc ht] := Hcoord aok ca cca cta E.
have hb1 : (to_nat x < nwB)%N by apply: to_nat_bounded.
have hb2 : (to_nat y < nwB)%N by apply: to_nat_bounded.
have hb3 : (to_nat z < nwB)%N by apply: to_nat_bounded.
have ha := HSweep.admisP he hc ht Hadmis.
by rewrite (advn_of_nat hb1) (advn_of_nat hb2) (advn_of_nat hb3)
           !to_natK in ha.
Qed.

(* a turn costs the table at most one, at a position                         *)
Lemma hn_step a m : tabi_ok flast a -> cubt (ti2t flast a) ->
  cubct (ti2t flast a) -> ctsum (inv_tabi flast a) -> (m < nq)%N ->
  (hn a <= (hn (comp_tabi flast a (mvq m))).+1)%N.
Proof.
move=> aok ca cca cta mL.
have ha := adm1_htriple aok ca cca cta.
have m12 : (m < 12)%N by [].
have hbm : (m < nwB)%N by apply: small_nwB; apply: leq_trans (ltnW mL) _.
rewrite /HSweep.adm1 in ha.
have hi : (Uint63.leb (hg (htriple a))
             (Uint63.add (hg (stp (htriple a) (HSweep.advn m 0%uint63)))
                         1%uint63))
  := HSweep.iterP m12 ha.
rewrite (advn_of_nat hbm) -(Hagree aok ca cca cta mL) in hi.
by move/nlebP: hi; rewrite hget_add1.
Qed.

(* the same along an axis                                                    *)
Lemma hnv_step a i m : pok a -> (i < nax)%N -> (m < nq)%N ->
  (hn (view i a) <= (hn (view i (comp_tabi flast a (mvq m)))).+1)%N.
Proof.
move=> pk iL mL.
have aok := pok_okP pk.
have vok := view_ok aok iL.
have /and3P[c1 c2 c3] := pokvP pk iL.
have cmL : (cmv i m < nq)%N by apply: cmv_ltP.
have h1 := hn_step vok c1 c2 c3 cmL.
have mok : tabi_ok flast (mvq m) by apply: tabi_ok_mvq.
have m2 : tabi_ok flast (mvq (cmv i m)) by apply: tabi_ok_mvq.
have cok : tabi_ok flast (comp_tabi flast a (mvq m))
  := tabi_ok_comp n47_small n47_len aok mok.
have cvok : tabi_ok flast (comp_tabi flast (view i a) (mvq (cmv i m)))
  := tabi_ok_comp n47_small n47_len vok m2.
have vcok := view_ok cok iL.
have he : htriple (view i (comp_tabi flast a (mvq m)))
        = htriple (comp_tabi flast (view i a) (mvq (cmv i m))).
  by apply: htriple_eq vcok cvok (view_step aok iL mL).
by rewrite he.
Qed.

(* ---- a word costs the table at most its length -------------------------- *)

Lemma pok_aw v : forall a, pok a -> qw v -> pok (aw a v).
Proof.
elim: v => [|m v ih] a pk vq.
  have -> : aw a [::] = a by [].
  by apply: pk.
have mL : (m < nq)%N by move: vq => /andP[].
have vq' : qw v by move: vq => /andP[].
have pk' : pok (comp_tabi flast a (mvq m)) by apply: pok_step.
rewrite aw_cons.
by apply: ih.
Qed.

Lemma hn_word v : forall a i, pok a -> qw v -> (i < nax)%N ->
  (hn (view i a) <= hn (view i (aw a v)) + seq.size v)%N.
Proof.
elim: v => [|m v ih] a i pk vq iL.
  have -> : aw a [::] = a by [].
  rewrite addn0.
  by apply: leqnn.
have mL : (m < nq)%N by move: vq => /andP[].
have vq' : qw v by move: vq => /andP[].
have pk' : pok (comp_tabi flast a (mvq m)) by apply: pok_step.
have h1 := hnv_step pk iL mL.
have h2 := ih (comp_tabi flast a (mvq m)) i pk' vq' iL.
rewrite aw_cons; apply: (leq_trans h1).
rewrite addnS ltnS.
by apply: h2.
Qed.

(* ---- and the solved position scores zero -------------------------------- *)

Lemma heqP v : heq v -> v = h0i.
Proof.
case: v => [[e c] t]; rewrite /heq.
case: h0i => [[e0 c0] t0]; rewrite !neq_eqE.
case: (e =P e0) => [->|_]; last by [].
case: (c =P c0) => [->|_]; last by [].
by case: (t =P t0) => [->|_].
Qed.

(* the three components of the solved test, one by one                      *)
Lemma hsolvedP x : hsolved x -> [/\ heq x.1.1, heq x.1.2 & heq x.2].
Proof.
case: x => [[x0 x1] x2]; rewrite /hsolved.
by case: (heq x0); case: (heq x1); case: (heq x2).
Qed.

Lemma hn_sol b i : pok b -> (i < nax)%N -> eq_tabi flast b idi ->
  hn (view i b) = 0%N.
Proof.
move=> pk iL hs.
have [k0 k1 k2] : [/\ heq (htriple (view 0 b)), heq (htriple (view 1 b)) &
                      heq (htriple (view 2 b))] := hsolvedP (stt_sol pk hs).
have hh : htriple (view i b) = h0i.
  case: i iL => [|[|[|i]]] iL; last by [].
  by apply: (heqP k0).
  by apply: (heqP k1).
  by apply: (heqP k2).
by rewrite hh Hzero to_nat_0.
Qed.

(* ---- what hsearch_complete asks for ------------------------------------- *)

Lemma stt_cut a v n : pok a -> qw v -> (seq.size v <= n)%N -> (n <= 24)%N ->
  eq_tabi flast (aw a v) idi ->
  hle which fam sym_cl sym_ct hfold (stt a) (of_nat n).
Proof.
move=> pk vq vs nL hs.
have pkw : pok (aw a v) by apply: pok_aw; [apply: pk|apply: vq].
have n48 : (n <= 48)%N by apply: leq_trans nL _.
have nb : (n < nwB)%N by apply: small_nwB.
have hnn : to_nat (of_nat n) = n by apply: of_natK.
have key i : (i < nax)%N ->
    hale which fam sym_cl sym_ct hfold (htriple (view i a)) (of_nat n).
  move=> iL.
  have h1 : (hn (view i a) <= hn (view i (aw a v)) + seq.size v)%N.
    by apply: hn_word; [apply: pk|apply: vq|apply: iL].
  have h2 : hn (view i (aw a v)) = 0%N.
    by apply: hn_sol; [apply: pkw|apply: iL|apply: hs].
  rewrite /hale; apply/nlebP; rewrite hnn.
  apply: leq_trans h1 _.
  rewrite h2 add0n.
  by apply: vs.
rewrite /stt hleE.
apply/and3P; split.
by apply: key.
by apply: key.
by apply: key.
Qed.

End Cut.
