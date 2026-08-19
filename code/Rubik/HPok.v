(* =========================================================================  *)
(*  HPok.v -- the positions the search meets, and the triples it carries.     *)
(* =========================================================================  *)

(* HRunS.hsearch_complete asks for a pok and a stt and four things about      *)
(* them.  This file fixes what they are and proves three of the four; what is *)
(* left is stt_cut, which is where obligation D is spent, and the root.       *)
(*                                                                            *)
(* THE THREE AXES ARE CONJUGATIONS, and that is what makes stt a function of  *)
(* the position at all.  A viewing angle relabels the faces, so the position  *)
(* seen along it is the position conjugated by a rotation, and HGlue.axtab is *)
(* that rotation.  Conjugation is a homomorphism, so a turn seen along an     *)
(* axis is that axis's turn -- which is the cmv the search steps with.        *)
(*                                                                            *)
(* WHAT pok HAS TO SAY is whatever the coordinates need of a position, along  *)
(* EVERY axis, since the triple is read along all three: the two facelet      *)
(* guards, and that the eight corner twists sum to zero mod three.  All three *)
(* survive a turn (HEdge.cubt_step, HCorner.cubct_step, HSweepC.ctsum_step),  *)
(* and so pok does.                                                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon
        HSound HEdge HRunS HCorner HSweepC HGlue.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- two lemmas the rest is short with ----------------------------------- *)

(* a fold whose body is only ever handed elements of the list                 *)
Lemma eq_in_foldl (T : eqType) (R : Type) (f g : R -> T -> R) s (x : R) :
  (forall y z, y \in s -> f z y = g z y) -> foldl f x s = foldl g x s.
Proof.
elim: s x => [//|y s ih] x he /=.
rewrite he ?inE ?eqxx //.
by apply: ih => z w hz; rewrite he // inE hz orbT.
Qed.

(* ---- conjugation, on tables ---------------------------------------------- *)

Lemma conjt_ok s t : tab_ok flast s -> tab_ok flast t ->
  tab_ok flast (conjt s t).
Proof.
by move=> sok tok; rewrite /conjt; apply: tab_ok_comp;
   [apply: tab_ok_inv | apply: tab_ok_comp].
Qed.

Lemma pt_conjt s t : tab_ok flast s -> tab_ok flast t ->
  pt flast (conjt s t) = (pt flast t) ^ (pt flast s).
Proof. by move=> sok tok; rewrite /conjt -ptJ. Qed.

(* what makes a view of a turn a turn: conjugation is a homomorphism          *)
Lemma conjt_hom s t1 t2 : tab_ok flast s -> tab_ok flast t1 ->
  tab_ok flast t2 ->
  conjt s (comp_tab t1 t2) = comp_tab (conjt s t1) (conjt s t2).
Proof.
move=> sok o1 o2.
apply: pt_tab_inj; [by apply: conjt_ok => //; apply: tab_ok_comp | |].
  by apply: tab_ok_comp; apply: conjt_ok.
rewrite (pt_conjt sok (tab_ok_comp o1 o2)) -ptM ?conjt_ok //.
by rewrite -ptM ?conjt_ok // !pt_conjt // conjMg.
Qed.

Lemma conjt_id1 s : tab_ok flast s -> conjt s (id_tab flast) = id_tab flast.
Proof.
move=> sok; apply: pt_tab_inj; [by apply: conjt_ok => //; apply: tab_ok_id |
  by apply: tab_ok_id |].
by rewrite pt_conjt ?tab_ok_id // !pt1 conj1g.
Qed.

(* ---- the axis view ------------------------------------------------------- *)

(* the rotation of each axis, as an array, and the view it gives              *)
Definition axi (i : nat) : arr := t2ti flast (axtab i).

Definition view (i : nat) (a : arr) : arr :=
  comp_tabi flast (inv_tabi flast (axi i)) (comp_tabi flast a (axi i)).

Lemma axtab_okP i : (i < nax)%N -> tab_ok flast (axtab i).
Proof. by move=> iL; apply: (allP axtab_ok); apply: mem_iota0. Qed.

Lemma ti2t_axi i : (i < nax)%N -> ti2t flast (axi i) = axtab i.
Proof.
by move=> iL; rewrite /axi (ti2t_t2ti n47_small n47_len (axtab_okP iL)).
Qed.

Lemma axi_ok i : (i < nax)%N -> tabi_ok flast (axi i).
Proof. by move=> iL; rewrite /tabi_ok ti2t_axi //; apply: axtab_okP. Qed.

Lemma tabi_ok_invi a : tabi_ok flast a -> tabi_ok flast (inv_tabi flast a).
Proof. exact: HEdge.tabi_ok_invi. Qed.

Lemma ti2t_view a i : tabi_ok flast a -> (i < nax)%N ->
  ti2t flast (view i a) = conjt (axtab i) (ti2t flast a).
Proof.
move=> aok iL; have sok := axi_ok iL.
rewrite /view /conjt !(ti2t_comp n47_small n47_len) ?tabi_ok_invi //;
  last by apply: (tabi_ok_comp n47_small n47_len).
by rewrite (ti2t_inv n47_small n47_len) // ti2t_axi.
Qed.

Lemma view_ok a i : tabi_ok flast a -> (i < nax)%N ->
  tabi_ok flast (view i a).
Proof.
by move=> aok iL; rewrite /tabi_ok ti2t_view //; apply: conjt_ok;
   [apply: axtab_okP | exact: aok].
Qed.

(* ---- a turn seen along an axis is that axis's turn ----------------------- *)

Lemma cmv_lt : all (fun i => all (fun m => (cmv i m < nq)%N) (iota 0 nq))
                   (iota 0 nax).
Proof. by vm_compute. Qed.

Lemma cmv_ltP i m : (i < nax)%N -> (m < nq)%N -> (cmv i m < nq)%N.
Proof.
move=> iL mL.
by apply: (allP (allP cmv_lt _ (mem_iota0 iL))); apply: mem_iota0.
Qed.

Lemma view_step a i m : tabi_ok flast a -> (i < nax)%N -> (m < nq)%N ->
  ti2t flast (view i (comp_tabi flast a (mvq m)))
    = ti2t flast (comp_tabi flast (view i a) (mvq (cmv i m))).
Proof.
move=> aok iL mL.
have sok := axtab_okP iL.
have cL := cmv_ltP iL mL.
have qok := tabi_ok_mvq mL; have qok' := tabi_ok_mvq cL.
have vok := view_ok aok iL.
rewrite ti2t_view ?(tabi_ok_comp n47_small n47_len) //.
rewrite (ti2t_comp n47_small n47_len aok qok).
rewrite (ti2t_comp n47_small n47_len vok qok').
rewrite (eqP (allP ti2t_mvq _ (mem_iota0 mL))).
rewrite (conjt_hom sok aok (mvt_ok mL)).
rewrite ti2t_view // (eqP (allP ti2t_mvq _ (mem_iota0 cL))).
by rewrite (eqP (allP (allP axtab_cmv _ (mem_iota0 iL)) _ (mem_iota0 mL))).
Qed.

(* ---- equal tables, equal triples ----------------------------------------- *)

(* Every coordinate reads the position through getn, and getn reads one       *)
(* facelet of the inverse, so two positions with the same table have the same *)
(* triple.  It is what lets a view be replaced by anything equal to it.       *)
Lemma getn_eq a b f : tabi_ok flast a -> tabi_ok flast b ->
  ti2t flast a = ti2t flast b -> (f < nfacelet)%N ->
  getn (inv_tabi flast a) f = getn (inv_tabi flast b) f.
Proof.
move=> aok bok he fL.
have hi : ti2t flast (inv_tabi flast a) = ti2t flast (inv_tabi flast b).
  rewrite (ti2t_inv n47_small n47_len aok).
  by rewrite (ti2t_inv n47_small n47_len bok) he.
have fL' : (f < flast.+1)%N by [].
by rewrite /getn -!(nth_ti2t (n := flast) _ fL') hi.
Qed.

Lemma htriple_eq a b : tabi_ok flast a -> tabi_ok flast b ->
  ti2t flast a = ti2t flast b -> htriple a = htriple b.
Proof.
move=> aok bok he.
have hg := getn_eq aok bok he.
have hpl : forall j, (j < nedge)%N ->
    eplace (inv_tabi flast a) j = eplace (inv_tabi flast b) j.
  move=> j jL; rewrite /eplace hg //.
  by have /andP[h _] := allP eprim_lt48 _ (mem_iota0 jL).
have hfl : forall j, (j < nedge)%N ->
    eflipn (inv_tabi flast a) j = eflipn (inv_tabi flast b) j.
  move=> j jL; rewrite /eflipn hg //.
  by have /andP[h _] := allP eprim_lt48 _ (mem_iota0 jL).
have hsl : forall i, eslot (inv_tabi flast a) i = eslot (inv_tabi flast b) i.
  move=> i; rewrite /eslot; apply: eq_in_foldl => y z.
  rewrite mem_iota add0n => /andP[_ yL].
  by rewrite (hpl _ yL) (hfl _ yL).
have rL : all (fun j => (rplace j < ncorn)%N) (iota 0 ncorn) by vm_compute.
have hcf : forall j, (j < ncorn)%N ->
    getn (inv_tabi flast a) (nth 0%N cprim (rplace j))
      = getn (inv_tabi flast b) (nth 0%N cprim (rplace j)).
  move=> j jL; apply: hg.
  have jrL : (rplace j < ncorn)%N by apply: (allP rL); apply: mem_iota0.
  by have h := allP cprim_lt48 _ (mem_iota0 jrL).
have hde : edat (inv_tabi flast a) = edat (inv_tabi flast b).
  by rewrite /edat; apply/eq_in_map => i _; rewrite hsl.
have hdc : cldat (inv_tabi flast a) = cldat (inv_tabi flast b).
  rewrite /cldat; apply/eq_in_map => j.
  rewrite mem_iota add0n => /andP[_ jL].
  by rewrite /cplace (hcf _ jL).
have hdt : ctdat (inv_tabi flast a) = ctdat (inv_tabi flast b).
  rewrite /ctdat; apply/eq_in_map => j.
  rewrite mem_iota add0n => /andP[_ jL].
  have jL8 : (j < ncorn)%N by apply: leq_trans jL _.
  by rewrite /ctwist (hcf _ jL8).
by rewrite /htriple !ecoordiE !clcoordiE !ctcoordiE hde hdc hdt.
Qed.

(* the same for the twist invariant, which is read off the same facelets      *)
Lemma ctsum_eq a b : tabi_ok flast a -> tabi_ok flast b ->
  ti2t flast a = ti2t flast b ->
  ctsum (inv_tabi flast a) = ctsum (inv_tabi flast b).
Proof.
move=> aok bok he.
have hg := getn_eq aok bok he.
have rL : all (fun j => (rplace j < ncorn)%N) (iota 0 ncorn) by vm_compute.
have hcf : forall j, (j < ncorn)%N ->
    getn (inv_tabi flast a) (nth 0%N cprim (rplace j))
      = getn (inv_tabi flast b) (nth 0%N cprim (rplace j)).
  move=> j jL; apply: hg.
  have jrL : (rplace j < ncorn)%N by apply: (allP rL); apply: mem_iota0.
  by have h := allP cprim_lt48 _ (mem_iota0 jrL).
have hm : [seq ctwist (inv_tabi flast a) j | j <- iota 0 ncorn]
        = [seq ctwist (inv_tabi flast b) j | j <- iota 0 ncorn].
  apply/eq_in_map => j; rewrite mem_iota add0n => /andP[_ jL].
  by rewrite /ctwist (hcf _ jL).
by apply: (f_equal (fun l : seq nat => (sumn l %% nslot == 0)%N)) hm.
Qed.

(* ---- pok and stt --------------------------------------------------------- *)

Section Pok.

Variable mt_e mt_cl mt_ct : arr.

(* what the coordinates need of a position seen along one axis                *)
Definition pokv (a : arr) : bool :=
  [&& cubt (ti2t flast a), cubct (ti2t flast a) & ctsum (inv_tabi flast a)].

Definition pok (a : arr) : bool :=
  tabi_ok flast a && all (fun i => pokv (view i a)) (iota 0 nax).

Definition stt (a : arr) : hst :=
  (htriple (view 0 a), htriple (view 1 a), htriple (view 2 a)).

Lemma pokvP a i : pok a -> (i < nax)%N -> pokv (view i a).
Proof. by move=> /andP[_ /allP h] iL; apply: h; apply: mem_iota0. Qed.

Lemma pok_okP a : pok a -> tabi_ok flast a.
Proof. by move=> /andP[]. Qed.

(* THE FIRST HYPOTHESIS.  A turn keeps every guard, along every axis, and     *)
(* that is the three step lemmas read through view_step.                      *)
Lemma pok_step a m : pok a -> (m < nq)%N -> pok (comp_tabi flast a (mvq m)).
Proof.
move=> pa mL; have aok := pok_okP pa.
have qok := tabi_ok_mvq mL.
have a'ok := tabi_ok_comp n47_small n47_len aok qok.
apply/andP; split; first by exact: a'ok.
apply/allP => i; rewrite mem_iota add0n => /andP[_ iL].
have /and3P[hc hcc hct] := pokvP pa iL.
have vok := view_ok aok iL.
have cL := cmv_ltP iL mL.
have cok := tabi_ok_comp n47_small n47_len vok (tabi_ok_mvq cL).
have v'ok := view_ok a'ok iL.
have hv := view_step aok iL mL.
have h1 : cubt (ti2t flast (view i (comp_tabi flast a (mvq m)))).
  by rewrite hv; apply: cubt_step.
have h2 : cubct (ti2t flast (view i (comp_tabi flast a (mvq m)))).
  by rewrite hv; apply: cubct_step.
have h3 : ctsum (inv_tabi flast (view i (comp_tabi flast a (mvq m)))).
  by rewrite (ctsum_eq v'ok cok hv); apply: ctsum_step.
by rewrite /pokv h1 h2 h3.
Qed.

(* ---- the sweeps are what the triples step by ----------------------------- *)

Hypothesis Hse : sweep_e mt_e.
Hypothesis Hscl : sweep_cl mt_cl.
Hypothesis Hsct : sweep_ct mt_ct.

(* THE SECOND HYPOTHESIS, and where obligation C is spent: along each axis    *)
(* the turn is that axis's turn, and the triple steps by the tables.          *)
Lemma stt_step a m : pok a -> (m < nq)%N ->
  stt (comp_tabi flast a (mvq m)) =
    (stepa mt_e mt_cl mt_ct (stt a).1.1 (of_nat (cmv 0 m)),
     stepa mt_e mt_cl mt_ct (stt a).1.2 (of_nat (cmv 1 m)),
     stepa mt_e mt_cl mt_ct (stt a).2 (of_nat (cmv 2 m))).
Proof.
move=> pa mL; have aok := pok_okP pa.
have qok := tabi_ok_mvq mL.
have a'ok := tabi_ok_comp n47_small n47_len aok qok.
have key : forall i, (i < nax)%N ->
    htriple (view i (comp_tabi flast a (mvq m)))
      = stepa mt_e mt_cl mt_ct (htriple (view i a)) (of_nat (cmv i m)).
  move=> i iL.
  have /and3P[hc hcc hct] := pokvP pa iL.
  have vok := view_ok aok iL.
  have cL := cmv_ltP iL mL.
  have cok := tabi_ok_comp n47_small n47_len vok (tabi_ok_mvq cL).
  have v'ok := view_ok a'ok iL.
  have hv := view_step aok iL mL.
  rewrite (htriple_eq v'ok cok hv).
  by apply: (sweeps_agree Hse Hscl Hsct).
by rewrite /stt (key 0%N isT) (key 1%N isT) (key 2%N isT).
Qed.

(* ---- and the solved position is recognised ------------------------------- *)

Lemma idi_ok : tabi_ok flast idi.
Proof.
by rewrite /idi /tabi_ok (ti2t_id n47_small n47_len); apply: tab_ok_id.
Qed.

Lemma ti2t_idi : ti2t flast idi = id_tab flast.
Proof. by rewrite /idi (ti2t_id n47_small n47_len). Qed.

(* THE THIRD HYPOTHESIS.  Every axis sees the solved cube as the solved cube, *)
(* because a rotation conjugates the identity to itself.                      *)
Lemma stt_sol a : pok a -> eq_tabi flast a idi -> hsolved (stt a).
Proof.
move=> pa he; have aok := pok_okP pa.
have hti : ti2t flast a = ti2t flast idi.
  by apply/eqP; rewrite -(eq_tabiE n47_small aok idi_ok).
have hid : forall i, (i < nax)%N -> htriple (view i a) = htriple idi.
  move=> i iL; apply: (htriple_eq (view_ok aok iL) idi_ok).
  rewrite ti2t_view // hti ti2t_idi.
  by apply: conjt_id1; apply: axtab_okP.
by rewrite /stt (hid 0%N isT) (hid 1%N isT) (hid 2%N isT); vm_compute.
Qed.

(* ---- the root ------------------------------------------------------------ *)

(* THE STATE THE RUN STARTS FROM IS THE STATE OF THE POSITION.  hstate is     *)
(* built by replaying a relabelled word from the identity, and stt reads the  *)
(* position itself along the three views; that these are the same is one      *)
(* computation, three axes by six positions.                                  *)
Lemma view_rooti :
  all (fun i => all (fun k => eq_tabi flast (view i (rooti k)) (rooti_ax i k))
      (iota 0 npfx)) (iota 0 nax).
Proof. by vm_compute. Qed.

Lemma rooti_ok : all (fun k => tabi_ok flast (rooti k)) (iota 0 npfx).
Proof. by vm_compute. Qed.

Lemma rooti_ax_ok :
  all (fun i => all (fun k => tabi_ok flast (rooti_ax i k)) (iota 0 npfx))
      (iota 0 nax).
Proof. by vm_compute. Qed.

(* the guards hold where the run starts, twist invariant and all              *)
Lemma pok_rooti : all (fun k => pok (rooti k)) (iota 0 npfx).
Proof. by vm_compute. Qed.

Lemma stt_rooti k : (k < npfx)%N -> stt (rooti k) = hstate k.
Proof.
move=> kL.
have hk : forall i, (i < nax)%N ->
    htriple (view i (rooti k)) = htriple (rooti_ax i k).
  move=> i iL.
  have h1 := allP (allP view_rooti _ (mem_iota0 iL)) _ (mem_iota0 kL).
  have o1 := view_ok (allP rooti_ok _ (mem_iota0 kL)) iL.
  have o2 := allP (allP rooti_ax_ok _ (mem_iota0 iL)) _ (mem_iota0 kL).
  apply: (htriple_eq o1 o2).
  by apply/eqP; rewrite -(eq_tabiE n47_small o1 o2).
by rewrite /stt /hstate (hk 0%N isT) (hk 1%N isT) (hk 2%N isT).
Qed.

End Pok.

(* ---- what is left -------------------------------------------------------- *)

(* Three of HRunS.hsearch_complete's four hypotheses are here, and so is the  *)
(* root of the run.  What is left: stt_cut, which is obligation D read        *)
(* through the coordinates -- HAdmis.h_cut over the sweep HSweep.admis -- and *)
(* the prefix, that playing a word on the state is stepping the state, which  *)
(* is an induction on the word off stt_step.                                  *)
