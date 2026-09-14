(* ---------------------------------------------------------------------------*)
(* Merge two magnitude-sorted sequences of floats into one, and its           *)
(* properties: it preserves format, size and exact sum, and (for [Merge] of   *)
(* the six triple-word limbs) yields a magnitude-sorted, pairwise-ulp         *)
(* separated sequence -- the two preconditions of paper Theorem 6.  Generic   *)
(* over [p]; built on [Nonoverlap].                                          *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Nonoverlap.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Merge.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.

Local Notation beta := radix2.

Open Scope R_scope.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Local Notation pow e := (bpow beta e).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).
Local Notation format_lt_ulp_le := (@format_lt_ulp_le p Hp2).
Local Notation guarded_ulp_le := (guarded_ulp_le Hp2).
Local Notation guarded_ulp_abs_le := (@guarded_ulp_abs_le p).
Local Notation guarded_ulp_trans := (guarded_ulp_trans Hp2).
Local Notation Pnonoverlap_imp_pairwise_ul :=
  (Pnonoverlap_imp_pairwise_ul Hp2).

(* ===========================================================================*)
(*  Merge two magnitude-sorted sequences into a magnitude-sorted one.         *)
(* ===========================================================================*)

Fixpoint Merge (l1 : seq R) : seq R -> seq R :=
  fix Merge_aux (l2 : seq R) : seq R :=
    match l1, l2 with
    | [::], _ => l2
    | _, [::] => l1
    | a1 :: l1', a2 :: l2' =>
        if Rle_bool (Rabs a2) (Rabs a1)
        then a1 :: Merge l1' l2
        else a2 :: Merge_aux l2'
    end.

(* ---- controlled unfolding ------------------------------------------------ *)
(* [Merge] is a nested fixpoint, so a bare [/=] exposes the inner             *)
(* [Merge_aux] and makes every goal unreadable.  These three equations are    *)
(* the ONLY way the definition should be unfolded: rewrite with them instead  *)
(* of simplifying, and [Merge] stays folded in the goal.                      *)
Lemma Merge_nil l : Merge [::] l = l.
Proof. by case: l. Qed.

Lemma Merge_nil_r l : Merge l [::] = l.
Proof. by case: l. Qed.

Lemma Merge_cons a1 l1 a2 l2 :
  Merge (a1 :: l1) (a2 :: l2) =
    if Rle_bool (Rabs a2) (Rabs a1)
    then a1 :: Merge l1 (a2 :: l2)
    else a2 :: Merge (a1 :: l1) l2.
Proof. by []. Qed.

Lemma format_Merge l1 l2 :
  {in l1, forall z, format z} -> {in l2, forall z, format z} -> 
  {in Merge l1 l2, forall z, format z}.
Proof.
elim: l1 l2 => /= [|a l1 IH l2 al1F]; first by elim.
have aF : format a by apply: al1F; rewrite !inE eqxx.
set u := (X in _ -> {in X l2, _}).
elim: l2 IH => /= [IH _ z| b l2 IH1 IH2 bl2F].
  rewrite inE => /orP[/eqP->|zIl1] //.
  by apply: al1F; rewrite inE zIl1 orbT.
case: Rle_bool => z; rewrite inE => /orP[/eqP->|zIl] //.
- apply: (IH2 (b :: l2)) => // z1 z1Il1.
  by apply: al1F; rewrite inE z1Il1 orbT.
- by apply: bl2F; rewrite inE eqxx.
apply: IH1 => // z1 z1Il2.
by apply: bl2F; rewrite inE z1Il2 orbT.
Qed.

Lemma size_Merge l1 l2 : size (Merge l1 l2) = (size l1 + size l2)%N.
Proof.
elim: l1 l2 => /= [|a1 l1 IH1]; first by elim.
elim => [/=|a2 l2 IH2]; first by rewrite addn0.
case: Rle_bool => /=; first by rewrite IH1.
by rewrite IH2 addnS.
Qed.

(* ===========================================================================*)
(*  Triple-word numbers                                                       *)
(* ===========================================================================*)

(* ===========================================================================*)
(*  Merge lemmas (beyond [format_Merge] above): a common magnitude bound, and *)
(*  the two preconditions of Theorem 6 -- magnitude order and pairwise ulp.   *)
(* ===========================================================================*)

(* Merge under a common dominating head [a]: if [a] tops both lists, it still *)
(* tops the merge, and the merge stays magnitude-sorted.  (Helper for         *)
(* [Merge_sorted_mag].)                                                       *)
Lemma Merge_asorted_mag a l1 l2 :
  sorted_mag (a :: l1) -> sorted_mag (a :: l2) -> sorted_mag (a :: Merge l1 l2).
Proof.
elim: l1 l2 a => /= [|a1 l1 IH1]; first by elim.
elim => // a2 l2 IH2 a a1l1S a2l2S.
case: Rle_bool_spec => [a2La1|a1La2].
  apply: sorted_mag_cons_inv.
    by case: (sorted_mag_cons a1l1S).
  apply: IH1; first by case: (sorted_mag_cons a1l1S).
  apply: sorted_mag_cons_inv => //.
  by case: (sorted_mag_cons a2l2S).
apply: sorted_mag_cons_inv => //.
  by case: (sorted_mag_cons a2l2S).
apply: IH2.
  apply: sorted_mag_cons_inv; first by apply: Rlt_le.
  by case: (sorted_mag_cons a1l1S).
by case: (sorted_mag_cons a2l2S).
Qed.

(* [Merge] picks the larger-magnitude head at each step, so it turns two      *)
(* magnitude-sorted sequences into a magnitude-sorted one.  Combined with     *)
(* [isTW_sorted_mag] on each input triple, this discharges [Hz_sorted] in     *)
(* [TWSum_isTW].                                                              *)
Lemma Merge_sorted_mag l1 l2 :
  sorted_mag l1 -> sorted_mag l2 -> sorted_mag (Merge l1 l2).
Proof.
elim: l1 l2 => /= [|a l1 IH1]; first by elim.
elim => // b l2 IH2 al1S bl2S.
case: Rle_bool_spec => [bLa|aLb].
  apply: Merge_asorted_mag => //.
  by apply: sorted_mag_cons_inv.
move : bl2S.
have: sorted_mag (b :: l1).
  case: (l1) al1S => // a3 l3 H.
  case: (sorted_mag_cons H) => H1 H2.
  by apply: sorted_mag_cons_inv => //; lra.
elim: (l2) (b) aLb => 
    /= [b1 aLb1 b1l1S _|b3 l3 IH3 b4 aLb4 b4l1S /sorted_mag_cons[b4Lb3 b3l3S]].
  by apply: sorted_mag_cons_inv => //; lra.
case: Rle_bool_spec => [b3La|aLb3].
  apply: sorted_mag_cons_inv; first by lra.
  apply: Merge_asorted_mag => //.
  by apply: sorted_mag_cons_inv.
apply: sorted_mag_cons_inv => //.
apply: IH3 => //.
by apply: sorted_mag_le al1S _; lra.
Qed.

(* The main Merge result for Theorem 6: merging two P-nonoverlapping (format) *)
(* lists yields a [pairwise_ulp] sequence.  The merge's own magnitude tests   *)
(* supply the ordering, so no [sorted_mag] hypothesis is needed -- among any  *)
(* three consecutive outputs, two come from the same input list and are       *)
(* consecutive there, giving the [Pnonoverlap] step; the mixed cases use the  *)
(* merge's comparison plus ulp monotonicity ([ulp_le]).                       *)
Lemma Merge_pairwise_ulp (l1 l2 : seq R) :
  {in l1, forall z, format z} ->   {in l2, forall z, format z} ->
  Pnonoverlap l1 -> Pnonoverlap l2 -> pairwise_ulp (Merge l1 l2).
Proof.
elim: l1 l2 => /= [|a l1 IH1].
  elim => // b [|c [|d l2]] IH _ bl2F _ bl2P //.
  apply: pairwise_ulp_cons_inv.
    have /= cLub := bl2P 0%N isT.
    have /= dLuc := bl2P 1%N isT.
    apply: (guarded_ulp_trans _ dLuc cLub).
    by apply: bl2F; rewrite !inE eqxx !orbT.
  apply: IH => //.
    by move=> z zIl; apply: bl2F; rewrite inE zIl orbT.
  by apply: Pnonoverlap_cons bl2P.
elim => [al1F _ al1P _|b l2 IH2 al1F bl2F al1P bl2P].
  by apply: Pnonoverlap_imp_pairwise_ul.
case: Rle_bool_spec => [bLa|aLb].
  apply: pairwise_ulp_cons1_inv.
    apply: IH1 => //.
      by move=> z zIl; apply: al1F; rewrite inE zIl orbT.
    by apply: Pnonoverlap_cons al1P.
  case: (l1) al1P al1F => //.
    case: (l2) bl2P bl2F => //= c l3 /(_ 0%N isT) /= cLub _ _ _ _.
    by apply: guarded_ulp_le cLub bLa.
  move=> a1 l3.
  rewrite /=; case: Rle_bool_spec => /=.
    case: l3 => //=.
      move=> bLa1 /(_ 0%N isT) /= a1Lua _ _.
      by apply: guarded_ulp_abs_le bLa1 a1Lua.
    move=> a2 l3 bLa1 aa1a2l3P aa1a2l3F _.
    case: Rle_bool_spec => [bLa2|a2Lb] /=.
      have /(_ 0%N isT)/= a1Lua :=  aa1a2l3P.
      have /(_ 1%N isT)/= a2Lua1 :=  aa1a2l3P.
      apply: (guarded_ulp_trans _ a2Lua1 a1Lua).
      by apply: aa1a2l3F; rewrite !inE eqxx !orbT.
    have /(_ 0%N isT)/= a1Lua :=  aa1a2l3P.
    by apply: guarded_ulp_abs_le bLa1 a1Lua.
  move=> a1Lb aa1l3P aa1l3F.
  case: (l2) bl2F bl2P => /= [_ _ _|b1 l4 bb1F bb1P _] /=.
    by apply: (aa1l3P 0%N).
  case: Rle_bool_spec => [b1La1|a1Lb1] /=.
    by apply: (aa1l3P 0%N).
  have /(_ 0%N isT)/= b1Lub :=  bb1P.
  by apply: guarded_ulp_le b1Lub bLa.
apply: pairwise_ulp_cons1_inv.
  apply: IH2 => //.
    by move=> z zIl; apply: bl2F; rewrite inE zIl orbT.
  by apply: Pnonoverlap_cons bl2P.
case: (l2) bl2F bl2P al1F al1P => /=.
  case: (l1) => // a1 l3 bF bP aa1l3F aa1l3P /= _.
  have /(_ 0%N isT)/= a1Lua :=  aa1l3P.
  by apply: guarded_ulp_le a1Lua (Rlt_le _ _ aLb).
move=> b1 l3.
case: Rle_bool_spec => [b1La|aLb1] /=.
  case: (l1) => //= [_ /(_ 0%N isT) //|a1 l4].
  case: Rle_bool_spec => [b1La1|a1Lb1]//=.
    move=> bb1l3F bb1l3P aa1l4F aa1l4P _.
    have /(_ 0%N isT)/= a1Lua :=  aa1l4P.
    by apply: guarded_ulp_le a1Lua (Rlt_le _ _ aLb).
  case: l3 => /= [bb1F bb1P aa1l4F aa1l4P _|
                  b2 l3 bb1b2l3F bb1b2l3P aa1l4F aa1l4P _].
    by apply: (bb1P 0%N).
  by apply: (bb1b2l3P 0%N).
case: l3 => /= [bb1F bb1P al1F al1P _|b2 l3 bb1b2l3F bb1b2l3P al1F al1P _].
  by apply: guarded_ulp_abs_le (Rlt_le _ _ aLb1) (bb1P 0%N isT).
case: Rle_bool_spec => [b2La|aLb2]//=.
  by apply: guarded_ulp_abs_le (Rlt_le _ _ aLb1) (bb1b2l3P 0%N isT).
have /(_ 1%N isT)/= b2Lub1 := bb1b2l3P.
have /(_ 0%N isT)/= b1Lub := bb1b2l3P.
apply: (guarded_ulp_trans _ b2Lub1 b1Lub).
by apply: bb1b2l3F; rewrite !inE eqxx !orbT.
Qed.

(* Merge is a permutation of its two inputs, so it preserves the exact sum.   *)
Lemma Merge_sumR (l1 l2 : seq R) : sumR (Merge l1 l2) = sumR l1 + sumR l2.
 Proof.
elim: l1 l2 => /= [|a l1 IH1]; first by elim => [/=| b l2] //; lra.
elim =>  [/=|b l2 IH2]; first by lra.
case: Rle_bool_spec => [bLa|aLb].
  by rewrite /= IH1 /=; lra.
by rewrite /= IH2; lra.
Qed.

End Merge.
