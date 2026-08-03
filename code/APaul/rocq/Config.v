(******************************************************************************)
(*                                                                            *)
(*   Reducing a two-length configuration by a given number of copies          *)
(*                                                                            *)
(*   [Alg2.step] always takes the Euclidean quotient.  Algorithm 1 (Alg1.v)   *)
(*    takes the quotient on one side of a turn and a single copy on the       *)
(*    other, so it walks through configurations [Alg2.step] skips.  The       *)
(*    operation is the same one in both cases:                                *)
(*                                                                            *)
(*      reduce [q]:  q -= k*p, u += k*v                                       *)
(*      reduce [p]:  p -= k*q, v += k*u                                       *)
(*                                                                            *)
(*   Alg2.v proves what this does to the configuration only at [k] maximal.   *)
(*    Here it is proved for any [k] up to the quotient, which is what         *)
(*    Algorithm 1 needs; Alg2's statements come back by taking [k] to be      *)
(*    the quotient.  Folding Alg2.v onto these is the plumbing still to do.   *)
(*                                                                            *)
(*   Nothing below mentions [d].  That is the one thing the two algorithms    *)
(*    do not share: [Alg2.invd] against [Alg1.invw].  The configuration and   *)
(*    its reduction they share entirely.                                      *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist Alg2.

Section Reduce.

(*  The same setting as Alg2.v's [Section Theory], so that its lemmas read    *)
(*    here as they are stated there.                                          *)

Variable M : nat.
Hypothesis M_gt0 : 0 < M.

Variables A B : nat.
Hypothesis ltn_A : A < M.
Hypothesis ltn_B : B < M.

Variable N : nat.
Local Notation g := (gcdn A M).

Hypothesis N_gt0 : 0 < N.
Hypothesis N_lt_Mg : N < M %/ g.

Local Notation pt := (pt M A).
Local Notation dst := (dst M A B).
Local Notation inf := (inf_dst M A B).

Local Notation inv := (inv M A).
Local Notation invx := (invx M A B).

(*  The vocabulary of Dist.v, with this section's parameters supplied, so    *)
(*  that the lemmas read here exactly as they are stated there.              *)
Local Notation ltn_pt := (ltn_pt M_gt0 A).
Local Notation pt0 := (pt0 M A).
Local Notation ptDE := (ptDE M A).
Local Notation ptB := (ptB M_gt0).
Local Notation ptBu := (ptBu M_gt0).
Local Notation ptM := (ptM M A).
Local Notation ptS := (ptS ltn_A).
Local Notation ptWE := (ptWE M A).
Local Notation leq_N_Mg := (leq_N_Mg N_lt_Mg).
Local Notation coprime_Mg_Ag := (coprime_Mg_Ag M_gt0 A).
Local Notation pt_neq0 := (pt_neq0 M_gt0 N_lt_Mg).
Local Notation pt_neq0M := (pt_neq0M M_gt0).
Local Notation ptD_leq := (ptD_leq M_gt0 N_lt_Mg).
Local Notation ptWv := (ptWv M_gt0 N_lt_Mg).
Local Notation dvdn_g_pt := (dvdn_g_pt M A).
Local Notation ltn_dst := (ltn_dst M_gt0 A B).
Local Notation dst0 := (dst0 A ltn_B).
Local Notation dstE := (dstE M A B).
Local Notation dstD := (dstD M_gt0).
Local Notation dst_below := (dst_below ltn_B).
Local Notation dst_above := (dst_above M_gt0).
Local Notation dstBE := (dstBE M_gt0 A B).
Local Notation dstDE := (dstDE M_gt0 A B).
Local Notation dst_diff := (dst_diff M_gt0 A B).
Local Notation dst_mod_g := (dst_mod_g M_gt0 A B).
Local Notation dst_ofD := (dst_ofD ltn_B).
Local Notation leq_mod_dst := (leq_mod_dst M_gt0 ltn_B).
Local Notation inf0 := (inf0 M A B).
Local Notation infSE := (infSE M A B).
Local Notation leq_inf_dst := (leq_inf_dst M A B).
Local Notation inf_ex := (inf_ex M_gt0 A B).
Local Notation leq_inf_mono := (leq_inf_mono M A B).
Local Notation dst_max_ex := (dst_max_ex M A B).


(*  and the lemmas of Alg2.v this file builds on, likewise.                  *)
Local Notation inv_qM := (@inv_qM M A).
Local Notation inv_qltM := (@inv_qltM M M_gt0 A N N_lt_Mg).
Local Notation gap_decomp := (@gap_decomp M M_gt0 A B).

Local Notation step_pt_one_lt := (@step_pt_one_lt M A B ltn_B).
Local Notation step_pt_one_ge := (@step_pt_one_ge M M_gt0 A B ltn_B).

Local Notation walk_lt_nowrap := (@walk_lt_nowrap M M_gt0 A B).
Local Notation walk_lt_wrap_ge := (@walk_lt_wrap_ge M M_gt0 A B).
Local Notation dst_sub_u := (dst_sub_u M_gt0).
Local Notation pt_add_u := (pt_add_u M_gt0).

(******************************************************************************)
(* Reducing [q] by [k] copies of [p]                                          *)
(******************************************************************************)

(*  [p] is still a point and [q - k*p] still a co-point.  This is             *)
(*    [Alg2.step_pt]'s first branch, whose proof is already an induction on   *)
(*    [j <= q %/ p]: only the instantiation at the end was special.           *)
Lemma red_lt_pt p q d u v k :
  inv p q d u v -> p < q -> k <= q %/ p -> 0 < q - k * p ->
  (p = pt v) /\ (q - k * p = M - pt (u + k * v)).
Proof.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 pLq kLq q'_gt0.
rewrite subn_gt0 in q'_gt0.
move: k kLq q'_gt0; elim => [_ _|j IH jLq q'_gt0];
    first by rewrite subn0 addn0.
have jLq' : j <= q %/ p by apply: ltnW.
have jpq : j * p < q.
  by rewrite (leq_ltn_trans _ q'_gt0) // leq_mul2r ltnW ?orbT.
have -> : q - j.+1 * p = q - j * p - p by rewrite mulSnr subnDA.
have -> : u + j.+1 * v = u + j * v + v by rewrite mulSnr addnA.
apply: step_pt_one_lt; last by rewrite ltn_subRL -mulSnr.
split => //.
- by rewrite subn_gt0.
- rewrite mulnDl mulnBr -addnA.
  rewrite mulnCA -mulnA [X in _ + X]addnC subnK //.
  by rewrite mulnCA leq_mul2l ltnW ?orbT.
- by case: (IH jLq' jpq).
- by rewrite -gE -{2}(subnKC (ltnW jpq)) gcdnMDl.
by rewrite addn_gt0 u_gt0.
Qed.

(*  The counts still tile the circle: [k] gaps of length [p] replace each     *)
(*    gap of length [q] that was split.                                       *)
Lemma red_lt_bez p q d u v k :
  inv p q d u v -> k * p <= q -> (u + k * v) * p + v * (q - k * p) = M.
Proof.
case => _ _ upvqE _ _ _ _ _ kpq.
rewrite mulnDl mulnBr addnBA; last by rewrite leq_mul2l kpq orbT.
by rewrite mulnCA mulnA addnAC addnK.
Qed.

(*  [inv] survives the reduction, for any [k] the larger gap can spare.       *)
Lemma inv_red_lt p q d u v k :
  inv p q d u v -> p < q -> k <= q %/ p -> 0 < q - k * p ->
  inv p (q - k * p) d (u + k * v) v.
Proof.
move=> iv pLq kLq q'_gt0.
have [p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0] := iv.
have kpq : k * p <= q by rewrite -leq_divRL.
have [pE' qE'] := red_lt_pt iv pLq kLq q'_gt0.
split => //; first by apply: (red_lt_bez iv kpq).
  by rewrite -gE -{2}(subnKC kpq) gcdnMDl.
by rewrite addn_gt0 u_gt0.
Qed.

(*  [ptD_leq] with the orbit bound in place of [N].  Its [<= N] is there      *)
(*    only to feed [pt_neq0], whose real content is [pt_neq0M] with           *)
(*    [n < M %/ g] -- and [Alg2.inv_uv_le] hands that bound to every state    *)
(*    satisfying [inv].  That is why nothing on the [p] side below needs a    *)
(*    range hypothesis.                                                       *)
Lemma ptD_leqM x y :
  0 < x + y < M %/ g -> pt x + pt y <= M -> pt (x + y) = pt x + pt y.
Proof.
move=> xyM; case: ltngtP => // [pxpyLM|pxpyE] _; first exact: ptD.
by have := pt_neq0M xyM; rewrite ptDE pxpyE modnn eqxx.
Qed.

(*  A new index is an old one walked up by [j <= k] copies of [v], and the    *)
(*    walk adds [j*p].  [Alg2.pt_new_lt] with the quotient replaced by [k].   *)
Lemma red_lt_new p q d u v m k :
  inv p q d u v -> (forall i, i < u + v -> pt i <= M - q) ->
  p < q -> k <= q %/ p -> u + k * v + v < N ->
  u + v <= m -> m < u + k * v + v ->
  exists2 j, 0 < j <= k &
    (m - j * v < u + v) /\ pt m = pt (m - j * v) + j * p.
Proof.
move=> iv Hmax pLq kLq uvN' mnew mLuv'.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M := inv_qM iv.
have uLN : u <= N.
  by rewrite (leq_trans _ (ltnW uvN')) // (leq_trans (leq_addr (k * v) u))
    // leq_addr.
have qltM : q < M := inv_qltM iv uLN.
have [j jk /andP[ylt jvm]] := new_index_decomp v_gt0 mnew mLuv'.
have /andP[j_gt0 jk2] := jk.
have jpq : j * p <= q by rewrite -leq_divRL // (leq_trans jk2).
have m_gt0 : 0 < m by rewrite (leq_trans _ mnew) // addn_gt0 u_gt0.
have mLN : m <= N by rewrite ltnW // (ltn_trans mLuv').
have mN : 0 < m <= N by rewrite m_gt0 mLN.
have HP : pt (m - j * v) + j * p <= M := leq_ptW (Hmax _ ylt) qM jpq.
have Hjv : pt (j * v) = j * p.
  have H1 : pt (j * v) = (j * pt v) %% M by rewrite /pt modnMmr mulnCA.
  by rewrite H1 -pE modn_small // (leq_ltn_trans jpq).
have Hne : pt (m - j * v) + j * p < M.
  rewrite ltn_neqAle HP andbT; apply/eqP => He.
  by have := pt_neq0 mN; rewrite -{1}(subnK jvm) ptDE Hjv He modnn eqxx.
exists j => //; split => //.
by rewrite -{1}(subnK jvm) pE ptWD // -pE // (leq_ltn_trans jpq).
Qed.

(*  The four [invx] fields that do not mention [inf], at a general [k].       *)
(*    [Alg2.invx_step_lt_min] and friends, with the quotient replaced.        *)
Lemma invx_red_lt_min p q d u v k :
  inv p q d u v -> (forall m, 0 < m < u + v -> p <= pt m) ->
  (forall m, m < u + v -> pt m <= M - q) ->
  p < q -> k <= q %/ p -> u + k * v + v < N ->
  forall m, 0 < m < u + k * v + v -> p <= pt m.
Proof.
move=> iv Hmin Hmax pLq kLq uvN' m /andP[m_gt0 mLuv'].
have [_ _ _ _ _ _ u_gt0 v_gt0] := iv.
have [mold|mnew] := ltnP m (u + v); first by apply: Hmin; rewrite m_gt0.
have [j /andP[j_gt0 jk] [ylt Hm]] :=
  red_lt_new iv Hmax pLq kLq uvN' mnew mLuv'.
rewrite Hm (leq_trans _ (leq_addl _ _)) //.
by rewrite -{1}[p]mul1n leq_mul2r j_gt0 orbT.
Qed.

Lemma invx_red_lt_max p q d u v k :
  inv p q d u v -> (forall m, m < u + v -> pt m <= M - q) ->
  p < q -> k <= q %/ p -> u + k * v + v < N ->
  forall m, m < u + k * v + v -> pt m <= M - (q - k * p).
Proof.
move=> iv Hmax pLq kLq uvN' m mLuv'.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have kpq : k * p <= q by rewrite -leq_divRL.
have [mold|mnew] := ltnP m (u + v).
  by rewrite (leq_trans (Hmax _ mold)) // leq_sub2l // leq_subr.
have [j /andP[j_gt0 jk] [ylt Hm]] :=
  red_lt_new iv Hmax pLq kLq uvN' mnew mLuv'.
have jpk : j * p <= k * p by rewrite leq_mul2r jk orbT.
have -> : M - (q - k * p) = M - q + k * p.
  by rewrite subnBA // addnBAC // (inv_qM iv).
by rewrite Hm leq_add // (Hmax _ ylt).
Qed.

Lemma invx_red_lt_p1 p q d u v k :
  inv p q d u v -> (forall m, m < u + v -> pt m <= M - q) ->
  p < q -> k <= q %/ p -> u + k * v + v < N ->
  forall z, z < u + k * v -> pt (z + v) = pt z + p.
Proof.
move=> iv Hmax pLq kLq uvN' z zL.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M := inv_qM iv.
have zLN : z <= N by rewrite ltnW // (ltn_trans zL) //
                             (leq_ltn_trans _ uvN') // leq_addr.
have zvN : 0 < z + v <= N.
  rewrite addn_gt0 v_gt0 orbT /=.
  by rewrite ltnW // (leq_ltn_trans _ uvN') // leq_add2r ltnW.
rewrite pE; apply: ptD_leq => //; rewrite -pE.
have [zold|znew] := ltnP z (u + v).
  by apply: leq_trans (leq_add (Hmax _ zold) (ltnW pLq)) _; rewrite subnK.
have [j /andP[j_gt0 jk] /andP[ylt jvz]] := new_index_decomp_sharp v_gt0 znew zL.
have jp1 : j.+1 * p <= q by rewrite -leq_divRL // (leq_trans jk).
have jpq : j * p <= q by rewrite (leq_trans _ jp1) // leq_mul2r leqnSn orbT.
have z_gt0 : 0 < z by rewrite (leq_trans _ znew) // addn_gt0 u_gt0.
have Hz : pt z = pt (z - j * v) + j * p.
  rewrite -{1}(subnK jvz) (ptWv (Hmax _ ylt) qM) -?pE //.
  by rewrite subnK // z_gt0 zLN.
rewrite Hz -addnA -mulSnr.
by apply: leq_trans (leq_add (Hmax _ ylt) jp1) _; rewrite subnK.
Qed.

Lemma invx_red_lt_p2 p q d u v k :
  inv p q d u v -> p < q -> k <= q %/ p -> 0 < q - k * p ->
  forall z, u + k * v <= z < u + k * v + v ->
  pt (z - (u + k * v)) = (pt z + (q - k * p)) %% M.
Proof.
move=> iv pLq kLq q'_gt0 z /andP[uLz _].
by have [_ qE'] := red_lt_pt iv pLq kLq q'_gt0; apply: ptBu.
Qed.

(*  and the gap decomposition, which needs only [inv] and the two above.      *)
Lemma invx_red_lt_gap p q d u v k :
  inv p q d u v -> invx p q u v ->
  p < q -> k <= q %/ p -> 0 < q - k * p -> u + k * v + v < N ->
  forall y, y < u + k * v + v ->
  exists a b, [/\ a <= u + k * v, b <= v &
                  dst y = inf (u + k * v + v) + a * p + b * (q - k * p)].
Proof.
move=> iv ix pLq kLq q'_gt0 uvN' y yL.
have Hmin' := invx_red_lt_min iv (invx_min ix) (invx_max ix) pLq kLq uvN'.
have Hmax' := invx_red_lt_max iv (invx_max ix) pLq kLq uvN'.
by apply: gap_decomp (inv_red_lt iv pLq kLq q'_gt0) Hmin' Hmax' yL.
Qed.

(*  The [inf] drop.  Reducing by [k] copies walks the closest point down by   *)
(*    [k] gaps of length [p], but the walk stops when it would wrap: at most  *)
(*    [inf %/ p] copies fit under [inf].  Hence the [minn] below.  At         *)
(*    [k = q %/ p] this is [Alg2.inf_new_eq_lt], where the [minn] collapses   *)
(*    to [inf %/ p] and the difference to [inf %% p].                         *)
Lemma inf_red_lt_le p q d u v k :
  inv p q d u v -> p < q -> k <= q %/ p ->
  inf (u + k * v + v) <= inf (u + v) - minn k (inf (u + v) %/ p) * p.
Proof.
move=> iv pLq kLq.
have [p_gt0 q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y yLuv HyE] := inf_ex uv_gt0.
set m := minn k (inf (u + v) %/ p).
have mLk : m <= k := geq_minl _ _.
have mq : m <= q %/ p := leq_trans mLk kLq.
have mpI : m * p <= inf (u + v).
  by rewrite (leq_trans (_ : _ <= inf (u + v) %/ p * p)) ?leq_divM //
             leq_mul2r geq_minr orbT.
have [m0|m_gt0] := posnP m.
  rewrite m0 mul0n subn0; apply: leq_inf_mono.
  by rewrite -addnA leq_add2l leq_addl.
have Hm : 0 < m <= q %/ p by rewrite m_gt0.
have Hmp : m * p <= dst y by rewrite -HyE.
have Hw := walk_lt_nowrap iv pLq yLuv Hm Hmp.
rewrite -HyE in Hw.
rewrite -Hw; apply: leq_inf_dst.
have -> : u + k * v + v = u + v + k * v by rewrite -!addnA (addnC v).
by rewrite (leq_ltn_trans (leq_add (leqnn y) (_ : m * v <= k * v)))
            ?leq_mul2r ?mLk ?orbT // ltn_add2r.
Qed.

(*  The converse bound.  Old indices are free; a new one is an old one        *)
(*    walked up by [j <= k] gaps, and the walk either stays under [inf]       *)
(*    (then the gap decomposition absorbs it) or wraps.  Wrapping needs       *)
(*    [inf %/ p < k], which is exactly the branch of the [minn] where         *)
(*    [inf - m*p] is [inf %% p], and a wrapped walk lands above [p].          *)
Lemma inf_red_lt_ge p q d u v k :
  inv p q d u v -> invx p q u v -> p < q -> k <= q %/ p ->
  inf (u + v) - minn k (inf (u + v) %/ p) * p <= inf (u + k * v + v).
Proof.
move=> iv ix pLq kLq.
have [p_gt0 q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
set m := minn k (inf (u + v) %/ p).
apply: leq_inf.
  by rewrite (leq_trans (leq_subr _ _)) // ltnW //
             (leq_ltn_trans (leq_inf_dst uv_gt0)) // ltn_dst.
move=> x xL.
have [xold|xnew] := ltnP x (u + v).
  by rewrite (leq_trans (leq_subr _ _)) // leq_inf_dst.
have xL' : x < u + k.+1 * v by rewrite mulSn addnA addnAC.
have [j /andP[j_gt0 jLk] /andP[ylt jvx]] :=
     new_index_decomp_sharp v_gt0 xnew xL'.
rewrite ltnS in jLk.
have jk : 0 < j <= q %/ p by rewrite j_gt0 (leq_trans jLk).
have xE : x = x - j * v + j * v by rewrite subnK.
have [Hmp|Hmp] := leqP (j * p) (dst (x - j * v)).
  have jLq : j <= q %/ p := leq_trans jLk kLq.
  have jpq : j * p <= q by rewrite -leq_divRL.
  rewrite xE (walk_lt_nowrap iv pLq ylt jk Hmp).
  have [a [b [aLu bLv Hgap]]] := invx_gap ix ylt.
  have [b0|b_gt0] := posnP b; last first.
(* a [q] in the gap absorbs the whole walk: [j*p <= q]                        *)
    apply: leq_trans (_ : inf (u + v) <= _); first exact: leq_subr.
    rewrite leq_subRL // Hgap addnC -addnA leq_add2l (leq_trans jpq) //.
    exact: leq_trans (leq_pmull q b_gt0) (leq_addl _ _).
(* no [q]: the walk eats at most [a + m] gaps [p] out of [inf + a*p]          *)
  have jam : j - a <= m.
    rewrite /m leq_min (leq_trans (leq_subr _ _)) //= leq_divRL // mulnBl.
    by rewrite leq_subLR addnC (leq_trans Hmp) // Hgap b0 mul0n addn0.
  have -> : inf (u + v) - m * p = dst (x - j * v) - (a + m) * p.
    by rewrite Hgap b0 mul0n addn0 mulnDl subnDA addnK.
  by apply: leq_sub2l; rewrite leq_mul2r -leq_subLR jam orbT.
(* the wrap case.  It cannot happen on the [k] branch of the [minn]           *)
have [kI|Ik] := leqP k (inf (u + v) %/ p).
  have jpI : j * p <= inf (u + v) by rewrite -leq_divRL // (leq_trans jLk).
  by move: Hmp; rewrite ltnNge (leq_trans jpI) // leq_inf_dst.
have mE : m = inf (u + v) %/ p by rewrite /m; apply/minn_idPr; apply: ltnW.
rewrite mE {1}(divn_eq (inf (u + v)) p) addKn.
rewrite xE; apply: leq_trans (walk_lt_wrap_ge iv pLq ylt jk Hmp).
exact: ltnW (ltn_pmod _ p_gt0).
Qed.

(*  The two halves together.  [Alg2.inf_new_eq_lt] is the case [k = q %/ p].  *)
Lemma inf_red_lt p q d u v k :
  inv p q d u v -> invx p q u v -> p < q -> k <= q %/ p -> u + k * v + v < N ->
  inf (u + k * v + v) = inf (u + v) - minn k (inf (u + v) %/ p) * p.
Proof.
move=> iv ix pLq kLq uvN'.
apply/eqP; rewrite eqn_leq (inf_red_lt_le iv pLq kLq) /=.
exact: inf_red_lt_ge iv ix pLq kLq.
Qed.

(*  The last [invx] field: the new infimum is below the new larger gap.       *)
(*    On the [inf %/ p] branch the drop lands in [0, p[; on the [k] branch    *)
(*    it lands below [q - k*p], as [inf < q] by [invx_inf].                   *)
Lemma invx_red_lt_inf p q d u v k :
  inv p q d u v -> invx p q u v -> p < q -> k <= q %/ p -> 0 < q - k * p ->
  u + k * v + v < N ->
  inf (u + k * v + v) < maxn p (q - k * p).
Proof.
move=> iv ix pLq kLq q'_gt0 uvN'.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
apply: leq_ltn_trans (inf_red_lt_le iv pLq kLq) _.
(*  [leqP] itself resolves the [minn] in each branch                          *)
have [kI|Ik] := leqP k (inf (u + v) %/ p); last first.
  rewrite {1}(divn_eq (inf (u + v)) p) addKn.
  by apply: leq_trans (leq_maxl _ _); rewrite ltn_pmod.
have Iq : inf (u + v) < q by have := invx_inf ix; rewrite /maxn ifT.
have kpI : k * p <= inf (u + v) by rewrite -leq_divRL.
apply: leq_trans (leq_maxr _ _).
by apply: ltn_sub2r => //; apply: leq_ltn_trans kpI Iq.
Qed.

(******************************************************************************)
(* Reducing [p] by [k] copies of [q]                                          *)
(******************************************************************************)

(*  The mirror of the three lemmas above, with [u] and [v] swapped.           *)
Lemma red_ge_bez p q d u v k :
  inv p q d u v -> k * q <= p -> u * (p - k * q) + (v + k * u) * q = M.
Proof.
case => _ _ upvqE _ _ _ _ _ kqp.
rewrite mulnBr mulnDl addnC addnBA; last by rewrite leq_mul2l kqp orbT.
by rewrite mulnCA mulnA addnAC addnK addnC.
Qed.

Lemma red_ge_pt p q d u v k :
  inv p q d u v -> q <= p -> k <= p %/ q -> 0 < p - k * q ->
  (p - k * q = pt (v + k * u)) /\ (q = M - pt u).
Proof.
move=> iv qLp kLp p'_gt0.
have [p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0] := iv.
rewrite subn_gt0 in p'_gt0.
move: k kLp p'_gt0; elim => [_ _|j IH jLp p'_gt0];
    first by rewrite subn0 addn0.
have jLp' : j <= p %/ q by apply: ltnW.
have jqp : j * q < p.
  by rewrite (leq_ltn_trans _ p'_gt0) // leq_mul2r ltnW ?orbT.
have -> : p - j.+1 * q = p - j * q - q by rewrite mulSnr subnDA.
have -> : v + j.+1 * u = v + j * u + u by rewrite mulSnr addnA.
apply: step_pt_one_ge; last first.
  rewrite leq_subRL.
    by rewrite -mulSnr; apply: ltnW.
  by apply: ltnW.
split => //.
- by rewrite subn_gt0.
- exact: (red_ge_bez iv (ltnW jqp)).
- by case: (IH jLp' jqp).
- by rewrite -gE gcdnC [in RHS]gcdnC -{2}(subnKC (ltnW jqp)) gcdnMDl.
by rewrite addn_gt0 v_gt0.
Qed.

Lemma inv_red_ge p q d u v k :
  inv p q d u v -> q <= p -> k <= p %/ q -> 0 < p - k * q ->
  inv (p - k * q) q d u (v + k * u).
Proof.
move=> iv qLp kLp p'_gt0.
have [p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0] := iv.
have kqp : k * q <= p by rewrite -leq_divRL.
have [pE' qE'] := red_ge_pt iv qLp kLp p'_gt0.
split => //; first by apply: (red_ge_bez iv kqp).
  by rewrite -gE gcdnC [in RHS]gcdnC -{2}(subnKC kqp) gcdnMDl.
by rewrite addn_gt0 v_gt0.
Qed.

(*  The mirror: a new index is an old one walked DOWN by [j <= k] copies of   *)
(*    [u], and the walk subtracts [j*q].  [Alg2.pt_new_ge] at [k].            *)
Lemma red_ge_new p q d u v m k :
  inv p q d u v -> (forall i, 0 < i < u + v -> p <= pt i) ->
  q <= p -> k <= p %/ q ->
  u + v <= m -> m < u + (v + k * u) ->
  exists2 j, 0 < j <= k &
    [/\ 0 < m - j * u < u + v, j * q <= pt (m - j * u) &
        pt m = pt (m - j * u) - j * q].
Proof.
move=> iv Hmin qLp kLp mnew mLuv'.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have mnew' : v + u <= m by rewrite addnC.
have mLuv2 : m < v + k * u + u by rewrite addnC.
have [j jk /andP[ylt jum]] := new_index_decomp u_gt0 mnew' mLuv2.
have /andP[j_gt0 jk2] := jk.
have jqp : j * q <= p by rewrite -leq_divRL // (leq_trans jk2).
rewrite addnC in ylt.
have key : forall i, 0 < i <= k -> 0 < m - i * u -> i * u <= m ->
    m - i * u < u + v ->
    [/\ 0 < m - i * u < u + v, i * q <= pt (m - i * u) &
        pt m = pt (m - i * u) - i * q].
  move=> i /andP[i_gt0 ik] y_gt0 ium ylt2.
  have iqp : i * q <= p by rewrite -leq_divRL // (leq_trans ik).
  have iqP : i * q <= pt (m - i * u).
    by rewrite (leq_trans iqp) // Hmin // y_gt0.
  have iqM : i * q < M by rewrite (leq_ltn_trans iqp) // pE ltn_pt.
  have PuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
  have Hiu : pt (i * u) = M - i * q.
    have H1 : pt (i * u) = (i * pt u) %% M by rewrite /pt modnMmr mulnCA.
    rewrite H1 PuE mulnBr.
    have -> : i * M - i * q = (i - 1) * M + (M - i * q).
      rewrite addnBA; last by apply: ltnW.
      by rewrite subn1 -mulSnr prednK.
    by rewrite modnMDl modn_small // ltn_subrL muln_gt0 i_gt0 q_gt0 M_gt0.
  split => //; first by rewrite y_gt0.
  rewrite -{1}(subnK ium) ptDE Hiu.
  rewrite addnBA; last exact: ltnW iqM.
  rewrite [pt (m - i * u) + M]addnC -addnBA // modnDl.
  by rewrite modn_small // (leq_ltn_trans (leq_subr _ _)) // ltn_pt.
(* the [Pt 0] corner: if the walk lands on the origin, take one step less     *)
have [y0|y_gt0] := posnP (m - j * u); last by exists j => //; apply: key.
have mE : m = j * u by apply/eqP; rewrite eqn_leq jum andbT -subn_eq0 y0.
have j_gt1 : 1 < j.
  rewrite ltnNge; apply/negP => jL1.
  have j1 : j = 1 by apply/eqP; rewrite eqn_leq jL1 j_gt0.
  move: mnew; rewrite mE j1 mul1n leqNgt => /negP[].
  by rewrite -{1}[u]addn0 ltn_add2l.
have yE : m - j.-1 * u = u.
  by rewrite mE -{1}(prednK j_gt0) mulSnr addnC addnK.
have jpk : 0 < j.-1 <= k.
  apply/andP; split; first by rewrite -subn1 subn_gt0.
  exact: leq_trans (leq_pred _) jk2.
exists j.-1 => //; apply: key => //.
- by rewrite yE.
- by rewrite (leq_trans _ jum) // leq_mul2r leq_pred orbT.
by rewrite yE -{1}[u]addn0 ltn_add2l.
Qed.

(*  The [invx] fields on the [p] side.  [_p1] cannot go through Alg2's        *)
(*    argument, which reads [p - k*q < q] off the remainder; at a general     *)
(*    [k] that is false.  It goes through the OLD [invx_p1] instead: it       *)
(*    already says [pt z + p] is a point, hence below [M], and the new gap    *)
(*    is shorter.                                                             *)
Lemma invx_red_ge_min p q d u v k :
  inv p q d u v -> (forall i, 0 < i < u + v -> p <= pt i) ->
  q <= p -> k <= p %/ q ->
  forall m, 0 < m < u + (v + k * u) -> p - k * q <= pt m.
Proof.
move=> iv Hmin qLp kLp m /andP[m_gt0 mLuv'].
have [mold|mnew] := ltnP m (u + v).
  by rewrite (leq_trans (leq_subr _ _)) // Hmin // m_gt0.
have [j /andP[j_gt0 jk] [/andP[y_gt0 ylt] jqP Hm]] :=
  red_ge_new iv Hmin qLp kLp mnew mLuv'.
rewrite Hm leq_sub ?Hmin ?y_gt0 //.
by rewrite leq_mul2r jk orbT.
Qed.

Lemma invx_red_ge_max p q d u v k :
  inv p q d u v -> (forall i, 0 < i < u + v -> p <= pt i) ->
  (forall i, i < u + v -> pt i <= M - q) ->
  q <= p -> k <= p %/ q ->
  forall m, m < u + (v + k * u) -> pt m <= M - q.
Proof.
move=> iv Hmin Hmax qLp kLp m mLuv'.
have [mold|mnew] := ltnP m (u + v); first by apply: Hmax.
have [j /andP[j_gt0 jk] [/andP[y_gt0 ylt] jqP Hm]] :=
  red_ge_new iv Hmin qLp kLp mnew mLuv'.
by rewrite Hm (leq_trans (leq_subr _ _)) // Hmax.
Qed.

Lemma invx_red_ge_p1 p q d u v k :
  inv p q d u v -> invx p q u v ->
  q <= p -> k <= p %/ q -> 0 < p - k * q ->
  forall z, z < u -> pt (z + (v + k * u)) = pt z + (p - k * q).
Proof.
move=> iv ix qLp kLp p'_gt0 z zLu.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have [pE' _] := red_ge_pt iv qLp kLp p'_gt0.
have Huv := inv_uv_le (inv_red_ge iv qLp kLp p'_gt0).
have zLuv : z + (v + k * u) < M %/ g by apply: leq_trans Huv; rewrite ltn_add2r.
rewrite pE'; apply: ptD_leqM.
  by rewrite zLuv andbT addn_gt0 addn_gt0 v_gt0 orbT.
rewrite -pE' (leq_trans (leq_add (leqnn (pt z)) (leq_subr (k * q) p))) //.
by rewrite -(invx_p1 ix zLu) ltnW // ltn_pt.
Qed.

Lemma invx_red_ge_p2 p q d u v k :
  inv p q d u v ->
  forall z, u <= z < u + (v + k * u) -> pt (z - u) = (pt z + q) %% M.
Proof. by move=> iv z /andP[uLz _]; apply: ptBu; case: iv. Qed.

Lemma invx_red_ge_gap p q d u v k :
  inv p q d u v -> invx p q u v ->
  q <= p -> k <= p %/ q -> 0 < p - k * q ->
  forall y, y < u + (v + k * u) ->
  exists a b, [/\ a <= u, b <= v + k * u &
                  dst y = inf (u + (v + k * u)) + a * (p - k * q) + b * q].
Proof.
move=> iv ix qLp kLp p'_gt0 y yL.
have Hmin' := invx_red_ge_min iv (invx_min ix) qLp kLp.
have Hmax' := invx_red_ge_max iv (invx_min ix) (invx_max ix) qLp kLp.
by apply: gap_decomp (inv_red_ge iv qLp kLp p'_gt0) Hmin' Hmax' yL.
Qed.

(*  How far the infimum drops when [p] is reduced -- and it is NOT the       *)
(*    mirror of the [q] side.  Property 3 is directional: a [q]-gap splits    *)
(*    into [k] gaps of length [p] then the residual, LEFT TO RIGHT, so every  *)
(*    point walks down by steps of [p]; a [p]-gap splits into the residual    *)
(*    [r = p - k*q] then [k] gaps of length [q], points entering FROM THE     *)
(*    RIGHT.  So here whether the infimum moves at all depends on which gap   *)
(*    [b] sits in, which is what the disjunction records: [inf (u+v) < q]     *)
(*    is the case where [b] is in a [q]-gap and nothing is added below it.    *)
(*    This is [Alg2.ge_inf_le] at a general [k]; the [if] is what replaces    *)
(*    Alg2's appeal to [r < q], which only holds at the quotient.             *)
Lemma inf_red_ge_le p q d u v k :
  inv p q d u v -> invx p q u v -> q <= p -> 0 < k -> k <= p %/ q ->
  inf (u + v) < q \/
  inf (u + (v + k * u)) <=
    (if p - k * q <= inf (u + v) then (inf (u + v) - (p - k * q)) %% q
     else inf (u + v)).
Proof.
move=> iv ix qLp k_gt0 kLp.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Heq] := inf_ex uv_gt0.
have kqp : k * q <= p by rewrite -leq_divRL.
case: (ltnP y0 u) => [y0u|uy0]; last first.
(* [b] is in a [q]-gap: nothing is added there, and [Inf] is already low      *)
  left; rewrite ltnNge; apply/negP => qI.
  have qDy : q <= dst y0 by rewrite -Heq.
  have Hd := dst_sub_u iv uy0 qDy.
  have Hle : inf (u + v) <= dst (y0 - u).
    by apply: leq_inf_dst; rewrite (leq_ltn_trans (leq_subr _ _)).
  by move: Hle; rewrite Hd -Heq leqNgt ltn_subrL q_gt0 (leq_trans q_gt0 qI).
(* [b] is in a [p]-gap, so [Inf] is below its length                          *)
have Ip : inf (u + v) < p.
  rewrite ltnNge; apply/negP => pI.
  have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
  have pDy : p <= dst y0 by rewrite -Heq.
  have Hdd := dst_ofD Hsucc pDy.
  have Hle : inf (u + v) <= dst (y0 + v).
    by apply: leq_inf_dst; rewrite ltn_add2r.
  by move: Hle; rewrite Hdd -Heq leqNgt ltn_subrL p_gt0 (leq_trans p_gt0 pI).
right; case: (leqP (p - k * q) (inf (u + v))) => [rI|Ir]; last first.
(* [b] is in the residual gap at the bottom: no point was added below it      *)
  by apply: leq_inf_mono; rewrite leq_add2l leq_addr.
(* [b] is in the [m]-th new [q]-gap; the point just below it is the witness   *)
set I := inf (u + v) in Heq Ip rI *.
set m := (I - (p - k * q)) %/ q.
have mk : m < k.
  by rewrite /m ltn_divLR // ltn_subLR // (subnK kqp).
set j := k - m.
have j_gt0 : 0 < j by rewrite /j subn_gt0.
have jk : j <= k by rewrite /j leq_subr.
have jqp : j * q <= p.
  by rewrite (leq_trans (leq_mul jk (leqnn q))).
have pjq : p - j * q = (p - k * q) + m * q.
  have mkq : m * q <= k * q by rewrite leq_mul2r (ltnW mk) orbT.
  have jqE : j * q = k * q - m * q by rewrite /j mulnBl.
  by rewrite jqE subnBA // addnBAC.
have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
have jqPt : j * q <= pt (y0 + v) by rewrite Hsucc (leq_trans jqp) // leq_addl.
have Hpt : pt (y0 + v + j * u) = pt y0 + ((p - k * q) + m * q).
  by rewrite (pt_add_u iv j_gt0 jqp jqPt) Hsucc -pjq addnBA.
have tI : (p - k * q) + m * q <= I.
  by rewrite addnC -(subnK rI) leq_add2r /m leq_divM.
have tDy : (p - k * q) + m * q <= dst y0 by rewrite -Heq.
have Hdst : dst (y0 + v + j * u) = I - ((p - k * q) + m * q).
  by rewrite (dst_ofD Hpt tDy) -Heq.
have HE : I - ((p - k * q) + m * q) = (I - (p - k * q)) %% q.
  by rewrite subnDA {1}(divn_eq (I - (p - k * q)) q) -/m addnC addnK.
rewrite -HE -Hdst; apply: leq_inf_dst.
rewrite addnA (leq_ltn_trans (leq_add (leqnn (y0 + v))
        (leq_mul jk (leqnn u)))) //.
by rewrite ltn_add2r ltn_add2r.
Qed.

(*  and the [inf] field of [invx] on this side, which holds under either      *)
(*    branch of the disjunction -- the same route as [Alg2].                  *)
Lemma invx_red_ge_inf p q d u v k :
  inv p q d u v -> invx p q u v -> q <= p -> 0 < k -> k <= p %/ q ->
  inf (u + (v + k * u)) < maxn (p - k * q) q.
Proof.
move=> iv ix qLp k_gt0 kLp.
have [_ q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
case: (inf_red_ge_le iv ix qLp k_gt0 kLp) => [Ilt|Hle].
  apply: leq_ltn_trans (_ : inf (u + v) < _); last by rewrite (leq_trans Ilt) //
    leq_maxr.
  by apply: leq_inf_mono; rewrite leq_add2l leq_addr.
move: Hle; case: (leqP (p - k * q) (inf (u + v))) => [rI|Ir] Hle.
  by rewrite (leq_ltn_trans Hle) // (leq_trans (ltn_pmod _ q_gt0)) ?leq_maxr.
by rewrite (leq_ltn_trans Hle) // (leq_trans Ir) // leq_maxl.
Qed.

End Reduce.
