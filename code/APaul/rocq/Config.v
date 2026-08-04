(******************************************************************************)
(*                                                                            *)
(*   The two-length configuration and its reduction                           *)
(*                                                                            *)
(*   Both algorithms walk the same object: [u] gaps of length [p] and [v] of  *)
(*    length [q] tiling the circle, with [u*p + v*q = M].  [inv] states the   *)
(*    tiling, [invx] the index structure it induces, and [invd] the bound on  *)
(*    the recorded distance [d] that AlgFGG.v uses.                           *)
(*                                                                            *)
(*   A turn reduces one gap by [k] copies of the other:                       *)
(*                                                                            *)
(*      reduce [q]:  q -= k*p, u += k*v                                       *)
(*      reduce [p]:  p -= k*q, v += k*u                                       *)
(*                                                                            *)
(*   The [red_] and [invx_red_] lemmas do this at any [k] up to the Euclidean *)
(*    quotient, which is what AlgLefevre.v needs.  [step] is the reduction at *)
(*    the quotient itself, which is one turn of AlgFGG.v; its lemmas          *)
(*    ([step_p_gt0], [inv_step_pos], [inf_new_eq_lt], [invx_step]) are the    *)
(*    general ones instantiated there.                                        *)
(*                                                                            *)
(*   Only [invd] mentions [d].  That is the one thing the two algorithms do   *)
(*    not share: [invd] against [AlgLefevre.invw].  The configuration and its *)
(*    reduction they share entirely.                                          *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist.

(*  Reduce the larger gap by every copy of the smaller one it holds: one      *)
(*    turn of AlgFGG.v.  [d] is carried along.                                *)
Definition step (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if p < q then
    let k := q %/ p in (p, q - k * p, d %% p, u + k * v, v)
  else
    let k := p %/ q in
    let p' := p - k * q in
    (p', q, (if p' <= d then (d - p') %% q else d), u, v + k * u).

Section Reduce.

(*  The setting the two algorithms share: the line is [y = a*x - b] with      *)
(*    [a = A/M] and [b = B/M], searched over the first [N] indices.           *)

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


(*  The vocabulary of Dist.v, with this section's parameters supplied, so     *)
(*  that the lemmas read here exactly as they are stated there.               *)
Local Notation ltn_pt := (ltn_pt M_gt0 A).
Local Notation pt0 := (pt0 M A).
Local Notation ptDE := (ptDE M A).
Local Notation ptBu := (ptBu M_gt0).
Local Notation ptM := (ptM M A).
Local Notation leq_N_Mg := (leq_N_Mg N_lt_Mg).
Local Notation pt_neq0 := (pt_neq0 M_gt0 N_lt_Mg).
Local Notation pt_neq0M := (pt_neq0M M_gt0).
Local Notation ptD_leq := (ptD_leq M_gt0 N_lt_Mg).
Local Notation ptWv := (ptWv M_gt0 N_lt_Mg).
Local Notation ltn_dst := (ltn_dst M_gt0 A B).
Local Notation dst0 := (dst0 A ltn_B).
Local Notation dstD := (dstD M_gt0).
Local Notation dst_below := (dst_below ltn_B).
Local Notation dst_above := (dst_above M_gt0).
Local Notation dstDE := (dstDE M_gt0 A B).
Local Notation dst_diff := (dst_diff M_gt0 A B).
Local Notation dst_mod_g := (dst_mod_g M_gt0 A B).
Local Notation dst_ofD := (dst_ofD ltn_B).
Local Notation inf0 := (inf0 M A B).
Local Notation infSE := (infSE M A B).
Local Notation leq_inf_dst := (leq_inf_dst M A B).
Local Notation inf_ex := (inf_ex M_gt0 A B).
Local Notation leq_inf_mono := (leq_inf_mono M A B).


(******************************************************************************)
(* The two-length configuration                                               *)
(******************************************************************************)

Record inv (p q d u v : nat) := Inv {
  inv_p0  : 0 < p;
  inv_q0  : 0 < q;
  (* slater.v: sum_min_max *)
  inv_bez : u * p + v * q = M;
  (* slater.v: p = `{get_min n * a}, with v = get_min n *)
  inv_pv  : p = pt v;
  (* slater.v: q = 1 - `{get_max n * a}, with u = get_max n *)
  inv_qu  : q = M - pt u;
  (* Euclid's invariant.  Measured to hold at every state including the
     initial one.  It is what bounds how long the loop can run: Euclid
     reaches 0 once [u + v] gets to [M / gcd], so the loop must exit
     first, i.e. [N <= M / gcdn A M]. *)
  inv_gcd : gcdn p q = g;
  (* [u] and [v] start at 1 and only grow.  NOT derivable from the fields
     above -- u = 0, v = 1, q = M satisfies all of them -- but needed: with
     both positive, [inv_bez] gives [p + q <= M], i.e. the two gaps of the
     three-distance configuration fit inside the circle. *)
  inv_u0  : 0 < u;
  inv_v0  : 0 < v
}.

(* [A] is not a multiple of [M].                                              *)
Lemma am_gt0 : 0 < A %% M.
Proof.
have : pt 1 != 0 by apply: pt_neq0.
by rewrite /pt muln1; case: (_ %% _).
Qed.

(* The initial state satisfies [inv].                                         *)
Lemma inv_init : inv (A %% M) (M - A %% M) (B %% M) 1 1.
Proof.
constructor => //.
- by apply: am_gt0.
- by rewrite ltn_subRL addn0 ltn_mod.
- by rewrite !mul1n addnC subnK // ltnW // ltn_mod.
- by rewrite /pt muln1.
- by rewrite /pt muln1.
by rewrite (modn_small ltn_A) -{2}(subnKC (ltnW ltn_A)) gcdnDl.
Qed.

(* [q] does not exceed [M].                                                   *)
Lemma inv_qM p q d u v : inv p q d u v -> q <= M.
Proof. by case=> _ _ _ _ -> _ _ _; apply: leq_subr. Qed.

(* The three-distance step.  Conditioned, as [inv_step] and [step_p_gt0]      *)
(* are, on the loop continuing: at a terminal state [invx_min] fails.         *)
(* [invx_step] is proved one field at a time, in each branch.                 *)
(* [q] is strictly below [M] while indices remain in range.                   *)
Lemma inv_qltM p q d u v : inv p q d u v -> u <= N -> q < M.
Proof.
move=> iv uN.
have [_ _ _ _ qE _ u_gt0 _] := iv.
have qM := inv_qM iv.
rewrite ltn_neqAle qM andbT; apply/eqP => qMe.
have H := subnK (ltnW (ltn_pt u)).
move: H; rewrite -qE qMe => H2.
have Hu : pt u = 0.
  have E0 : M + pt u == M + 0 by rewrite addn0; apply/eqP.
  by move: E0; rewrite eqn_add2l => /eqP.
have uN' : 0 < u <= N by rewrite u_gt0 uN.
by have := pt_neq0 uN'; rewrite Hu eqxx.
Qed.

(* A two-length configuration has no more points than the orbit.              *)
Lemma inv_uv_le p q d u v : inv p q d u v -> u + v <= M %/ g.
Proof.
move=> iv; have [p_gt0 q_gt0 bez _ _ gE u_gt0 v_gt0] := iv.
rewrite -gE.
have g_gt0 : 0 < gcdn p q by rewrite gcdn_gt0 p_gt0.
have Hp := dvdn_gcdl p q; have Hq := dvdn_gcdr p q.
have p1_gt0 : 0 < p %/ gcdn p q by rewrite divn_gt0 // dvdn_leq.
have q1_gt0 : 0 < q %/ gcdn p q by rewrite divn_gt0 // dvdn_leq.
suff -> : M %/ gcdn p q = u * (p %/ gcdn p q) + v * (q %/ gcdn p q).
  by rewrite leq_add // leq_pmulr.
apply/eqP; rewrite -(eqn_pmul2r g_gt0) divnK; last first.
  by rewrite -bez dvdn_add // dvdn_mull.
by rewrite mulnDl -!mulnA !divnK // -bez.
Qed.

(* the batched Euclid step: [k] applications of slater's [get_minS] /         *)
(* [get_maxS] at once (Property 2 of the paper).  Induction on [k],           *)
(* through the two one-step lemmas below.                                     *)
(* The new [p] is still a point, in the [p < q] branch.                       *)
Lemma step_pt_one_lt p q u v :
  inv p q (dst 0) u v -> p < q -> (p = pt v) /\ (q - p = M - pt (u + v)).
Proof.
rewrite dst0.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /= pLq; split => //.
rewrite ptDE modn_small; last by rewrite -ltn_subRL // -pE -qE.
by rewrite subnDA -qE -pE.
Qed.

(* The new [q] is still a co-point, in the [q <= p] branch.                   *)
Lemma step_pt_one_ge p q u v :
  inv p q (dst 0) u v -> q <= p -> (p - q = pt (v + u)) /\ (q = M - pt u).
Proof.
rewrite dst0.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /= qLp; split => //.
rewrite pE qE ptDE subnBA; last by rewrite ltnW // ltn_pt.
rewrite [pt _ + _]addnC.
have MLuv : M <= pt u + pt v by rewrite -leq_subLR -pE -qE.
rewrite -[in RHS](subnK MLuv) modnDr modn_small // ltn_subLR //.
rewrite (ltn_trans _ (_ : M + pt v < _)) //.
  by rewrite ltn_add2r ltn_pt.
by rewrite ltn_add2l ltn_pt.
Qed.

Record invd (p q d u v : nat) := Invd {
  invd_max : d < maxn p q;
  invd_le  : d <= inf (u + v);
  (* [d] lies in the same residue class mod [p] as the closest distance.
     Independent of [invx]: that one constrains the configuration, this one
     constrains [d] relative to it. *)
  invd_cong : d = inf (u + v) %[mod p]
}.

Record invx (p q u v : nat) := Invx {
  invx_min : forall m, 0 < m < u + v -> p <= pt m;
  invx_max : forall m, m < u + v -> pt m <= M - q;
(* free wherever [invx] is established: [inv_qu] gives [q = M - pt u].        *)
  invx_qM  : q <= M;
(* [b] lies in a gap, and every gap is [p] or [q], so the nearest point       *)
(*     below it is within [maxn p q].                                         *)
  invx_inf : inf (u + v) < maxn p q;
(* the three-distance content: every distance is the closest one plus         *)
(*     whole gaps.  Not implied by the fields above.                          *)
  invx_gap : forall y, y < u + v ->
             exists a b, [/\ a <= u, b <= v &
                             dst y = inf (u + v) + a * p + b * q];
(* three-distance in INDEX form (Lefevre 2.4 / slater get_nextDmin,           *)
(*     get_nextDmax): [u] gaps of length [p], [v] of length [q].              *)
  invx_p1  : forall z, z < u -> pt (z + v) = pt z + p;
  invx_p2  : forall z, u <= z < u + v -> pt (z - u) = (pt z + q) %% M
}.

(* the wrapping companion of [pt_sub]: when the order inverts, the            *)
(* difference of indices lands on the far side of [M].                        *)
(* slater.get_minB: points in index order are at least [p] apart.             *)
(* The initial two-point configuration satisfies [invx].                      *)
Lemma invx_init : invx (A %% M) (M - A %% M) 1 1.
Proof.
have AME : A %% M = A by apply: modn_small.
have p1E : pt 1 = A by rewrite /pt muln1.
have inf2E : inf 2 = minn (dst 1) (dst 0).
  rewrite !infSE inf0.
  suff -> : minn (dst 0) M = dst 0 by [].
  by apply/minn_idPl; rewrite ltnW // ltn_dst.
(* the two points are [0] and [A]; [b] sits either above [A] (gap [p]) or     *)
(* below it (gap [q]), and that fixes both [Inf] and the decomposition        *)
have HI : inf 2 = if A <= B then B - A else B.
  have [AB|AB] := leqP A B.
    rewrite inf2E dst0 (_ : dst 1 = B - A); last by rewrite dst_below p1E.
    by apply/minn_idPl; rewrite leq_subr.    
  rewrite inf2E dst0 (_ : dst 1 = B + M - A).
    by apply/minn_idPr; rewrite -addnBA ?leq_addr // ltnW.
  by rewrite dst_above p1E.
have Hinf : inf 2 < maxn (A %% M) (M - A %% M).
  rewrite HI AME; have [AB|AB] := leqP A B.
    by rewrite (leq_trans _ (leq_maxr _ _)) // ltn_sub2r.
  by rewrite (leq_trans _ (leq_maxl _ _)).
have Hgap : forall y, y < 2 ->
    exists a b, [/\ a <= 1, b <= 1 &
                    dst y = inf 2 + a * (A %% M) + b * (M - A %% M)].
  move=> y; move: HI; (have [AB|AB] := leqP A B) => HI.
    have d1E : dst 1 = B - A by rewrite dst_below p1E.
    case: y => [|[|y]] //= _.
      by exists 1, 0; split=> //; rewrite dst0 HI AME mul1n mul0n addn0 subnK.
    by exists 0, 0; split=> //; rewrite d1E HI !mul0n !addn0.
  have d1E : dst 1 = B + M - A by rewrite dst_above p1E.
  case: y => [|[|y]] //= _.
    by exists 0, 0; split=> //; rewrite dst0 HI !mul0n !addn0.
  exists 0, 1; split=> //.
  by rewrite d1E HI mul0n addn0 mul1n AME addnBA // ltnW.
have HP1 : forall z, z < 1 -> pt z.+1 = pt z + A %% M.
  by move=> z; case: z => // _; rewrite p1E AME pt0.
have HP2 : forall z, 1 <= z < 2 -> pt z.-1  = (pt z + (M - A %% M)) %% M.
  move=> z; case: z => [|[|z]] //= _.
  by rewrite p1E AME pt0 subnKC ?modnn // ltnW.
split => //.
- by move=> m; case: m => [|[|m]] //= _; rewrite p1E AME.
- move=> m; case: m => [|[|m]] //= _; first by rewrite pt0.
  by rewrite p1E AME subKn // ltnW.
- by rewrite leq_subr.
- by move=> z; rewrite addn1; apply: HP1.
by move=> z zB; rewrite subn1; apply: HP2.
Qed.

(* Stepping the index down by [u] lowers the distance by [q].                 *)
Lemma dst_sub_u p q d u v y :
  inv p q d u v -> u <= y -> q <= dst y -> dst (y - u) = dst y - q.
Proof.
move=> iv uy qDy.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M by rewrite qE leq_subr.
have ptuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
have Heq := @dstDE (y - u) u.
rewrite subnK // ptuE subnBA // addnAC addnK in Heq.
have [dLM|MLd] := ltnP (dst (y - u) + q) M.
  by rewrite Heq (modn_small dLM) addnK.
have dLM : dst (y - u) + q - M < M.
  by rewrite ltn_subLR // (leq_ltn_trans (leq_add (leqnn (dst (y - u))) qM)) //
             ltn_add2r ltn_dst.
move: Heq; rewrite -{1}(subnK MLd) modnDr (modn_small dLM) => Heq.
have Hc : dst y < q by rewrite Heq ltn_subLR // ltn_add2r ltn_dst.
by move: qDy; rewrite leqNgt Hc.
Qed.

(* The same step when [B] is nearer than [q]: it lands beyond [B].            *)
Lemma dst_sub_u_wrap p q d u v w :
  inv p q d u v -> u <= w -> dst w < q -> dst (w - u) = dst w + M - q.
Proof.
move=> iv uw qDw.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M by rewrite qE leq_subr.
have PtuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
have Heq := dstDE (w - u) u.
rewrite subnK // PtuE subnBA // addnAC addnK in Heq.
have [dLM|MLd] := ltnP (dst (w - u) + q) M.
  by move: qDw; rewrite Heq (modn_small dLM) ltnNge leq_addl.
have dLM : dst (w - u) + q - M < M.
  by rewrite ltn_subLR // (leq_ltn_trans (leq_add (leqnn (dst (w - u))) qM)) //
             ltn_add2r ltn_dst.
move: Heq; rewrite -{1}(subnK MLd) modnDr (modn_small dLM) => Heq.
by rewrite Heq subnK // addnK.
Qed.

(*  Stepping the index up by [u] lowers the point by [q].                     *)
Lemma pt_add_u p q d u v y i :
  inv p q d u v -> 0 < i -> i * q <= p -> i * q <= pt y ->
  pt (y + i * u) = pt y - i * q.
Proof.
move=> iv i_gt0 iqp iqP.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have iqM : i * q < M by rewrite (leq_ltn_trans iqp) // pE ltn_pt.
have PuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
have Hiu : pt (i * u) = M - i * q.
  have H1 : pt (i * u) = (i * pt u) %% M by rewrite /pt modnMmr mulnCA.
  rewrite H1 PuE mulnBr.
  have -> : i * M - i * q = (i - 1) * M + (M - i * q).
    rewrite addnBA; last by apply: ltnW.
    by rewrite subn1 -mulSnr prednK.
  by rewrite modnMDl modn_small // ltn_subrL muln_gt0 i_gt0 q_gt0 M_gt0.
rewrite ptDE Hiu addnBA; last exact: ltnW iqM.
rewrite [pt y + M]addnC -addnBA // modnDl.
by rewrite modn_small // (leq_ltn_trans (leq_subr _ _)) // ltn_pt.
Qed.

(* Two points whose index and value orders agree differ by a plain point.     *)
Lemma dst_gap_up m1 m2 : 
  m1 <= m2 -> dst m2 <= dst m1 -> pt (m2 - m1) + dst m2 = dst m1.
Proof.
move=> m12 D21; move: (dst_diff m12) => Heq.
have [Hlt|Hge] := ltnP (dst m2 + pt (m2 - m1)) M.
  by rewrite Heq (modn_small Hlt) addnC.
have Hs : dst m2 + pt (m2 - m1) - M < M.
  rewrite ltn_subLR //.
  by rewrite (leq_ltn_trans (leq_add (ltnW (ltn_dst _)) (leqnn _))) // 
             ltn_add2l ltn_pt.
have HD : dst m1 = dst m2 + pt (m2 - m1) - M.
  by rewrite Heq -{1}(subnK Hge) modnDr modn_small.
suff : dst m1 < dst m2 by rewrite ltnNge D21.
by rewrite HD ltn_subLR // [M + _]addnC ltn_add2l ltn_pt.
Qed.

(* Two points whose orders disagree differ by one turn of the circle.         *)
Lemma dst_gap_down m1 m2 :
  m2 <= m1 -> m1 < M %/ g -> dst m2 <= dst m1 -> m2 != m1 ->
  pt (m1 - m2) + dst m1 = M + dst m2.
Proof.
move=> m21 m1N D21 m2Dm1; move: (dst_diff m21) => Heq.
have Hd : 0 < m1 - m2 < M %/ g.
  by rewrite subn_gt0 ltn_neqAle m2Dm1 m21 (leq_ltn_trans (leq_subr _ _)).
have [Hlt|Hge] := ltnP (dst m1 + pt (m1 - m2)) M.
  have /eqP := pt_neq0M Hd; case.
  apply/eqP; rewrite -(eqn_add2l (dst m1)) addn0 eqn_leq.
  by rewrite leq_addr andbT -(modn_small Hlt) -Heq D21.
have Hs : dst m1 + pt (m1 - m2) - M < M.
  rewrite ltn_subLR //.
  by rewrite (leq_ltn_trans (leq_add (ltnW (ltn_dst _)) (leqnn _))) // 
             ltn_add2l ltn_pt.
have HD : dst m2 = dst m1 + pt (m1 - m2) - M.
  by rewrite Heq -{1}(subnK Hge) modnDr modn_small.
by rewrite HD addnC subnKC // (leq_trans Hge) // leq_addl.
Qed.

(* One [p]-step of the walk towards a nearer point; it never overshoots.      *)
Lemma gap_step_p p q d u v y z :
  inv p q d u v ->
  (forall m, 0 < m < u + v -> p <= pt m) ->
  y < u -> z < u + v -> dst z <= dst y -> z != y ->
  p + dst z <= dst y /\ dst (y + v) = dst y - p.
Proof.
move=> iv Hmin yu zL Dzy zDy.
have uvN := inv_uv_le iv.
have [p_gt0 q_gt0 bez pE qE _ u_gt0 v_gt0] := iv.
have yL : y < u + v by rewrite (leq_trans yu) // leq_addr.
suff Hp : p + dst z <= dst y.
  split => //.
  have pDy : p <= dst y by rewrite (leq_trans _ Hp) // leq_addr.
  by rewrite dstDE -pE -addnBAC // modnDr modn_small //
             (leq_ltn_trans (leq_subr p (dst y))) // ltn_dst.
have [zy|yz] := leqP z y; last first.
  rewrite -(dst_gap_up (ltnW yz) Dzy) leq_add2r.
  by apply: Hmin; rewrite subn_gt0 yz (leq_ltn_trans (leq_subr _ _)).
(* Slater's trick: (6) at the pair [(z, y+v)]                                 *)
have Hw := dst_gap_down zy (leq_trans yL uvN) Dzy zDy.
rewrite leqNgt; apply/negP => Hlt.
have HP : pt (y - z) = M - (dst y - dst z) by rewrite subnBA // -Hw addnK.
have t_gt0 : 0 < dst y - dst z.
  have [t0|//] := posnP (dst y - dst z).
  by have := ltn_pt (y - z); rewrite HP t0 subn0 ltnn.
have tp : dst y - dst z < p by rewrite ltn_subLR // addnC.
have Hk : p <= pt (y - z + v).
  by apply: Hmin;
     rewrite addn_gt0 v_gt0 orbT ltn_add2r (leq_ltn_trans (leq_subr z y) yu).
move: Hk; rewrite ptDE -pE HP.
have -> : M - (dst y - dst z) + p = M + (p - (dst y - dst z)).
  have tp' : dst y - dst z <= p := ltnW tp.
  have pM : p <= M by rewrite pE ltnW // ltn_pt.
  have tM : dst y - dst z <= M := leq_trans tp' pM.
  by rewrite addnBAC // addnBA.
rewrite modnDl modn_small; last first.
  by rewrite (leq_ltn_trans (leq_subr _ _)) // pE ltn_pt.
by rewrite leqNgt ltn_subrL t_gt0 p_gt0.
Qed.

(* One [q]-step of the walk towards a nearer point; it never overshoots.      *)
Lemma gap_step_q p q d u v y z :
  inv p q d u v ->
  (forall m, m < u + v -> pt m <= M - q) ->
  u <= y -> y < u + v -> z < u + v -> dst z <= dst y -> z != y ->
  q + dst z <= dst y /\ dst (y - u) = dst y - q.
Proof.
move=> iv Hmax uy yL zL Dzy zDy.
have uvN := inv_uv_le iv.
have [p_gt0 q_gt0 bez pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M by rewrite qE leq_subr.
have PtuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
suff Hq : q + dst z <= dst y.
  split => //.
  have qDy : q <= dst y by rewrite (leq_trans _ Hq) // leq_addr.
  have Heq := @dstDE (y - u) u.
  rewrite subnK // PtuE subnBA // addnAC addnK in Heq.
  have [Hs|Hs] := ltnP (dst (y - u) + q) M.
    by rewrite Heq (modn_small Hs) addnK.
  have Hlt2 : dst (y - u) + q - M < M.
    by rewrite ltn_subLR // (leq_ltn_trans (leq_add (leqnn (dst (y - u))) qM))
               // ltn_add2r ltn_dst.
  move: Heq; rewrite -{1}(subnK Hs) modnDr (modn_small Hlt2) => Heq.
  have Hc : dst y < q by rewrite Heq ltn_subLR // ltn_add2r ltn_dst.
  by move: qDy; rewrite leqNgt Hc.
have [zy|yz] := leqP z y.
  have Hw := dst_gap_down zy (leq_trans yL uvN) Dzy zDy.
  have HP : pt (y - z) = M + dst z - dst y by rewrite -Hw addnK.
  have Hk : pt (y - z) <= M - q.
    by apply: Hmax; rewrite (leq_ltn_trans (leq_subr _ _)).
  move: Hk; rewrite HP leq_subLR addnBA // leq_subRL; last first.
    by rewrite (leq_trans qM) // leq_addl.
  by rewrite addnCA [dst y + M]addnC leq_add2l.
(* Slater's trick again, now at the pair [(y, (z-y)+u)]                       *)
have Hu := dst_gap_up (ltnW yz) Dzy.
rewrite -Hu leq_add2r leqNgt; apply/negP => Hlt.
have Hk : pt (z - y + u) <= M - q.
  apply: Hmax; rewrite addnC ltn_add2l ltn_subLR; last exact: ltnW yz.
  by rewrite (leq_trans zL) // leq_add2r.
move: Hk; rewrite ptDE PtuE modn_small; last first.
  by rewrite addnBA // ltn_subLR ?(leq_trans qM) ?leq_addl // ltn_add2r.
rewrite -{2}[M - q]add0n leq_add2r leqn0 => /eqP H0.
have Hd : 0 < z - y < M %/ g.
  by rewrite subn_gt0 yz (leq_ltn_trans (leq_subr y z)) // (leq_trans zL).
by move: (pt_neq0M Hd); rewrite H0 eqxx.
Qed.

(* The walk to a nearer point, carrying both the value and index equations.   *)
Lemma gap_walk n p q d u v y z :
  inv p q d u v ->
  (forall m, 0 < m < u + v -> p <= pt m) ->
  (forall m, m < u + v -> pt m <= M - q) ->
  y < u + v -> z < u + v -> dst z <= dst y -> dst y - dst z <= n ->
  exists a b, a * p + b * q = dst y - dst z /\ a * v + y = b * u + z.
Proof.
elim: n y => [|n IH] y iv Hmin Hmax yL zL Dzy Hn.
have uvN := inv_uv_le iv.
  have Dyz : dst y = dst z.
    by apply/eqP; rewrite eqn_leq Dzy andbT -subn_eq0 -leqn0.
  have -> : y = z.
    have [yz|//|//] := ltngtP y z; last move=> zy.
      have := dst_gap_up (ltnW yz) Dzy; 
        rewrite Dyz -{2}[dst z]add0n => /addIn H0.
      have Hd : 0 < z - y < M %/ gcdn A M.
        by rewrite subn_gt0 yz (leq_ltn_trans (leq_subr y z)) // (leq_trans zL).
      by move: (pt_neq0M Hd); rewrite H0 eqxx.
    have Hne : z != y by rewrite ltn_eqF.
    have := dst_gap_down (ltnW zy) (leq_trans yL uvN) Dzy Hne.
    rewrite Dyz => /addIn HH.
    by have := ltn_pt (y - z); rewrite HH ltnn.
  by exists 0, 0; rewrite !mul0n subnn.
have [p_gt0 _ _ _ _ _ _ _] := iv.
have [/eqP zEy|zDy] := boolP (z == y).
  by exists 0, 0; rewrite !mul0n zEy subnn.
have [yu|uy] := ltnP y u.
  have [Hp Hstep] := gap_step_p iv Hmin yu zL Dzy zDy.
  have pDy : p <= dst y by rewrite (leq_trans _ Hp) // leq_addr.
  have yvL : y + v < u + v by rewrite ltn_add2r.
  have Dz2 : dst z <= dst (y + v) by rewrite Hstep leq_subRL // addnC.
  have Hn2 : dst (y + v) - dst z <= n.
    by rewrite Hstep subnAC leq_subLR (leq_trans Hn) // -add1n leq_add2r.
  have [a [b [Hval Hix]]] := IH (y + v) iv Hmin Hmax yvL zL Dz2 Hn2.
  exists a.+1, b; split.
    by rewrite mulSn -addnA Hval Hstep subnAC addnC subnK // leq_subRL // addnC.
  by rewrite -Hix mulSn -addnA addnCA [v + y]addnC.
have [Hq Hstep] := gap_step_q iv Hmax uy yL zL Dzy zDy.
have qDy : q <= dst y by rewrite (leq_trans _ Hq) // leq_addr.
have q_gt0 : 0 < q by have [_ ? _ _ _ _ _ _] := iv.
have yuL : y - u < u + v by rewrite (leq_ltn_trans (leq_subr _ _)).
have Dz2 : dst z <= dst (y - u) by rewrite Hstep leq_subRL // addnC.
have Hn2 : dst (y - u) - dst z <= n.
  by rewrite Hstep subnAC leq_subLR (leq_trans Hn) // -add1n leq_add2r.
have [a [b [Hval Hix]]] := IH (y - u) iv Hmin Hmax yuL zL Dz2 Hn2.
exists a, b.+1; split.
  by rewrite mulSn addnCA Hval Hstep subnAC subnKC // leq_subRL // addnC.
by rewrite mulSn -addnA -Hix addnCA subnKC.
Qed.

(* The index equation bounds the two gap counts by [u] and [v].               *)
Lemma gap_bounds p q u v y z a b :
  0 < u -> 0 < v -> u * p + v * q = M -> y < u + v -> z < u + v ->
  a * v + y = b * u + z -> a * p + b * q < M -> a <= u /\ b <= v.
Proof.
move=> u_gt0 v_gt0 bez yL zL Hix Hval.
have ua_bv : u <= a -> b < v.
  rewrite ltnNge => ua; apply/negP => vb.
  move: Hval; rewrite ltnNge -bez => /negP; apply.
  by rewrite leq_add // leq_mul2r ?ua ?vb orbT.
split.
  case: leqP => // H.
  suff : v <= b by rewrite leqNgt ua_bv ?(ltnW H) //.
  apply: gap_count_aux u_gt0 H zL _.
  by rewrite -Hix leq_addr.
case: leqP => // H.
suff : b < v by case: ltngtP H.
apply/ua_bv/(gap_count_aux v_gt0 H (_ : y < _)) => //; first by rewrite addnC.
by rewrite Hix leq_addr.
Qed.

(* Every distance is the infimum plus [a] gaps [p] and [b] gaps [q].          *)
Lemma gap_decomp p q d u v y :
  inv p q d u v ->
  (forall m, 0 < m < u + v -> p <= pt m) ->
  (forall m, m < u + v -> pt m <= M - q) ->
  y < u + v ->
  exists a b, [/\ a <= u, b <= v & dst y = inf (u + v) + a * p + b * q].
Proof.
move=> iv Hmin Hmax yL.
have uvN := inv_uv_le iv.
have [p_gt0 q_gt0 bez _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [z zL Heq] := inf_ex uv_gt0.
have Dzy : dst z <= dst y by rewrite -Heq leq_inf_dst.
have [a [b [Hval Hix]]] :=
  gap_walk iv Hmin Hmax yL zL Dzy (leqnn (dst y - dst z)).
have [aLu bLv] : a <= u /\ b <= v.
  apply: (gap_bounds u_gt0 v_gt0 bez yL zL Hix).
  by rewrite Hval (leq_ltn_trans (leq_subr _ _)) // ltn_dst.
exists a, b; split => //.
by rewrite Heq -addnA Hval subnKC.
Qed.

(* A point with [B] inside the [q]-gap above it is the nearest below [B].     *)
Lemma gap_q_empty p q d u v w z :
  inv p q d u v -> (forall m, m < u + v -> pt m <= M - q) ->
  q + q <= M -> u <= w -> w < u + v -> z < u + v ->
  dst w < q -> dst w <= dst z.
Proof.
move=> iv Hmax qqM uw wL zL qDw; case: leqP => // Dzw.
have uvN := inv_uv_le iv.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M by rewrite (leq_trans _ qqM) // leq_addl.
have zDw : dst z <= dst w := ltnW Dzw.
have zNw : z != w by apply/eqP => zw; move: Dzw; rewrite zw ltnn.
(* (6) at the pair [(w,z)] : [z] cannot be below [w] in index order           *)
have wz : w < z.
  rewrite ltnNge; apply/negP => zw.
  have Hd := dst_gap_down zw (leq_trans wL uvN) zDw zNw.
  have Hk : pt (w - z) <= M - q.
    by apply: Hmax; rewrite (leq_ltn_trans (leq_subr _ _)).
  move: Hk; rewrite -(leq_add2r (dst w)) Hd addnBAC // leq_subRL; last first.
    by rewrite (leq_trans qM) // leq_addr.
  rewrite addnCA leq_add2l => H.
  by move: qDw; rewrite ltnNge (leq_trans _ H) // leq_addr.
(* (6) at the pair [(z, w-u)] : nor above the successor                       *)
have Hw' : dst (w - u) = dst w + M - q := dst_sub_u_wrap iv uw qDw.
have zDw' : dst z <= dst (w - u).
  rewrite Hw' (leq_trans (ltnW (leq_ltn_trans zDw qDw))) // leq_subRL.
    by rewrite (leq_trans qqM) // leq_addl.
  by rewrite (leq_trans qM) // leq_addl.
have zw' : z < w - u.
  rewrite ltnNge; apply/negP => w'z.
  have Hd := dst_gap_up w'z zDw'.
  have: pt (z - (w - u)) <= M - q.
    by apply: Hmax; rewrite (leq_ltn_trans (leq_subr _ _)).
  rewrite -(leq_add2r (dst z)) Hd Hw' -addnBA // addnC leq_add2l => H2.
  by move: Dzw; rewrite ltnNge H2.
(* so [w < z < w - u], and [w - u <= w]                                       *)
by move: zw'; rewrite ltnNge (leq_trans (leq_subr u w)) // ltnW.
Qed.

(* A point with [B] inside the [p]-gap above it is the nearest below [B].     *)
Lemma gap_p_empty p q d u v w z :
  inv p q d u v -> (forall m, 0 < m < u + v -> p <= pt m) ->
  (forall m, m < u + v -> pt m <= M - q) ->
  p <= q -> w < u + v -> z < u + v ->
  dst w < p -> dst w <= dst z.
Proof.
move=> iv Hmin Hmax pq wL zL pDw; case: leqP => // Dzw.
have uvN := inv_uv_le iv.
have [p_gt0 q_gt0 _ pE qE _ u_gt0 v_gt0] := iv.
have qM : q <= M by rewrite qE leq_subr.
have zDw : dst z <= dst w := ltnW Dzw.
have zNw : z != w by apply/eqP => zw; move: Dzw; rewrite zw ltnn.
have wz : w < z.
  rewrite ltnNge; apply/negP => zw.
  have Hd := dst_gap_down zw (leq_trans wL uvN) zDw zNw.
  have Hk : pt (w - z) <= M - q.
    by apply: Hmax; rewrite (leq_ltn_trans (leq_subr _ _)).
  move: Hk; rewrite -(leq_add2r (dst w)) Hd addnBAC // leq_subRL; last first.
    by rewrite (leq_trans qM) // leq_addr.
  rewrite addnCA leq_add2l => H.
  have qDw : q <= dst w by rewrite (leq_trans _ H) // leq_addr.
  by move: pDw; rewrite ltnNge (leq_trans pq qDw).
have Hd := dst_gap_up (ltnW wz) zDw.
have Hk : p <= pt (z - w).
  by apply: Hmin; rewrite subn_gt0 wz (leq_ltn_trans (leq_subr _ _)).
move: Hk; rewrite -(leq_add2r (dst z)) Hd => H.
by move: pDw; rewrite ltnNge (leq_trans _ H) // leq_addr.
Qed.

(* The [v]-walk lowers the distance by [m * p] when it does not wrap.         *)
Lemma walk_lt_nowrap p q d u v y m :
  inv p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> m * p <= dst y -> dst (y + m * v) = dst y - m * p.
Proof.
move=> iv pLq yLuv mk Hmp.
have [p_gt0 _ _ pE _ _ _ _] := iv.
elim: m Hmp {mk} => [|m IH Hmp]; first by rewrite !mul0n addn0 subn0.
have Hm : m * p <= dst y by rewrite (leq_trans _ Hmp) // leq_mul2r leqnSn orbT.
have -> : y + m.+1 * v = y + m * v + v by rewrite mulSnr addnA.
rewrite dstD; first by rewrite IH // -pE mulSnr subnDA.
by rewrite IH // -pE leq_psubRL // -mulSnr.
Qed.

(* The [v]-walk when it does wrap.                                            *)
Lemma walk_lt_wrapeq p q d u v y m :
  inv p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> dst y < m * p -> dst (y + m * v) = dst y + M - m * p.
Proof.
move=> iv pLq yLuv /andP[m_gt0 mk] Hy.
have [p_gt0 _ _ pE qE _ _ _] := iv.
have mpq : m * p <= q by rewrite -leq_divRL.
have mpM : m * p <= M by rewrite (leq_trans mpq) // qE leq_subr.
rewrite dstDE ptM -pE.
have [Hlt|Hge] := ltnP (m * p) M.
  rewrite (modn_small Hlt) modn_small //.
  rewrite ltn_subLR ?ltn_add2r //.
  by rewrite (leq_trans mpM) // leq_addl.
have mpE : m * p = M by apply/eqP; rewrite eqn_leq mpM Hge.
by rewrite mpE modnn subn0 modnDr modn_small ?ltn_dst // addnK.
Qed.

(* A wrapped [v]-walk lands at least [p] away from [B].                       *)
Lemma walk_lt_wrap_ge p q d u v y m :
  inv p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> dst y < m * p -> p <= dst (y + m * v).
Proof.
move=> iv pLq yLuv mk Hy.
rewrite (walk_lt_wrapeq iv pLq yLuv mk Hy).
have [p_gt0 q_gt0 bez _ _ _ u_gt0 v_gt0] := iv.
have /andP[m_gt0 mkd] := mk.
have mpq : m * p <= q by rewrite -leq_divRL.
(* the whole point of [inv_u0]/[inv_v0]: [p + q <= M]                         *)
have pqM : p + q <= M by rewrite -bez leq_add // leq_pmull.
have mpM : m * p <= M by rewrite (leq_trans mpq) // (leq_trans _ pqM) //
  leq_addl.
rewrite leq_subRL; last by rewrite (leq_trans mpM) // leq_addl.
apply: leq_trans (_ : M <= _); last by rewrite leq_addl.
by rewrite (leq_trans (leq_add mpq (leqnn p))) // addnC.
Qed.

(* The [u]-walk raises the distance by [m * q] when it does not wrap.         *)
Lemma walk_ge_nowrap p q d u v y m :
  inv p q d u v -> q <= p -> y < u + v -> 0 < m <= p %/ q ->
  dst y + m * q < M -> dst (y + m * u) = dst y + m * q.
Proof.
move=> iv qLp yLuv /andP[m_gt0 mk] Hw.
have [p_gt0 q_gt0 _ pE qE _ _ _] := iv.
have PuE : pt u = M - q by rewrite qE subKn // ltnW // ltn_pt.
have mqM : m * q < M by rewrite (leq_ltn_trans (leq_addl (dst y) _)).
have Hpm : pt (m * u) = M - m * q.
  rewrite ptM PuE mulnBr.
  have -> : m * M - m * q = (m - 1) * M + (M - m * q).
    rewrite addnBA; last by apply: ltnW.
    by rewrite subn1 -mulSnr prednK.
  by rewrite modnMDl modn_small // ltn_subrL muln_gt0 m_gt0 q_gt0 M_gt0.
by rewrite dstDE Hpm (subnBA _ (ltnW mqM)) addnAC addnK modn_small.
Qed.

(* The last quotient, where [q] is the gcd: all gaps are [q] and [d] is the   *)
(* global minimum.                                                            *)
Lemma ge_exit p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> q <= p ->
  p - p %/ q * q = 0 ->
  (forall y m, y < u + v -> 0 < m <= p %/ q -> M <= dst y + m * q ->
     (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
       <= dst (y + m * u))
  /\ (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
       = inf (u + (v + p %/ q * u)) %[mod p - p %/ q * q].
Proof.
move=> iv ivd ix qLp p'0.
have [p_gt0 q_gt0 bez pE qE gE u_gt0 v_gt0] := iv.
have rE : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
have qp : q %| p by rewrite /dvdn -rE p'0.
(* the last quotient: [q] IS the gcd, so all gaps are [g]                     *)
have qg : q = gcdn A M by rewrite -gE gcdnC; apply/esym/gcdn_idPl.
have dE : (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
            = d %% q by rewrite p'0 leq0n subn0.
have [_ _ dcong] := ivd.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Heq] := inf_ex uv_gt0.
(* [d] is congruent to [B] mod [g], so [d %% q] is the global minimum         *)
have dB : d = B %[mod q].
  have H1 : d = inf (u + v) %[mod q].
    by rewrite -(modn_dvdm d qp) dcong modn_dvdm.
  by rewrite H1 Heq qg dst_mod_g.
have Hlow : forall x, d %% q <= dst x.
  by move=> x; rewrite dB qg -(dst_mod_g x) leq_mod.
split; first by move=> y m *; rewrite dE Hlow.
rewrite dE p'0 !modn0.
have pk : p %/ q * q = p by rewrite divnK.
have k_gt0 : 0 < p %/ q by rewrite divn_gt0.
apply/eqP; rewrite eqn_leq; apply/andP; split.
  apply: leq_inf; last by move=> x _; exact: Hlow.
  by rewrite (leq_trans (ltnW (ltn_pmod _ q_gt0))) // qE leq_subr.
have y0L' : y0 < u + (v + p %/ q * u).
  by rewrite (leq_trans y0L) // leq_add2l leq_addr.
have [Iq|qI] := ltnP (dst y0) q.
(* [b] is already within [g] of the old minimum                               *)
  have -> : d %% q = dst y0.
    by rewrite dB qg -(dst_mod_g y0) modn_small // -qg.
  by apply: leq_inf_dst.
have y0u : y0 < u.
  rewrite ltnNge; apply/negP => uy0.
  have Hd := dst_sub_u iv uy0 qI.
  have Hle : inf (u + v) <= dst (y0 - u).
    by apply: leq_inf_dst; rewrite (leq_ltn_trans (leq_subr _ _)).
  by move: Hle; rewrite Hd Heq leqNgt ltn_subrL q_gt0 (leq_trans q_gt0 qI).
(* otherwise the same witness as Property 3, with residual [r = 0]            *)
have Ip : dst y0 < p.
  by rewrite -Heq; have := invx_inf ix; rewrite /maxn ifN // -leqNgt.
set m := dst y0 %/ q.
have mk : m < p %/ q by rewrite /m ltn_divLR // pk.
set j := p %/ q - m.
have j_gt0 : 0 < j by rewrite /j subn_gt0.
have jk : j <= p %/ q by rewrite /j leq_subr.
have jqp : j * q <= p by rewrite -pk leq_mul2r jk orbT.
have pjq : p - j * q = m * q.
  have mqp : m * q <= p by rewrite -pk leq_mul2r (ltnW mk) orbT.
  by rewrite /j mulnBl pk subKn.
have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
have jqPt : j * q <= pt (y0 + v) by rewrite Hsucc (leq_trans jqp) // leq_addl.
have Hpt : pt (y0 + v + j * u) = pt y0 + m * q.
  by rewrite (pt_add_u iv j_gt0 jqp jqPt) Hsucc -pjq addnBA.
have tI : m * q <= dst y0 by rewrite /m leq_divM.
have Hdst : dst (y0 + v + j * u) = dst y0 - m * q by rewrite (dst_ofD Hpt tI).
have HE : dst y0 - m * q = dst y0 %% q.
  by rewrite {1}(divn_eq (dst y0) q) -/m addnC addnK.
have x0L : y0 + v + j * u < u + (v + p %/ q * u).
  rewrite addnA (leq_ltn_trans (leq_add (leqnn (y0 + v)) 
          (leq_mul jk (leqnn u)))) //.
  by rewrite ltn_add2r ltn_add2r.
have -> : d %% q = dst (y0 + v + j * u).
  by rewrite Hdst HE dB qg -(dst_mod_g y0) -qg.
by apply: leq_inf_dst.
Qed.

(******************************************************************************)
(* Reducing [q] by [k] copies of [p]                                          *)
(******************************************************************************)

(*  [p] is still a point and [q - k*p] still a co-point.                      *)
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
(*    [n < M %/ g] -- and [inv_uv_le] hands that bound to every state         *)
(*    satisfying [inv].  That is why nothing on the [p] side below needs a    *)
(*    range hypothesis.                                                       *)
Lemma ptD_leqM x y :
  0 < x + y < M %/ g -> pt x + pt y <= M -> pt (x + y) = pt x + pt y.
Proof.
move=> xyM; case: ltngtP => // [pxpyLM|pxpyE] _; first exact: ptD.
by have := pt_neq0M xyM; rewrite ptDE pxpyE modnn eqxx.
Qed.

(*  A new index is an old one walked up by [j <= k] copies of [v], and the    *)
(*    walk adds [j*p].                                                        *)
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

(*  The four [invx] fields that do not mention [inf].                         *)
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
(*    [k = q %/ p] the [minn] collapses to [inf %/ p] and the difference to   *)
(*    [inf %% p], which is [inf_new_eq_lt].                                   *)
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

(*  The two halves together.                                                  *)
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
(*    [u], and the walk subtracts [j*q].                                      *)
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

(*  The [invx] fields on the [p] side.  [_p1] cannot read [p - k*q < q] off   *)
(*    the remainder -- at a general [k] that is false -- so it goes through   *)
(*    the OLD [invx_p1] instead: it                                           *)
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

(*  How far the infimum drops when [p] is reduced -- and it is NOT the        *)
(*    mirror of the [q] side.  Property 3 is directional: a [q]-gap splits    *)
(*    into [k] gaps of length [p] then the residual, LEFT TO RIGHT, so every  *)
(*    point walks down by steps of [p]; a [p]-gap splits into the residual    *)
(*    [r = p - k*q] then [k] gaps of length [q], points entering FROM THE     *)
(*    RIGHT.  So here whether the infimum moves at all depends on which gap   *)
(*    [b] sits in, which is what the disjunction records: [inf (u+v) < q]     *)
(*    is the case where [b] is in a [q]-gap and nothing is added below it.    *)
(*    The [if] is what replaces the appeal to [r < q] available only at the   *)
(*    quotient.                                                               *)
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
(*    branch of the disjunction.                                              *)
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

(******************************************************************************)
(* The reduction at the Euclidean quotient                                    *)
(******************************************************************************)

(*  [inv] does not constrain [d].                                             *)
Lemma inv_dW p q d d' u v : inv p q d u v -> inv p q d' u v.
Proof. by case. Qed.

(*  The step preserves [u * p + v * q = M].                                   *)
Lemma step_bez p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in u' * p' + v' * q' = M.
Proof.
move=> iv; rewrite /step; have [pLq|qLp] := ltnP => /=.
  by apply: red_lt_bez iv _; apply: leq_divM.
by apply: red_ge_bez iv _; apply: leq_divM.
Qed.

(*  The step preserves [p = pt v] and [q = M - pt u].                         *)
Lemma step_pt p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in
  0 < p' -> 0 < q' -> (p' = pt v') /\ (q' = M - pt u').
Proof.
move=> iv; rewrite /step; have [pLq|qLp] := ltnP => /= Hp Hq.
  by apply: red_lt_pt iv pLq (leqnn _) Hq.
by apply: red_ge_pt iv qLp (leqnn _) Hp.
Qed.

(*  Both gaps stay positive while the range stays below [N]: a gap reaching   *)
(*    zero would put the counts at [M %/ g], which [N] is below.              *)
Lemma step_p_gt0 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, u', v') := step p q d u v in
  u' + v' < N -> 0 < p' /\ 0 < q'.
Proof.
move=> iv uvLN.
have [p_gt0 q_gt0 bez pE qE gE _ _] := iv.
have Hb := step_bez iv.
move: Hb; rewrite /step.
have [pLq|qLp] := ltnP => /= Hb Huv; split => //.
  case: (posnP (q - q %/ p * p)) => [q0|] //.
  have qme : q - q %/ p * p = q %% p by rewrite {1}(divn_eq q p) addnC addnK.
  have qmp : q %% p = 0 by rewrite -qme q0.
  have pg : p = gcdn A M by rewrite -gE; apply/esym/gcdn_idPl; rewrite /dvdn
    qmp.
  move: Hb; rewrite q0 muln0 addn0 => Hb.
  have Hu : u + q %/ p * v = M %/ p by rewrite -Hb mulnK.
  by move: Huv; rewrite Hu pg ltnNge (leq_trans leq_N_Mg (leq_addr v _)).
have [p0|//] := posnP (p - p %/ q * q).
have pme : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
have pmq : p %% q = 0 by rewrite -pme p0.
have qg : q = g by rewrite -gE gcdnC; apply/esym/gcdn_idPl; rewrite /dvdn pmq.
move: Hb; rewrite p0 muln0 add0n => Hb.
have Hv : v + p %/ q * u = M %/ q by rewrite -Hb mulnK.
by move: Huv; rewrite Hv qg ltnNge (leq_trans leq_N_Mg (leq_addl u _)).
Qed.

(*  The step preserves [inv], given that both new gaps are positive.          *)
Lemma inv_step_pos p q d u v :
  inv p q d u v ->
  let: (p', q', d', u', v') := step p q d u v in
  0 < p' -> 0 < q' -> inv p' q' d' u' v'.
Proof.
move=> iv; rewrite /step; have [pLq|qLp] := ltnP => /= Hp Hq.
  by apply: inv_dW (inv_red_lt iv pLq (leqnn _) Hq).
by apply: inv_dW (inv_red_ge iv qLp (leqnn _) Hp).
Qed.

(*  On the [p < q] branch the whole quotient is taken, so the infimum drops   *)
(*    to its remainder mod [p].                                               *)
Lemma inf_new_eq_lt p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> u + q %/ p * v + v < N ->
  inf (u + q %/ p * v + v) = inf (u + v) %% p.
Proof.
move=> iv ix pLq uvN'.
have IL : inf (u + v) %/ p <= q %/ p.
  apply: leq_div2r; apply: ltnW.
  by rewrite -(maxn_idPr (ltnW pLq)); apply: invx_inf.
rewrite (inf_red_lt iv ix pLq (leqnn _) uvN') (minn_idPr IL).
by rewrite {1}(divn_eq (inf (u + v)) p) addnC addnK.
Qed.

(*  and [invx] survives the step, on either branch.                           *)
Lemma invx_step p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := step p q d u v in
  u' + v' < N -> invx p' q' u' v'.
Proof.
move=> iv ix uvN.
have [_ q_gt0 _ _ _ _ _ _] := iv.
have qM := inv_qM iv.
have Hg := step_p_gt0 iv uvN.
move: Hg; rewrite /step; case: (ltnP p q) => [pLq|qLp] /= Hg uvN'.
  have [_ q'_gt0] := Hg uvN'; split.
  - by apply: invx_red_lt_min iv (invx_min ix) (invx_max ix) pLq (leqnn _) uvN'.
  - by apply: invx_red_lt_max iv (invx_max ix) pLq (leqnn _) uvN'.
  - by rewrite (leq_trans _ qM) // leq_subr.
  - by apply: invx_red_lt_inf iv ix pLq (leqnn _) q'_gt0 uvN'.
  - by apply: invx_red_lt_gap iv ix pLq (leqnn _) q'_gt0 uvN'.
  - by apply: invx_red_lt_p1 iv (invx_max ix) pLq (leqnn _) uvN'.
  by apply: invx_red_lt_p2 iv pLq (leqnn _) q'_gt0.
have [p'_gt0 _] := Hg uvN'; split.
- by apply: invx_red_ge_min iv (invx_min ix) qLp (leqnn _).
- by apply: invx_red_ge_max iv (invx_min ix) (invx_max ix) qLp (leqnn _).
- by apply: qM.
- have k_gt0 : 0 < p %/ q by rewrite divn_gt0.
  by apply: invx_red_ge_inf iv ix qLp k_gt0 (leqnn _).
- by apply: invx_red_ge_gap iv ix qLp (leqnn _) p'_gt0.
- by apply: invx_red_ge_p1 iv ix qLp (leqnn _) p'_gt0.
by apply: invx_red_ge_p2 iv.
Qed.

End Reduce.
