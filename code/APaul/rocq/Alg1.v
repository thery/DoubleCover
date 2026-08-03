(******************************************************************************)
(*                                                                            *)
(*   Lefevre's original lower-bound algorithm                                 *)
(*                                                                            *)
(*   Algorithm 1 of doc/mourad.pdf (hal-00751446, 4.1), which Alg2.v's        *)
(*    Algorithm 2 replaces.  Same specification: with [a = A/M], [b = B/M],   *)
(*    a lower bound on [inf { b - a*x mod 1 | x < N }].                       *)
(*                                                                            *)
(*   A turn is TWO reductions, a division one then a single subtraction,      *)
(*    with the exit test BETWEEN them (lines 7 and 14):                       *)
(*                                                                            *)
(*      branch [d < p]   q -= (q %/ p)*p, u += k*v | exit | p -= q, v += u    *)
(*      branch [p <= d]  d -= p, p -= (p %/ q)*q, v += k*u | exit |           *)
(*                                                          q -= p, u += v    *)
(*                                                                            *)
(*   So [half1] is [Alg2.step] -- the quotient agrees when the branch test    *)
(*    agrees with [p < q] and is [0] otherwise -- and [half2] is the same     *)
(*    reduction at [k = 1], which is Config.v.                                *)
(*                                                                            *)
(*   [d] is the distance from [b] to the nearest point on its left BETWEEN    *)
(*    the halves, where the exit test reads it and the loop returns it.  At   *)
(*    a turn start [half2] has added points and left [d] alone, and what      *)
(*    holds is [invw]: [inf (u + v) = if d < p then d else d - p], with       *)
(*    [d < p + q].  Algorithm 2's [invd] does not hold here.                  *)
(*                                                                            *)
(*   Line 13 of the listing prints as [q <- p - k*q]; it has to be            *)
(*    [p <- p - k*q], else line 15 goes negative.  The [Example]s check it.   *)
(*                                                                            *)
(*   Lines 2 and 11 return Failure early when [d < eps].  [d] never           *)
(*    increases ([leq_run1]), so the loop returns [d] and the test is         *)
(*    [lefevre1_test].                                                        *)
(*                                                                            *)
(*   Companion notes: doc/mourad-notes.md, doc/lefevre-these-notes.md.        *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From APaulRocq Require Import Dist Alg2 Config.

Fixpoint run1 (fuel p q d u v N : nat) : nat :=
  if fuel is fuel1.+1 then
    if d < p then
      let k  := q %/ p in
      let q1 := q - k * p in
      let u1 := u + k * v in
      if N <= u1 + v then d
      else run1 fuel1 (p - q1) q1 d u1 (v + u1) N
    else
      let d1 := d - p in
      let k  := p %/ q in
      let p1 := p - k * q in
      let v1 := v + k * u in
      if N <= u + v1 then d1
      else run1 fuel1 p1 (q - p1) d1 (u + v1) v1 N
  else d.

Definition lefevre1 (M A B N : nat) : nat :=
  run1 M (A %% M) (M - A %% M) (B %% M) 1 1 N.

(*  Sanity checks (computed), on Alg2.v's figures.  [a = 17/45] is the       *)
(*    example of Figure 4.                                                    *)

Example lefevre1_fig4 : lefevre1 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

(*  Alg2.lefevre_strict's case: Algorithm 2 returns 1, the infimum is 2.     *)
Example lefevre1_sharper : (lefevre1 32 23 12 8, lefevre 32 23 12 8) = (2, 1).
Proof. by vm_compute. Qed.

(*  Not exact in general: both return 0 and the infimum is 1.                *)
Example lefevre1_strict : (lefevre1 5 2 3 4, inf_dst 5 2 3 4) = (0, 1).
Proof. by vm_compute. Qed.

(******************************************************************************)
(* The theory                                                                 *)
(******************************************************************************)

Section Theory.

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
Local Notation invd := (invd M A B).
Local Notation invx := (invx M A B).

Local Notation ltn_pt := (ltn_pt M_gt0 A).
Local Notation pt0 := (pt0 M A).
Local Notation ltn_dst := (ltn_dst M_gt0 A B).
Local Notation dst0 := (dst0 A ltn_B).
Local Notation dstE := (dstE M A B).
Local Notation inf0 := (inf0 M A B).
Local Notation infSE := (infSE M A B).
Local Notation leq_inf_dst := (leq_inf_dst M A B).
Local Notation leq_inf_mono := (leq_inf_mono M A B).
Local Notation inf_ex := (inf_ex M_gt0 A B).
Local Notation leq_N_Mg := (leq_N_Mg N_lt_Mg).
Local Notation dst_diff := (dst_diff M_gt0 A B).
Local Notation dst_ofD := (dst_ofD ltn_B).
Local Notation dst_gap_up := (@dst_gap_up M M_gt0 A B).
Local Notation gap_walk := (@gap_walk M M_gt0 A B).
Local Notation gap_bounds := (@gap_bounds M).
Local Notation pt_neq0 := (pt_neq0 M_gt0 N_lt_Mg).
Local Notation pt_neq0M := (pt_neq0M M_gt0).
Local Notation red_ge_pt := (@red_ge_pt M M_gt0 A B ltn_B).
Local Notation inv_uv_le := (@inv_uv_le M A).

Local Notation step_p_gt0 := (@step_p_gt0 M A N N_lt_Mg).
Local Notation inv_step_pos := (@inv_step_pos M M_gt0 A B ltn_B).
Local Notation inf_new_eq_lt := (@inf_new_eq_lt M M_gt0 A B N).

Local Notation inv_red_lt := (@inv_red_lt M A B ltn_B).
Local Notation inv_red_ge := (@inv_red_ge M M_gt0 A B ltn_B).
Local Notation inf_red_lt_le := (@inf_red_lt_le M M_gt0 A B).
Local Notation inf_red_lt_ge := (@inf_red_lt_ge M M_gt0 A B).
Local Notation inv_init := (@inv_init M M_gt0 A B ltn_A N N_gt0 N_lt_Mg).
Local Notation invx_init := (@invx_init M M_gt0 A B ltn_A ltn_B).
Local Notation inv_qM := (@inv_qM M A).
Local Notation invx_red_lt_min := (@invx_red_lt_min M M_gt0 A N N_lt_Mg).
Local Notation invx_red_lt_max := (@invx_red_lt_max M M_gt0 A N N_lt_Mg).
Local Notation invx_red_lt_p1 := (@invx_red_lt_p1 M M_gt0 A N N_lt_Mg).
Local Notation invx_red_lt_p2 := (@invx_red_lt_p2 M M_gt0 A B ltn_B).
Local Notation invx_red_lt_inf := (@invx_red_lt_inf M M_gt0 A B N).
Local Notation invx_red_lt_gap :=
  (@invx_red_lt_gap M M_gt0 A B ltn_B N N_lt_Mg).
Local Notation invx_step := (@invx_step M M_gt0 A B ltn_B N N_lt_Mg).
Local Notation gap_q_empty := (@gap_q_empty M M_gt0 A B).
Local Notation gap_p_empty := (@gap_p_empty M M_gt0 A B).
Local Notation walk_lt_nowrap := (@walk_lt_nowrap M M_gt0 A B).
Local Notation walk_ge_nowrap := (@walk_ge_nowrap M M_gt0 A B).
Local Notation ge_exit := (@ge_exit M M_gt0 A B ltn_B).
Local Notation red_ge_new := (@red_ge_new M M_gt0 A).
Local Notation invx_red_ge_min := (@invx_red_ge_min M M_gt0 A).
Local Notation invx_red_ge_max := (@invx_red_ge_max M M_gt0 A).
Local Notation invx_red_ge_p2 := (@invx_red_ge_p2 M M_gt0 A).
Local Notation invx_red_ge_p1 := (@invx_red_ge_p1 M M_gt0 A B ltn_B).
Local Notation invx_red_ge_inf := (@invx_red_ge_inf M M_gt0 A B ltn_B).
Local Notation invx_red_ge_gap := (@invx_red_ge_gap M M_gt0 A B ltn_B).

Definition half1 (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if d < p then
    let k := q %/ p in (p, q - k * p, d, u + k * v, v)
  else
    let k := p %/ q in (p - k * q, q, d - p, u, v + k * u).

Definition half2 (b : bool) (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if b then (p - q, q, d, u, v + u) else (p, q - p, d, u + v, v).

(*  The two gaps are never equal while the loop runs: [p = q] forces          *)
(*    [u + v = M %/ g], which is past [N].                                    *)
Lemma inv_pq_neq p q d u v : inv p q d u v -> u + v < N -> p != q.
Proof.
move=> iv uvN; apply/eqP => pqE.
have [p_gt0 q_gt0 bez _ _ gE _ _] := iv.
have gp : g = p by rewrite -gE pqE gcdnn.
have Hm : (u + v) * p = M by rewrite mulnDl {2}pqE.
have Huv : u + v = M %/ g by rewrite gp -Hm mulnK.
by move: uvN; rewrite Huv ltnNge leq_N_Mg.
Qed.

(*  [inv] does not constrain [d], so it transfers across the two halves'      *)
(*    differing [d] components.                                               *)
Lemma inv_dW p q d d' u v : inv p q d u v -> inv p q d' u v.
Proof. by case. Qed.

(*  The point [b] sits above attains the infimum: [Alg2.gap_p_empty] and     *)
(*    [gap_q_empty] make it a lower bound, [leq_inf_dst] an equation.         *)
Lemma inv_qqM p q d u v : inv p q d u v -> q <= p -> q + q <= M.
Proof.
case=> p_gt0 q_gt0 bez _ _ _ u_gt0 v_gt0 qLp.
rewrite -bez (leq_trans (leq_add qLp (leqnn q))) // leq_add //.
  by rewrite leq_pmull.
by rewrite leq_pmull.
Qed.

(*  Distances are distinct below [N], so that point is unique.               *)
Lemma dst_inj x y : x <= N -> y <= N -> dst x = dst y -> x = y.
Proof.
wlog yx : x y / y <= x => [H xN yN dE|].
  case: (leqP y x) => [yx|xy]; first by apply: H.
  by apply/esym; apply: H => //; apply: ltnW.
move=> xN yN dE; have := dst_diff yx; rewrite -dE => HE.
have ptE : pt (x - y) = 0.
  have dM : dst y < M := ltn_dst _.
  have pM : pt (x - y) < M := ltn_pt _.
  case: (ltnP (dst y + pt (x - y)) M) => [dpM|Mdp].
    move: HE; rewrite modn_small; last by rewrite dE.
    by rewrite -{1}[dst x]addn0 => /addnI.
  rewrite dE in HE; move: HE; rewrite -(subnK Mdp) modnDr modn_small;
      last first.
    by rewrite ltn_subLR //
       (leq_ltn_trans (leq_add (ltnW dM) (leqnn (pt (x - y))))) // ltn_add2l.
  move=> /eqP; rewrite -(eqn_add2r M) subnK // eqn_add2l => /eqP ME.
  by move: pM; rewrite -ME ltnn.
apply/eqP; rewrite eqn_leq yx andbT leqNgt; apply/negP => yLx.
have H : 0 < x - y <= N by rewrite subn_gt0 yLx (leq_trans (leq_subr _ _)).
by have := pt_neq0 H; rewrite ptE eqxx.
Qed.

(*  [b] lies inside the gap of the point below it, so its distance is below  *)
(*    that gap's length.                                                      *)
Lemma argmin_lt_p p q d u v y0 :
  inv p q d u v -> invx p q u v -> y0 < u -> inf (u + v) = dst y0 ->
  dst y0 < p.
Proof.
move=> iv ix y0u Hy0; have [p_gt0 _ _ _ _ _ _ _] := iv.
rewrite ltnNge; apply/negP => pDy0.
have Hsucc : pt (y0 + v) = pt y0 + p by apply: (invx_p1 ix).
have Hdd := dst_ofD Hsucc pDy0.
have Hle : inf (u + v) <= dst (y0 + v) by apply: leq_inf_dst; rewrite ltn_add2r.
by move: Hle; rewrite Hdd Hy0 leqNgt ltn_subrL p_gt0 (leq_trans p_gt0 pDy0).
Qed.

(*  [q + q <= M] rather than [q <= p], which a reduced configuration lacks.  *)
Lemma inf_at_q p q d u v w :
  inv p q d u v -> invx p q u v -> q + q <= M -> u <= w -> w < u + v ->
  dst w < q -> inf (u + v) = dst w.
Proof.
move=> iv ix qqM uw wL qDw; apply/eqP; rewrite eqn_leq (leq_inf_dst wL) /=.
apply: leq_inf; first by apply: ltnW; exact: ltn_dst.
by move=> z zL; apply: (gap_q_empty iv (invx_max ix) qqM uw wL zL qDw).
Qed.

(*  The [w < u] analogue of [Alg2.gap_p_empty], whose [p <= q] covers only   *)
(*    the case where [w]'s gap is the smaller one.  Its [z < w] case is the   *)
(*    only one that differs: [Alg2.gap_walk] is the tiling, and               *)
(*    [dst w - dst z < p] forces [a = 0] there, so the index equation gives   *)
(*    [w = z] or [w >= u], both excluded.                                     *)
Lemma gap_pu_down p q d u v w z :
  inv p q d u v -> invx p q u v -> w < u -> z < w -> dst z <= dst w ->
  dst w < p -> False.
Proof.
move=> iv ix wu zw Dzw pDw.
have [p_gt0 q_gt0 bez _ _ _ u_gt0 v_gt0] := iv.
have wL : w < u + v by rewrite (leq_trans wu) // leq_addr.
have zL : z < u + v by rewrite (ltn_trans zw).
have [a [b [Hval Hix]]] :=
  gap_walk (n := dst w - dst z) iv (invx_min ix) (invx_max ix) wL zL Dzw
           (leqnn _).
have Hlt : a * p + b * q < M.
  by rewrite Hval (leq_ltn_trans (leq_subr _ _)) // ltn_dst.
have [aLu bLv] := gap_bounds u_gt0 v_gt0 bez wL zL Hix Hlt.
have a0 : a = 0.
  case: a Hval Hix aLu Hlt => // a Hval _ _ _.
  have : p <= dst w - dst z.
    by rewrite -Hval (leq_trans _ (leq_addr _ _)) // -{1}[p]mul1n leq_mul2r
       orbT.
  by rewrite leqNgt (leq_ltn_trans (leq_subr _ _) pDw).
move: Hix; rewrite a0 mul0n add0n => Hix.
have [b0|b_gt0] := posnP b.
  by move: zw; rewrite b0 mul0n add0n in Hix; rewrite -Hix ltnn.
move: wu; rewrite Hix ltnNge => /negP[].
by rewrite (leq_trans (leq_pmull u b_gt0)) // leq_addr.
Qed.

Lemma gap_pu_empty p q d u v w z :
  inv p q d u v -> invx p q u v -> w < u -> z < u + v -> dst w < p ->
  dst w <= dst z.
Proof.
move=> iv ix wu zL pDw; case: leqP => // Dzw.
have wL : w < u + v by rewrite (leq_trans wu) // leq_addr.
have zDw : dst z <= dst w := ltnW Dzw.
have [wz|zw] := ltnP w z; last first.
  have zNw : z != w by apply/eqP => zw'; move: Dzw; rewrite zw' ltnn.
  have zLw : z < w by rewrite ltn_neqAle zNw zw.
  by case: (gap_pu_down iv ix wu zLw zDw pDw).
(* the [w < z] half is [Alg2.gap_p_empty]'s, and runs on [invx_min] alone *)
have Hd := dst_gap_up (ltnW wz) zDw.
have Hk : p <= pt (z - w).
  by apply: (invx_min ix); rewrite subn_gt0 wz (leq_ltn_trans (leq_subr _ _)).
move: Hk; rewrite -(leq_add2r (dst z)) Hd => H.
by move: pDw; rewrite ltnNge (leq_trans _ H) // leq_addr.
Qed.

Lemma inf_at_pu p q d u v w :
  inv p q d u v -> invx p q u v -> w < u -> dst w < p -> inf (u + v) = dst w.
Proof.
move=> iv ix wu pDw.
have wL : w < u + v by rewrite (leq_trans wu) // leq_addr.
apply/eqP; rewrite eqn_leq (leq_inf_dst wL) /=.
apply: leq_inf; first by apply: ltnW; exact: ltn_dst.
by move=> z zL; apply: (gap_pu_empty iv ix wu zL pDw).
Qed.

Record invw (p q d u v : nat) := Invw {
  invw_max : d < p + q;
  invw_inf : inf (u + v) = if d < p then d else d - p;
  invw_gap : u + v <= N ->
             forall y, y < u + v -> inf (u + v) = dst y -> (y < u) = (d < p)
}.

(*  At the start [u = v = 1], so the configuration is the two points [0] and  *)
(*    [1] and the infimum is [B] or [B - A %% M], which is exactly what the   *)
(*    branch test picks out.                                                  *)
Lemma invw_init_inf :
  inf (1 + 1) = if B %% M < A %% M then B %% M else B %% M - A %% M.
Proof.
have am : A %% M < M by rewrite ltn_mod.
have bm : B %% M = B by apply: modn_small.
have pt1 : pt 1 = A %% M by rewrite /Dist.pt muln1.
rewrite !infSE inf0 dst0 dstE pt1.
have [BLa|aLB] := ltnP B (A %% M).
  rewrite bm ifT // (minn_idPl (ltnW ltn_B)).
  have -> : (B + M - A %% M) %% M = B + M - A %% M.
    apply: modn_small.
    rewrite ltn_subLR ?ltn_add2r //.
    by rewrite (leq_trans (ltnW am)) // leq_addl.
  apply/minn_idPr; rewrite -{1}[B]addn0 -addnBA ?leq_addr //.
    by rewrite leq_add2l.
  by apply: ltnW.
rewrite bm ifN -?leqNgt // (minn_idPl (ltnW ltn_B)).
have -> : (B + M - A %% M) %% M = B - A %% M.
  by rewrite -addnBAC // modnDr modn_small // (leq_ltn_trans (leq_subr _ _)).
by apply/minn_idPl; rewrite leq_subr.
Qed.

(*  and the two points are distinct, so the argmin is the one the test        *)
(*    names: [0] when [d < p], [1] otherwise.                                 *)
Lemma invw_init_gap :
  1 + 1 <= N ->
  forall y, y < 1 + 1 -> inf (1 + 1) = dst y -> (y < 1) = (B %% M < A %% M).
Proof.
move=> N2 y yL yE.
have bm : B %% M = B by apply: modn_small.
have yN : y <= N by apply: ltnW; exact: leq_trans yL N2.
have Hi := invw_init_inf.
have [BLa|aLB] := ltnP (B %% M) (A %% M).
  have -> : y = 0.
    apply: dst_inj yN (leq0n N) _.
    by rewrite -yE Hi ifT // bm dst0.
  by [].
have amB : A %% M <= B by rewrite -bm.
have d1 : dst 1 = B - A %% M.
  rewrite dstE /Dist.pt muln1 -addnBAC // modnDr modn_small //.
  by rewrite (leq_ltn_trans (leq_subr _ _)).
have -> : y = 1.
  apply: dst_inj yN (leq_trans _ N2) _ => //.
  by rewrite -yE Hi ifN -?leqNgt // bm d1.
by rewrite ltnn.
Qed.

Lemma invw_init : invw (A %% M) (M - A %% M) (B %% M) 1 1.
Proof.
have am : A %% M < M by rewrite ltn_mod.
have bm : B %% M = B by apply: modn_small.
split; [by rewrite subnKC ?bm // ltnW| |exact: invw_init_gap].
by rewrite invw_init_inf bm.
Qed.

(*  [half1] is [Alg2.step] whenever the branch test agrees with [p < q]: same *)
(*    quotient, same counts.  When they disagree the quotient is [0] and      *)
(*    [half1] leaves the configuration alone.                                 *)
Lemma inv_half1 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, u', v') := half1 p q d u v in
  u' + v' < N -> inv p' q' d u' v'.
Proof.
move=> iv uvN.
have pqN := inv_pq_neq iv uvN.
have Hg := step_p_gt0 iv uvN.
have Hi := inv_step_pos iv.
rewrite /half1; case: (ltnP d p) => [dLp|pLd].
  case: (ltnP p q) => [pLq|qLp] /=.
    move: Hg Hi; rewrite /step ifT // => Hg Hi Huv.
    have [Hp Hq] := Hg Huv.
    by apply: inv_dW (Hi Hp Hq).
  have qLp' : q < p by rewrite ltn_neqAle qLp andbT eq_sym.
  by rewrite (divn_small qLp') mul0n subn0 addn0.
case: (ltnP p q) => [pLq|qLp] /=.
  by rewrite (divn_small pLq) mul0n subn0 addn0.
move: Hg Hi; rewrite /step ifN -?leqNgt // => Hg Hi Huv.
have [Hp Hq] := Hg Huv.
by apply: inv_dW (Hi Hp Hq).
Qed.

(*  [half2] is the same reduction with [k = 1], which is what Config.v is     *)
(*    for.  Stated on its own two shapes rather than through [half2], so      *)
(*    that each carries only the hypothesis it needs.                         *)
Lemma inv_sub_p p q d u v : inv p q d u v -> q < p -> inv (p - q) q d u (v + u).
Proof.
move=> iv qLp; have [_ q_gt0 _ _ _ _ _ _] := iv.
have k1 : 1 <= p %/ q by rewrite divn_gt0 //; apply: ltnW.
have p1 : 0 < p - 1 * q by rewrite mul1n subn_gt0.
by have H := inv_red_ge iv (ltnW qLp) k1 p1; rewrite !mul1n in H.
Qed.

Lemma inv_sub_q p q d u v : inv p q d u v -> p < q -> inv p (q - p) d (u + v) v.
Proof.
move=> iv pLq; have [p_gt0 _ _ _ _ _ _ _] := iv.
have k1 : 1 <= q %/ p by rewrite divn_gt0 //; apply: ltnW.
have q1 : 0 < q - 1 * p by rewrite mul1n subn_gt0.
by have H := inv_red_lt iv pLq k1 q1; rewrite !mul1n in H.
Qed.

(*  One turn strictly shrinks [p + q]: it comes out as [p] resp. [q].         *)
Lemma run1_measure p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p1, q1, d1, u1, v1) := half1 p q d u v in
  let: (p', q', _, _, _) := half2 (d < p) p1 q1 d1 u1 v1 in
  p' + q' < p + q.
Proof.
move=> iv uvN.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have pqN := inv_pq_neq iv uvN.
rewrite /half1 /half2; case: (ltnP d p) => [dLp|pLd] /=.
  have q1Lp : q - q %/ p * p < p.
    have [pLq|qLp] := ltnP p q; first by apply: q'_lt_p.
    have qLp' : q < p by rewrite ltn_neqAle qLp andbT eq_sym.
    by rewrite (divn_small qLp') mul0n subn0.
  by rewrite (subnK (ltnW q1Lp)) -{1}[p]addn0 ltn_add2l.
have p1Lq : p - p %/ q * q < q.
  have [pLq|qLp] := ltnP p q; last by apply: q'_lt_p.
  by rewrite (divn_small pLq) mul0n subn0.
by rewrite (subnKC (ltnW p1Lq)) -{1}[q]add0n ltn_add2r.
Qed.

(*  [d] never increases: it is only ever reduced by [p], in [half1].          *)
Lemma leq_run1 fuel p q d u v : run1 fuel p q d u v N <= d.
Proof.
elim: fuel p q d u v => //= fuel IH p q d u v.
case: (d < p); first by case: (N <= _) => //; apply: IH.
case: (N <= _); first by apply: leq_subr.
by apply: leq_trans (IH _ _ _ _ _) (leq_subr _ _).
Qed.

(*  and the sharper form, which is what the exit test returns: the loop       *)
(*    returns at most the [d] that [half1] leaves behind.                     *)
Lemma run1_decr fuel p q d u v :
  0 < fuel -> run1 fuel p q d u v N <= (if d < p then d else d - p).
Proof.
case: fuel => // fuel _ /=.
case: (d < p); first by case: (N <= _) => //; apply: leq_run1.
by case: (N <= _) => //; apply: leq_run1.
Qed.

(******************************************************************************)
(* Where [d] is the distance: between the halves                              *)
(******************************************************************************)

(*  [half1] does not move the infimum.  In this branch [invw] says [d] is     *)
(*    already the infimum, so it is below [p] and [Alg2.inf_new_eq_lt]'s      *)
(*    [Inf %% p] is [Inf] itself.                                             *)
Lemma half1_inf_lt p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> d < p ->
  u + q %/ p * v + v < N ->
  inf (u + q %/ p * v + v) = inf (u + v).
Proof.
move=> iv ix iw uvN dLp uvN'.
have infE : inf (u + v) = d by have := invw_inf iw; rewrite ifT.
have [pLq|qLp] := ltnP p q.
  by rewrite (inf_new_eq_lt iv ix pLq uvN') infE modn_small.
have pqN := inv_pq_neq iv uvN.
have qLp' : q %/ p = 0 by rewrite divn_small // ltn_neqAle qLp andbT eq_sym.
by rewrite qLp' mul0n addn0.
Qed.

(*  [b] is in a [q]-gap here ([invw] gives [Inf = d - p] and [Inf < q]), and *)
(*    reducing [p] splits [p]-gaps only, so [Inf] cannot drop.  Stated as one *)
(*    inequality with no bound on the new range, so it serves the exit too.   *)
Lemma half1_ge_nodrop p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> p <= d ->
  u + (v + p %/ q * u) < N ->
  inf (u + v) <= inf (u + (v + p %/ q * u)).
Proof.
move=> iv ix iw uvN pLd uvN'.
have [p_gt0 q_gt0 bez pE qE gE u_gt0 v_gt0] := iv.
have [pLq|qLp] := ltnP p q; first by rewrite (divn_small pLq) mul0n addn0.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Hy0] := inf_ex uv_gt0.
(* [invw_gap]: the test is false, so [b] is in a [q]-gap *)
have uy0 : u <= y0.
  by rewrite leqNgt (invw_gap iw (ltnW uvN) y0L Hy0) ltnNge pLd.
(* and [b] is inside it: [invw_max] gives [d - p < q] *)
have dy0q : dst y0 < q.
  rewrite -Hy0 (invw_inf iw) ifN -?leqNgt //.
  by rewrite ltn_subLR //; exact: invw_max iw.
have qqM : q + q <= M.
  rewrite -bez (leq_trans (leq_add qLp (leqnn q))) // leq_add //.
    by rewrite leq_pmull.
  by rewrite leq_pmull.
(* the reduced configuration, which needs both gaps positive *)
have Hg := step_p_gt0 iv uvN.
move: Hg; rewrite /step ifN -?leqNgt // => Hg.
have [Hp Hq] := Hg uvN'.
have iv' := inv_red_ge iv qLp (leqnn (p %/ q)) Hp.
have Hmax' := invx_red_ge_max iv (invx_min ix) (invx_max ix) qLp
                              (leqnn (p %/ q)).
have y0L' : y0 < u + (v + p %/ q * u).
  by rewrite (leq_trans y0L) // leq_add2l leq_addr.
apply: leq_inf; first by rewrite Hy0; apply: ltnW; exact: ltn_dst.
move=> z zL; rewrite Hy0.
exact: (gap_q_empty iv' Hmax' qqM uy0 y0L' zL dy0q).
Qed.

(*  so [half1] does not move [Inf] in this branch either.                     *)
Lemma half1_inf_ge p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> p <= d ->
  u + (v + p %/ q * u) < N ->
  inf (u + (v + p %/ q * u)) = inf (u + v).
Proof.
move=> iv ix iw uvN pLd uvN'; apply/eqP; rewrite eqn_leq.
rewrite (half1_ge_nodrop iv ix iw uvN pLd uvN') andbT.
by apply: leq_inf_mono; rewrite leq_add2l leq_addr.
Qed.

(*  and it leaves [b] where it was: in the [d < p] branch it splits           *)
(*    [q]-gaps, so a [b] in a [p]-gap keeps its neighbour below.  Property 3  *)
(*    again, and what [invw_sub_p_*] above ask for.                           *)
Lemma half1_gap_lt p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> d < p ->
  u + q %/ p * v + v < N ->
  forall y, y < u + q %/ p * v + v -> inf (u + q %/ p * v + v) = dst y ->
  y < u + q %/ p * v.
Proof.
move=> iv ix iw uvN dLp uvN' y yL yE.
have [_ _ _ _ _ _ u_gt0 _] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Hy0] := inf_ex uv_gt0.
have y0u : y0 < u by rewrite (invw_gap iw (ltnW uvN) y0L Hy0).
have dEq : dst y = dst y0.
  by rewrite -yE -Hy0 (half1_inf_lt iv ix iw uvN dLp uvN').
have yN : y <= N by apply: ltnW; exact: ltn_trans yL uvN'.
have y0N : y0 <= N by apply: ltnW; exact: ltn_trans y0L uvN.
have -> : y = y0 by apply: dst_inj yN y0N dEq.
by rewrite (leq_trans y0u) // leq_addr.
Qed.

(*  Between the halves, [d] is exactly the infimum -- which is what 4.1 says  *)
(*    [d] is, and it is true HERE, not at the top of the loop.                *)
Lemma half1_exact p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N ->
  let: (_, _, d', u', v') := half1 p q d u v in
  u' + v' < N -> d' = inf (u' + v').
Proof.
move=> iv ix iw uvN; rewrite /half1; case: (ltnP d p) => [dLp|pLd] /= uvN'.
  by rewrite (half1_inf_lt iv ix iw uvN dLp uvN'); have := invw_inf iw;
     rewrite ifT.
by rewrite (half1_inf_ge iv ix iw uvN pLd uvN'); have := invw_inf iw;
   rewrite ifN // -leqNgt.
Qed.

(******************************************************************************)
(* [half2] puts the invariant back                                            *)
(******************************************************************************)

(*  [half2] adds points and leaves [d] alone, so it is where the infimum      *)
(*    drops -- by nothing, or by the new [p].  That is the [k = 1] case of    *)
(*    Config.v's reduction, and the reason [invw] is stated with a test       *)
(*    rather than an equation.                                                *)
Lemma invx_sub_p p q d u v :
  inv p q d u v -> invx p q u v -> q < p -> invx (p - q) q u (v + u).
Proof.
move=> iv ix qLp; have [_ q_gt0 _ _ _ _ _ _] := iv.
have k1 : 1 <= p %/ q by rewrite divn_gt0 //; apply: ltnW.
have p1 : 0 < p - 1 * q by rewrite mul1n subn_gt0.
split.
- by have H := invx_red_ge_min iv (invx_min ix) (ltnW qLp) k1;
     rewrite !mul1n in H.
- by have H := invx_red_ge_max iv (invx_min ix) (invx_max ix) (ltnW qLp) k1;
     rewrite !mul1n in H.
- exact: inv_qM iv.
- by have H := invx_red_ge_inf (k := 1) iv ix (ltnW qLp) isT k1;
     rewrite !mul1n in H.
- by have H := invx_red_ge_gap iv ix (ltnW qLp) k1 p1; rewrite !mul1n in H.
- by have H := invx_red_ge_p1 iv ix (ltnW qLp) k1 p1; rewrite !mul1n in H.
by have H := invx_red_ge_p2 (k := 1) iv; rewrite !mul1n in H.
Qed.

(*  [ptD_leq] with the orbit bound: its [<= N] only feeds [pt_neq0], and     *)
(*    [Alg2.inv_uv_le] bounds every [inv] state by [M %/ g].                  *)
Lemma ptD_leqM x y :
  0 < x + y < M %/ g -> pt x + pt y <= M -> pt (x + y) = pt x + pt y.
Proof.
move=> xyM; case: ltngtP => // [pxpyLM|pxpyE] _; first exact: ptD.
by have := pt_neq0M xyM; rewrite ptDE pxpyE modnn eqxx.
Qed.

(*  The point entering [b]'s gap from the right, and its distance.           *)
Lemma sub_p_new_dst p q d u v y0 :
  inv p q d u v -> invx p q u v -> q < p -> y0 < u -> p - q <= dst y0 ->
  dst (y0 + (v + u)) = dst y0 - (p - q).
Proof.
move=> iv ix qLp y0u pqD.
have [_ q_gt0 _ _ _ _ _ v_gt0] := iv.
have k1 : 1 <= p %/ q by rewrite divn_gt0 //; apply: ltnW.
have p1 : 0 < p - 1 * q by rewrite mul1n subn_gt0.
have iv' : inv (p - q) q d u (v + u).
  by have H := inv_red_ge iv (ltnW qLp) k1 p1; rewrite !mul1n in H.
have Huv := inv_uv_le iv'.
have [pE' _] := red_ge_pt iv (ltnW qLp) k1 p1.
rewrite !mul1n in pE'.
have Hlt : y0 + (v + u) < M %/ g by apply: leq_trans Huv; rewrite ltn_add2r.
have Hsucc : pt (y0 + (v + u)) = pt y0 + (p - q).
  rewrite [in RHS]pE'; apply: ptD_leqM.
    by rewrite Hlt andbT addn_gt0 orbC addn_gt0 v_gt0.
  rewrite -pE' (leq_trans (leq_add (leqnn (pt y0)) (leq_subr q p))) //.
  by rewrite -(invx_p1 ix y0u); apply: ltnW; exact: ltn_pt.
by rewrite (dst_ofD Hsucc).
Qed.

(*  After the reduction the point below [b] is the one it had, or the one    *)
(*    that entered from the right.  Both [_inf] and [_gap] read off it.       *)
Lemma sub_p_argmin p q d u v y0 :
  inv p q d u v -> invx p q u v -> q < p -> d = inf (u + v) -> d < p ->
  y0 < u -> inf (u + v) = dst y0 ->
  inf (u + (v + u)) = dst (if d < p - q then y0 else y0 + (v + u)) /\
  inf (u + (v + u)) = (if d < p - q then d else d - (p - q)).
Proof.
move=> iv ix qLp dE dLp y0u Hy0.
have [_ q_gt0 _ _ _ _ _ _] := iv.
have k1 : 1 <= p %/ q by rewrite divn_gt0 //; apply: ltnW.
have p1 : 0 < p - 1 * q by rewrite mul1n subn_gt0.
have iv' : inv (p - q) q d u (v + u).
  by have H := inv_red_ge iv (ltnW qLp) k1 p1; rewrite !mul1n in H.
have ix' : invx (p - q) q u (v + u) := invx_sub_p iv ix qLp.
have dy0 : dst y0 = d by rewrite -Hy0 -dE.
have [dLpq|pqLd] := ltnP d (p - q).
  have Hinf : inf (u + (v + u)) = dst y0.
    by apply: (inf_at_pu iv' ix' y0u); rewrite dy0.
  by split; [exact: Hinf | rewrite Hinf dy0].
have Hd : dst (y0 + (v + u)) = d - (p - q).
  by rewrite (sub_p_new_dst iv ix qLp y0u) ?dy0.
have Hinf : inf (u + (v + u)) = dst (y0 + (v + u)).
  apply: (inf_at_q iv' ix' (inv_qqM iv (ltnW qLp))).
  - exact: leq_trans (leq_addl v u) (leq_addl y0 (v + u)).
  - by rewrite ltn_add2r.
  rewrite Hd ltn_subLR // (leq_trans dLp) //.
  by rewrite -{1}(subnK (ltnW qLp)) leq_add2l.
by split; [exact: Hinf | rewrite Hinf Hd].
Qed.

(*  A new index is [y + j*u] ([Config.red_ge_new]); the walk adds [j*q] to   *)
(*    the distance unless it wraps, and [gap_q_empty] on the reduced          *)
(*    configuration covers both.                                              *)
Lemma ge_wrap_dst p q d u v y j y0 :
  inv p q d u v -> invx p q u v -> q <= p -> 0 < p - p %/ q * q ->
  y0 < u + v -> inf (u + v) = dst y0 -> u <= y0 -> inf (u + v) < q ->
  y < u + v -> 0 < j <= p %/ q -> inf (u + v) <= dst (y + j * u).
Proof.
move=> iv ix qLp p'_gt0 y0L Hy0 uy0 Iq yL /andP[j_gt0 jk2].
have iv' := inv_red_ge iv qLp (leqnn (p %/ q)) p'_gt0.
have Hmax' := invx_red_ge_max iv (invx_min ix) (invx_max ix) qLp (leqnn _).
have y0L' : y0 < u + (v + p %/ q * u).
  by rewrite (leq_trans y0L) // leq_add2l leq_addr.
have yjL : y + j * u < u + (v + p %/ q * u).
  rewrite addnA (leq_ltn_trans (leq_add (leqnn y) (leq_mul jk2 (leqnn u)))) //.
  by rewrite ltn_add2r.
rewrite Hy0; apply: (gap_q_empty iv' Hmax' (inv_qqM iv qLp) uy0 y0L' yjL).
by rewrite -Hy0.
Qed.

(*  The degenerate case [q] divides [p], where the reduction leaves no       *)
(*    two-length configuration: [Alg2.ge_exit] is stated for it.              *)
Lemma ge_wrap_deg p q d u v y j :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> p <= d ->
  p - p %/ q * q = 0 -> y < u + v -> 0 < j <= p %/ q ->
  inf (u + v) <= dst (y + j * u).
Proof.
move=> iv ix iw uvN pLd p'0 yL jk.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have qLp : q <= p.
  rewrite leqNgt; apply/negP => pLq.
  by move: p'0 p_gt0; rewrite (divn_small pLq) mul0n subn0 => ->.
have Iq : inf (u + v) < q.
  rewrite (invw_inf iw) ifN -?leqNgt //.
  by rewrite ltn_subLR //; exact: invw_max iw.
have [Hnw|Hw] := ltnP (dst y + j * q) M.
  rewrite (walk_ge_nowrap iv qLp yL jk Hnw).
  by rewrite (leq_trans _ (leq_addr _ _)) // leq_inf_dst.
have ivd : invd p q (inf (u + v)) u v.
  by split => //; exact: (invx_inf ix).
have [H1 _] := ge_exit (inv_dW (inf (u + v)) iv) ivd ix qLp p'0.
have := H1 y j yL jk Hw.
by rewrite p'0 leq0n subn0 modn_small.
Qed.

Lemma ge_new_dst p q d u v z :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> p <= d ->
  u + v <= z -> z < u + (v + p %/ q * u) -> inf (u + v) <= dst z.
Proof.
move=> iv ix iw uvN pLd zge zlt.
have [pLq|qLp] := ltnP p q.
  by move: zlt; rewrite (divn_small pLq) mul0n addn0 ltnNge zge.
have [_ _ _ _ _ _ u_gt0 _] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Hy0] := inf_ex uv_gt0.
have [j jk [yb jqP Hm]] := red_ge_new iv (invx_min ix) qLp (leqnn _) zge zlt.
have /andP[y_gt0 ylt] := yb.
have jul : j * u <= z by apply: ltnW; rewrite -subn_gt0.
have zE : z = z - j * u + j * u by rewrite subnK.
have [p'0|p'_gt0] := posnP (p - p %/ q * q).
  by rewrite zE; apply: ge_wrap_deg iv ix iw uvN pLd p'0 ylt jk.
have uy0 : u <= y0.
  by rewrite leqNgt (invw_gap iw (ltnW uvN) y0L Hy0) ltnNge pLd.
have Iq : inf (u + v) < q.
  rewrite (invw_inf iw) ifN -?leqNgt //.
  by rewrite ltn_subLR //; exact: invw_max iw.
by rewrite zE; apply: ge_wrap_dst iv ix qLp p'_gt0 y0L Hy0 uy0 Iq ylt jk.
Qed.

(*  Reducing [p] splits [p]-gaps, into [p - q] on the left and [q] on the    *)
(*    right (Property 3: the residual is leftmost, points enter from the      *)
(*    right).  So these two need to know that [b] is in a [p]-gap: for a [b]  *)
(*    in an untouched [q]-gap all one gets is [Inf < q], which says nothing   *)
(*    about the new test [d < p - q].  In the loop [b] IS in a [p]-gap here,  *)
(*    the turn having taken the [d < p] branch, and [half1] splits only       *)
(*    [q]-gaps there -- that is [half1_gap_lt].                               *)
(*                                                                            *)
(*  This is the paper's row 6: [b] is in an interval of length [p], points    *)
(*    enter it from the right one by one, so the last one added is the        *)
(*    nearest below [b] and [d] loses the new [p].                            *)
Lemma invw_sub_p_inf p q d u v :
  inv p q d u v -> invx p q u v -> q < p -> d = inf (u + v) -> d < p ->
  (forall y, y < u + v -> inf (u + v) = dst y -> y < u) ->
  inf (u + (v + u)) = (if d < p - q then d else d - (p - q)).
Proof.
move=> iv ix qLp dE dLp pg.
have [_ _ _ _ _ _ u_gt0 _] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Hy0] := inf_ex uv_gt0.
by have [_ ->] := sub_p_argmin iv ix qLp dE dLp (pg _ y0L Hy0) Hy0.
Qed.

Lemma invw_sub_p_gap p q d u v :
  inv p q d u v -> invx p q u v -> q < p -> d = inf (u + v) -> d < p ->
  (forall y, y < u + v -> inf (u + v) = dst y -> y < u) ->
  u + (v + u) <= N ->
  forall y, y < u + (v + u) -> inf (u + (v + u)) = dst y ->
  (y < u) = (d < p - q).
Proof.
move=> iv ix qLp dE dLp pg uvuN y yL yE.
have [_ _ _ _ _ _ u_gt0 _] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Hy0] := inf_ex uv_gt0.
have y0u : y0 < u := pg _ y0L Hy0.
have [Ha _] := sub_p_argmin iv ix qLp dE dLp y0u Hy0.
have yN : y <= N by apply: ltnW; exact: leq_trans yL uvuN.
have y0uv : y0 + (v + u) < u + (v + u) by rewrite ltn_add2r.
have [dLpq|pqLd] := ltnP d (p - q).
  rewrite ifT // in Ha.
  have y0N : y0 <= N.
    by apply: ltnW; apply: leq_trans uvuN; rewrite (leq_trans y0L) // leq_add2l
       leq_addr.
  have -> : y = y0 by apply: dst_inj yN y0N _; rewrite -yE Ha.
  by rewrite y0u.
rewrite ifN -?leqNgt // in Ha.
have wN : y0 + (v + u) <= N by apply: ltnW; exact: leq_trans y0uv uvuN.
have -> : y = y0 + (v + u) by apply: dst_inj yN wN _; rewrite -yE Ha.
apply/negbTE; rewrite -leqNgt.
exact: leq_trans (leq_addl v u) (leq_addl y0 (v + u)).
Qed.

Lemma invw_sub_p p q d u v :
  inv p q d u v -> invx p q u v -> q < p -> d = inf (u + v) -> d < p ->
  (forall y, y < u + v -> inf (u + v) = dst y -> y < u) ->
  invw (p - q) q d u (v + u).
Proof.
move=> iv ix qLp dE dLp pg; split.
- by rewrite (subnK (ltnW qLp)).
- exact: invw_sub_p_inf iv ix qLp dE dLp pg.
exact: invw_sub_p_gap iv ix qLp dE dLp pg.
Qed.

(*  The [q] side needs no such hypothesis: reducing [q] leaves [p]-gaps       *)
(*    alone, and "[b] is in a [p]-gap" already forces [Inf < p], so both      *)
(*    cases agree with the test on their own.                                 *)
Lemma invw_sub_q_inf p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> d = inf (u + v) ->
  inf (u + v + v) = (if d < p then d else d - p).
Proof.
move=> iv ix pLq dE; have [p_gt0 _ _ _ _ _ _ _] := iv.
have k1 : 1 <= q %/ p by rewrite divn_gt0 //; apply: ltnW.
have Hle := inf_red_lt_le iv pLq k1; have Hge := inf_red_lt_ge iv ix pLq k1.
have H : inf (u + 1 * v + v) = inf (u + v) - minn 1 (inf (u + v) %/ p) * p.
  by apply/eqP; rewrite eqn_leq Hle Hge.
rewrite mul1n in H.
rewrite H -dE; have [dLp|pLd] := ltnP d p.
  by rewrite (divn_small dLp) minn0 mul0n subn0.
by rewrite (minn_idPl _) ?mul1n // divn_gt0.
Qed.

(*  the mirror of [invw_sub_p_gap]: reducing [q] splits [q]-gaps into a [p]   *)
(*    on the left and the residual on the right, so a [b] whose [d] is        *)
(*    below [p] lands in the new [p]-gap and one whose [d] is not gets the    *)
(*    new point underneath it.                                               *)
Lemma invw_sub_q_gap p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> d = inf (u + v) -> d < q ->
  u + v + v <= N ->
  forall y, y < u + v + v -> inf (u + v + v) = dst y -> (y < u + v) = (d < p).
Proof.
move=> iv ix pLq dE dLq uvvN y yL yE.
have [p_gt0 _ _ _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y0 y0L Hy0] := inf_ex uv_gt0.
have Hinf := invw_sub_q_inf iv ix pLq dE.
have yN : y <= N by apply: ltnW; exact: leq_trans yL uvvN.
have y0N : y0 <= N.
  by apply: ltnW; apply: leq_trans uvvN; rewrite (leq_trans y0L) // leq_addr.
have [dLp|pLd] := ltnP d p.
(* [b] keeps its neighbour: nothing was added below it *)
  have dEq : dst y = dst y0 by rewrite -yE -Hy0 Hinf ifT // -dE.
  have -> : y = y0 by apply: dst_inj yN y0N dEq.
  by rewrite y0L.
(* [b] is in a [q]-gap, and the point added at [p] above its left end is
   now the nearest below it *)
have uy0 : u <= y0.
  rewrite leqNgt; apply/negP => y0u.
  by move: pLd; rewrite leqNgt dE Hy0 (argmin_lt_p iv ix y0u Hy0).
have pDy0 : 1 * p <= dst y0 by rewrite mul1n -Hy0 -dE.
have k1 : 0 < 1 <= q %/ p by rewrite divn_gt0 //; apply: ltnW.
have Hw := walk_lt_nowrap iv pLq y0L k1 pDy0.
have dEq : dst y = dst (y0 + 1 * v).
  by rewrite -yE Hw mul1n Hinf ifN -?leqNgt // -Hy0 -dE.
have y0vN : y0 + 1 * v <= N.
  by rewrite mul1n; apply: leq_trans uvvN; rewrite leq_add2r; apply: ltnW.
have -> : y = y0 + 1 * v by apply: dst_inj yN y0vN dEq.
by rewrite mul1n ltnNge leq_add // leqNgt pLd.
Qed.

Lemma invw_sub_q p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> d = inf (u + v) -> d < q ->
  invw p (q - p) d (u + v) v.
Proof.
move=> iv ix pLq dE dLq; split.
- by rewrite (subnKC (ltnW pLq)).
- exact: invw_sub_q_inf iv ix pLq dE.
exact: invw_sub_q_gap iv ix pLq dE dLq.
Qed.

(*  the [p <= d] half of the exit.                                           *)
Lemma half1_leq_inf_ge p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> p <= d ->
  N <= u + (v + p %/ q * u) -> d - p <= inf N.
Proof.
move=> iv ix iw uvN pLd NL.
have dE : inf (u + v) = d - p by have := invw_inf iw; rewrite ifN // -leqNgt.
rewrite -dE; apply: leq_inf.
  by rewrite -inf0; apply: leq_inf_mono.
move=> z zL; have [zold|znew] := ltnP z (u + v); first exact: leq_inf_dst zold.
by apply: ge_new_dst iv ix iw uvN pLd znew _; apply: leq_trans zL NL.
Qed.

(*  At the exit the count has passed [N], so [half1_exact] is out of reach:   *)
(*    its range hypothesis is exactly what the exit denies.  On the [q] side  *)
(*    [N <= u'+v'] gives [Inf (u'+v') <= Inf N], and the lower half of        *)
(*    Config's [inf] law carries no range bound, so [d] passes through it.    *)
Lemma half1_leq_inf p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N ->
  let: (_, _, d', u', v') := half1 p q d u v in
  N <= u' + v' -> d' <= inf N.
Proof.
move=> iv ix iw uvN; have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have pqN := inv_pq_neq iv uvN.
rewrite /half1; case: (ltnP d p) => [dLp|pLd] /= NL; last first.
  exact: half1_leq_inf_ge iv ix iw uvN pLd NL.
apply: leq_trans (leq_inf_mono NL).
have dE : inf (u + v) = d by have := invw_inf iw; rewrite ifT.
have [pLq|qLp] := ltnP p q; last first.
  have qLp' : q < p by rewrite ltn_neqAle qLp andbT eq_sym.
  by rewrite (divn_small qLp') mul0n addn0 dE.
have H := inf_red_lt_ge iv ix pLq (leqnn (q %/ p)).
by rewrite dE (divn_small dLp) minn0 mul0n subn0 in H.
Qed.

(*  [invx] through the two halves, and both are assemblies.  [half1] is       *)
(*    [Alg2.step] whenever the branch test agrees with [p < q], and the       *)
(*    identity otherwise, so [Alg2.invx_step] does it; [half2] is Config.v's  *)
(*    reduction at [k = 1], so its six [invx_red_*] fields do.                *)
Lemma invx_half1 p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := half1 p q d u v in
  u' + v' < N -> invx p' q' u' v'.
Proof.
move=> iv ix uvN.
have pqN := inv_pq_neq iv uvN.
have Hs := invx_step iv ix uvN.
rewrite /half1; case: (ltnP d p) => [dLp|pLd].
  case: (ltnP p q) => [pLq|qLp] /=; first by move: Hs; rewrite /step ifT.
  have qLp' : q < p by rewrite ltn_neqAle qLp andbT eq_sym.
  by rewrite (divn_small qLp') mul0n subn0 addn0.
case: (ltnP p q) => [pLq|qLp] /=.
  by rewrite (divn_small pLq) mul0n subn0 addn0.
by move: Hs; rewrite /step ifN -?leqNgt.
Qed.


Lemma invx_sub_q p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> u + v + v < N ->
  invx p (q - p) (u + v) v.
Proof.
move=> iv ix pLq uvN; have [p_gt0 _ _ _ _ _ _ _] := iv.
have k1 : 1 <= q %/ p by rewrite divn_gt0 //; apply: ltnW.
have q1 : 0 < q - 1 * p by rewrite mul1n subn_gt0.
have uvN' : u + 1 * v + v < N by rewrite mul1n.
split.
- by have H := invx_red_lt_min iv (invx_min ix) (invx_max ix) pLq k1 uvN';
     rewrite !mul1n in H.
- by have H := invx_red_lt_max iv (invx_max ix) pLq k1 uvN';
     rewrite !mul1n in H.
- by rewrite (leq_trans (leq_subr _ _)) // (inv_qM iv).
- by have H := invx_red_lt_inf iv ix pLq k1 q1 uvN'; rewrite !mul1n in H.
- by have H := invx_red_lt_gap iv ix pLq k1 q1 uvN'; rewrite !mul1n in H.
- by have H := invx_red_lt_p1 iv (invx_max ix) pLq k1 uvN'; rewrite !mul1n in H.
by have H := invx_red_lt_p2 iv pLq k1 q1; rewrite !mul1n in H.
Qed.

(******************************************************************************)
(* Soundness                                                                  *)
(******************************************************************************)

(*  Once the count has passed [N] the invariant alone finishes: the loop      *)
(*    returns at most the [d] that [half1] leaves ([run1_decr]), which        *)
(*    [invw] says is the infimum over a range at least as large as [N].       *)
Lemma run1_past fuel p q d u v :
  invw p q d u v -> N <= u + v -> 0 < fuel -> run1 fuel p q d u v N <= inf N.
Proof.
move=> iw Nuv f_gt0.
apply: leq_trans (run1_decr p q d u v f_gt0) _.
by rewrite -(invw_inf iw); apply: leq_inf_mono.
Qed.

(*  Induction on [fuel]: [half1_exact] makes [d] the infimum, the exit is    *)
(*    [half1_leq_inf], and the recursive case rebuilds the three records.     *)
(*    A turn can begin with [N <= u + v], since the exit test bounds the      *)
(*    mid-turn count; [run1_past] closes that case from [invw] alone.         *)
Lemma run1_sound fuel p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N ->
  p + q <= fuel -> run1 fuel p q d u v N <= inf N.
Proof.
elim: fuel p q d u v =>
    [p q d u v iv _ _ _ pqf|f IH p q d u v iv ix iw uvN pqf].
  have [p_gt0 _ _ _ _ _ _ _] := iv.
  by move: pqf; rewrite leqn0 addn_eq0 => /andP[/eqP p0 _]; rewrite p0 in p_gt0.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have f_gt0 : 0 < f.
  by rewrite -ltnS (leq_trans _ pqf) // -addn1 leq_add.
have pqN := inv_pq_neq iv uvN.
have Hi := inv_half1 iv uvN.
have Hx := invx_half1 iv ix uvN.
have H1 := half1_exact iv ix iw uvN.
have Hle := half1_leq_inf iv ix iw uvN.
have Hm := run1_measure iv uvN.
move: Hi Hx H1 Hle Hm; rewrite /half1 /half2 /=.
case: (ltnP d p) => [dLp|pLd] Hi Hx H1 Hle Hm.
(* [b] is in a [p]-gap: [half1] divides [q], [half2] takes one [p] off       *)
  set k := q %/ p in Hi Hx H1 Hle Hm *.
  set q1 := q - k * p in Hi Hx H1 Hle Hm *.
  set u1 := u + k * v in Hi Hx H1 Hle Hm *.
  case: (leqP N (u1 + v)) => [Nu1v|u1vN]; first exact: Hle.
  have q1Lp : q1 < p.
    have [pLq|qLp] := ltnP p q; first by apply: q'_lt_p.
    have qLp' : q < p by rewrite ltn_neqAle qLp andbT eq_sym.
    by rewrite /q1 /k (divn_small qLp') mul0n subn0.
  have iv1 := Hi u1vN; have ix1 := Hx u1vN; have d1 := H1 u1vN.
  have iw2 := invw_sub_p iv1 ix1 q1Lp d1 dLp
                         (half1_gap_lt iv ix iw uvN dLp u1vN).
  case: (leqP N (u1 + (v + u1))) => [Nuv2|uv2N].
    exact: run1_past iw2 Nuv2 f_gt0.
  apply: IH => //; first exact: inv_sub_p iv1 q1Lp.
    exact: invx_sub_p iv1 ix1 q1Lp.
  by rewrite -ltnS (leq_trans Hm).
(* [b] is in a [q]-gap: [half1] divides [p], [half2] takes one [q] off       *)
set k := p %/ q in Hi Hx H1 Hle Hm *.
set p1 := p - k * q in Hi Hx H1 Hle Hm *.
set v1 := v + k * u in Hi Hx H1 Hle Hm *.
case: (leqP N (u + v1)) => [Nuv1|uv1N]; first exact: Hle.
have p1Lq : p1 < q.
  have [pLq|qLp] := ltnP p q; last by apply: q'_lt_p.
  by rewrite /p1 /k (divn_small pLq) mul0n subn0.
have iv1 := Hi uv1N; have ix1 := Hx uv1N; have d1 := H1 uv1N.
have dpLq : d - p < q by rewrite -(ltn_add2l p) subnKC // (invw_max iw).
have iw2 := invw_sub_q (inv_dW (d - p) iv1) ix1 p1Lq d1 dpLq.
case: (leqP N (u + v1 + v1)) => [Nuv2|uv2N].
  exact: run1_past iw2 Nuv2 f_gt0.
apply: IH => //; first exact: inv_sub_q (inv_dW (d - p) iv1) p1Lq.
  exact: invx_sub_q iv1 ix1 p1Lq uv2N.
by rewrite -ltnS (leq_trans Hm).
Qed.

(*  The algorithm returns a lower bound on the infimum.                       *)
Theorem lefevre1_sound : 2 < N -> lefevre1 M A B N <= inf N.
Proof.
move=> N_gt2.
have am : A %% M < M by rewrite ltn_mod.
apply: run1_sound; [exact: inv_init | exact: invx_init | exact: invw_init | |].
  by rewrite (leq_trans _ N_gt2).
by rewrite subnKC // ltnW.
Qed.

(*  The form the search uses: if the returned bound clears the threshold,     *)
(*    there is no hard-to-round case in this sub-interval.                    *)
Corollary lefevre1_test eps :
  2 < N -> eps < lefevre1 M A B N -> forall x, x < N -> eps < dst x.
Proof.
move=> N_gt2 epsL x xLN.
apply: leq_trans epsL _.
by apply: leq_trans (lefevre1_sound N_gt2) _; apply: leq_inf_dst xLN.
Qed.

End Theory.

(******************************************************************************)
(* Comparison with Algorithm 2                                                *)
(******************************************************************************)

(*  Neither is exact ([lefevre1_strict]), but Algorithm 1 is the sharper of  *)
(*    the two: [lefevre M A B N <= lefevre1 M A B N], measured over all      *)
(*    [M <= 24], all [A, B < M] and all [3 <= N < M %/ gcdn A M], with       *)
(*    [lefevre1_sharper] a strict witness.  Not proved.                      *)
