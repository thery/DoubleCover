(******************************************************************************)
(*                                                                            *)
(*   Lefevre's original lower-bound algorithm                                 *)
(*                                                                            *)
(*   Algorithm 1 of doc/mourad.pdf (hal-00751446, 4.1), the algorithm         *)
(*    Alg2.v's Algorithm 2 was designed to replace.  Same specification:      *)
(*    with [a = A/M], [b = B/M], a lower bound on                             *)
(*    [inf { b - a*x mod 1 | x < N }].                                        *)
(*                                                                            *)
(*   The two differ in what they branch on.  Algorithm 2 tests [p < q] and    *)
(*    always takes the Euclidean quotient.  Algorithm 1 tests [d < p], and    *)
(*    one of its turns is TWO reductions -- a division one then a single      *)
(*    subtraction -- with the exit test BETWEEN them (lines 7 and 14).  That  *)
(*    is why the loop cannot be written as a [step] plus a check, the way     *)
(*    Alg2.run is, and why it visits configurations Algorithm 2 skips.        *)
(*                                                                            *)
(*      branch [d < p]   q -= (q %/ p)*p, u += k*v | exit | p -= q, v += u    *)
(*      branch [p <= d]  d -= p, p -= (p %/ q)*q, v += k*u | exit |           *)
(*                                                          q -= p, u += v    *)
(*                                                                            *)
(*   [half1] is therefore [Alg2.step] (the quotient agrees whenever the       *)
(*    branch test agrees with [p < q], and is [0] otherwise), and [half2] is  *)
(*    the same reduction with [k = 1], which is what Config.v provides.       *)
(*                                                                            *)
(*   WHAT [d] IS, AND WHERE.  4.1 and Lefevre's thesis both say [d] is the    *)
(*    distance from [b] down to the nearest point on its left, i.e.           *)
(*    [inf (u + v)].  That is true BETWEEN the halves -- where the exit test  *)
(*    reads it and where the loop returns it -- and not at the top of a       *)
(*    turn: [half2] adds points and leaves [d] alone.  So at a turn start     *)
(*    what holds is [invw] below,                                            *)
(*                                                                            *)
(*      inf (u + v) = if d < p then d else d - p     and   d < p + q,         *)
(*                                                                            *)
(*    i.e. [d] is the infimum plus the one [p]-step [half1] has not yet       *)
(*    taken -- which is exactly what the branch test decides.  Algorithm 2's  *)
(*    [invd] does NOT hold here: it fails at the initial state already.       *)
(*                                                                            *)
(*   NOTE ON THE SOURCE.  Line 13 of the paper's listing prints as            *)
(*    [q <- p - k*q].  That has to be a typo for [p <- p - k*q]: as           *)
(*    printed it leaves [p] at its old, larger value and line 15's            *)
(*    [q <- q - p] would go negative.  The counter update on the same line,   *)
(*    [v <- v + k*u], is the one that goes with reducing [p] by [k*q].  The   *)
(*    [Example]s below are what check that reading.                           *)
(*                                                                            *)
(*   NOTE ON eps.  The paper's lines 2 and 11 return Failure early when       *)
(*    [d < eps].  That is an optimisation, not part of the bound: [d] never   *)
(*    increases ([leq_run1]), so an early Failure and a final [d < eps]       *)
(*    agree.  The loop below therefore returns [d], as Alg2.run does, and     *)
(*    the test is the corollary [lefevre1_test].                             *)
(*                                                                            *)
(*   Companion notes: doc/mourad-notes.md (the six cases and Property 3),     *)
(*    doc/lefevre-these-notes.md (what the variables mean).                   *)
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

(*  Sanity checks (computed).  These are what validate the transcription      *)
(*    of the listing, in particular the line 13 reading above.  They are      *)
(*    the same figures Alg2.v checks, so the two algorithms can be compared   *)
(*    on them directly.                                                       *)
(*                                                                            *)
(*   [a = 17/45] is the example of Figure 4 of the paper.                     *)

Example lefevre1_fig4 : lefevre1 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

(*  Alg2.lefevre_strict's case, where Algorithm 2 returns 1 and the true      *)
(*    infimum is 2.  Algorithm 1 is exact here -- it is the sharper of the    *)
(*    two, see [leq_lefevre_1_2] at the bottom of the file.                   *)
Example lefevre1_sharper : (lefevre1 32 23 12 8, lefevre 32 23 12 8) = (2, 1).
Proof. by vm_compute. Qed.

(*  But not exact in general: here both return 0 and the infimum is 1.  This  *)
(*    is the smallest counterexample.                                         *)
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

Local Notation step_p_gt0 := (@step_p_gt0 M A N N_lt_Mg).
Local Notation inv_step_pos := (@inv_step_pos M M_gt0 A B ltn_B).
Local Notation inf_new_eq_lt := (@inf_new_eq_lt M M_gt0 A B N).

Local Notation inv_red_lt := (@inv_red_lt M A B ltn_B).
Local Notation inv_red_ge := (@inv_red_ge M M_gt0 A B ltn_B).
Local Notation inf_red_lt := (@inf_red_lt M M_gt0 A B N).
Local Notation inv_qM := (@inv_qM M A).
Local Notation invx_red_lt_min := (@invx_red_lt_min M M_gt0 A N N_lt_Mg).
Local Notation invx_red_lt_max := (@invx_red_lt_max M M_gt0 A N N_lt_Mg).
Local Notation invx_red_lt_p1 := (@invx_red_lt_p1 M M_gt0 A N N_lt_Mg).
Local Notation invx_red_lt_p2 := (@invx_red_lt_p2 M M_gt0 A B ltn_B).
Local Notation invx_red_lt_inf := (@invx_red_lt_inf M M_gt0 A B N).
Local Notation invx_red_lt_gap :=
  (@invx_red_lt_gap M M_gt0 A B ltn_B N N_lt_Mg).

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

Record invw (p q d u v : nat) := Invw {
  invw_max : d < p + q;
  invw_inf : inf (u + v) = if d < p then d else d - p
}.

(*  At the start [u = v = 1], so the configuration is the two points [0] and  *)
(*    [1] and the infimum is [B] or [B - A %% M], which is exactly what the   *)
(*    branch test picks out.                                                  *)
Lemma invw_init : invw (A %% M) (M - A %% M) (B %% M) 1 1.
Proof.
have am : A %% M < M by rewrite ltn_mod.
have bm : B %% M = B by apply: modn_small.
have pt1 : pt 1 = A %% M by rewrite /Dist.pt muln1.
split; first by rewrite subnKC ?bm // ltnW.
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

(*  The other branch.  [invw] says [b] is NOT in a [p]-gap here: [d] is       *)
(*    [Inf + p], so [Inf < q] by [invw_max].  That is the paper's fourth      *)
(*    case -- [b] sits in a [q]-gap, and reducing [p] splits [p]-gaps only,   *)
(*    so no point enters [b]'s gap and [Inf] does not move.                   *)
(*                                                                           *)
(*  ROUTE.  [Alg2.ge_inf_alt] is this statement with a disjunction, and its   *)
(*    right disjunct is exactly the conclusion below.  It asks for [invd],    *)
(*    which Algorithm 1 does not have -- but only to get [d = Inf] out of     *)
(*    [ge_d_eq_inf], so it can be applied at [d := inf (u + v)], for which    *)
(*    [invd] is immediate.  What is then left is to rule out its left         *)
(*    disjunct, i.e. the [gap_q_empty] half of its proof.                     *)
Lemma half1_inf_ge p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N -> p <= d ->
  u + (v + p %/ q * u) < N ->
  inf (u + (v + p %/ q * u)) = inf (u + v).
Proof. Admitted.

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
Lemma invw_sub_p p q d u v :
  inv p q d u v -> invx p q u v -> q < p -> d = inf (u + v) -> d < p ->
  u + (v + u) < N -> invw (p - q) q d u (v + u).
Proof. Admitted.

Lemma invw_sub_q p q d u v :
  inv p q d u v -> invx p q u v -> p < q -> d = inf (u + v) -> d < q ->
  u + v + v < N -> invw p (q - p) d (u + v) v.
Proof.
move=> iv ix pLq dE dLq uvN; have [p_gt0 _ _ _ _ _ _ _] := iv.
have k1 : 1 <= q %/ p by rewrite divn_gt0 //; apply: ltnW.
have uvN' : u + 1 * v + v < N by rewrite mul1n.
split; first by rewrite subnKC //; apply: ltnW.
have H := inf_red_lt iv ix pLq k1 uvN'; rewrite !mul1n -dE in H.
rewrite H; have [dLp|pLd] := ltnP d p.
  by rewrite (divn_small dLp) minn0 mul0n subn0.
by rewrite (minn_idPl _) ?mul1n // divn_gt0.
Qed.

(*  At the exit the count has passed [N], so the equality above is out of     *)
(*    reach ([Alg2]'s [inf] lemmas need the new range below [N]).  Only the   *)
(*    inequality is needed, and only at the indices below [N]: this is        *)
(*    [Alg2.inf_ge_new] with [x < N] in place of the range hypothesis.        *)
Lemma half1_leq_inf p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N ->
  let: (_, _, d', u', v') := half1 p q d u v in
  N <= u' + v' -> d' <= inf N.
Proof. Admitted.

(*  [invx] through the two halves.  [half1] is [Alg2.step], [half2] is        *)
(*    Config.v's reduction at [k = 1]; both are assemblies of the six         *)
(*    [invx_red_*] fields, once Config.v has the [inf] one.                   *)
Lemma invx_half1 p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := half1 p q d u v in
  u' + v' < N -> invx p' q' u' v'.
Proof. Admitted.

Lemma invx_sub_p p q d u v :
  inv p q d u v -> invx p q u v -> q < p -> u + (v + u) < N ->
  invx (p - q) q u (v + u).
Proof. Admitted.

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

(*  The loop returns a lower bound on the infimum.                            *)
(*                                                                            *)
(*  ROUTE, and the one thing in the way.  Induction on [fuel]: at each turn   *)
(*    [half1_exact] makes [d] the infimum, the exit case is                   *)
(*    [half1_leq_inf], and the recursive case rebuilds the three records by   *)
(*    [inv_half1]/[inv_sub_*], [invx_half1]/[invx_sub_*] and                  *)
(*    [half1_exact]/[invw_sub_*].                                             *)
(*                                                                            *)
(*  What does NOT go through as stated: the exit test sits BETWEEN the        *)
(*    halves, so it bounds [u1 + v], not the count after [half2].  A turn     *)
(*    can therefore begin with [N <= u + v], and then the range hypotheses    *)
(*    of the [inf] lemmas above (and of Alg2's) are unavailable.              *)
(*    [run1_past] closes that case from [invw] alone -- so what is missing is *)
(*    exactly [invw] at an overshot count, i.e. the [invw_sub_*] pair without *)
(*    their [< N] hypothesis.                                                 *)
Lemma run1_sound fuel p q d u v :
  inv p q d u v -> invx p q u v -> invw p q d u v -> u + v < N ->
  p + q <= fuel -> run1 fuel p q d u v N <= inf N.
Proof. Admitted.

(*  The algorithm returns a lower bound on the infimum.                       *)
Theorem lefevre1_sound : 2 < N -> lefevre1 M A B N <= inf N.
Proof. Admitted.

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

(*  Both algorithms bound the same quantity, so they can be compared.        *)
(*    Neither is exact ([lefevre1_strict]), but Algorithm 1 is the sharper   *)
(*    of the two: measured true over all [M <= 24], all [A, B < M] and all   *)
(*    [3 <= N < M %/ gcdn A M], with [lefevre1_sharper] a witness that the   *)
(*    inequality is strict somewhere.  Not proved.                           *)
(*                                                                           *)
(*  This is a statement about the two algorithms only, with no [inf] in it,  *)
(*    so it needs neither soundness proof and could be attacked first.       *)

(* TODO: proof.
Lemma leq_lefevre_1_2 M A B N : lefevre M A B N <= lefevre1 M A B N.
*)
