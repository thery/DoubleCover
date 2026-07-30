(** * Lefèvre's lower-bound algorithm — skeleton

    Target: Algorithm 2 of [doc/mourad.pdf] (Fortin, Gouicem, Graillat,
    "Correctly rounding elementary functions on GPU", hal-00751446, §4.2,
    p. 8) — the "regular" variant of Lefèvre's HR-case test.  Two branches
    instead of Algorithm 1's six, and it uses only Property 2 (the
    division-based Euclid), never Properties 1/3.

    ** What it computes

    With [a = A/M] and [b = B/M], the search needs a lower bound on

        inf { b - a*x  mod 1  |  x < N }                          (the spec)

    and then answers the Boolean question "is that inf above eps?".  If
    yes, there is no hard-to-round case in this sub-interval.

    ** Note on the arithmetic

    Modular arithmetic occurs ONLY in the specification ([dst] below).
    The algorithm itself manipulates a 5-tuple of ordinary naturals
    [(p, q, d, u, v)] with no wraparound at all: [p], [q] are the two
    interval lengths of a two-length configuration, [d] a distance, and
    [u], [v] the two indices.  They stay below [M] because of the
    invariant [u*p + v*q = M], not because anything is reduced.  So the
    tools here are [ssrnat] and [div] — NOT [zmodp]/['Z_M], which would
    destroy that equation.

    ** Where the mathematics comes from

    [CFrac/slater.v] (Slater, "Gaps and steps for the sequence n@ mod 1")
    already has the three-distance structure, with this dictionary:

        p            <->  `{get_min n * a}          (scaled by M: pt v)
        q            <->  1 - `{get_max n * a}      (scaled by M: M - pt u)
        v            <->  get_min n
        u            <->  get_max n
        u*p + v*q = M<->  sum_min_max
        u + v >= N   <->  LminDmax  (n < get_min n + get_max n)
        one-point step<-> get_minS / get_maxS
        left neighbour<-> get_left / get_prev

    [slater.v] does NOT assume [a] irrational: it assumes only
    [Ndiff0 : forall n, 0 < n <= N -> `{n * a} <> 0].  Scaled, that is
    [pt_neq0] below; for [M = 2^64] and [N = 2^20] it holds as soon as
    [A] is not divisible by [2^44].

    ** Which holes CFrac can discharge, and which it cannot

    Each lemma below is tagged in place with one of

      (* CFrac: <name> *)   the content is already in CFrac, modulo the
                            scaling bridge -- do NOT reprove it
      (* pure *)            plain [ssrnat]/[div]; CFrac is irrelevant
      (* glue *)            assembles the two kinds above

    Summary:

      pure                pt_lt pt0 ptD dst_lt dst0 dstE
                          inf_dstS inf_dst_le inf_dst_mono
                          step_measure fuel_enough
      CFrac (slater.v)    dstD            <- get_minD / get_maxD
                          inv_bez         <- sum_min_max (csum_min_max)
                          inv_init        <- get_min1 / get_max1
                          step_pt_one_lt  <- get_maxS
                          step_pt_one_ge  <- get_minS
                          step_pt         <- the two above, batched
                          step_d_lt/_ge   <- get_nextDmin / get_nextDmax
                          step_d_*_mem    <- get_prev / get_prev_spec
                          step_p_gt0      <- get_min_NZ / get_max_NZ
                          exit_bound      <- LminDmax + get_prev_spec
      glue                step_bez inv_step step_d run_sound
                          lefevre_sound lefevre_test

    So roughly half the obligations are CFrac's, half are arithmetic, and
    only [step_d] is genuinely new -- and even there the geometry
    ([step_d_lt], [step_d_ge]) is slater's; what is new is the
    bookkeeping that keeps [d] a distance.

    *** The scaling bridge

    CFrac is stated over [R] with [`{_}] (frac_part), this file over
    [nat].  Every use above goes through one lemma, to be proved once:

      Lemma pt_frac n : `{n%:R * (A%:R / M%:R)} = (Pt n)%:R / M%:R.

    It is deliberately NOT stated here, so that this file stays free of
    [Reals] and of a dependency on CFrac while the skeleton is being
    filled in.  Add it (and [Require Import cfrac.slater]) at the point
    where the first CFrac-tagged hole is attacked.

    A cheaper alternative worth one day of measurement first: reprove the
    handful of needed [slater.v] facts directly over [nat].  Only
    [get_minS], [get_maxS], [get_minD], [get_maxD], [sum_min_max],
    [LminDmax] and [get_prev_spec] are used, and their proofs are
    [lra]-light -- transporting [R] statements may well cost more than
    redoing them.

    ** Roadmap (suggested order of attack)

      1. [inf_dstS], [inf_dst_le]                  -- trivial, warm-up
      2. [inv_init]                                -- easy
      3. [step_bez]                                -- easy, Bezout-shaped
      4. [step_measure], [fuel_enough]             -- easy, termination
      5. [step_pt]                                 -- MEDIUM: the batched
         Euclid step, by induction on [k] over slater's get_minS/get_maxS
      6. [step_d]                                  -- HARD: the [d] update.
         This is the one that stopped the previous attempt.  Only an
         INEQUALITY is needed (see [inv_d] / [exit_bound]) -- the value of
         [d] never has to be characterised exactly, because Algorithm 2
         returns a strict lower bound, not the infimum.  Checked by
         computation: with M=32, A=23, B=12 it returns 1 while the true
         infimum is 2.
      7. [exit_bound], then [lefevre_sound]        -- assembly

    Everything below [step] is [Admitted]. *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** The specification *)

(** the lattice point [a*x mod 1], scaled by [M]. *)
Definition pt (M A x : nat) := (A * x) %% M.

(** distance from [pt x] up to [b], i.e. [b - a*x mod 1], scaled by [M]. *)
Definition dst (M A B x : nat) := (B + M - pt M A x) %% M.

(** [inf { b - a*x mod 1 | x < n }], scaled by [M].

    Sealed with [nosimpl] so that [/=] never unfolds it.  Without the
    seal, [Inf] silently expands whenever its index happens to be a
    literal successor -- sometimes to depth two, giving nested [minn] --
    and every proof about it then has to fold the result back with
    [-inf_dstS].  Access it through [inf_dst0] and [inf_dstS] below. *)
Fixpoint inf_dst (M A B n : nat) : nat :=
  if n is n1.+1 then minn (dst M A B n1) (inf_dst M A B n1) else M.

Arguments inf_dst : simpl never.

(** ** Algorithm 2

    One turn of the loop.  [p], [q] are the two interval lengths, [d] the
    running distance, [u], [v] the two indices.

        if p < q then k <- q/p; q <- q - k*p; u <- u + k*v; d <- d mod p
        else          k <- p/q; p <- p - k*q; v <- v + k*u;
                      if d >= p then d <- d - p; d <- d mod q          *)
Definition step (p q d u v : nat) : nat * nat * nat * nat * nat :=
  if p < q then
    let k := q %/ p in (p, q - k * p, d %% p, u + k * v, v)
  else
    let k := p %/ q in
    let p' := p - k * q in
    (p', q, (if p' <= d then (d - p') %% q else d), u, v + k * u).

(** The loop.  [fuel] is a structural bound; [fuel_enough] below says [M]
    always suffices, since [p + q] strictly decreases and starts at [M]. *)
Fixpoint run (fuel p q d u v N : nat) : nat :=
  if fuel is fuel1.+1 then
    let: (p', q', d', u', v') := step p q d u v in
    if N <= u' + v' then d' else run fuel1 p' q' d' u' v' N
  else d.

(** [p <- {a}; q <- 1 - {a}; d <- {b}; u <- 1; v <- 1].

    NB the initial [q] is [1 - {a}], not [1]: the invariant
    [u*p + v*q = M] fails otherwise.  (The paper's Algorithm 2 box reads
    [q <- 1]; checked by computation that this is wrong -- with M=32,
    A=5, B=3, N=8 it returns 3 while the true infimum is 0.) *)
Definition lefevre (M A B N : nat) : nat :=
  run M (A %% M) (M - A %% M) (B %% M) 1 1 N.

(** ** Sanity checks (computed, not admitted)

    [a = 17/45] is the example of Figure 4 of the paper. *)

Example lefevre_fig4 : lefevre 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

Example inf_dst_fig4 : inf_dst 45 17 30 5 = 7.
Proof. by vm_compute. Qed.

(** a case where the bound is strict: the algorithm returns 1, the true
    infimum is 2.  So only an inequality can be proved below. *)
Example lefevre_strict : (lefevre 32 23 12 8, inf_dst 32 23 12 8) = (1, 2).
Proof. by vm_compute. Qed.

(** ** The theory *)

Section Theory.

Variable M : nat.
Hypothesis M_gt0 : 0 < M.

Variables A B : nat.
Hypothesis A_lt : A < M.
Hypothesis B_lt : B < M.

(** [slater.v]'s [Ndiff0], scaled: [a] behaves irrationally up to [N]. *)
Variable N : nat.
Hypothesis N_gt0 : 0 < N.
Hypothesis pt_neq0 : forall n, 0 < n <= N -> pt M A n != 0.

(** The loop must exit before Euclid's descent bottoms out.  With
    [g = gcdn A M], the configuration can hold at most [M %/ g] points, so
    [N <= M %/ g] is what keeps [p] and [q] positive throughout (see
    [step_p_gt0]).  Validated by [inv_probe.py]/[degen.py]: over
    [M] in {32,64,128,256} and several [N], a run degenerates ([p] or [q]
    reaching 0 before the exit) if and only if this fails -- 0
    counterexamples in either direction of the "if" side. *)
Hypothesis N_le_Mg : N <= M %/ gcdn A M.

Local Notation Pt := (pt M A).
Local Notation Dst := (dst M A B).
Local Notation Inf := (inf_dst M A B).

(** *** Warm-up: elementary facts about the specification *)

Lemma pt_lt x : Pt x < M.
Proof. by rewrite ltn_mod. Qed.

Lemma pt0 : Pt 0 = 0.
Proof. by rewrite /Pt muln0 mod0n. Qed.

(** the lattice is additive mod M *)
Lemma ptD x y : Pt (x + y) = (Pt x + Pt y) %% M.
Proof. by rewrite modnDm -mulnDr. Qed.

Lemma dst_lt x : Dst x < M.
Proof. by rewrite ltn_mod. Qed.

Lemma dst0 : Dst 0 = B.
Proof. by rewrite /Dst pt0 subn0 modnDr modn_small. Qed.

Lemma dstE x : Dst x = (B + M - Pt x) %% M.
Proof. by []. Qed.

(** moving one lattice step to the right lowers the distance by [Pt y],
    unless it wraps.  The workhorse for [step_d]. *)
Lemma dstD x y : Pt y <= Dst x -> Dst (x + y) = Dst x - Pt y.
Proof.
move=> ptLdx; rewrite dstE ptD.
have F : Pt x + Pt y < M.*2.
  rewrite -addnn; apply: ltn_trans (_ : M + Pt y < _).
    by rewrite ltn_add2r pt_lt.
  by rewrite ltn_add2l pt_lt.
have [xyLM|MLxy]:= ltnP (Pt x + Pt y) M.
  rewrite [(Pt x + _) %% _]modn_small //.
  rewrite subnDA modnB //; last by apply: leq_trans ptLdx (leq_mod _ _).
  rewrite -[(B + M - Pt x) %% M]/(Dst x) ltnNge modn_small; last by apply: pt_lt.
  by rewrite ptLdx add0n.
have -> : (Pt x + Pt y) %% M  = Pt x + Pt y - M.
  by rewrite -[in LHS](subnK MLxy) modnDr modn_small // ltn_subLR // addnn.
rewrite subnCBA // addnCA addnn [Pt x + _]addnC subnDAC.
rewrite modnB ?pt_lt //; last first.
  rewrite leq_subRL.
    by apply: leq_trans (ltnW _) (leq_addl _ _).
  apply: leq_trans (ltnW (pt_lt _)) _.
  apply: leq_trans (leq_addl _ _).
  by rewrite -addnn leq_addr.
rewrite ![Pt _ %% _]modn_small ?pt_lt //.
have -> : (B + M.*2 - Pt x) %% M = Dst x.
  have -> : B + M.*2 = M + B + M by rewrite addnAC addnn addnC.
  rewrite subDnCA; first by rewrite modnDl addnC.
  by rewrite (leq_trans (ltnW (pt_lt _))) // leq_addr.
by rewrite ltnNge ptLdx.
Qed.

(** the only two ways to look inside [Inf]. *)
Lemma inf_dst0 : Inf 0 = M.
Proof. by []. Qed.

Lemma inf_dstS n : Inf n.+1 = minn (Dst n) (Inf n).
Proof. by []. Qed.

(** the infimum is a lower bound on every distance in range *)
Lemma inf_dst_le n x : x < n -> Inf n <= Dst x.
Proof.
elim: n => // n IH; rewrite leq_eqVlt => /orP[/eqP[->]|/IH // nLx].
  by rewrite inf_dstS geq_minl.
apply: leq_trans nLx.
by rewrite inf_dstS geq_minr.
Qed.

(** the minimum is attained -- needed to name a witness for the walk *)
Lemma inf_dst_ex n : 0 < n -> exists2 y, y < n & Inf n = Dst y.
Proof.
elim: n => // [] [_ _|n IH _].
  by exists 0; rewrite // inf_dstS inf_dst0; apply/minn_idPl; rewrite ltnW // dst_lt.
rewrite inf_dstS.
have [y yLn Hy] := IH isT; rewrite Hy.
case: (leqP (Dst n.+1) (Dst y)) => [H|H].
  by exists n.+1 => //; apply/minn_idPl.
by exists y => //; exact: leq_trans yLn (leqnSn _).
Qed.

(** more points can only lower the infimum *)
Lemma inf_dst_mono m n : m <= n -> Inf n <= Inf m.
Proof.
move=> /subnK<-; elim: (_ - _) => // k kmLm.
by rewrite addSn inf_dstS (leq_trans _ kmLm) // geq_minr.
Qed.


(** *** The loop invariant

    [p] is the length of the leftmost interval and [v] the index that
    realises it; [q] is the length of the rightmost interval and [u] the
    index that realises it; [d] is the distance from [b] down to some
    point already placed. *)

Record inv (p q d u v : nat) : Prop := Inv {
  inv_p0  : 0 < p;
  inv_q0  : 0 < q;
  (* slater.v: sum_min_max *)
  inv_bez : u * p + v * q = M;
  (* slater.v: p = `{get_min n * a}, with v = get_min n *)
  inv_pv  : p = Pt v;
  (* slater.v: q = 1 - `{get_max n * a}, with u = get_max n *)
  inv_qu  : q = M - Pt u;
  (* Euclid's invariant.  Measured to hold at every state including the
     initial one.  It is what bounds how long the loop can run: Euclid
     reaches 0 once [u + v] gets to [M / gcd], so the loop must exit
     first, i.e. [N <= M / gcdn A M]. *)
  inv_gcd : gcdn p q = gcdn A M;
  (* [u] and [v] start at 1 and only grow.  NOT derivable from the fields
     above -- u = 0, v = 1, q = M satisfies all of them -- but needed: with
     both positive, [inv_bez] gives [p + q <= M], i.e. the two gaps of the
     three-distance configuration fit inside the circle. *)
  inv_u0  : 0 < u;
  inv_v0  : 0 < v
}.

(** *** The [d] part of the invariant, separately

    The old [inv_d] ("[d] is the distance to SOME placed point") is FALSE:
    the reductions walk the index past [u + v], so [d] can be the distance
    to a point outside the current configuration, and then [d < Inf (u+v)].

    What actually holds -- measured by the Python harness over 6 (M,N)
    pairs and ~290000 loop states, at EVERY state after the first -- is

      invd_max : d < maxn p q
      invd_le  : d <= Inf (u + v)

    [invd_le] is exactly the direction [exit_bound] needs (with
    [inf_dst_mono] and [N <= u + v]).  Note it is an INEQUALITY, not
    [d = Inf (u+v)]: equality fails in a small number of cases where the
    reduction overshoots.

    Both fields FAIL at initialisation ([d = B], the distance to the point
    0, which need not be closest and can exceed both gaps).  [d] only
    becomes meaningful after the first reduction, so the entry point is
    [invd_first] below, not an [invd_init]. *)

Record invd (p q d u v : nat) : Prop := Invd {
  invd_max : d < maxn p q;
  invd_le  : d <= Inf (u + v);
  (* [d] sits on the same residue class mod [p] as the true closest
     distance.  Independent of [invx]: [invx] constrains the CONFIGURATION
     (gaps at least p / q), this constrains [d] RELATIVE to it, and the two
     leaves need both.  Validated: 0 counterexamples over 5152 states, and
     it makes the leaves hold in 121183 of 121183 cases.  See the
     correction note above for why [invx] alone does not suffice. *)
  invd_cong : d = Inf (u + v) %[mod p]
}.

Lemma am_gt0 : 0 < A %% M.
Proof.
have : Pt 1 != 0 by apply: pt_neq0.
by rewrite /Pt muln1; case: (_ %% _).
Qed.

(** *** Initialisation *)

Lemma inv_init : inv (A %% M) (M - A %% M) (B %% M) 1 1.
Proof.
constructor => //.
- by apply: am_gt0.
- by rewrite ltn_subRL addn0 ltn_mod.
- by rewrite !mul1n addnC subnK // ltnW // ltn_mod.
- by rewrite /Pt muln1.
- by rewrite /Pt muln1.
- by rewrite (modn_small A_lt) -{2}(subnKC (ltnW A_lt)) gcdnDl.
Qed.


(** *** One step preserves the invariant

    Split into the four independent obligations so they can be attacked
    separately; [inv_step] just glues them. *)

(* glue -- pure algebra from [inv_bez], no geometry needed.
   Case [p < q], with [k = q %/ p]:
     (u + k*v) * p + v * (q - k*p)
       = u*p + k*v*p + v*q - v*k*p           (needs [k*p <= q], i.e. [leq_trunc_div])
       = u*p + v*q = M.
   Case [q <= p] is symmetric with [k = p %/ q].
   The only real work is discharging the [nat] subtraction side
   conditions; [leq_trunc_div] and [mulnBr]/[subnDA] do it. *)
Lemma step_bez p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in u' * p' + v' * q' = M.
Proof.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /=.
rewrite /step; have [pLq|qLp] := ltnP.
  rewrite mulnDl mulnBr addnBA; last by rewrite leq_mul2l leq_divM orbT.
  by rewrite mulnCA mulnA addnAC addnK.
rewrite mulnBr mulnDl addnC addnBA; last by rewrite leq_mul2l leq_divM orbT.
by rewrite mulnCA mulnA addnAC addnK addnC.
Qed.

(** the batched Euclid step: [k] applications of slater's [get_minS] /
    [get_maxS] at once (Property 2 of the paper).  Induction on [k],
    through the two one-step lemmas below. *)

(** one point added on the left: [v] keeps realising the smallest
    positive point, [u] moves to [u + v].  (slater: [get_maxS].) *)
Lemma step_pt_one_lt p q u v :
  inv p q (Dst 0) u v -> p < q ->
  (p = Pt v) /\ (q - p = M - Pt (u + v)).
Proof.
rewrite dst0.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /= pLq; split => //.
rewrite ptD modn_small; last by rewrite -ltn_subRL // -pE -qE.
by rewrite subnDA -qE -pE.
Qed.

(** one point added on the right. *)
Lemma step_pt_one_ge p q u v :
  inv p q (Dst 0) u v -> q <= p ->
  (p - q = Pt (v + u)) /\ (q = M - Pt u).
Proof.
rewrite dst0.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0 /= qLp; split => //.
rewrite pE qE ptD subnBA; last by rewrite ltnW // pt_lt.
rewrite [Pt _ + _]addnC.
suff MLuv : M <= Pt u + Pt v.
  rewrite -[in RHS](subnK MLuv) modnDr modn_small // ltn_subLR //.
  rewrite (ltn_trans _ (_ : M + Pt v < _)) //.
    by rewrite ltn_add2r pt_lt.
  by rewrite ltn_add2l pt_lt.
by rewrite -leq_subLR -pE -qE.
Qed.

(* CFrac: the two lemmas above, iterated [k] times (Property 2 of the
   paper -- "it is similar as repeating |h/l| times Property 1").
   Proof plan: strengthen to an auxiliary statement over [j <= k]
     forall j, j <= q %/ p -> (p = Pt v) /\ (q - j*p = M - Pt (u + j*v))
   and induct on [j], each step being [step_pt_one_lt].  Then instantiate
   at [j := k].  Symmetrically for the other branch.
   This is the long-but-mechanical row of the estimate: no new
   mathematics, just the induction that turns single steps into the
   division-based Euclid. *)
Lemma step_pt p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in
  0 < p' -> 0 < q' -> (p' = Pt v') /\ (q' = M - Pt u').
Proof.
case => p_gt0 q_gt0 upvqE pE qE gE u_gt0 v_gt0.
rewrite /step; have [pLq|qLp] := ltnP; rewrite /= => p'_gt0 q'_gt0.
  rewrite subn_gt0 in q'_gt0.
  suff : forall j, j <= q %/ p -> p = Pt v /\ q -  j * p = M - Pt (u + j * v).
    by move=> /(_ (q %/ p)); apply.
  elim => [|j IH jLq]; first by rewrite subn0 addn0.
  have -> :  q - j.+1 * p = q - j * p - p by rewrite mulSnr subnDA.
  have -> : u + j.+1 * v = u + j * v + v by rewrite mulSnr addnA.
  apply: step_pt_one_lt; last first.
    rewrite ltn_subRL -mulSnr.
    apply: leq_ltn_trans q'_gt0.
    by rewrite leq_mul2r jLq orbT.
  split => //.
  - rewrite subn_gt0 (leq_trans _ (_ :  q %/ p * p <= _)) //.
      by rewrite ltn_mul2r p_gt0.
    by rewrite leq_divM.
  - rewrite mulnDl mulnBr -addnA.
    rewrite mulnCA -mulnA [X in _ + X]addnC subnK //.
    rewrite mulnCA leq_mul2l.
    by rewrite (leq_trans _ (leq_divM q p)) ?orbT // leq_mul2r ltnW ?orbT.
  - by case: IH => //; apply: ltnW.
  have Hjp : j * p <= q.
    by rewrite ltnW // (leq_ltn_trans _ q'_gt0) // leq_mul2r ltnW ?orbT.
  by rewrite -gE -{2}(subnKC Hjp) gcdnMDl.
  by rewrite addn_gt0 u_gt0.
rewrite subn_gt0 in p'_gt0.
suff : forall j, j <= p %/ q -> p - j * q = Pt (v + j * u) /\ q = M - Pt u.
  by move=> /(_ (p %/ q)); apply.
elim => [|j IH jLq]; first by rewrite subn0 addn0.
have -> :  p - j.+1 * q = p - j * q - q by rewrite mulSnr subnDA.
have -> : v + j.+1 * u = v + j * u + u by rewrite mulSnr addnA.
apply: step_pt_one_ge; last first.
  rewrite leq_subRL.
    by rewrite -mulSnr (leq_trans _ (ltnW p'_gt0)) // leq_mul2r jLq orbT.
  by rewrite (leq_trans _ (leq_divM p q)) // leq_mul2r ltnW // orbT.
split => //.
- rewrite subn_gt0 (leq_trans _ (_ :  p %/ q * q <= _)) //.
    by rewrite ltn_mul2r q_gt0.
  by rewrite leq_divM.
- rewrite mulnBr mulnDl.
  rewrite mulnCA -mulnA addnC addnBA.
    by rewrite addnAC addnK addnC.
  rewrite mulnCA leq_mul2l (leq_trans _ (_ :  p %/ q * q <= _)) ?orbT //.
    by rewrite leq_mul2r ltnW // orbT.
  by apply: leq_divM.
- by case: IH => //; apply: ltnW.
have Hjq : j * q <= p.
  by rewrite ltnW // (leq_ltn_trans _ p'_gt0) // leq_mul2r ltnW ?orbT.
  by rewrite -gE gcdnC [in RHS]gcdnC -{2}(subnKC Hjq) gcdnMDl.
by rewrite addn_gt0 v_gt0.
Qed.

(** THE hard one: the [d] update stays a genuine distance.

    Attack it through the two branches separately.  In each, the claim is
    that reducing [d] modulo an interval length lands on another point of
    the configuration -- because, by Property 3 (directed reduction), the
    points added in this step are placed at regular spacing [p] (resp.
    [q]) going from [b] towards 0. *)

(** ** The [d] obligations, after the redesign

    The old chain [step_d_lt] / [step_d_lt_mem] / [step_d_ge] /
    [step_d_ge_mem] / [step_d] tried to track a WITNESS INDEX for [d].
    That is the wrong object: the reductions walk the index past [u + v],
    so no bound on the witness holds.  [step_d_lt] survives (it is proved,
    and it is the workhorse); the four "_mem"/glue lemmas are replaced by
    the single obligation [step_invd] below, phrased directly on the two
    quantities that do hold. *)

(** the converse of [inf_dst_le]: a pointwise lower bound gives a bound
    on the infimum.  This is what turns [mod_le_dst] (pointwise) into the
    [invd_le] field (about [Inf]). *)
Lemma le_inf_dst e n : e <= M -> (forall x, x < n -> e <= Dst x) -> e <= Inf n.
Proof.
move=> eM; elim: n => [//|n IH H]; rewrite inf_dstS leq_min H // IH // => x xn.
by apply: H (ltnW xn).
Qed.

(** ** The two remaining [d] obligations

    Both fields of [invd] are needed, and they differ sharply in cost:

      invd_max : d < maxn p q     -- cheap: [d] is always a [_ %% _] by a
                                    gap, and a remainder is below its
                                    modulus, which is below the max.
      invd_le  : d <= Inf (u+v)   -- the real content.  Note this is a
                                    UNIVERSAL claim ("d <= Dst x for every
                                    x < u+v"), not the exhibition of a
                                    witness.  That is what makes it more
                                    than an application of [step_d_lt].

    The universal claim splits on whether the point at index [x] is still
    below [b] or has wrapped past it, so both obligations want these three
    elementary lemmas first.  None needs CFrac. *)

Lemma dst_below x : Pt x <= B -> Dst x = B - Pt x.
Proof.
move=> H; rewrite dstE addnC -addnBA // modnDl modn_small //.
apply: leq_ltn_trans (leq_subr _ _) B_lt.
Qed.

Lemma dst_above x : B < Pt x -> Dst x = B + M - Pt x.
Proof.
move=> H; rewrite dstE modn_small //.
rewrite ltn_subLR; last by rewrite (leq_trans (ltnW (pt_lt x))) // leq_addl.
by rewrite ltn_add2r.
Qed.

(** the lattice is linear while it has not wrapped -- needed to turn an
    index bound into a bound on [Pt]. *)
Lemma pt_mul_small k : Pt 1 * k < M -> Pt k = Pt 1 * k.
Proof.
move=> H; have -> : Pt k = (Pt 1 * k) %% M by rewrite /pt muln1 modnMml.
by rewrite modn_small.
Qed.

(** the shape [invd_le] reduces to, in both [invd_first] and [step_invd]:
    a remainder by a gap is below every distance whose index is in range.
    Proof plan: [x <= d %/ g] gives [Dst x = B - Pt x >= B %% g] by
    [dst_below] and [leq_trunc_div]; [x > d %/ g] makes the point wrap, and
    [dst_above] bounds [Dst x] below by [M - Pt x >= B %% g] as long as
    [Pt 1 * x <= B + M], which the index range provides. *)
Lemma mod_le_dst g x : 0 < g -> g = Pt 1 -> Pt 1 * x <= M -> B %% g <= Dst x.
Proof.
move=> g_gt0 gE Hx.
have PtE : Pt x = (g * x) %% M by rewrite gE /pt muln1 modnMml.
have BMg : B %% g <= B by apply: leq_mod.
case: (ltnP (g * x) M) => [gxM|Mgx].
  have Ptx : Pt x = g * x by rewrite PtE modn_small.
  case: (leqP (g * x) B) => [gxB|Bgx].
    rewrite dst_below ?Ptx //.
    have Hd : g * x <= B %/ g * g.
      have Hx1 : x <= B %/ g by rewrite leq_divRL // mulnC.
      by rewrite mulnC leq_mul2r Hx1 orbT.
    have -> : B %% g = B - B %/ g * g by rewrite {2}(divn_eq B g) addnC addnK.
    exact: leq_sub2l Hd.
  rewrite dst_above ?Ptx //.
  apply: leq_trans BMg _.
  rewrite leq_subRL; last by rewrite (leq_trans (ltnW gxM)) // leq_addl.
  by rewrite addnC leq_add2l ltnW.
have gxE : g * x = M by apply/eqP; rewrite eqn_leq Mgx andbT gE.
by rewrite dstE PtE gxE modnn subn0 modnDr (modn_small B_lt).
Qed.

(** the entry point: after the FIRST step, [d] satisfies [invd].

    ** Goal breakdown (obtained interactively; [A %% M = A], [B %% M = B],
    [Pt 1 = A]).  After [rewrite /step; case: ltnP; split] there are four
    goals, two per branch:

    [A < M - A] branch, with [k := (M - A) %/ A]:
      (1) invd_max : B %% A < maxn A (M - A - k * A)
          CHEAP: [B %% A < A] by [ltn_mod], then [leq_maxl].
      (2) invd_le  : B %% A <= Inf (1 + k * 1 + 1)
          [le_inf_dst] then [mod_le_dst] at [g := A] for each [x < k + 2].
          Its side condition [Pt 1 * x <= M] holds because
          [A * (k+1) = A*k + A <= (M - A) + A = M] by [leq_trunc_div] --
          and note it is an EQUALITY at the top index, which is exactly why
          [mod_le_dst] had to be proved with [<= M] rather than [< M].

    [M - A <= A] branch, with [k := A %/ (M - A)] and
    [p' := A - k * (M - A)]:
      (3) invd_max : (if p' <= B then (B - p') %% (M-A) else B)
                       < maxn p' (M - A)
          CHEAP: in the [then] case [ltn_mod] + [leq_maxr]; in the [else]
          case the test itself gives [B < p'], then [leq_maxl].
      (4) invd_le  : same value <= Inf (1 + (1 + k * 1))
          NOT covered by [mod_le_dst]: the reduced quantity is
          [(B - p') %% (M - A)], not [B %% g].  What is true here is that
          the points of index [0 .. k+1] are
            0, A, A - (M-A), A - 2*(M-A), ..., A - k*(M-A) = p',
          i.e. [{0}] together with an arithmetic progression of step
          [M - A] running down from [A] to [p'], and [(B - p') %% (M-A)]
          is the distance from [b] to the nearest element of it below [b].
          So the generic lemma wanted is "distance to the nearest element
          of an arithmetic progression of step [q]", which [step_invd]
          needs too -- formulate it once, for both, and validate it before
          stating it. *)
(** Goals (1) and (3) of the breakdown above -- the [invd_max] field in
    both branches.  Cheap, and now proved. *)
Lemma invd_first_max :
  let: (p', q', d', _, _) := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' < maxn p' q'.
Proof.
have Ha := am_gt0.
have Hq : 0 < M - A %% M by rewrite subn_gt0 ltn_mod.
rewrite /step; case: ltnP => [pLq|qLp]; rewrite /=.
  by rewrite (leq_trans (ltn_pmod _ Ha)) ?leq_maxl.
case: (leqP (A %% M - A %% M %/ (M - A %% M) * (M - A %% M)) (B %% M))
   => [p'Ld|dLp'].
  by rewrite (leq_trans (ltn_pmod _ Hq)) ?leq_maxr.
by rewrite (leq_trans dLp') // leq_maxl.
Qed.

(** Goals (2) and (4): the [invd_le] field.  Goal (2) is [le_inf_dst] plus
    [mod_le_dst]; goal (4) needs the same universal bound as
    [step_invd_le_pt].  Left as one obligation so the two are attacked
    together. *)
(** ** The points added in the [M - A <= A] branch

    They form a DESCENDING arithmetic progression of step [M - A]:
    [Pt (j+1) = A - j*(M-A)] for [j*(M-A) <= A].  Validated over 89101
    instances (all [M < 200], all [A] with [M - A <= A], all [j] in
    range): 0 counterexamples.

    Proof: [A*(j+1) = (A - j*(M-A)) + j*M] once [j*(M-A) <= A], so the
    [%% M] is [modnMDl] followed by [modn_small]. *)
Lemma pt_desc j : j * (M - A) <= A -> Pt (j + 1) = A - j * (M - A).
Proof.
move=> Hj.
have HAM : A <= M by rewrite ltnW.
have HjM : j * M = j * (M - A) + j * A by rewrite -mulnDr subnK.
rewrite /pt.
have -> : A * (j + 1) = A - j * (M - A) + j * M.
  by rewrite HjM addnA subnK // mulnDr muln1 mulnC addnC.
rewrite addnC modnMDl modn_small //.
by rewrite (leq_ltn_trans (leq_subr _ _)).
Qed.

(** The [A < M - A] branch is fully covered by [mod_le_dst]: the index
    range gives [A * x <= A * ((M-A) %/ A + 1) <= (M-A) + A = M], which is
    exactly its side condition (and is an EQUALITY at the top index, hence
    the [<= M] form).  Only the [M - A <= A] branch is left.

    NB [Inf] unfolds under [/=] when its index is a literal successor,
    which is why [-inf_dstS] appears below to fold it back.  Sealing
    [inf_dst] (Opaque, or a nosimpl wrapper) would make these proofs less
    brittle -- worth doing, but it touches the existing ones. *)
(** The [M - A <= A] branch.  By [pt_desc] the points at indices
    [1 .. k+1] are the descending progression [A - j*(M-A)], and index 0
    contributes [Dst 0 = B].

    The [else] case ([p' > B], so [d' = B]) is proved below: every point of
    the progression then exceeds [B], so [dst_above] applies and
    [B <= B + M - Pt x] reduces to [Pt x <= M].

    The [then] case is what remains: [d' = (B - p') %% (M-A)] is congruent
    mod [M-A] to [B - (A - j*(M-A))] for every [j], so [leq_mod] gives the
    bound -- the missing step is that congruence through nat subtraction. *)
(** [modnB] is available (and [pt_sub] uses it, killing its boolean term
    with [ltnNge Hp /= mul0n add0n]), but it is not what this shape wants.
    The clean route is ADDITIVE: with [q = M - A], [k = A %/ q] and
    [p' = A - k*q], the identity

      B - p' = (B - (A - j*q)) + (k*q - j*q)

    holds for [j <= k] whenever [p' <= A - j*q <= B], and the added term is
    [(k - j) * q] by [mulnBl] -- a multiple of the modulus.  So [modnMDl]
    strips it and [leq_mod] finishes, with no case analysis on residues at
    all.  Assembling the identity is just [addnBA] + [subnK] + [subnDA]. *)
Lemma invd_first_le_ge_then : M - A %% M <= A %% M ->
  A - A %/ (M - A) * (M - A) <= B ->
  forall x, x < (A %/ (M - A)).+2 ->
  (B - (A - A %/ (M - A) * (M - A))) %% (M - A) <= Dst x.
Proof.
move=> qLp0 p'LB x xLk.
have HA : A %% M = A by rewrite modn_small.
have qLp : M - A <= A by move: qLp0; rewrite HA.
have HAM : A <= M by rewrite ltnW.
have Hq : 0 < M - A by rewrite subn_gt0.
have kqA : A %/ (M - A) * (M - A) <= A by rewrite leq_divM.
case: x xLk => [_|j jLk].
  by rewrite dst0 (leq_trans (leq_mod _ _)) // leq_subr.
have jk : j <= A %/ (M - A) by rewrite -ltnS.
have jqk : j * (M - A) <= A %/ (M - A) * (M - A) by rewrite leq_mul2r jk orbT.
have jqA : j * (M - A) <= A by rewrite (leq_trans jqk).
have HPt : Pt j.+1 = A - j * (M - A) by rewrite -addn1 pt_desc.
have HAj : (A - A %/ (M - A) * (M - A)) + (A %/ (M - A) * (M - A) - j * (M - A))
         = A - j * (M - A).
  by rewrite addnBA // subnK.
case: (leqP (A - j * (M - A)) B) => [AjLB|BLAj].
  rewrite dst_below ?HPt //.
  have Hs : A %/ (M - A) * (M - A) - j * (M - A)
          <= B - (A - A %/ (M - A) * (M - A)).
    by rewrite leq_subRL // HAj.
  rewrite -{1}(subnK Hs) -subnDA HAj.
  by rewrite -mulnBl addnC modnMDl leq_mod.
rewrite dst_above ?HPt //.
rewrite (leq_trans (ltnW (ltn_pmod _ Hq))) // leq_subRL; last first.
  by rewrite (leq_trans (leq_subr _ _)) // (leq_trans HAM) // leq_addl.
rewrite (leq_trans (_ : A - j * (M - A) + (M - A) <= M)) ?leq_addl //.
apply: leq_trans (leq_add (leq_subr _ _) (leqnn (M - A))) _.
by rewrite subnKC.
Qed.

Lemma invd_first_le_ge : M - A %% M <= A %% M ->
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' <= Inf (u' + v').
Proof.
move=> qLp0.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have HAM : A <= M by rewrite ltnW.
have Hq : 0 < M - A by rewrite subn_gt0.
have Hthen := invd_first_le_ge_then qLp0.
have qLp : M - A <= A by move: qLp0; rewrite HA.
rewrite /step HA HB.
rewrite ifN /=; last by rewrite -leqNgt.
apply: le_inf_dst.
  case: (leqP (A - A %/ (M - A) * (M - A)) B) => [_|_]; last by rewrite ltnW.
  by rewrite (leq_trans (leq_mod _ _)) // (leq_trans (leq_subr _ _)) // ltnW.
move=> x xLk; rewrite !muln1 !add1n in xLk.
have Hjq : forall j, j <= A %/ (M - A) -> Pt (j + 1) = A - j * (M - A).
  move=> j jLk; apply: pt_desc.
  by rewrite (leq_trans _ (leq_divM A (M - A))) // leq_mul2r jLk orbT.
case: (leqP (A - A %/ (M - A) * (M - A)) B) => [p'LB|BLp']; last first.
  case: x xLk => [_|j jLk]; first by rewrite dst0.
  have jk : j <= A %/ (M - A) by rewrite -ltnS.
  have HPt : Pt j.+1 = A - j * (M - A) by rewrite -addn1 Hjq.
  have HB2 : B < Pt j.+1.
    by rewrite HPt (leq_trans BLp') // leq_sub2l // leq_mul2r jk orbT.
  rewrite dst_above //.
  rewrite leq_subRL; last by rewrite (leq_trans (ltnW (pt_lt _))) // leq_addl.
  rewrite [Pt j.+1 + B]addnC leq_add2l.
  exact: ltnW (pt_lt _).
by apply: Hthen.
Qed.

Lemma invd_first_le :
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' <= Inf (u' + v').
Proof.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have Hp1 : Pt 1 = A by rewrite /pt muln1 HA.
have HAM : A <= M by rewrite ltnW.
have Hk : (M - A) %/ A * A + A <= M.
  by rewrite -{2}(subnK HAM) leq_add2r leq_divM.
have Hge := invd_first_le_ge.
move: Hge; rewrite /step HA HB; case: ltnP => [pLq|qLp] /= Hge; last by apply: Hge.
apply: le_inf_dst; first by rewrite (leq_trans (leq_mod _ _)) // ltnW.
move=> x xLk; rewrite !muln1 !add1n in xLk.
have Hk2 : A * ((M - A) %/ A + 1) <= M by rewrite mulnDr muln1 mulnC.
apply: mod_le_dst.
- by rewrite -HA.
- by rewrite Hp1.
rewrite Hp1 (leq_trans _ Hk2) // leq_mul2l.
by rewrite -ltnS xLk orbT.
Qed.

(** After the FIRST step [d] is EXACTLY the closest distance -- measured,
    0 violations over 3696 cases -- so the congruence there is free once the
    two inequalities are in hand.  ([invd_first_le] is the [<=] half.)
    NB this equality is special to the first step: at later steps it fails
    (150 violations out of 5152), which is why [invd] carries the weaker
    congruence rather than an equation. *)
(** The [A < M - A] branch: the witness is [B %/ A], because
    [Dst (B %/ A) = B %% A] exactly -- the point [A * (B %/ A)] is the
    largest multiple of [A] below [b].  Its index is in range because
    [M = A + (M-A) = A + ((M-A)%/A)*A + (M-A)%%A < ((M-A)%/A + 2) * A]. *)
(** The [else] case ([B < p']) is immediate: [d' = B = Dst 0].  NB the
    rewrite must be targeted -- [dst0 : Dst 0 = B] and [Inf] itself mentions
    [B], so a bare [-dst0] breaks the [Inf] on the left.

    The [then] case needs a witness: with [k = A %/ q], [q = M - A],
    [p' = A - k*q] and [t = (B - p') %/ q], the point at index [(k-t)+1] is
    [A - (k-t)*q = p' + t*q] by [pt_desc], and its distance is
    [B - (p' + t*q) = (B - p') - t*q = (B - p') %% q = d']. *)
Lemma invd_first_ge_ge_then : M - A %% M <= A %% M ->
  A - A %/ (M - A) * (M - A) <= B ->
  Inf (1 + (1 + A %/ (M - A) * 1))
    <= (B - (A - A %/ (M - A) * (M - A))) %% (M - A).
Proof.
move=> Hge Hp.
have A_gt0 : 0 < A.
  rewrite (modn_small A_lt) in Hge.
  case: (posnP A) => // A0; move: Hge; rewrite A0 subn0 leqn0 => /eqP MM.
  by move: M_gt0; rewrite MM.
have q_gt0 : 0 < M - A by rewrite subn_gt0.
set q := M - A in Hp q_gt0 *.
set k := A %/ q in Hp *.
set p' := A - k * q in Hp *.
set t := (B - p') %/ q.
have kqA : k * q <= A by rewrite leq_divM.
have p'E : p' = A %% q by rewrite /p' /k {1}(divn_eq A q) addnC addnK.
(* [t <= k] because [B - p' < M - p' = k*q + q] *)
have tk : t <= k.
  rewrite -ltnS /t ltn_divLR // mulSnr.
  have p'A : p' <= A by rewrite leq_subr.
  have Ap' : A - p' = k * q by rewrite /p' subKn.
  have -> : k * q + q = M - p' by rewrite -Ap' addnBAC // /q subnKC // ltnW.
  by rewrite ltn_sub2r // (leq_ltn_trans Hp).
(* the witness: index [(k-t)+1], whose point is [A - (k-t)*q = p' + t*q] *)
have ktq : (k - t) * q <= A.
  by rewrite (leq_trans _ kqA) // leq_mul2r leq_subr orbT.
have PxE : Pt ((k - t) + 1) = A - (k - t) * q by apply: pt_desc.
have tqkq : t * q <= k * q by rewrite leq_mul2r tk orbT.
have PxE2 : A - (k - t) * q = p' + t * q.
  by rewrite mulnBl subnBA // /p' addnBAC.
have tqB : t * q <= B - p' by rewrite leq_divM.
have PxB : Pt ((k - t) + 1) <= B.
  by rewrite PxE PxE2 -{1}(subnKC Hp) leq_add2l.
have DxE : Dst ((k - t) + 1) = (B - p') %% q.
  rewrite dst_below // PxE PxE2 subnDA.
  by rewrite {1}(divn_eq (B - p') q) addnC addnK.
rewrite -DxE; apply: inf_dst_le.
apply: (@leq_ltn_trans (k + 1)); first by rewrite leq_add2r leq_subr.
by rewrite muln1 addnA addnC ltn_add2l.
Qed.

Lemma invd_first_ge_ge : M - A %% M <= A %% M ->
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  Inf (u' + v') <= d'.
Proof.
move=> qLp0.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have Hthen := invd_first_ge_ge_then qLp0.
rewrite /step HA HB; rewrite ifN /=; last by rewrite -leqNgt -HA.
case: (leqP (A - A %/ (M - A) * (M - A)) B) => [p'LB|BLp']; last first.
  by rewrite -[X in _ <= X]dst0; apply: inf_dst_le.
by apply: Hthen.
Qed.

Lemma invd_first_ge :
  let: (_, _, d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  Inf (u' + v') <= d'.
Proof.
have Ha := am_gt0.
have HA : A %% M = A by rewrite modn_small.
have HB : B %% M = B by rewrite modn_small.
have Hp1 : Pt 1 = A by rewrite /pt muln1 HA.
have Hge := invd_first_ge_ge.
move: Hge; rewrite /step HA HB; case: ltnP => [pLq|qLp] /= Hge; last by apply: Hge.
have HzA : A * (B %/ A) <= B by rewrite mulnC leq_divM.
have Hz : Dst (B %/ A) = B %% A.
  rewrite dst_below; last by rewrite pt_mul_small Hp1 // (leq_ltn_trans HzA).
  have HPz : Pt (B %/ A) = A * (B %/ A).
    have H : Pt 1 * (B %/ A) < M by rewrite Hp1 (leq_ltn_trans HzA).
    by rewrite (pt_mul_small H) Hp1.
  by rewrite HPz mulnC {1}(divn_eq B A) addKn.
rewrite -Hz; apply: inf_dst_le.
rewrite muln1 ltn_divLR //.
apply: leq_trans B_lt _.
rewrite !mulnDl mul1n -{1}(subnKC (ltnW A_lt)) {1}(divn_eq (M - A) A).
rewrite addnA leq_add2l.
  by apply: ltnW; rewrite ltn_mod -HA.
by rewrite -HA.
Qed.

Lemma invd_first_cong :
  let: (p', q', d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  d' = Inf (u' + v') %[mod p'].
Proof.
have Hle := invd_first_le.
have Hge := invd_first_ge.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hle Hge.
by have -> : d' = Inf (u' + v') by apply/eqP; rewrite eqn_leq Hle Hge.
Qed.

Lemma invd_first :
  let: (p', q', d', u', v') := step (A %% M) (M - A %% M) (B %% M) 1 1 in
  invd p' q' d' u' v'.
Proof.
have Hm := invd_first_max.
have Hl := invd_first_le.
have Hc := invd_first_cong.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1)
     => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hm Hl Hc.
by split.
Qed.

(** and [invd] is preserved.  THE hardest of the file.

    [p < q] branch: [d' = d %% p] and the new indices are
    [u' = u + (q %/ p) * v], [v' = v].
      invd_max : [d %% p < p <= maxn p q'] -- cheap.
      invd_le  : [mod_le_dst] again, with [g := p]; [step_d_lt] (PROVED)
                 supplies the geometry that walking right by [p] realises
                 [d %% p] as a distance, and the index range of the new
                 configuration supplies the wrap bound.
    [q <= p] branch: needs the MIRROR of [step_d_lt].  Careful -- this is
    where the skeleton was wrong before: walking by [u] moves the point
    LEFT by [q], so the correct shape is
      Dst (x - j * u) = d - j * q,  side condition  j * u <= x
    which wants [pt_sub] / [dstB] below. *)
Lemma pt_sub x y : y <= x -> Pt y <= Pt x -> Pt (x - y) = Pt x - Pt y.
Proof.
move=> yx Hp; rewrite /pt mulnBr modnB //; last by rewrite leq_mul2l yx orbT.
by rewrite ltnNge Hp /= mul0n add0n.
Qed.

Lemma dstB x y : y <= x -> Pt y <= Pt x -> Dst (x - y) = (Dst x + Pt y) %% M.
Proof.
move=> yx Hp.
have HxM : Pt x <= B + M by rewrite (leq_trans (ltnW (pt_lt x))) // leq_addl.
rewrite dstE pt_sub // subnBA // dstE modnDml.
by rewrite addnBAC.
Qed.

(** [dstB] holds WITHOUT the [Pt y <= Pt x] hypothesis -- validated over
    104326944 instances (M in {24,32,48,64}, all A, B, x, y <= x): 0
    counterexamples.  This matters: it is what removes the need to
    establish [Pt u <= Pt (x - j*u)] inside [step_d_ge]'s induction, which
    is otherwise the awkward part.

    Proof plan (a two-case computation, no geometry).  Put
    [P := Pt (x-y)], [Q := Pt y]; the proved [ptD] with [subnK] gives
    [Pt x = (P + Q) %% M].  Then
      P + Q < M : [(P+Q) %% M = P+Q], and both sides reduce to
                  [(B + M - P) %% M] by [subnDA] / [subnK];
      M <= P + Q: [(P+Q) %% M = P+Q-M], and the left side picks up an
                  extra [M] which [modnDr] discards.
    The [Pt y <= Pt x] version above is the special case, already proved. *)
Lemma dstB_gen x y : y <= x -> Dst (x - y) = (Dst x + Pt y) %% M.
Proof.
move=> yx.
have Hpx : Pt x = (Pt (x - y) + Pt y) %% M by rewrite -ptD subnK.
have HP := pt_lt (x - y); have HQ := pt_lt y.
rewrite dstE [in RHS]dstE modnDml Hpx.
case: (ltnP (Pt (x - y) + Pt y) M) => H.
  rewrite (modn_small H) subnDA subnK //.
  by rewrite leq_subRL ?(leq_trans (ltnW HP)) ?leq_addl //
             (leq_trans (ltnW H)) // leq_addl.
have e2 : (Pt (x - y) + Pt y) %% M = Pt (x - y) + Pt y - M.
  rewrite -{1}(subnK H) modnDr modn_small // ltn_subLR //.
  apply: leq_ltn_trans (leq_add (ltnW HP) (leqnn _)) _.
  by rewrite ltn_add2l.
have HPB : Pt (x - y) <= B + M by rewrite (leq_trans (ltnW HP)) // leq_addl.
rewrite e2 subnBA // subnDA subnK.
  by rewrite -[in RHS]addnBAC // modnDr.
rewrite leq_subRL; last by rewrite (leq_trans HPB) // leq_addr.
apply: leq_trans (leq_add (ltnW HP) (ltnW HQ)) _.
by rewrite leq_add2r leq_addl.
Qed.

(** the mirror of [step_d_lt], with the direction of travel corrected:
    walking by index [u] moves the point LEFT by [q], hence DOWN the
    index, so it is [x - j*u].  The core identity
      q = M - Pt u -> j*u <= x -> j*q <= Dst x ->
      Dst (x - j*u) = Dst x - j*q
    is validated over 17816512 instances, 0 counterexamples.

    Proof plan: induction on [j].  The step is [dstB_gen] at [y := u],
    giving [Dst (z - u) = (Dst z + Pt u) %% M] with [Pt u = M - q]
    ([inv_qu]); then [Dst z = d - j*q >= q] (from [j.+1 <= d %/ q]) makes
    [(Dst z + M - q) %% M = Dst z - q] by [modnDr] and [subnK]. *)
Lemma step_d_ge p q d u v x j :
  inv p q d u v -> q <= p -> x < u + v -> d = Dst x ->
  j <= d %/ q -> j * u <= x -> Dst (x - j * u) = d - j * q.
Proof.
move=> iv qLp xLuv dE.
have [_ q_gt0 _ _ qE _ _ _] := iv.
have Hpu : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
have dM : d < M by rewrite dE dst_lt.
have qM : q <= M by rewrite qE leq_subr.
elim: j => [|j IH jLd juLx]; first by rewrite !mul0n !subn0 dE.
have jLd' : j <= d %/ q by apply: ltnW.
have juLx' : j * u <= x by rewrite (leq_trans _ juLx) // leq_mul2r ltnW ?orbT.
have Hq : j.+1 * q <= d.
  by rewrite (leq_trans _ (leq_divM d q)) // leq_mul2r jLd orbT.
have HqD : q <= d - j * q.
  rewrite leq_subRL; last by rewrite (leq_trans _ Hq) // leq_mul2r leqnSn orbT.
  by rewrite -mulSnr.
have H1 : d - j * q - q <= d by rewrite (leq_trans (leq_subr _ _)) // leq_subr.
have -> : x - j.+1 * u = x - j * u - u by rewrite mulSnr subnDA.
have Hu : u <= x - j * u by rewrite leq_subRL // -mulSnr.
rewrite dstB_gen // IH //.
rewrite Hpu addnBA // -addnBAC // modnDr.
rewrite (modn_small (leq_ltn_trans H1 dM)).
by rewrite mulSnr subnDA.
Qed.

(** [invd] splits into its two fields, which differ sharply in cost.
    The [invd_max] half needs nothing but [ltn_pmod]: [d'] is always a
    remainder by one of the two gaps (or, in the [else] case, is [d] with
    the test itself giving [d < p']). *)
Lemma step_invd_max p q d u v :
  inv p q d u v -> invd p q d u v ->
  let: (p', q', d', _, _) := step p q d u v in d' < maxn p' q'.
Proof.
move=> iv ivd.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
rewrite /step; case: ltnP => [pLq|qLp]; rewrite /=.
  by rewrite (leq_trans (ltn_pmod _ p_gt0)) ?leq_maxl.
case: (leqP (p - p %/ q * q) d) => [p'Ld|dLp'].
  by rewrite (leq_trans (ltn_pmod _ q_gt0)) ?leq_maxr.
by rewrite (leq_trans dLp') // leq_maxl.
Qed.

(** the [invd_le] half: the real content, shared with [invd_first]'s
    goal (4).  Both reduce to the SAME pointwise obligation.

    ** What is settled

    - [d' <= Inf (u' + v')] holds at every step: 0 violations over 14272
      steps (M in {32,64}, all A, B, N = M %/ g).
    - [d' = Inf (u' + v')] is NOT universal -- equality holds in only
      13986 of those 14272.  So the [<=] form is necessary and cannot be
      sharpened to an equation; do not try.
    - The route must therefore be [le_inf_dst] (proved) plus a POINTWISE
      bound [d' <= Dst x] for every [x < u' + v'].  That is where the
      remaining work is, and it is genuinely a universal claim -- neither
      [step_d_lt] nor [step_d_ge] gives it, since both only EXHIBIT one
      index realising a given distance.

    ** The two branches

    [p < q]: d' = d %% p, and by [step_d_lt] (proved) the points
      [x0 + j*v], [j <= d %/ p], realise [d - j*p], so [d %% p] is the
      last of them.  The new gaps are [p] and [q %% p].
    [q <= p]: d' = (d - p') %% q with [p' = p %% q], and by [step_d_ge]
      (proved) the points [x0 - j*u] realise [d - j*q], walking DOWN the
      index.  The new gaps are [p %% q] and [q].

    In both, the pointwise bound is "no point of the new configuration
    lies strictly between [b - d'] and [b]" -- i.e. [d'] is minimal.  The
    natural formulation is in terms of the two-length structure: every
    point is [j*v] or [x0 - j*u] steps from a known one, so any [x] in
    range decomposes, and its distance is [d' + (a nonneg multiple of a
    gap)].  Formulate THAT as the shared lemma, validate it, then both
    this and [invd_first] goal (4) follow by [le_inf_dst]. *)
(** The missing content, isolated.  [d' <= M] is bundled in because
    [le_inf_dst] needs it for its [n = 0] base case; the second component
    is the universal bound, which is the real work.  Both parts are
    consequences of the validated [d' <= Inf (u' + v')], so this helper is
    a faithful decomposition, not a new conjecture. *)
(** Only the NEW indices can be hard.  For [x < u + v] the bound is free:
    [d' <= d] (a remainder by a gap, or [d] itself), [d <= Inf (u+v)] by
    [invd_le], and [Inf (u+v) <= Dst x] by [inf_dst_le].  So the whole
    obligation reduces to the indices the step has just added. *)
(** The two branches add points of opposite orientation, so they are
    genuinely different obligations and are split here.

    [p < q]: the added indices run upward from [u+v]; the points ASCEND by
      [p], and [step_d_lt] (proved) is the corresponding walk.
    [q <= p]: the added indices also run upward, but the points DESCEND by
      [q] -- [step_d_ge] (proved) walks DOWN the index.  [pt_desc] above is
      the first-step instance of exactly this shape.

    In both, what remains is that EVERY index of the window is reached by
    the walk, not merely that the walk stays inside it.  That is a
    surjectivity-style claim; validate it before stating it. *)
(** ** The two-length structure, reproved natively (after CFrac/slater.v)

    ** Why this layer is needed

    [inv_pv] and [inv_qu] say [p = Pt v] and [q = M - Pt u].  They do NOT
    say that [Pt v] is the SMALLEST positive point, nor that [Pt u] is the
    largest.  [slater.v] never has this problem because there [get_min]
    and [get_max] are *defined* as the extremisers, so extremality is free.
    Our [inv] recorded only the values, and that is why every attempt to
    bound a distance from below has stalled.

    Measured (0 violations over 230 reachable states):

      p     = min {Pt m : 0 < m < u + v}
      M - q = max {Pt m :     m < u + v}

    ** The dictionary

      invx_min             <->  slater.get_min_min
      invx_max             <->  slater.get_max_max
      pt_gap_min           <->  slater.get_minB
      pt_gap_max           <->  slater.get_maxB
      pt_sub / pt_sub_wrap <->  slater's fracB / fracN steps

    Reproved rather than bridged: [slater.v] is stated over [R] with
    [frac_part], and every one of these would have to be transported back
    to a [nat] inequality.  The two gap lemmas below follow from
    extremality plus [pt_sub] (already proved) in a few lines each, which
    is cheaper than the bridge. *)

Record invx (p q u v : nat) : Prop := Invx {
  invx_min : forall m, 0 < m < u + v -> p <= Pt m;
  invx_max : forall m, m < u + v -> Pt m <= M - q;
  (* free wherever [invx] is established, since [inv_qu] gives
     [q = M - Pt u]; carried here so [pt_gap_max] need not take [inv]. *)
  invx_qM  : q <= M;
  (* [b] lies in a gap, and every gap is [p] or [q], so the nearest point
     below it is within [maxn p q].  Needed by [inf_new_lt_le], whose
     witness walks [Inf %/ p] steps and must stay inside the new range.
     Probed: 0 violations / 17608. *)
  invx_inf : Inf (u + v) < maxn p q;
  (* THE three-distance content, and what the remaining leaves actually
     use.  The [u+v] points cut the circle into gaps of size [p] and [q]
     only, so every distance in range is the closest one plus a whole
     number of gaps.  NOT implied by the three fields above -- they bound
     the points against 0 and [M-q], they say nothing about the gaps in
     between.  Probed over M in {24,32,48}, all A, all B, every reachable
     state: 0 violations / 53120. *)
  invx_gap : forall y, y < u + v ->
             exists a b, Dst y = Inf (u + v) + a * p + b * q
}.

(** the wrapping companion of [pt_sub]: when the order inverts, the
    difference of indices lands on the far side of [M]. *)
(** Here [modnB] IS the right tool -- unlike in [invd_first_le_ge_then],
    where the additive route won.  The hypothesis [Pt x < Pt y] makes
    [modnB]'s boolean term [true] (rather than killing it as in [pt_sub]),
    so the [+ M] it contributes is exactly the wrap. *)
Lemma pt_sub_wrap x y : y <= x -> Pt x < Pt y -> Pt (x - y) = M - (Pt y - Pt x).
Proof.
move=> yx Hp; rewrite /pt mulnBr modnB //; last by rewrite leq_mul2l yx orbT.
move: Hp; rewrite /pt => Hp.
have Hle : (A * x) %% M <= (A * y) %% M by apply: ltnW.
by rewrite Hp mul1n subnBA.
Qed.

(** slater.get_minB: points in index order are at least [p] apart. *)
Lemma pt_gap_min p q u v m1 m2 :
  invx p q u v -> m1 < m2 -> m2 < u + v -> Pt m1 <= Pt m2 ->
  p <= Pt m2 - Pt m1.
Proof.
move=> ix m12 m2n Hp.
rewrite -(pt_sub (ltnW m12) Hp).
apply: (invx_min ix).
by rewrite subn_gt0 m12 (leq_ltn_trans (leq_subr _ _)).
Qed.

(** slater.get_maxB: points whose order INVERTS the index order are at
    least [q] apart. *)
Lemma pt_gap_max p q u v m1 m2 :
  invx p q u v -> m2 < m1 -> m1 < u + v -> Pt m1 < Pt m2 ->
  q <= Pt m2 - Pt m1.
Proof.
move=> ix m21 m1n Hp.
have Hw : Pt (m1 - m2) = M - (Pt m2 - Pt m1) by rewrite (pt_sub_wrap (ltnW m21) Hp).
have Hmax : Pt (m1 - m2) <= M - q.
  by apply: (invx_max ix); rewrite (leq_ltn_trans (leq_subr _ _)).
move: Hmax; rewrite Hw => Hmax.
rewrite -(leq_sub2lE (m := M)) //.
exact: (invx_qM ix).
Qed.

Lemma invx_init : invx (A %% M) (M - A %% M) 1 1.
Proof.
have HA : A %% M = A by apply: modn_small.
have Hp1 : Pt 1 = A by rewrite /pt muln1.
have Inf2 : Inf (1 + 1) = minn (Dst 1) (Dst 0).
  rewrite !inf_dstS inf_dst0.
  by have -> : minn (Dst 0) M = Dst 0 by apply/minn_idPl; rewrite ltnW // dst_lt.
(* the two points are [0] and [A]; [b] sits either above [A] (gap [p]) or
   below it (gap [q]), and that fixes both [Inf] and the decomposition *)
have HI : Inf (1 + 1) = if A <= B then B - A else B.
  case: (leqP A B) => [AB|AB].
    rewrite Inf2 dst0 (_ : Dst 1 = B - A); first by apply/minn_idPl; rewrite leq_subr.
    by rewrite dst_below Hp1.
  rewrite Inf2 dst0 (_ : Dst 1 = B + M - A).
    by apply/minn_idPr; rewrite -addnBA ?leq_addr // ltnW.
  by rewrite dst_above Hp1.
have Hinf : Inf (1 + 1) < maxn (A %% M) (M - A %% M).
  rewrite HI HA; case: (leqP A B) => [AB|AB].
    by rewrite (leq_trans _ (leq_maxr _ _)) // ltn_sub2r.
  by rewrite (leq_trans _ (leq_maxl _ _)).
have Hgap : forall y, y < 1 + 1 ->
    exists a b, Dst y = Inf (1 + 1) + a * (A %% M) + b * (M - A %% M).
  move=> y; move: HI; case: (leqP A B) => [AB|AB] HI.
    have D1 : Dst 1 = B - A by rewrite dst_below Hp1.
    case: y => [|[|y]] //= _.
      by exists 1, 0; rewrite dst0 HI HA mul1n mul0n addn0 subnK.
    by exists 0, 0; rewrite D1 HI !mul0n !addn0.
  have D1 : Dst 1 = B + M - A by rewrite dst_above Hp1.
  case: y => [|[|y]] //= _.
    by exists 0, 0; rewrite dst0 HI !mul0n !addn0.
  by exists 0, 1; rewrite D1 HI mul0n addn0 mul1n HA addnBA // ltnW.
split => //.
- by move=> m; case: m => [|[|m]] //= _; rewrite Hp1 HA.
- move=> m; case: m => [|[|m]] //= _; first by rewrite pt0.
  by rewrite Hp1 HA subKn // ltnW.
by rewrite leq_subr.
Qed.

(** The one real obligation left: the three-distance step.  Conditioned as
    [inv_step] and [step_p_gt0] are -- only when the loop continues -- since
    at the terminal states ([q = 0], [u + v >= N]) [invx_min] genuinely
    fails: probed 78 violations there, 0 under the guard (376 states). *)
Lemma invx_step p q d u v :
  inv p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', _, u', v') := step p q d u v in
  u' + v' < N -> invx p' q' u' v'.
Proof. Admitted.

(** ** Top-down skeleton for the [p < q] branch

    [x] ranges over the indices this step ADDS, i.e. [u+v <= x < u+k*v+v]
    with [k = q %/ p].  Decomposition:

      L1  every such [x] is [y + m*v] with [y < u+v] and [0 < m <= k]
          (pure arithmetic: [m = (x - (u+v)) %/ v + 1]).
      L2  at such a point, [d %% p <= Dst (y + m*v)].

    L2 is the content.  Walking up the index by [v] moves the point up by
    [p] ([dstD], proved, since [p = Pt v]), so [Dst (y + m*v) = Dst y - m*p]
    while no wrap occurs, and [d %% p] must sit below every one of those.

    ** WARNING -- [invd] AS IT STANDS IS TOO WEAK FOR L2

    Measured (Python): quantifying over ALL [d0 <= Inf (u+v)] rather than
    the algorithm's [d], L2 fails 2762 times out of 184850.  Smallest:
    [M=24, A=9, B=6], state [p=3, q=6, u=2, v=3], where [Inf (u+v) = 3]
    but [Inf (u+k*v+v) = 0]; taking [d0 = 1 <= 3] gives
    [d0 %% p = 1 > 0].  So [invd_le] alone cannot prove L2.

    What the algorithm's [d] additionally satisfies -- 0 counterexamples
    over 5152 states, and it makes L2 hold in 121183 out of 121183 cases:

      d = Inf (u + v)  %[mod p]

    i.e. [p] divides the gap between [d] and the true closest distance.
    NB two weaker candidates were tested and REJECTED: [d0 <= Inf (u+v)]
    alone (above), and "[d0] is a genuine distance [Dst x0] for some
    [x0 < M]" (1456 violations out of 152992).  Being a distance is not
    enough; the congruence is what matters.

    So closing this branch needs [invd] extended with a congruence field,
    which is an invariant change rather than a new helper -- and the [q <= p]
    branch will want the analogue modulo [q], to be validated separately. *)

Lemma new_index_decomp k u v x :
  0 < v -> u + v <= x -> x < u + k * v + v ->
  exists2 m, 0 < m <= k & (x - m * v < u + v) && (m * v <= x).
Proof.
move=> v_gt0 xge xlt.
set r := x - (u + v).
have Hr : r < k * v by rewrite /r ltn_subLR // addnAC.
have Hmv : r %/ v * v + v <= x.
  apply: leq_trans (leq_add (leq_divM r v) (leqnn v)) _.
  by rewrite -(subnK xge) -/r leq_add2l leq_addl.
exists (r %/ v + 1).
  rewrite addn1 ltn0Sn /= (ltn_divLR _ _ v_gt0) //.
rewrite mulnDl mul1n Hmv andbT.
have -> : x - (r %/ v * v + v) = u + r %% v.
  rewrite -(subnK xge) -/r {1}(divn_eq r v).
  by rewrite subnDA -addnA addKn addnA addnK addnC.
by rewrite ltn_add2l ltn_mod.
Qed.

(** ** CORRECTION to the note in PR #108

    I claimed there that the congruence field might be unnecessary "if the
    gap lemmas give minimality directly".  That is WRONG, and the same
    counterexample settles it: [M=24, A=9, B=6] at state
    [p=3, q=6, u=2, v=3] is a REACHABLE state, so [invx] holds there, yet
    [Inf (u+v) = 3] while [Inf (u+k*v+v) = 0], and [d0 = 1 <= 3] gives
    [d0 %% p = 1 > 0].

    So extremality and the congruence are independent, and BOTH are needed:

      invx        constrains the CONFIGURATION (gaps are at least p / q)
      congruence  constrains [d] relative to the configuration

    The gap lemmas bound distances between two POINTS; they say nothing
    about where [b] sits relative to them, which is what [d] measures.
    That is the gap the congruence fills.

    Remaining structural change: add to [invd] the field

      invd_cong : d = Inf (u + v) %[mod p]

    (validated, 0 counterexamples over 5152 states, and it makes the two
    leaves below hold in 121183 of 121183 cases), then re-establish it in
    [invd_first] and preserve it in [step_invd].  The [q <= p] branch will
    want the analogue modulo [q], to be validated separately. *)

(** ** Scaffold for the two content leaves

    Both split on whether the walk WRAPS, i.e. whether [m * p <= Dst y]
    (resp. [m * q <= Dst y]).  Not wrapping, the walk is exact and the goal
    becomes a pure inequality about [d %% p] and [Dst y - m*p]; wrapping,
    the distance jumps and the bound comes from [d %% p < p] instead.

    NOTE, recorded so it is not retried: the tempting shortcut

      le_mod_sub : 0 < p -> d = z %[mod p] -> m * p <= z -> d %% p <= z - m*p

    does NOT apply here.  It would need [d = Dst y %[mod p]], but [invd_cong]
    only gives [d = Inf (u+v) %[mod p]], and distinct [y] have distinct
    residues.  That is why the no-wrap case keeps [inv]/[invd] as hypotheses
    rather than reducing to bare arithmetic. *)

(** NB an earlier version of this file had [step_d_lt], which is exactly
    this statement with [d = Dst x] threaded through; several comments above
    still call it "(PROVED)".  It was removed in the round-8 cleanup, so the
    induction is redone here directly on [dstD].  Note [inv] does not mention
    [d] at all, so [inv p q d1 u v -> inv p q d2 u v] -- which is why the
    [Dst y] instance below needs no extra hypothesis. *)
(** two general facts the walk lemmas share: stepping the index by [w]
    lowers the distance by [Pt w] modulo [M], and [Pt] is linear modulo [M]. *)
Lemma dst_add x w : Dst (x + w) = (Dst x + M - Pt w) %% M.
Proof.
have Hd := dstB_gen (x := x + w) (y := w) (leq_addl x w).
rewrite addnK in Hd.
have HD := dst_lt (x + w); have HP := pt_lt w.
rewrite Hd; case: (ltnP (Dst (x + w) + Pt w) M) => H.
  by rewrite (modn_small H) addnAC addnK modnDr modn_small.
have e2 : (Dst (x + w) + Pt w) %% M = Dst (x + w) + Pt w - M.
  rewrite -{1}(subnK H) modnDr modn_small // ltn_subLR //.
  by apply: leq_ltn_trans (leq_add (ltnW HD) (leqnn _)) _; rewrite ltn_add2l.
by rewrite e2 subnK ?addnK ?modn_small // (leq_trans (ltnW HP)) // leq_addl.
Qed.

Lemma pt_muln k x : Pt (k * x) = (k * Pt x) %% M.
Proof. by rewrite /pt modnMmr mulnCA. Qed.

Lemma walk_lt_nowrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> m * p <= Dst y -> Dst (y + m * v) = Dst y - m * p.
Proof.
move=> iv ivd pLq yLuv mk Hmp.
have [p_gt0 _ _ pE _ _ _ _] := iv.
elim: m Hmp {mk} => [|m IH Hmp]; first by rewrite !mul0n addn0 subn0.
have Hm : m * p <= Dst y by rewrite (leq_trans _ Hmp) // leq_mul2r leqnSn orbT.
have -> : y + m.+1 * v = y + m * v + v by rewrite mulSnr addnA.
rewrite dstD; first by rewrite IH // -pE mulSnr subnDA.
by rewrite IH // -pE leq_psubRL // -mulSnr.
Qed.

(** DEAD END, recorded so it is not retried.  The natural route here is to
    hope that [Dst y = Inf (u+v) %[mod p]] for every [y < u+v]; then
    [Dst y - m*p] would be congruent to [d] and, being non-negative, at
    least [d %% p].  That hope is FALSE: 4884 violations out of 22864
    (smallest [M=24, A=13, B=0] at [p=2, q=11, u=1, v=2], where
    [Dst 1 = 11] and [Inf (u+v) = 0]).  Distances in a two-length
    configuration differ by sums of [p]s AND [q]s, and [q] is not a multiple
    of [p].

    So this leaf needs the configuration itself, i.e. [invx] -- which is not
    yet among its hypotheses.  Adding it (with [invx_init] / [invx_step] as
    the new obligations) is the next structural step. *)
(** Split on [m] versus [Dst y %/ p]:

    - [m < Dst y %/ p]: then [(m+1)*p <= Dst y], so [p <= Dst y - m*p], and
      [d %% p < p].  No configuration knowledge needed.
    - otherwise [m = Dst y %/ p] (using [m*p <= Dst y]), so the goal reads
      [d %% p <= Dst y %% p], and [m <= q %/ p] hands us the side condition
      [Dst y %/ p <= q %/ p].

    That restricted residue comparison is [mod_le_restricted].  Probed on
    M in {24,32,48}: 0 violations / 7532.  Note the UNrestricted version is
    FALSE (2174 / 26560) -- the [Dst y %/ p <= q %/ p] guard is essential. *)
Lemma mod_le_restricted p q d u v y :
  inv p q d u v -> invd p q d u v -> invx p q u v -> p < q -> y < u + v ->
  Dst y %/ p <= q %/ p -> d %% p <= Dst y %% p.
Proof.
move=> iv ivd ix pLq yLuv Hg.
have [p_gt0 q_gt0 _ _ _ _ _ _] := iv.
have [_ _ dcong] := ivd.
have [a [b Hab]] := invx_gap ix yLuv.
have qdiv : q %/ p * p <= q by rewrite leq_divM.
(* the guard says exactly [Dst y < p + q] *)
have Hlt : Dst y < p + q.
  rewrite {1}(divn_eq (Dst y) p) addnC.
  apply: leq_ltn_trans (_ : Dst y %% p + q %/ p * p < _).
    by rewrite leq_add2l leq_mul2r Hg orbT.
  apply: leq_ltn_trans (leq_add (leqnn (Dst y %% p)) qdiv) _.
  by rewrite ltn_add2r ltn_pmod.
case: b Hab => [|[|b]] Hab.
(* no [q] in the decomposition: the two residues agree outright *)
- by rewrite Hab mul0n addn0 addnC modnMDl dcong.
(* exactly one [q]: then [a = 0] and [Dst y %% p = Inf + q %% p] *)
- have a0 : a = 0.
    case: a Hab => // a Hab; move: Hlt; rewrite Hab mul1n ltnNge => /negP[].
    by rewrite leq_add2r (leq_trans _ (leq_addl _ _)) // mulSnr leq_addl.
  move: Hab; rewrite a0 mul0n addn0 mul1n => Hab.
  have Hd : Dst y %/ p = q %/ p.
    apply/eqP; rewrite eqn_leq Hg /=.
    by rewrite leq_div2r // Hab leq_addl.
  have -> : Dst y %% p = Dst y - Dst y %/ p * p.
    by rewrite {2}(divn_eq (Dst y) p) addKn.
  rewrite Hd Hab dcong modn_small; last first.
    by move: Hlt; rewrite Hab ltn_add2r.
  rewrite leq_subRL; last by rewrite (leq_trans qdiv) // leq_addl.
  by rewrite addnC leq_add2l.
(* two or more [q]s is impossible: [p < q] gives [p + q < 2*q <= Dst y] *)
have Hq2 : p + q < 2 * q by rewrite mul2n -addnn ltn_add2r.
have HD : 2 * q <= Dst y.
  rewrite Hab (leq_trans _ (leq_addl _ _)) // leq_mul2r.
  by apply/orP; right.
by move: Hlt; rewrite ltnNge => /negP[]; exact: leq_trans (ltnW Hq2) HD.
Qed.

Lemma le_lt_nowrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> m * p <= Dst y -> d %% p <= Dst y - m * p.
Proof.
move=> iv ivd ix pLq yLuv /andP[m_gt0 mk] Hmp.
have [p_gt0 _ _ _ _ _ _ _] := iv.
have mdiv : m <= Dst y %/ p by rewrite leq_divRL.
case: (ltnP m (Dst y %/ p)) => [Hlt|Hge].
  apply: leq_trans (_ : p <= _); first by rewrite ltnW // ltn_pmod.
  by rewrite leq_subRL // -mulSnr -leq_divRL.
have mE : m = Dst y %/ p by apply/eqP; rewrite eqn_leq mdiv Hge.
rewrite mE.
have -> : Dst y - Dst y %/ p * p = Dst y %% p.
  by rewrite {1}(divn_eq (Dst y) p) addKn.
by apply: mod_le_restricted iv ivd ix pLq yLuv _; rewrite -mE.
Qed.

(** The WRAP case.  [Dst (y + m*v)] is congruent to [Dst y - m*p] mod [M],
    and [m * p <= q < M] (from [m <= q %/ p]), so when [Dst y < m*p] the
    walk lands one turn round:

      walk_lt_wrapeq : Dst (y + m * v) = Dst y + M - m * p

    -- the wrap companion of [walk_lt_nowrap], and provable the same way,
    by induction on [m] off [dstD] / [dstB_gen].

    Given it, the goal is [d %% p <= Dst y + M - m*p], where the right side
    is at least [M - q = Pt u].  What is NOT immediate is comparing that
    with [d %% p < p]: [p < q] does not by itself give [p <= Pt u].  So the
    remaining inequality is where [invx] is likely needed, exactly as in
    [le_lt_nowrap]. *)
Lemma walk_lt_wrapeq p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> Dst y < m * p -> Dst (y + m * v) = Dst y + M - m * p.
Proof.
move=> iv ivd pLq yLuv /andP[m_gt0 mk] Hy.
have [p_gt0 _ _ pE qE _ _ _] := iv.
have mpq : m * p <= q by rewrite -leq_divRL.
have mpM : m * p <= M by rewrite (leq_trans mpq) // qE leq_subr.
rewrite dst_add pt_muln -pE.
case: (ltnP (m * p) M) => [Hlt|Hge].
  rewrite (modn_small Hlt) modn_small //.
  rewrite ltn_subLR ?ltn_add2r //.
  by rewrite (leq_trans mpM) // leq_addl.
have mpE : m * p = M by apply/eqP; rewrite eqn_leq mpM Hge.
by rewrite mpE modnn subn0 modnDr modn_small ?dst_lt // addnK.
Qed.

Lemma le_lt_wrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> p < q -> y < u + v ->
  0 < m <= q %/ p -> Dst y < m * p -> d %% p <= Dst (y + m * v).
Proof.
move=> iv ivd pLq yLuv mk Hy.
rewrite (walk_lt_wrapeq iv ivd pLq yLuv mk Hy).
have [p_gt0 q_gt0 bez _ _ _ u_gt0 v_gt0] := iv.
have /andP[m_gt0 mkd] := mk.
have mpq : m * p <= q by rewrite -leq_divRL.
(* the whole point of [inv_u0]/[inv_v0]: [p + q <= M] *)
have pqM : p + q <= M by rewrite -bez leq_add // leq_pmull.
have mpM : m * p <= M by rewrite (leq_trans mpq) // (leq_trans _ pqM) // leq_addl.
apply: leq_trans (_ : p <= _); first by rewrite ltnW // ltn_pmod.
rewrite leq_subRL; last by rewrite (leq_trans mpM) // leq_addl.
apply: leq_trans (_ : M <= _); last by rewrite leq_addl.
by rewrite (leq_trans (leq_add mpq (leqnn p))) // addnC.
Qed.

Lemma step_invd_le_new_lt_at p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  p < q -> y < u + v -> 0 < m <= q %/ p -> d %% p <= Dst (y + m * v).
Proof.
move=> iv ivd ix uvLN pLq yLuv mk.
case: (leqP (m * p) (Dst y)) => [Hmp|Hmp].
  rewrite (walk_lt_nowrap iv ivd pLq yLuv mk Hmp).
  exact: le_lt_nowrap iv ivd ix pLq yLuv mk Hmp.
exact: le_lt_wrap iv ivd pLq yLuv mk Hmp.
Qed.

Lemma step_invd_le_new_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  forall x, u + v <= x < u + (q %/ p) * v + v -> d %% p <= Dst x.
Proof.
move=> iv ivd ix uvLN pLq x /andP[xge xlt].
have v_gt0 : 0 < v.
  case: (posnP v) => // v0.
  have [p_gt0 _ _ pE _ _ _ _] := iv.
  by move: p_gt0; rewrite pE v0 pt0.
have [m mk /andP[ylt myx]] := new_index_decomp v_gt0 xge xlt.
rewrite -{1}(subnK myx).
exact: step_invd_le_new_lt_at iv ivd ix uvLN pLq ylt mk.
Qed.

(** the mirror.  [new_index_decomp] is reused with [u] and [v] SWAPPED:
    its window [u + k*v + v] becomes [v + k*u + u], which is exactly this
    branch's [u + (v + (p %/ q) * u)].  The walk then descends the index
    ([step_d_ge]) instead of ascending. *)
(** the [ge] branch is EASIER than its mirror, for two reasons:

    - the new [d] is always [<= d] (the branch either subtracts and takes a
      remainder, or leaves [d] alone), so we never need a congruence -- see
      [step_ge_d_le];
    - [q = M - Pt u], so stepping the index by [u] RAISES [Dst] by [q]:
      [Dst (y + m*u) = Dst y + m*q] as long as it does not pass [M].

    So the no-wrap half is just [d' <= d <= Inf (u+v) <= Dst y <= Dst y + m*q].
    Only the wrap half ([M < Dst y + m*q]) has content. *)
Lemma step_ge_d_le p q d : q <= p ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) <= d.
Proof.
move=> qLp; case: (leqP (p - p %/ q * q) d) => // dge.
by apply: leq_trans (leq_mod _ _) _; rewrite leq_subr.
Qed.

Lemma walk_ge_nowrap p q d u v y m :
  inv p q d u v -> q <= p -> y < u + v -> 0 < m <= p %/ q ->
  Dst y + m * q < M -> Dst (y + m * u) = Dst y + m * q.
Proof.
move=> iv qLp yLuv /andP[m_gt0 mk] Hw.
have [p_gt0 q_gt0 _ pE qE _ _ _] := iv.
have PuE : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
have mqM : m * q < M by rewrite (leq_ltn_trans (leq_addl (Dst y) _)).
have Hpm : Pt (m * u) = M - m * q.
  rewrite pt_muln PuE mulnBr.
  have -> : m * M - m * q = (m - 1) * M + (M - m * q).
    rewrite addnBA; last by apply: ltnW.
    by rewrite subn1 -mulSnr prednK.
  by rewrite modnMDl modn_small // ltn_subrL muln_gt0 m_gt0 q_gt0 M_gt0.
by rewrite dst_add Hpm (subnBA _ (ltnW mqM)) addnAC addnK modn_small.
Qed.

(** the wrap companion of [walk_ge_nowrap].  [m * q <= p < M] now comes
    from [p + q <= M] ([inv_bez] with [inv_u0]/[inv_v0]), not from the
    no-wrap hypothesis. *)
Lemma walk_ge_wrapeq p q d u v y m :
  inv p q d u v -> q <= p -> y < u + v -> 0 < m <= p %/ q ->
  M <= Dst y + m * q -> Dst (y + m * u) = Dst y + m * q - M.
Proof.
move=> iv qLp yLuv /andP[m_gt0 mk] Hw.
have [p_gt0 q_gt0 bez pE qE _ u_gt0 v_gt0] := iv.
have pqM : p + q <= M by rewrite -bez leq_add // leq_pmull.
have mqp : m * q <= p by rewrite -leq_divRL.
have mqM : m * q < M.
  have pM : p < M by rewrite (leq_trans _ pqM) // -addn1 leq_add2l.
  by rewrite (leq_ltn_trans mqp).
have PuE : Pt u = M - q by rewrite qE subKn // ltnW // pt_lt.
have Hpm : Pt (m * u) = M - m * q.
  rewrite pt_muln PuE mulnBr.
  have -> : m * M - m * q = (m - 1) * M + (M - m * q).
    rewrite addnBA; last by apply: ltnW.
    by rewrite subn1 -mulSnr prednK.
  by rewrite modnMDl modn_small // ltn_subrL muln_gt0 m_gt0 q_gt0 M_gt0.
rewrite dst_add Hpm (subnBA _ (ltnW mqM)) addnAC addnK.
rewrite -{1}(subnK Hw) modnDr modn_small // ltn_subLR //.
by rewrite (leq_ltn_trans (leq_add (ltnW (dst_lt y)) (leqnn _))) // ltn_add2l.
Qed.

(** With [walk_ge_wrapeq] the goal is [d' <= Dst y + m*q - M].  This is the
    one case with no slack: the probe finds [Dst y + m*q = M] does occur
    (M=24, A=5, B=1: p=5, q=4, d=1, u=4, v=1, y=1, m=1), and there the right
    side is 0, so it forces [d' = 0].  It does come out 0 there -- [p' = 1]
    and [d = 1], so [d' = (1-1) %% 4 = 0] -- but only because [d] is tied to
    the configuration.  So unlike [le_lt_wrap], no counting argument closes
    this; it needs [d]'s relation to the walk, i.e. [invd_cong] or [invx].
    The wrap is common, not a corner case: 16809 of 80376 instances.

    Why [invx_gap] alone does NOT close it, unlike [mod_le_restricted].
    With [walk_ge_wrapeq] and [inv_bez] the goal becomes

      d' <= Inf (u+v) + a*p + (b+m)*q - M,   M <= Inf (u+v) + a*p + (b+m)*q

    and since [d' <= d <= Inf (u+v)] it would suffice that
    [M <= a*p + (b+m)*q] on its own.  That is where it breaks: [invx_inf]
    gives [Inf (u+v) < p] here (as [q <= p]), so the combination is only
    known to exceed [M - p], and [a = u-1, b+m = v+1] lands on [M - p + q],
    which is strictly inside [(M-p, M)] whenever [q < p].  So the slack
    argument fails on a reachable shape, and what is needed is the sharper
    [d = Inf (u+v) %[mod p]] fed through the walk -- the same ingredient
    [inf_cong_ge] wants.  Both remaining leaves are this one gap. *)
Lemma le_ge_wrap p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  q <= p -> y < u + v -> 0 < m <= p %/ q -> M <= Dst y + m * q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= Dst (y + m * u).
Proof. Admitted.

Lemma step_invd_le_new_ge_at p q d u v y m :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  q <= p -> y < u + v -> 0 < m <= p %/ q ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    <= Dst (y + m * u).
Proof.
move=> iv ivd ix uvLN qLp yLuv mk.
case: (ltnP (Dst y + m * q) M) => [Hw|Hw]; last first.
  by apply: le_ge_wrap iv ivd ix uvLN qLp yLuv mk Hw.
rewrite (walk_ge_nowrap iv qLp yLuv mk Hw).
apply: leq_trans (step_ge_d_le d qLp) _.
apply: leq_trans (leq_addr _ _).
have [_ dle _] := ivd.
by apply: leq_trans dle _; apply: inf_dst_le.
Qed.

Lemma step_invd_le_new_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> q <= p ->
  forall x, u + v <= x < u + (v + (p %/ q) * u) ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d) <= Dst x.
Proof.
move=> iv ivd ix uvLN qLp x /andP[xge xlt].
(* NOT derivable from [inv] (u = 0, v = 1, q = M is a model of it);
   but when [u = 0] the index range is empty, so [xge]/[xlt] clash. *)
have u_gt0 : 0 < u.
  case: (posnP u) => // u0.
  move: xlt xge; rewrite u0 muln0 addn0 add0n => H1 H2.
  by have := leq_ltn_trans H2 H1; rewrite ltnn.
have xge' : v + u <= x by rewrite addnC.
have xlt' : x < v + p %/ q * u + u by rewrite addnC.
have [m mk /andP[ylt myx]] := new_index_decomp (k := p %/ q) u_gt0
  (x := x) (u := v) (v := u) xge' xlt'.
rewrite -{1}(subnK myx).
rewrite addnC in ylt.
exact: step_invd_le_new_ge_at iv ivd ix uvLN qLp ylt mk.
Qed.

Lemma step_invd_le_new p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  forall x, u + v <= x < u' + v' -> d' <= Dst x.
Proof.
move=> iv ivd ix uvLN.
have Hlt := step_invd_le_new_lt iv ivd ix uvLN.
have Hge := step_invd_le_new_ge iv ivd ix uvLN.
rewrite /step; case: ltnP => [pLq|qLp] /=.
  by apply: Hlt.
by apply: Hge.
Qed.

Lemma step_invd_le_pt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  d' <= M /\ (forall x, x < u' + v' -> d' <= Dst x).
Proof.
move=> iv ivd ix uvLN.
have [_ dle _] := ivd.
have HdM : d <= M by rewrite (leq_trans dle) // (inf_dst_mono (leq0n (u + v))).
have Hnew := step_invd_le_new iv ivd ix uvLN.
have Hdd : let: (_, _, d', _, _) := step p q d u v in d' <= d.
  rewrite /step; case: ltnP => /= _; first by rewrite leq_mod.
  case: (leqP (p - p %/ q * q) d) => [_|_] //.
  by rewrite (leq_trans (leq_mod _ _)) // leq_subr.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hnew Hdd.
split; first by rewrite (leq_trans Hdd).
move=> x xLuv.
case: (ltnP x (u + v)) => [xold|xnew].
  by rewrite (leq_trans Hdd) // (leq_trans dle) // inf_dst_le.
by apply: Hnew; rewrite xnew xLuv.
Qed.

Lemma step_invd_le p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in d' <= Inf (u' + v').
Proof.
move=> iv ivd ix uvLN.
have H := step_invd_le_pt iv ivd ix uvLN.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in H.
have [HM Hpt] := H.
by apply: le_inf_dst.
Qed.

(** and preserve it.  The two branches are genuinely different: [p < q]
    keeps the modulus ([p' = p]) so [invd_cong] transports directly, while
    [q <= p] CHANGES it to [p %% q], so its congruence is a different
    statement and gets its own helper. *)
(** Probed on M in {24,32,48}, all A, all B: 0 violations / 2576.  This is
    STRONGER than the congruence [inf_cong_lt] needs, and it splits into two
    halves of very unequal difficulty:

    - [>=] is already proved.  [step_invd_le] gives [d %% p <= Inf (new)],
      and [invd_cong] says [d %% p] IS [Inf (u+v) %% p].
    - [<=] is the only real content: exhibit an index in the new range whose
      distance is [Inf (u+v) %% p].  Take [y] realising [Inf (u+v)] and walk
      [m := Inf (u+v) %/ p] steps of [v]; [walk_lt_nowrap] then gives
      [Dst (y + m*v) = Inf (u+v) - m*p = Inf (u+v) %% p], and [y + m*v] is in
      range because [m <= q %/ p]. *)
Lemma inf_new_lt_le p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  Inf (u + (q %/ p) * v + v) <= Inf (u + v) %% p.
Proof.
move=> iv ivd ix uvLN pLq.
have [p_gt0 q_gt0 _ _ _ _ u_gt0 v_gt0] := iv.
have uv_gt0 : 0 < u + v by rewrite addn_gt0 u_gt0.
have [y yLuv HyE] := inf_dst_ex uv_gt0.
(* [invx_inf] is what puts the walk inside the new range *)
have Iq : Inf (u + v) < q.
  by have := invx_inf ix; rewrite /maxn ifT.
set m := Inf (u + v) %/ p.
have mq : m <= q %/ p by rewrite leq_div2r // ltnW.
have mpI : m * p <= Inf (u + v) by rewrite leq_divM.
case: (posnP m) => [m0|m_gt0].
  have IltP : Inf (u + v) < p by rewrite ltnNge -divn_gt0 // -/m m0.
  rewrite (modn_small IltP).
  by apply: inf_dst_mono; rewrite -addnA leq_add2l leq_addl.
have Hm : 0 < m <= q %/ p by rewrite m_gt0.
have Hmp : m * p <= Dst y by rewrite -HyE.
have Hw := walk_lt_nowrap iv ivd pLq yLuv Hm Hmp.
rewrite -HyE in Hw.
have HwE : Dst (y + m * v) = Inf (u + v) %% p.
  by rewrite Hw /m {1}(divn_eq (Inf (u + v)) p) addKn.
rewrite -HwE; apply: inf_dst_le.
have -> : u + q %/ p * v + v = u + v + q %/ p * v.
  by rewrite -!addnA (addnC v).
by rewrite (leq_ltn_trans (leq_add (leqnn y) (_ : m * v <= q %/ p * v)))
   ?leq_mul2r ?mq ?orbT // ltn_add2r.
Qed.

Lemma inf_new_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  Inf (u + (q %/ p) * v + v) = Inf (u + v) %% p.
Proof.
move=> iv ivd ix uvLN pLq.
have [_ _ dcong] := ivd.
apply/eqP; rewrite eqn_leq (inf_new_lt_le iv ivd ix uvLN pLq) /=.
rewrite -dcong.
have := step_invd_le iv ivd ix uvLN.
by rewrite /step pLq /=.
Qed.

Lemma inf_cong_lt p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p < q ->
  Inf (u + (q %/ p) * v + v) = Inf (u + v) %[mod p].
Proof. by move=> iv ivd ix uvLN pLq; rewrite (inf_new_lt iv ivd ix uvLN pLq) modn_mod. Qed.

Lemma inf_cong_ge p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> q <= p ->
  (if p - p %/ q * q <= d then (d - (p - p %/ q * q)) %% q else d)
    = Inf (u + (v + (p %/ q) * u)) %[mod (p - p %/ q * q)].
Proof. Admitted.

Lemma step_invd_cong p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in
  d' = Inf (u' + v') %[mod p'].
Proof.
move=> iv ivd ix uvLN.
have [_ _ dcong] := ivd.
have Hlt := inf_cong_lt iv ivd ix uvLN.
have Hge := inf_cong_ge iv ivd ix uvLN.
rewrite /step; case: ltnP => [pLq|qLp] /=; last by apply: Hge.
by rewrite modn_mod dcong (Hlt pLq).
Qed.

Lemma step_invd p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in invd p' q' d' u' v'.
Proof.
move=> iv ivd ix uvLN.
have Hm := step_invd_max iv ivd.
have Hl := step_invd_le iv ivd ix uvLN.
have Hc := step_invd_cong iv ivd ix uvLN.
case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hm Hl Hc.
by split.
Qed.

(* CFrac: slater.get_min_NZ / get_max_NZ (both indices stay nonzero)
   Proof plan: by [step_pt], [p' = Pt v'] and [q' = M - Pt u'].  If
   [p' = 0] then [Pt v' = 0] with [0 < v' <= N], contradicting
   [pt_neq0]; if [q' = 0] then [Pt u' = M], impossible by [pt_lt].
   The bound [v' <= N] is where [u + v < N] is used -- check it survives
   the batched step (it does: [u' + v' <= N] after one step, because the
   loop tests [N <= u' + v'] and exits). *)
(** ** WARNING -- [inv_complete] was FALSE and is removed

    Round 3 proved [step_p_gt0] "modulo [inv_complete]":

      inv_complete : inv p q d u v -> minn p q = gcdn A M ->
                     u + v = M %/ gcdn A M

    That statement is false: 92 counterexamples out of 94 reachable states
    with [minn p q = gcdn A M] (M in {32,64}).  The smallest is M=32, A=1,
    where the INITIAL state already has [p = 1], [q = 31], [u = v = 1], so
    [minn p q = 1 = gcdn 1 32] while [u + v = 2] and [M %/ g = 32].
    Bezout only gives [u*p0 + v*q0 = M %/ g] with [gcdn p0 q0 = 1], and
    [minn p q = g] merely says [minn p0 q0 = 1] -- it does not force
    [p0 = q0 = 1], which is what completeness would need.

    Worse, [step_p_gt0] itself is FALSE as it was stated.  Counterexample,
    with [M = 32], [A = 3], [N = 32] (so [N <= M %/ gcdn A M = 32] holds):

      p=3  q=29  u=1   v=1    u+v=2
      p=3  q=2   u=10  v=1    u+v=11
      p=1  q=2   u=10  v=11   u+v=21 < N,  and the step gives q' = 0.

    So [u + v < N] does NOT keep the next [q] positive.  What is true is
    that positivity is only needed when the loop CONTINUES: [run] returns
    [d'] as soon as [N <= u' + v'], and [exit_bound] needs only [invd],
    never [inv].  Hence the corrected statements below condition on
    [u' + v' < N] rather than [u + v < N], and [run_sound] must apply
    [inv_step] inside its recursive branch, where that is available.

    Both [step_p_gt0] and [inv_step] were rewritten against those
    corrected statements and are now proved (their earlier proofs were
    worthless, having gone through a false lemma).  The right replacement for [inv_complete] is not a completeness
    statement at all; it is whatever rules out [p %| q] while the loop is
    still running, and that should be characterised by the harness before
    anything is stated. *)

(** The proof needs NO completeness statement -- Bezout on the NEW state
    plus [N <= M %/ gcdn A M] is exactly enough.  If [q' = 0] then
    [step_bez] degenerates to [u' * p = M], and [p %| q] forces
    [p = gcdn p q = gcdn A M], so [u' = M %/ gcdn A M >= N], contradicting
    [u' + v' < N].  Symmetrically for [p' = 0].  ([inv_complete], the false
    lemma of round 3, was a wrong turn: it was never needed.) *)
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
  have pg : p = gcdn A M by rewrite -gE; apply/esym/gcdn_idPl; rewrite /dvdn qmp.
  move: Hb; rewrite q0 muln0 addn0 => Hb.
  have Hu : u + q %/ p * v = M %/ p by rewrite -Hb mulnK.
  by move: Huv; rewrite Hu pg ltnNge (leq_trans N_le_Mg (leq_addr v _)).
case: (posnP (p - p %/ q * q)) => [p0|] //.
have pme : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
have pmq : p %% q = 0 by rewrite -pme p0.
have qg : q = gcdn A M by rewrite -gE gcdnC; apply/esym/gcdn_idPl; rewrite /dvdn pmq.
move: Hb; rewrite p0 muln0 add0n => Hb.
have Hv : v + p %/ q * u = M %/ q by rewrite -Hb mulnK.
by move: Huv; rewrite Hv qg ltnNge (leq_trans N_le_Mg (leq_addl u _)).
Qed.

(* glue -- assemble [step_p_gt0], [step_bez], [step_pt], [step_d] into
   the record.  Mechanical once the four are done; write it last. *)
(** conditioned as [step_p_gt0] is: only needed when the loop continues. *)
Lemma inv_step p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in
  u' + v' < N -> inv p' q' d' u' v'.
Proof.
move=> iv uvLN.
have Hg := step_p_gt0 iv uvLN.
have Hb := step_bez iv.
have Hpt := step_pt iv.
have [_ _ _ _ _ gE u_gt0 v_gt0] := iv.
move: Hg Hb Hpt; rewrite /step.
have [pLq|qLp] := ltnP => /= Hg Hb Hpt Huv.
  have [Hp Hq] := Hg Huv.
  have [Hpv Hqu] := Hpt Hp Hq.
  split => //.
    have -> : q - q %/ p * p = q %% p by rewrite {1}(divn_eq q p) addnC addnK.
    by rewrite gcdn_modr.
  by rewrite addn_gt0 u_gt0.
have [Hp Hq] := Hg Huv.
have [Hpv Hqu] := Hpt Hp Hq.
split => //.
  have -> : p - p %/ q * q = p %% q by rewrite {1}(divn_eq p q) addnC addnK.
  by rewrite gcdnC gcdn_modr gcdnC.
by rewrite addn_gt0 v_gt0.
Qed.

(** *** Termination *)

(** [p + q] strictly decreases: each branch subtracts at least the other
    length, which is positive. *)
(* pure -- [q - (q %/ p) * p = q %% p < p <= q] by [ltn_mod] (needs
   [0 < p], from [inv_p0]), so [q] strictly drops in the first branch and
   [p] in the second.  One [modn_def]/[ltn_mod] each; no geometry. *)
Lemma step_measure p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, _, _) := step p q d u v in p' + q' < p + q.
Proof.
case => p_gt0 q_gt0 _ _ _ _ _ _ _.
rewrite /step; have [pLq|qLp] := ltnP; rewrite /=.
  have kp_gt0 : 0 < q %/ p * p by rewrite muln_gt0 p_gt0 andbT divn_gt0 // ltnW.
  by rewrite ltn_add2l ltn_subrL kp_gt0 q_gt0.
have kq_gt0 : 0 < p %/ q * q by rewrite muln_gt0 q_gt0 andbT divn_gt0.
by rewrite ltn_add2r ltn_subrL kq_gt0 p_gt0.
Qed.

(** [fuel_enough] was in the skeleton to relate an arbitrary fuel to
    [p + q]; it turned out to be unnecessary and has been removed.
    [run_sound] carries [p + q <= fuel] directly, and [lefevre] runs with
    [fuel = M] while [p + q = A %% M + (M - A %% M) = M], so the
    hypothesis is met exactly.  Nothing else referred to it. *)


(** *** The exit, and the main result *)

(** At the exit [u + v >= N], so the configuration has at least [N]
    points; [d] is a distance in that configuration, hence at most the
    infimum taken over the smaller set [x < N]. *)
(* CFrac: slater.LminDmax is the reason [u + v] overshoots [N] at all
     LminDmax : n < get_min n + get_max n
   Proof plan -- this one is SHORT and worth doing early to see the
   endgame.  From [inv_d] get [x < u + v] with [d = Dst x].  Then
     d = Dst x >= Inf (u + v)      by [inf_dst_le]
   and                              Inf (u + v) <= Inf N   is the wrong way!
   So instead argue directly: [x < u + v] and [N <= u + v] do NOT give
   [x < N].  The correct route is
     d = Dst x  and  Inf N = min over y < N,
   so we need [x < N] OR a point of the configuration below [N].  Use
   [inf_dst_mono] with [N <= u + v]: [Inf (u+v) <= Inf N], and
   [Inf (u+v) <= Dst x = d] gives the WRONG direction too.
   ==> The statement as written may need [d <= Dst x] for some [x < N]
   rather than [inv_d]'s equality.  RESOLVE THIS FIRST: it is the one
   place where I am not certain the invariant as stated is strong enough,
   and it is cheap to settle by extending the vm_compute harness in
   scratch (test [d <= Inf N] at every state, not just at the exit).
   If it fails, strengthen [inv_d] to
     exists2 x, x < minn (u + v) N & d = Dst x
   which is what the algorithm actually maintains. *)
(** At the exit [N <= u + v], so the configuration has at least [N]
    points and its closest-left distance is at most the one over the
    smaller index range; [invd_le] then gives the bound. *)
Lemma exit_bound p q d u v :
  invd p q d u v -> N <= u + v -> d <= Inf N.
Proof.
by case=> _ dLinf _ NLuv; apply: leq_trans dLinf (inf_dst_mono NLuv).
Qed.


(* glue -- induction on [fuel]; at each turn either the loop exits and
   [exit_bound] applies, or [inv_step] re-establishes the invariant. *)
Lemma run_sound fuel p q d u v :
  inv p q d u v -> invd p q d u v -> invx p q u v -> u + v < N -> p + q <= fuel ->
  run fuel p q d u v N <= Inf N.
Proof.
elim: fuel p q d u v => [|fuel IH] p q d u v iv ivd ix uvLN Lf.
  have [p_gt0 _ _ _ _ _ _ _] := iv.
  by move: Lf; rewrite leqn0 addn_eq0 => /andP[/eqP p0 _]; rewrite p0 in p_gt0.
have Hi := inv_step iv uvLN.
have Hx := invx_step iv ix uvLN.
have Hd := step_invd iv ivd ix uvLN.
have Hm := step_measure iv uvLN.
rewrite /=; case E: (step p q d u v) => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hi Hx Hd Hm.
case: (leqP N (u' + v')) => [NLuv|uvLN'].
  exact: exit_bound Hd NLuv.
apply: IH => //; [exact: Hi uvLN' | exact: Hx uvLN' | ].

by rewrite -ltnS (leq_trans Hm).
Qed.

(** The algorithm returns a lower bound on the infimum. *)
(* glue -- [run_sound] applied to [inv_init], with fuel [M] and
   [A %% M + (M - A %% M) = M] by [subnKC]. *)
Theorem lefevre_sound : 2 < N -> lefevre M A B N <= Inf N.
Proof.
move=> N_gt2; rewrite /lefevre.
have HM : A %% M <= M by rewrite ltnW // ltn_mod.
have Hpq : A %% M + (M - A %% M) = M by rewrite subnKC.
have Hi := inv_step inv_init N_gt2.
have Hx := invx_step inv_init invx_init N_gt2.
have Hd := invd_first.
have Hm := step_measure inv_init N_gt2.
rewrite -{1}(prednK M_gt0) /=.
case E: (step (A %% M) (M - A %% M) (B %% M) 1 1)
     => [[[[p' q'] d'] u'] v'].
rewrite E /= in Hi Hx Hd Hm.
case: (leqP N (u' + v')) => [NLuv|uvLN'].
  exact: exit_bound Hd NLuv.
apply: run_sound => //; [exact: Hi uvLN' | exact: Hx uvLN' |].
by rewrite -ltnS prednK // (leq_trans Hm) // Hpq.
Qed.

(** The form the search actually uses: if the returned bound clears the
    threshold, there is no hard-to-round case in this sub-interval. *)
(* glue -- [lefevre_sound] then [inf_dst_le]; two lines.
   This is the statement the HR-case search consumes, so it is worth
   writing down even while everything above is admitted: it pins the
   interface and lets Search.v/Check.v be re-plumbed against it. *)
Corollary lefevre_test eps :
  2 < N -> eps < lefevre M A B N -> forall x, x < N -> eps < Dst x.
Proof.
move=> N_gt2 epsL x xLN.
apply: leq_trans epsL _.
by apply: leq_trans (lefevre_sound N_gt2) _; apply: inf_dst_le xLN.
Qed.

End Theory.
