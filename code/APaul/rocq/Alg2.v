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

(** [inf { b - a*x mod 1 | x < n }], scaled by [M]. *)
Fixpoint inf_dst (M A B n : nat) : nat :=
  if n is n1.+1 then minn (dst M A B n1) (inf_dst M A B n1) else M.

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

Local Notation Pt := (pt M A).
Local Notation Dst := (dst M A B).
Local Notation Inf := (inf_dst M A B).

(** *** Warm-up: elementary facts about the specification *)

(* pure -- [ltn_pmod], needs [M_gt0]. *)
Lemma pt_lt x : Pt x < M.
Proof. Admitted.

(* pure -- [muln0], [mod0n]. *)
Lemma pt0 : Pt 0 = 0.
Proof. Admitted.

(** the lattice is additive mod M *)
(* pure -- [mulnDr] then [modnDm].  Do this one first, everything about
   the geometry is phrased with it. *)
Lemma ptD x y : Pt (x + y) = (Pt x + Pt y) %% M.
Proof. Admitted.

(* pure -- [ltn_pmod]. *)
Lemma dst_lt x : Dst x < M.
Proof. Admitted.

(* pure -- [pt0], then [B + M - 0 = B + M] and [modnDr], using [B_lt]. *)
Lemma dst0 : Dst 0 = B.
Proof. Admitted.

(** [Dst] read as a difference: this is the bridge to the geometry. *)
(* pure -- definitional, [by []].  Kept as a named lemma so the proofs
   below never unfold [dst]. *)
Lemma dstE x : Dst x = (B + M - Pt x) %% M.
Proof. Admitted.

(** moving one lattice step to the right lowers the distance by [Pt y],
    unless it wraps.  The workhorse for [step_d]. *)
(* CFrac: slater.get_minD / get_maxD
     get_minD : `{(m + get_min n) * a} = `{m * a} + `{get_min n * a}
   i.e. exactly "the fractional parts add when they do not wrap".
   Scaled: [ptD] plus the fact that under [Pt y <= Dst x] the sum stays
   below [M], so the outer [%% M] disappears.
   Proof plan: rewrite [dstE], [ptD]; the hypothesis gives
   [Pt x + Pt y < M] (else the distance would have wrapped), so
   [modn_small] applies and it is [subnDA] bookkeeping.
   PROVE THIS EARLY -- step_d_lt and step_d_ge are both iterations of it. *)
Lemma dstD x y : Pt y <= Dst x -> Dst (x + y) = Dst x - Pt y.
Proof. Admitted.

(* pure -- definitional, [by []]. *)
Lemma inf_dstS n : Inf n.+1 = minn (Dst n) (Inf n).
Proof. Admitted.

(** the infimum is a lower bound on every distance in range *)
(* pure -- induction on [n]; [inf_dstS] then [geq_minl]/[geq_minr] and
   [ltnS], case on [x == n]. *)
Lemma inf_dst_le n x : x < n -> Inf n <= Dst x.
Proof. Admitted.

(** more points can only lower the infimum *)
(* pure -- induction on [n - m] (or [subnK] then induction); each step is
   [geq_minr].  Needed at the exit: the configuration has [u+v >= N]
   points, so its infimum is below [Inf N]. *)
Lemma inf_dst_mono m n : m <= n -> Inf n <= Inf m.
Proof. Admitted.

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
  (* [d] is a genuine distance to a point of the current configuration.
     NB this is the SAFE direction: it gives [Inf (u+v) <= d].  The
     useful bound [d <= Inf N] comes out at the exit, from [u+v >= N]. *)
  inv_d   : exists2 x, x < u + v & d = Dst x
}.

(** *** Initialisation *)

(* CFrac: slater.get_min1 / (the get_max analogue)
     get_min 1 = 1, get_max 1 = 1 -- the configuration on {0, {a}}.
   Proof plan, field by field:
     inv_p0/inv_q0 : from [A_lt] and [pt_neq0 1] (needs [N_gt0]);
     inv_bez       : 1 * A + 1 * (M - A) = M, i.e. [subnKC] with [A_lt];
     inv_pv        : [Pt 1 = A %% M], by [muln1];
     inv_qu        : ditto;
     inv_d         : witness [x := 0], since [dst0] gives [Dst 0 = B]
                     and [B %% M = B] by [B_lt] -- note [0 < 1 + 1].
   Nothing here is hard; it is the natural warm-up after [dstD]. *)
Lemma inv_init : inv (A %% M) (M - A %% M) (B %% M) 1 1.
Proof. Admitted.

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
Proof. Admitted.

(** the batched Euclid step: [k] applications of slater's [get_minS] /
    [get_maxS] at once (Property 2 of the paper).  Induction on [k],
    through the two one-step lemmas below. *)

(** one point added on the left: [v] keeps realising the smallest
    positive point, [u] moves to [u + v].  (slater: [get_maxS].) *)
(* CFrac: slater.get_maxS
     get_max n.+1 = if `{get_max n * a} <= `{n.+1 * a} then n.+1 else get_max n
   Here the new point is [Pt (u + v)] and it lands in the RIGHTMOST
   interval (that is what [p < q] encodes), so [get_max] moves to
   [u + v] and the right gap shrinks from [q] to [q - p].
   Proof plan: [inv_qu] gives [q = M - Pt u]; [ptD] gives
   [Pt (u + v) = (Pt u + Pt v) %% M = Pt u + p] (no wrap, since
   [p = Pt v < q = M - Pt u]).  Then [M - Pt (u+v) = q - p] by [subnDA].
   The [u + v < N] hypothesis is only needed to invoke [pt_neq0]. *)
Lemma step_pt_one_lt p q u v :
  inv p q (Dst 0) u v -> p < q -> u + v < N ->
  (p = Pt v) /\ (q - p = M - Pt (u + v)).
Proof. Admitted.

(** one point added on the right.  (slater: [get_minS].) *)
(* CFrac: slater.get_minS
     get_min n.+1 = if `{n.+1 * a} <= `{get_min n * a} then n.+1 else get_min n
   Mirror image of the previous one: the new point falls in the LEFTMOST
   interval, [get_min] moves to [v + u], and the left gap shrinks from
   [p] to [p - q].  Same proof plan with [inv_pv] in place of [inv_qu]. *)
Lemma step_pt_one_ge p q u v :
  inv p q (Dst 0) u v -> q <= p -> u + v < N ->
  (p - q = Pt (v + u)) /\ (q = M - Pt u).
Proof. Admitted.

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
  inv p q d u v -> u + v < N ->
  let: (p', q', _, u', v') := step p q d u v in
  (p' = Pt v') /\ (q' = M - Pt u').
Proof. Admitted.

(** THE hard one: the [d] update stays a genuine distance.

    Attack it through the two branches separately.  In each, the claim is
    that reducing [d] modulo an interval length lands on another point of
    the configuration -- because, by Property 3 (directed reduction), the
    points added in this step are placed at regular spacing [p] (resp.
    [q]) going from [b] towards 0. *)

(** branch [p < q]: [k = q/p] points of the configuration lie at
    [x + j*v] for [j <= k], spaced by [p]; so [d %% p] is again a
    distance. *)
(* CFrac: slater.get_nextDmin
     get_next n m = (m + get_min n)%N   when  m + get_min n <= n
   i.e. the successor of a point is obtained by adding [get_min n] to its
   index -- which is precisely "walking right by [p] at a time".
   Proof plan: induction on [j].  The step is [dstD] with [y := v],
   using [Pt v = p] ([inv_pv]) and [j * p <= d] (from [j <= d %/ p] and
   [leq_trunc_div]) to discharge [Pt v <= Dst (x + j*v)].
   This is the heart of Property 3 (directed reduction). *)
Lemma step_d_lt p q d u v x j :
  inv p q d u v -> p < q -> x < u + v -> d = Dst x ->
  j <= d %/ p -> Dst (x + j * v) = d - j * p.
Proof. Admitted.

(* CFrac: slater.get_prev / get_prev_spec (the closest point on the left)
   Proof plan: take [j := d %/ p] in [step_d_lt].  Then
     Dst (x + j*v) = d - (d %/ p) * p = d %% p    by [divn_eq]/[modnE],
   so the witness is [x := x + (d %/ p) * v].  The index bound
   [x + (d %/ p)*v < u + (q %/ p)*v + v] holds because [d < q] (from
   [inv_d] and the configuration) forces [d %/ p <= q %/ p].
   NB only membership is claimed, not minimality -- that is what makes
   the inequality version of the invariant enough. *)
Lemma step_d_lt_mem p q d u v :
  inv p q d u v -> p < q -> u + v < N ->
  exists2 x, x < u + (q %/ p) * v + v & d %% p = Dst x.
Proof. Admitted.

(** branch [q <= p]: same, spaced by [q], after one subtraction of the
    new [p]. *)
(* CFrac: slater.get_nextDmax (mirror of get_nextDmin)
   Same induction as [step_d_lt], with [y := u] and [Pt u = M - q]
   ([inv_qu]).  Careful: here walking by [u] moves LEFT by [q], so the
   [dstD] instance is the one where the step size is [q], not [Pt u].
   Expect this to be the fiddliest of the four -- do [step_d_lt] first
   and mirror it. *)
Lemma step_d_ge p q d u v x j :
  inv p q d u v -> q <= p -> x < u + v -> d = Dst x ->
  j <= d %/ q -> Dst (x + j * u) = d - j * q.
Proof. Admitted.

(* CFrac: slater.get_prev / get_prev_spec
   This is the branch where the algorithm first subtracts the NEW [p]
   (line 13-14 of Algorithm 2) and only then reduces modulo [q].  So:
     - [p' <= d] is the guard, and [d - p'] is again a distance, by
       [dstD] with [y := v'] where [v' = v + (p %/ q) * u] (this needs
       [step_pt] for the branch, so prove [step_pt] BEFORE this one);
     - then take [j := (d - p') %/ q] in [step_d_ge].
   Witness: [x + v' + ((d - p') %/ q) * u]. *)
Lemma step_d_ge_mem p q d u v (p' := p - (p %/ q) * q) :
  inv p q d u v -> q <= p -> u + v < N -> p' <= d ->
  exists2 x, x < u + (v + (p %/ q) * u) & (d - p') %% q = Dst x.
Proof. Admitted.

(* glue -- case on [p < q] and feed [step_d_lt_mem] / [step_d_ge_mem].
   The [q <= p] branch has a third case, [~~ (p' <= d)], where [d] is
   left UNCHANGED: there the old witness from [inv_d] still works, since
   [u + v <= u' + v'] (the indices only grow).  Do not overlook it -- it
   is the case that makes the returned bound strict rather than tight. *)
Lemma step_d p q d u v :
  inv p q d u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  exists2 x, x < u' + v' & d' = Dst x.
Proof. Admitted.

(** [p] cannot collapse to 0 before the loop exits (that would be Euclid
    terminating, i.e. the whole configuration placed, which [pt_neq0]
    forbids while [u + v <= N]). *)
(* CFrac: slater.get_min_NZ / get_max_NZ (both indices stay nonzero)
   Proof plan: by [step_pt], [p' = Pt v'] and [q' = M - Pt u'].  If
   [p' = 0] then [Pt v' = 0] with [0 < v' <= N], contradicting
   [pt_neq0]; if [q' = 0] then [Pt u' = M], impossible by [pt_lt].
   The bound [v' <= N] is where [u + v < N] is used -- check it survives
   the batched step (it does: [u' + v' <= N] after one step, because the
   loop tests [N <= u' + v'] and exits). *)
Lemma step_p_gt0 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, _, _) := step p q d u v in 0 < p' /\ 0 < q'.
Proof. Admitted.

(* glue -- assemble [step_p_gt0], [step_bez], [step_pt], [step_d] into
   the record.  Mechanical once the four are done; write it last. *)
Lemma inv_step p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in inv p' q' d' u' v'.
Proof. Admitted.

(** *** Termination *)

(** [p + q] strictly decreases: each branch subtracts at least the other
    length, which is positive. *)
(* pure -- [q - (q %/ p) * p = q %% p < p <= q] by [ltn_mod] (needs
   [0 < p], from [inv_p0]), so [q] strictly drops in the first branch and
   [p] in the second.  One [modn_def]/[ltn_mod] each; no geometry. *)
Lemma step_measure p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, _, _) := step p q d u v in p' + q' < p + q.
Proof. Admitted.

(** hence [M] units of fuel always suffice, since [p + q = M] initially. *)
(* pure -- induction on [fuel], using [step_measure] to keep the
   hypothesis [p' + q' <= fuel'].  The point is only that [run] stops
   asking for fuel before it runs out, so the [else d] branch of [run] is
   never reached; state it that way if the equation form is awkward. *)
Lemma fuel_enough fuel p q d u v :
  inv p q d u v -> p + q <= fuel ->
  run fuel p q d u v N = run (p + q) p q d u v N.
Proof. Admitted.

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
Lemma exit_bound p q d u v :
  inv p q d u v -> N <= u + v -> d <= Inf N.
Proof. Admitted.

(* glue -- induction on [fuel]; at each turn either the loop exits and
   [exit_bound] applies, or [inv_step] re-establishes the invariant. *)
Lemma run_sound fuel p q d u v :
  inv p q d u v -> p + q <= fuel -> run fuel p q d u v N <= Inf N.
Proof. Admitted.

(** The algorithm returns a lower bound on the infimum. *)
(* glue -- [run_sound] applied to [inv_init], with fuel [M] and
   [A %% M + (M - A %% M) = M] by [subnKC]. *)
Theorem lefevre_sound : lefevre M A B N <= Inf N.
Proof. Admitted.

(** The form the search actually uses: if the returned bound clears the
    threshold, there is no hard-to-round case in this sub-interval. *)
(* glue -- [lefevre_sound] then [inf_dst_le]; two lines.
   This is the statement the HR-case search consumes, so it is worth
   writing down even while everything above is admitted: it pins the
   interface and lets Search.v/Check.v be re-plumbed against it. *)
Corollary lefevre_test eps :
  eps < lefevre M A B N -> forall x, x < N -> eps < Dst x.
Proof. Admitted.

End Theory.
