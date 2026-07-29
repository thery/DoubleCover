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

Lemma pt_lt x : Pt x < M.
Proof. Admitted.

Lemma pt0 : Pt 0 = 0.
Proof. Admitted.

(** the lattice is additive mod M *)
Lemma ptD x y : Pt (x + y) = (Pt x + Pt y) %% M.
Proof. Admitted.

Lemma dst_lt x : Dst x < M.
Proof. Admitted.

Lemma dst0 : Dst 0 = B.
Proof. Admitted.

(** [Dst] read as a difference: this is the bridge to the geometry. *)
Lemma dstE x : Dst x = (B + M - Pt x) %% M.
Proof. Admitted.

(** moving one lattice step to the right lowers the distance by [Pt y],
    unless it wraps.  The workhorse for [step_d]. *)
Lemma dstD x y : Pt y <= Dst x -> Dst (x + y) = Dst x - Pt y.
Proof. Admitted.

Lemma inf_dstS n : Inf n.+1 = minn (Dst n) (Inf n).
Proof. Admitted.

(** the infimum is a lower bound on every distance in range *)
Lemma inf_dst_le n x : x < n -> Inf n <= Dst x.
Proof. Admitted.

(** more points can only lower the infimum *)
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

Lemma inv_init : inv (A %% M) (M - A %% M) (B %% M) 1 1.
Proof. Admitted.

(** *** One step preserves the invariant

    Split into the four independent obligations so they can be attacked
    separately; [inv_step] just glues them. *)

Lemma step_bez p q d u v :
  inv p q d u v ->
  let: (p', q', _, u', v') := step p q d u v in u' * p' + v' * q' = M.
Proof. Admitted.

(** the batched Euclid step: [k] applications of slater's [get_minS] /
    [get_maxS] at once (Property 2 of the paper).  Induction on [k],
    through the two one-step lemmas below. *)

(** one point added on the left: [v] keeps realising the smallest
    positive point, [u] moves to [u + v].  (slater: [get_maxS].) *)
Lemma step_pt_one_lt p q u v :
  inv p q (Dst 0) u v -> p < q -> u + v < N ->
  (p = Pt v) /\ (q - p = M - Pt (u + v)).
Proof. Admitted.

(** one point added on the right.  (slater: [get_minS].) *)
Lemma step_pt_one_ge p q u v :
  inv p q (Dst 0) u v -> q <= p -> u + v < N ->
  (p - q = Pt (v + u)) /\ (q = M - Pt u).
Proof. Admitted.

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
Lemma step_d_lt p q d u v x j :
  inv p q d u v -> p < q -> x < u + v -> d = Dst x ->
  j <= d %/ p -> Dst (x + j * v) = d - j * p.
Proof. Admitted.

Lemma step_d_lt_mem p q d u v :
  inv p q d u v -> p < q -> u + v < N ->
  exists2 x, x < u + (q %/ p) * v + v & d %% p = Dst x.
Proof. Admitted.

(** branch [q <= p]: same, spaced by [q], after one subtraction of the
    new [p]. *)
Lemma step_d_ge p q d u v x j :
  inv p q d u v -> q <= p -> x < u + v -> d = Dst x ->
  j <= d %/ q -> Dst (x + j * u) = d - j * q.
Proof. Admitted.

Lemma step_d_ge_mem p q d u v (p' := p - (p %/ q) * q) :
  inv p q d u v -> q <= p -> u + v < N -> p' <= d ->
  exists2 x, x < u + (v + (p %/ q) * u) & (d - p') %% q = Dst x.
Proof. Admitted.

Lemma step_d p q d u v :
  inv p q d u v -> u + v < N ->
  let: (_, _, d', u', v') := step p q d u v in
  exists2 x, x < u' + v' & d' = Dst x.
Proof. Admitted.

(** [p] cannot collapse to 0 before the loop exits (that would be Euclid
    terminating, i.e. the whole configuration placed, which [pt_neq0]
    forbids while [u + v <= N]). *)
Lemma step_p_gt0 p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, _, _) := step p q d u v in 0 < p' /\ 0 < q'.
Proof. Admitted.

Lemma inv_step p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', d', u', v') := step p q d u v in inv p' q' d' u' v'.
Proof. Admitted.

(** *** Termination *)

(** [p + q] strictly decreases: each branch subtracts at least the other
    length, which is positive. *)
Lemma step_measure p q d u v :
  inv p q d u v -> u + v < N ->
  let: (p', q', _, _, _) := step p q d u v in p' + q' < p + q.
Proof. Admitted.

(** hence [M] units of fuel always suffice, since [p + q = M] initially. *)
Lemma fuel_enough fuel p q d u v :
  inv p q d u v -> p + q <= fuel ->
  run fuel p q d u v N = run (p + q) p q d u v N.
Proof. Admitted.

(** *** The exit, and the main result *)

(** At the exit [u + v >= N], so the configuration has at least [N]
    points; [d] is a distance in that configuration, hence at most the
    infimum taken over the smaller set [x < N]. *)
Lemma exit_bound p q d u v :
  inv p q d u v -> N <= u + v -> d <= Inf N.
Proof. Admitted.

Lemma run_sound fuel p q d u v :
  inv p q d u v -> p + q <= fuel -> run fuel p q d u v N <= Inf N.
Proof. Admitted.

(** The algorithm returns a lower bound on the infimum. *)
Theorem lefevre_sound : lefevre M A B N <= Inf N.
Proof. Admitted.

(** The form the search actually uses: if the returned bound clears the
    threshold, there is no hard-to-round case in this sub-interval. *)
Corollary lefevre_test eps :
  eps < lefevre M A B N -> forall x, x < N -> eps < Dst x.
Proof. Admitted.

End Theory.
