(** * Generating the polynomial approximations: the Taylor shifts

    Section 5 of [doc/mourad.pdf] (Fortin, Gouicem, Graillat).  The search
    of Section 4 needs, for every interval of [N] consecutive arguments, a
    polynomial approximating the target function there.  Section 5 builds
    all of them from a single polynomial, using only additions.

    Everything in that section is exact: the coefficients are fixed-point
    integers and the shifts do no rounding.  So what follows is plain
    algebra over an abelian group [V].  The approximation error is a
    separate matter: [Cheb.v] certifies one polynomial against [exp], and
    because the shifts are exact that one certificate covers every
    interval the shifts produce ([ShiftExp.v]).

    The pieces, in the order of the paper:

    - the forward difference [diff f n = f n.+1 - f n] and Newton's formula
      [f (n + k) = sum_i (diff^i f n) * C(k, i)] (Definition 5, Figure 7);
    - the tabulated difference shift: one step of [tstep] on the table of
      the first [d+1] differences advances it by one argument, using
      additions only (Figure 8);
    - the straightforward shift [sstep k]: [k] steps at once, through the
      upper triangular Toeplitz matrix of binomials [C(k, j - i)];
    - the hybrid split of Section 5.2: a shift by [t S + s] as [t]
      straightforward steps then [s] tabulated ones;
    - the hierarchical method: writing [x = k N + m] gives
      [P (k N + m) = sum_j a_j (k) C(m, j)] with each [a_j] again a
      polynomial in [k], so one shift by [N] becomes [d+1] shifts by [1].

    The last section gives the degree toolkit needed to see that a
    concrete polynomial has a finite difference table at all. *)

From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Difference.

Variable V : zmodType.
Implicit Types (f g : nat -> V) (c : V).

(** ** The forward difference operator *)

(** [diff] is the paper's [Delta] and [diffn i] its [i]-th power.  A
    function [nat -> V] stands for a polynomial sampled at the integers. *)
Definition diff f : nat -> V := fun n => f n.+1 - f n.

Definition diffn i f : nat -> V := iter i diff f.

Lemma diffn0 f : diffn 0 f = f.
Proof. by []. Qed.

Lemma diffnS i f : diffn i.+1 f = diff (diffn i f).
Proof. by []. Qed.

Lemma diffnSr i f : diffn i.+1 f = diffn i (diff f).
Proof. exact: iterSr. Qed.

Lemma diffnD i j f : diffn (i + j)%N f = diffn i (diffn j f).
Proof. by rewrite /diffn iterD. Qed.

(** The recurrence the tabulated shift runs on: entry [i] of the table
    moves forward by adding entry [i + 1]. *)
Lemma diff_stepE i f n : diffn i f n.+1 = diffn i f n + diffn i.+1 f n.
Proof. by rewrite diffnS /diff addrC subrK. Qed.

(** Differences commute with a shift of the argument. *)
Lemma diffn_shift i f o n :
  diffn i (fun m => f (o + m)%N) n = diffn i f (o + n)%N.
Proof.
by elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH addnS.
Qed.

Lemma diffn_opp i f n : diffn i (fun m => - f m) n = - diffn i f n.
Proof.
by elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH opprK opprB addrC.
Qed.

Lemma diffn_add i f g n :
  diffn i (fun m => f m + g m) n = diffn i f n + diffn i g n.
Proof.
by elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH opprD addrACA.
Qed.

Lemma diffn_sub i f g n :
  diffn i (fun m => f m - g m) n = diffn i f n - diffn i g n.
Proof. by rewrite diffn_add diffn_opp. Qed.

Lemma diffn_eq0 i f : (forall n, f n = 0) -> forall n, diffn i f n = 0.
Proof.
move=> f0; elim: i => [|i IH] n; first exact: f0.
by rewrite diffnS /diff !IH subr0.
Qed.

(** [diffn i f n] looks at [f] on finitely many points only, so a
    pointwise equality is enough to rewrite under it -- no functional
    extensionality anywhere in this file. *)
Lemma diffn_ext i f g n : (forall m, f m = g m) -> diffn i f n = diffn i g n.
Proof. by move=> fg; elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH. Qed.

Lemma diffn_mulrn i f (c : nat) n :
  diffn i (fun m => f m *+ c) n = diffn i f n *+ c.
Proof. by elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH mulrnBl. Qed.

Lemma diffn_sum i (F : nat -> nat -> V) r n :
  diffn i (fun m => \sum_(j <- r) F j m) n = \sum_(j <- r) diffn i (F j) n.
Proof.
elim: r => [|a r IH]; first by rewrite big_nil; apply: diffn_eq0 => m;
  rewrite big_nil.
rewrite big_cons -IH -diffn_add; apply: diffn_ext => m.
by rewrite big_cons.
Qed.

(** ** Vanishing differences

    When the [d+1]-st difference of [f] is zero everywhere, so is every
    later one, and the [d]-th difference does not depend on the argument. *)
Lemma diffn_zero d i f :
  (forall n, diffn d.+1 f n = 0) -> (d < i)%N -> forall n, diffn i f n = 0.
Proof.
move=> fd di n; have -> : i = ((i - d.+1) + d.+1)%N by rewrite subnK.
by rewrite diffnD; apply: diffn_eq0.
Qed.

Lemma diffn_const d f :
  (forall n, diffn d.+1 f n = 0) -> forall n, diffn d f n = diffn d f 0%N.
Proof. by move=> fd; elim=> [//|n IH]; rewrite diff_stepE fd addr0. Qed.

(** ** Newton's formula

    Shifting by [k] is [(1 + diff)^k]: no degree hypothesis is needed, the
    sum is finite for every [k].  This single identity is both the Newton
    interpolation of Figure 7 and the binomial matrix of the
    straightforward shift. *)
Lemma diff_shiftn f n k :
  f (n + k)%N = \sum_(0 <= i < k.+1) (diffn i f n) *+ 'C(k, i).
Proof.
elim: k n => [|k IH] n.
  by rewrite addn0 big_nat1 bin0 mulr1n.
rewrite addnS -addSn IH.
transitivity (\sum_(0 <= i < k.+1) (diffn i f n) *+ 'C(k, i)
            + \sum_(0 <= i < k.+1) (diffn i.+1 f n) *+ 'C(k, i)).
  rewrite -big_split /=; apply: eq_bigr => i _.
  by rewrite diff_stepE mulrnDl.
rewrite [RHS]big_nat_recl //= bin0 mulr1n.
under [in RHS]eq_bigr => i _ do rewrite binS mulrnDr.
rewrite big_split /= addrA; congr (_ + _).
rewrite [LHS]big_nat_recl //= bin0 mulr1n; congr (_ + _).
by rewrite [RHS]big_nat_recr //= bin_small // mulr0n addr0.
Qed.

Lemma diff_shift f n k :
  f (n + k)%N = \sum_(i < k.+1) (diffn i f n) *+ 'C(k, i).
Proof. by rewrite diff_shiftn big_mkord. Qed.

(** Truncating a sum at the point where its terms die. *)
Lemma sum_tail (u : nat -> V) a b :
  (a <= b)%N -> (forall i, (a <= i)%N -> u i = 0) ->
  \sum_(i < b) u i = \sum_(i < a) u i.
Proof.
move=> ab u0; rewrite (big_ord_widen b (fun i => u i) ab).
rewrite [RHS]big_mkcond /=; apply: eq_bigr => i _.
by case: ltnP => // /u0 ->.
Qed.

(** Newton's formula for a polynomial of degree at most [d]: the sum stops
    at [d], whatever the argument.  Started at an arbitrary [n], this is
    the [k]-step shift of the whole table. *)
Lemma diff_shift_deg d f n k :
  (forall m, diffn d.+1 f m = 0) ->
  f (n + k)%N = \sum_(i < d.+1) (diffn i f n) *+ 'C(k, i).
Proof.
move=> fd; rewrite diff_shift.
case: (leqP d.+1 k.+1) => [dk|kd].
  apply: (sum_tail (u := fun i => (diffn i f n) *+ 'C(k, i))) => // i di.
  by rewrite (diffn_zero fd) ?mul0rn.
apply/esym/(sum_tail (u := fun i => (diffn i f n) *+ 'C(k, i)));
  first exact: ltnW.
by move=> i ki; rewrite bin_small ?mulr0n.
Qed.

Lemma newton d f n :
  (forall m, diffn d.+1 f m = 0) ->
  f n = \sum_(i < d.+1) (diffn i f 0%N) *+ 'C(n, i).
Proof. by move=> fd; rewrite -[n in LHS]add0n; apply: diff_shift_deg. Qed.

(** ** Polynomials

    A polynomial of degree at most [d]: its value at [n] is
    [l_0 C(n, 0) + ... + l_d C(n, d)] for some [l_0, ..., l_d] in [V].  The
    basis is the binomials [C(n, i)], not the powers [n^i]: [V] can add but
    not divide, and [C(n, 2) = (n^2 - n) / 2] has no coefficients in [V] in
    the basis of the powers. *)
Definition is_poly d f :=
  exists l : seq V, forall n, f n = \sum_(i < d.+1) l`_i *+ 'C(n, i).

(** Pascal's rule, read as a difference: [diff C(., i + 1) = C(., i)]. *)
Lemma diff_binS c i n : diff (fun m => c *+ 'C(m, i.+1)) n = c *+ 'C(n, i).
Proof. by rewrite /diff /= binS mulrnDr addrAC subrr add0r. Qed.

(** So the [j]-th difference of [C(., i)] is zero as soon as [j > i]. *)
Lemma diffn_binom c i j n : (i < j)%N -> diffn j (fun m => c *+ 'C(m, i)) n = 0.
Proof.
elim: i j n => [|i IH] [|j] n // ij.
  by rewrite diffnSr; apply: diffn_eq0 => m; rewrite /diff !bin0 subrr.
rewrite diffnSr -(IH j n ij); apply: diffn_ext => m; exact: diff_binS.
Qed.

(** A polynomial of degree at most [d] is exactly a function whose
    [d+1]-st difference is zero everywhere.  From left to right by
    [diffn_binom]; from right to left by Newton's formula, with the
    differences at [0] as coefficients. *)
Lemma is_polyP d f : is_poly d f <-> forall n, diffn d.+1 f n = 0.
Proof.
split=> [[l fl] n|fd]; last first.
  exists (mkseq (fun i => diffn i f 0%N) d.+1) => n.
  by rewrite (newton n fd); apply: eq_bigr => i _; rewrite nth_mkseq.
have -> : diffn d.+1 f n
        = diffn d.+1 (fun m => \sum_(0 <= i < d.+1) l`_i *+ 'C(m, i)) n.
  by apply: diffn_ext => m; rewrite fl big_mkord.
rewrite diffn_sum big_nat big1 // => i /andP[_ id].
exact: diffn_binom.
Qed.

Lemma is_polyW d e f : (d <= e)%N -> is_poly d f -> is_poly e f.
Proof.
by move=> de /is_polyP fd; apply/is_polyP => n; apply: (diffn_zero fd).
Qed.

End Difference.

Arguments is_poly {V} d f.

(** ** The difference table and the two shifts *)

Section Shifts.

Variable V : zmodType.
Implicit Types (f : nat -> V) (t : seq V).

(** The table the algorithms carry: the [d+1] first differences of [f] at
    the argument [n].  Its first entry is the value [f n]. *)
Definition dtab d f n : seq V := mkseq (fun i => diffn i f n) d.+1.

Lemma size_dtab d f n : size (dtab d f n) = d.+1.
Proof. exact: size_mkseq. Qed.

(** Reading past the end of the table gives [0], which for a degree-[d]
    polynomial is the right value: the entries past the end are null. *)
Lemma nth_dtab d f n i : is_poly d f -> nth 0 (dtab d f n) i = diffn i f n.
Proof.
move=> /is_polyP fd; case: (ltnP i d.+1) => [id|di]; first by rewrite nth_mkseq.
by rewrite nth_default ?size_dtab // (diffn_zero fd).
Qed.

(** *** The tabulated difference shift (Figure 8)

    One step adds to each entry the next one.  Only additions, and they
    are the multi-precision additions the GPU kernel performs. *)
Definition tstep t : seq V :=
  mkseq (fun i => nth 0 t i + nth 0 t i.+1) (size t).

Lemma size_tstep t : size (tstep t) = size t.
Proof. exact: size_mkseq. Qed.

Lemma tstepE d f n : is_poly d f -> tstep (dtab d f n) = dtab d f n.+1.
Proof.
move=> fd; apply: (@eq_from_nth _ 0) => [|i].
  by rewrite size_tstep !size_dtab.
rewrite size_tstep size_dtab => id.
by rewrite nth_mkseq ?size_dtab // !nth_dtab // -diff_stepE.
Qed.

(** Iterating it walks the table along consecutive arguments. *)
Lemma tstep_iter d f n k :
  is_poly d f -> iter k tstep (dtab d f n) = dtab d f (n + k)%N.
Proof.
move=> fd; elim: k n => [|k IH] n; first by rewrite addn0.
by rewrite iterSr tstepE // IH addSnnS.
Qed.

(** *** The straightforward shift

    [k] steps at once: the table is multiplied by the upper triangular
    Toeplitz matrix whose [(i, j)] entry is [C(k, j - i)].  This needs
    multi-precision multiplications, so the paper keeps it on the CPU. *)
Definition sstep k t : seq V :=
  mkseq (fun i => \sum_(l < size t) (nth 0 t (i + l)%N) *+ 'C(k, l)) (size t).

Lemma size_sstep k t : size (sstep k t) = size t.
Proof. exact: size_mkseq. Qed.

Lemma sstepE d f n k :
  is_poly d f -> sstep k (dtab d f n) = dtab d f (n + k)%N.
Proof.
move=> fd; have /is_polyP fz := fd; apply: (@eq_from_nth _ 0) => [|i].
  by rewrite size_sstep !size_dtab.
rewrite size_sstep size_dtab => id.
rewrite nth_mkseq ?size_dtab // nth_mkseq //.
rewrite (eq_bigr (fun l : 'I_d.+1 => (diffn (i + l)%N f n) *+ 'C(k, l)));
  last by move=> l _; rewrite nth_dtab.
rewrite (diff_shift_deg (d := d)) //.
  by apply: eq_bigr => l _; rewrite addnC diffnD.
by move=> m; rewrite -diffnD; apply: (diffn_zero fz); exact: leq_addr.
Qed.

(** One straightforward step is one tabulated step. *)
Lemma sstep1 d f n : is_poly d f -> sstep 1 (dtab d f n) = tstep (dtab d f n).
Proof. by move=> fd; rewrite sstepE // tstepE // addn1. Qed.

(** *** The hybrid split of Section 5.2

    A shift by [t S + s] is [t] straightforward steps of size [S] on the
    CPU followed by [s] tabulated steps inside a GPU thread. *)
Lemma hybridE d f Sz s nt :
  is_poly d f ->
  iter s tstep (sstep (nt * Sz)%N (dtab d f 0%N)) = dtab d f (nt * Sz + s)%N.
Proof. by move=> fd; rewrite sstepE // tstep_iter // add0n. Qed.

End Shifts.

Arguments dtab {V} d f n.
Arguments tstep {V} t.
Arguments sstep {V} k t.

(** ** A degree toolkit

    What it takes to see that a concrete polynomial has a finite
    difference table: degree is preserved by sums and by shifts of the
    argument, and raised by exactly one by a multiplication by the
    argument, so a Horner form with [d+1] coefficients has degree at most
    [d]. *)

Section Degree.

Variable V : zmodType.
Implicit Types (f g : nat -> V).

Lemma is_poly_const (c : V) : is_poly 0 (fun _ : nat => c).
Proof. by apply/is_polyP => n; rewrite /diffn /= /diff subrr. Qed.

Lemma is_polyD d f g :
  is_poly d f -> is_poly d g -> is_poly d (fun n => f n + g n).
Proof.
move=> /is_polyP fd /is_polyP gd; apply/is_polyP => n.
by rewrite diffn_add fd gd addr0.
Qed.

Lemma is_poly_shift d f : is_poly d f -> is_poly d (fun n => f n.+1).
Proof.
move=> /is_polyP fd; apply/is_polyP => n.
have -> : diffn d.+1 (fun m : nat => f m.+1) n
        = diffn d.+1 (fun m : nat => f (1 + m)%N) n by apply: diffn_ext => m.
by rewrite diffn_shift.
Qed.

(** The one place a degree goes up: [diff (f X) = (diff f) X + f(. + 1)]. *)
Lemma diff_mulX f n : diff (fun m => f m *+ m) n = diff f n *+ n + f n.+1.
Proof. by rewrite /diff mulrSr addrAC mulrnBl. Qed.

Lemma is_poly_mulX d f : is_poly d f -> is_poly d.+1 (fun n => f n *+ n).
Proof.
move=> /is_polyP; elim: d f => [|d IH] f fd; apply/is_polyP => n.
  transitivity (diff (fun m : nat => f m *+ m) n.+1
              - diff (fun m : nat => f m *+ m) n); first by [].
  rewrite !diff_mulX.
  have f0 : forall m, diff f m = 0 by move=> m; apply: (fd m).
  by rewrite !f0 !mul0rn !add0r; apply: (fd n.+1).
rewrite diffnSr.
have -> : diffn d.+2 (diff (fun m : nat => f m *+ m)) n
        = diffn d.+2 (fun m : nat => diff f m *+ m + f m.+1) n.
  by apply: diffn_ext => m; rewrite diff_mulX.
move: n; apply/is_polyP; apply: is_polyD.
  by apply: IH => m; rewrite -diffnSr; apply: (fd m).
by apply: is_poly_shift; apply/is_polyP.
Qed.

(** Degree passes through a finite sum of terms. *)
Lemma is_poly_sum d (F : nat -> nat -> V) r :
  (forall j, j \in r -> is_poly d (F j)) ->
  is_poly d (fun n => \sum_(j <- r) F j n).
Proof.
move=> Fd; apply/is_polyP => n; rewrite diffn_sum big1_seq // => j /andP[_ jr].
by have /is_polyP := Fd j jr; apply.
Qed.

(** A polynomial in Horner form, least significant coefficient first. *)
Fixpoint hpoly (c : seq V) : nat -> V :=
  if c is a :: c' then fun n => a + (hpoly c' n) *+ n else fun _ => 0.

Lemma is_poly_hpoly c : is_poly (size c) (hpoly c).
Proof.
elim: c => [|a c IH]; first by apply/is_polyP => n; apply: diffn_eq0.
apply: is_polyD; last exact: is_poly_mulX.
exact: (is_polyW (leq0n _) (is_poly_const a)).
Qed.

End Degree.

(** ** The degree of a concrete polynomial

    Over a ring, degree is preserved by scaling and raised by exactly one
    by a multiplication by a monic linear factor.  That is all it takes to
    give a polynomial written in the monomial basis around a centre -- the
    shape [Cheb.v] uses -- a finite difference table. *)

Section DegreeRing.

Variable R : nzRingType.
Implicit Types f : nat -> R.

Lemma diffn_scale i (a : R) f n :
  diffn i (fun m => a * f m) n = a * diffn i f n.
Proof. by elim: i n => [//|i IH] n; rewrite !diffnS /diff !IH mulrBr. Qed.

Lemma is_poly_scale d (a : R) f : is_poly d f -> is_poly d (fun n => a * f n).
Proof.
by move=> /is_polyP fd; apply/is_polyP => n; rewrite diffn_scale fd mulr0.
Qed.

Lemma mulrB1l (a b u : R) : a * (u + 1) - b * u = (a - b) * (u + 1) + b.
Proof. by rewrite mulrBl !mulrDr !mulr1 opprD addrA subrK. Qed.

Lemma diff_mulL (c : R) f n :
  diff (fun m => f m * (c + m%:R)) n = diff f n * (c + n.+1%:R) + f n.
Proof. by rewrite /diff -natr1 addrA; exact: mulrB1l. Qed.

Lemma is_poly_mulL d (c : R) f :
  is_poly d f -> is_poly d.+1 (fun n => f n * (c + n%:R)).
Proof.
move=> /is_polyP; elim: d c f => [|d IH] c f fd; apply/is_polyP => n.
  transitivity (diff (fun m => f m * (c + m%:R)) n.+1
              - diff (fun m => f m * (c + m%:R)) n); first by [].
  rewrite !diff_mulL.
  have f0 : forall m, diff f m = 0 by move=> m; apply: (fd m).
  by rewrite !f0 !mul0r !add0r; apply: (fd n).
rewrite diffnSr.
have -> : diffn d.+2 (diff (fun m => f m * (c + m%:R))) n
        = diffn d.+2 (fun m => diff f m * (c + 1 + m%:R) + f m) n.
  apply: diffn_ext => m; rewrite diff_mulL -natr1 addrA.
  by rewrite [(c + m%:R + 1)]addrAC.
move: n; apply/is_polyP; apply: is_polyD; last exact/is_polyP.
by apply: IH => m; rewrite -diffnSr; apply: (fd m).
Qed.

(** A power of a monic linear factor has exactly that degree. *)
Lemma is_poly_linX k (c : R) : is_poly k (fun n => (c + n%:R) ^+ k).
Proof.
elim: k => [|k IH]; apply/is_polyP => n.
  by rewrite /diffn /= /diff !expr0 subrr.
have -> : diffn k.+2 (fun m => (c + m%:R) ^+ k.+1) n
        = diffn k.+2 (fun m => (c + m%:R) ^+ k * (c + m%:R)) n.
  by apply: diffn_ext => m; rewrite exprSr.
by move: n; apply/is_polyP; apply: is_poly_mulL.
Qed.

End DegreeRing.

(** ** The hierarchical method

    Cutting the argument as [x = k N + m] turns the shift by [N] into
    [d+1] shifts by [1]: the coefficients [a_j] of [P (k N + .)] in the
    binomial basis are themselves polynomials in [k] of degree at most
    [d], so one difference table per [j] produces every [P_k]. *)

Section Hierarchical.

Variable V : zmodType.
Implicit Types (f : nat -> V).

(** The difference over a stride of [h] arguments: the paper's shift by
    [N], the one the hierarchical method removes. *)
Definition diffh h f : nat -> V := fun n => f (n + h)%N - f n.

(** Written in the binomial basis, a shift by [h] is a combination of the
    differences of order [1] to [h]: the constant term is gone, which is
    why the degree drops. *)
Lemma diffh_sumE h f n :
  diffh h f n = \sum_(0 <= i < h) diffn i.+1 f n *+ 'C(h, i.+1).
Proof.
rewrite /diffh diff_shiftn big_nat_recl //= bin0 mulr1n.
by rewrite addrAC subrr add0r.
Qed.

Lemma diffh_deg e h f : is_poly e.+1 f -> is_poly e (diffh h f).
Proof.
move=> /is_polyP fe; apply/is_polyP => n.
have -> : diffn e.+1 (diffh h f) n
        = diffn e.+1
            (fun m => \sum_(0 <= i < h) diffn i.+1 f m *+ 'C(h, i.+1)) n.
  by apply: diffn_ext => m; rewrite diffh_sumE.
rewrite diffn_sum big1 // => i _.
rewrite diffn_mulrn -diffnD.
have -> : diffn (e.+1 + i.+1)%N f n = 0.
  by apply: (diffn_zero fe); rewrite addnS ltnS leq_addr.
by rewrite mul0rn.
Qed.

(** [e+1] shifts by [h] annihilate a polynomial of degree at most [e]. *)
Lemma diffhn_deg e h f : is_poly e f -> forall n, iter e.+1 (diffh h) f n = 0.
Proof.
elim: e f => [|e IH] f /is_polyP fe n.
  have fc : forall m, f m.+1 = f m.
    by move=> m; move: (fe m); rewrite /diffn /= /diff => /eqP;
       rewrite subr_eq0 => /eqP.
  have fk : forall c m, f (m + c)%N = f m.
    by move=> c; elim: c => [m|c IHc m]; rewrite ?addn0 // addnS fc IHc.
  by rewrite /= /diffh fk subrr.
by rewrite iterSr; apply: IH; apply: diffh_deg; apply/is_polyP.
Qed.

Variables (d N : nat) (P : nat -> V).
Hypothesis Pd : is_poly d P.

(** [acoef j k] is the [j]-th coefficient of [P (k N + .)] in the binomial
    basis, that is the [j]-th entry of the difference table of the [k]-th
    interval. *)
Definition acoef j k : V := diffn j (fun m => P (k * N + m)%N) 0%N.

Lemma acoef_deg0 k : is_poly d (fun m => P (k * N + m)%N).
Proof.
have /is_polyP Pz := Pd.
by apply/is_polyP => n; rewrite diffn_shift Pz.
Qed.

(** The interpolation of Section 5: the [k]-th polynomial of the search,
    in the binomial basis, has the [a_j (k)] as coefficients. *)
Lemma hierarchicalE k m :
  P (k * N + m)%N = \sum_(j < d.+1) acoef j k *+ 'C(m, j).
Proof. by apply: newton; apply/is_polyP; exact: acoef_deg0. Qed.

(** The difference table of the [k]-th interval is exactly the vector of
    the [a_j (k)], so running the shifts on the [a_j] produces every
    [P_k]. *)
Lemma dtab_acoef k :
  dtab d (fun m => P (k * N + m)%N) 0%N = mkseq (fun j => acoef j k) d.+1.
Proof. by []. Qed.

(** Stepping [k] by one turns [P] into its shift by [N]: that is the whole
    reason the [a_j] are again polynomials in [k]. *)
Lemma diffn_acoef i j k :
  diffn i (fun k' => diffn j (fun m => P (k' * N + m)%N) 0%N) k
    = diffn j (fun m => iter i (diffh N) P (k * N + m)%N) 0%N.
Proof.
elim: i k => [//|i IH] k.
rewrite diffnS /diff !IH -diffn_sub; apply: diffn_ext => m.
rewrite -[iter i.+1 _ _]/(diffh N (iter i (diffh N) P)) /diffh.
have -> : (k.+1 * N + m = k * N + m + N)%N.
  by rewrite mulSn [(N + k * N)%N]addnC -addnA [(N + m)%N]addnC addnA.
by [].
Qed.

Lemma acoef_deg j : is_poly d (acoef j).
Proof.
apply/is_polyP => k; rewrite /acoef diffn_acoef.
have -> : diffn j (fun m => iter d.+1 (diffh N) P (k * N + m)%N) 0%N
        = diffn j (fun _ : nat => 0) 0%N.
  by apply: diffn_ext => m; apply: diffhn_deg.
by apply: diffn_eq0.
Qed.

End Hierarchical.
