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

    - the forward difference [dif f n = f n.+1 - f n] and Newton's formula
      [f (n + k) = sum_i (dif^i f n) * C(k, i)] (Definition 5, Figure 7);
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

(** [dif] is the paper's [Delta] and [difn i] its [i]-th power.  A
    function [nat -> V] stands for a polynomial sampled at the integers. *)
Definition dif f : nat -> V := fun n => f n.+1 - f n.

Definition difn i f : nat -> V := iter i dif f.

Lemma difn0 f : difn 0 f = f.
Proof. by []. Qed.

Lemma difnS i f : difn i.+1 f = dif (difn i f).
Proof. by []. Qed.

Lemma difnSr i f : difn i.+1 f = difn i (dif f).
Proof. exact: iterSr. Qed.

Lemma difnD i j f : difn (i + j)%N f = difn i (difn j f).
Proof. by rewrite /difn iterD. Qed.

(** The recurrence the tabulated shift runs on: a row of the table moves
    forward by adding the row below it. *)
Lemma dif_stepE i f n : difn i f n.+1 = difn i f n + difn i.+1 f n.
Proof. by rewrite difnS /dif addrC subrK. Qed.

(** Differences commute with a shift of the argument. *)
Lemma difn_shift i f o n : difn i (fun m => f (o + m)%N) n = difn i f (o + n)%N.
Proof.
by elim: i n => [//|i IH] n; rewrite !difnS /dif !IH addnS.
Qed.

Lemma difn_opp i f n : difn i (fun m => - f m) n = - difn i f n.
Proof.
by elim: i n => [//|i IH] n; rewrite !difnS /dif !IH opprK opprB addrC.
Qed.

Lemma difn_add i f g n :
  difn i (fun m => f m + g m) n = difn i f n + difn i g n.
Proof.
by elim: i n => [//|i IH] n; rewrite !difnS /dif !IH opprD addrACA.
Qed.

Lemma difn_sub i f g n :
  difn i (fun m => f m - g m) n = difn i f n - difn i g n.
Proof. by rewrite difn_add difn_opp. Qed.

Lemma difn_eq0 i f : (forall n, f n = 0) -> forall n, difn i f n = 0.
Proof.
move=> f0; elim: i => [|i IH] n; first exact: f0.
by rewrite difnS /dif !IH subr0.
Qed.

(** [difn i f n] looks at [f] on finitely many points only, so a
    pointwise equality is enough to rewrite under it -- no functional
    extensionality anywhere in this file. *)
Lemma difn_ext i f g n : (forall m, f m = g m) -> difn i f n = difn i g n.
Proof. by move=> fg; elim: i n => [//|i IH] n; rewrite !difnS /dif !IH. Qed.

Lemma difn_mulrn i f (c : nat) n :
  difn i (fun m => f m *+ c) n = difn i f n *+ c.
Proof. by elim: i n => [//|i IH] n; rewrite !difnS /dif !IH mulrnBl. Qed.

Lemma difn_sum i (F : nat -> nat -> V) r n :
  difn i (fun m => \sum_(j <- r) F j m) n = \sum_(j <- r) difn i (F j) n.
Proof.
elim: r => [|a r IH]; first by rewrite big_nil; apply: difn_eq0 => m;
  rewrite big_nil.
rewrite big_cons -IH -difn_add; apply: difn_ext => m.
by rewrite big_cons.
Qed.

(** ** Degree

    A polynomial of degree at most [d] is a function whose [d+1]-st
    difference vanishes.  We need no other notion of degree. *)
Definition degle d f := forall n, difn d.+1 f n = 0.

Lemma degle_difn d i f : degle d f -> (d < i)%N -> forall n, difn i f n = 0.
Proof.
move=> fd di n; have -> : i = ((i - d.+1) + d.+1)%N by rewrite subnK.
by rewrite difnD; apply: difn_eq0.
Qed.

Lemma degleW d e f : (d <= e)%N -> degle d f -> degle e f.
Proof. by move=> de fd n; apply: (degle_difn fd). Qed.

(** The [d]-th difference of a degree-[d] polynomial is constant: it is
    the top row of the table, the one the shifts never change. *)
Lemma degle_const d f : degle d f -> forall n, difn d f n = difn d f 0%N.
Proof. by move=> fd; elim=> [//|n IH]; rewrite dif_stepE fd addr0. Qed.

(** ** Newton's formula

    Shifting by [k] is [(1 + dif)^k]: no degree hypothesis is needed, the
    sum is finite for every [k].  This single identity is both the Newton
    interpolation of Figure 7 and the binomial matrix of the
    straightforward shift. *)
Lemma dif_shiftn f n k :
  f (n + k)%N = \sum_(0 <= i < k.+1) (difn i f n) *+ 'C(k, i).
Proof.
elim: k n => [|k IH] n.
  by rewrite addn0 big_nat1 bin0 mulr1n.
rewrite addnS -addSn IH.
transitivity (\sum_(0 <= i < k.+1) (difn i f n) *+ 'C(k, i)
            + \sum_(0 <= i < k.+1) (difn i.+1 f n) *+ 'C(k, i)).
  rewrite -big_split /=; apply: eq_bigr => i _.
  by rewrite dif_stepE mulrnDl.
rewrite [RHS]big_nat_recl //= bin0 mulr1n.
under [in RHS]eq_bigr => i _ do rewrite binS mulrnDr.
rewrite big_split /= addrA; congr (_ + _).
rewrite [LHS]big_nat_recl //= bin0 mulr1n; congr (_ + _).
by rewrite [RHS]big_nat_recr //= bin_small // mulr0n addr0.
Qed.

Lemma dif_shift f n k :
  f (n + k)%N = \sum_(i < k.+1) (difn i f n) *+ 'C(k, i).
Proof. by rewrite dif_shiftn big_mkord. Qed.

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
Lemma dif_shift_deg d f n k :
  degle d f -> f (n + k)%N = \sum_(i < d.+1) (difn i f n) *+ 'C(k, i).
Proof.
move=> fd; rewrite dif_shift.
case: (leqP d.+1 k.+1) => [dk|kd].
  apply: (sum_tail (u := fun i => (difn i f n) *+ 'C(k, i))) => // i di.
  by rewrite (degle_difn fd) ?mul0rn.
apply/esym/(sum_tail (u := fun i => (difn i f n) *+ 'C(k, i)));
  first exact: ltnW.
by move=> i ki; rewrite bin_small ?mulr0n.
Qed.

Lemma newton d f n :
  degle d f -> f n = \sum_(i < d.+1) (difn i f 0%N) *+ 'C(n, i).
Proof. by move=> fd; rewrite -[n in LHS]add0n; apply: dif_shift_deg. Qed.

End Difference.

Arguments degle {V} d f.

(** ** The difference table and the two shifts *)

Section Shifts.

Variable V : zmodType.
Implicit Types (f : nat -> V) (t : seq V).

(** The table the algorithms carry: the [d+1] first differences of [f] at
    the argument [n].  Its first entry is the value [f n]. *)
Definition dtab d f n : seq V := mkseq (fun i => difn i f n) d.+1.

Lemma size_dtab d f n : size (dtab d f n) = d.+1.
Proof. exact: size_mkseq. Qed.

(** Reading past the end of the table gives [0], which for a degree-[d]
    polynomial is the right value: the rows below the table are null. *)
Lemma nth_dtab d f n i : degle d f -> nth 0 (dtab d f n) i = difn i f n.
Proof.
move=> fd; case: (ltnP i d.+1) => [id|di]; first by rewrite nth_mkseq.
by rewrite nth_default ?size_dtab // (degle_difn fd).
Qed.

(** *** The tabulated difference shift (Figure 8)

    One step adds each row to the one below it.  Only additions, and they
    are the multi-precision additions the GPU kernel performs. *)
Definition tstep t : seq V :=
  mkseq (fun i => nth 0 t i + nth 0 t i.+1) (size t).

Lemma size_tstep t : size (tstep t) = size t.
Proof. exact: size_mkseq. Qed.

Lemma tstepE d f n : degle d f -> tstep (dtab d f n) = dtab d f n.+1.
Proof.
move=> fd; apply: (@eq_from_nth _ 0) => [|i].
  by rewrite size_tstep !size_dtab.
rewrite size_tstep size_dtab => id.
by rewrite nth_mkseq ?size_dtab // !nth_dtab // -dif_stepE.
Qed.

(** Iterating it walks the table along consecutive arguments. *)
Lemma tstep_iter d f n k :
  degle d f -> iter k tstep (dtab d f n) = dtab d f (n + k)%N.
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
  degle d f -> sstep k (dtab d f n) = dtab d f (n + k)%N.
Proof.
move=> fd; apply: (@eq_from_nth _ 0) => [|i].
  by rewrite size_sstep !size_dtab.
rewrite size_sstep size_dtab => id.
rewrite nth_mkseq ?size_dtab // nth_mkseq //.
rewrite (eq_bigr (fun l : 'I_d.+1 => (difn (i + l)%N f n) *+ 'C(k, l)));
  last by move=> l _; rewrite nth_dtab.
rewrite (dif_shift_deg (d := d)) //.
  by apply: eq_bigr => l _; rewrite addnC difnD.
by move=> m; rewrite -difnD; apply: (degle_difn fd); exact: leq_addr.
Qed.

(** One straightforward step is one tabulated step. *)
Lemma sstep1 d f n : degle d f -> sstep 1 (dtab d f n) = tstep (dtab d f n).
Proof. by move=> fd; rewrite sstepE // tstepE // addn1. Qed.

(** *** The hybrid split of Section 5.2

    A shift by [t S + s] is [t] straightforward steps of size [S] on the
    CPU followed by [s] tabulated steps inside a GPU thread. *)
Lemma hybridE d f Sz s nt :
  degle d f ->
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

Lemma degle_const0 (c : V) : degle 0 (fun _ : nat => c).
Proof. by move=> n; rewrite /difn /= /dif subrr. Qed.

Lemma degleD d f g : degle d f -> degle d g -> degle d (fun n => f n + g n).
Proof. by move=> fd gd n; rewrite difn_add fd gd addr0. Qed.

Lemma degle_shift d f : degle d f -> degle d (fun n => f n.+1).
Proof.
move=> fd n.
have -> : difn d.+1 (fun m : nat => f m.+1) n
        = difn d.+1 (fun m : nat => f (1 + m)%N) n by apply: difn_ext => m.
by rewrite difn_shift.
Qed.

(** The one place a degree goes up: [dif (f X) = (dif f) X + f(. + 1)]. *)
Lemma dif_mulX f n : dif (fun m => f m *+ m) n = dif f n *+ n + f n.+1.
Proof. by rewrite /dif mulrSr addrAC mulrnBl. Qed.

Lemma degle_mulX d f : degle d f -> degle d.+1 (fun n => f n *+ n).
Proof.
elim: d f => [|d IH] f fd n.
  transitivity (dif (fun m : nat => f m *+ m) n.+1
              - dif (fun m : nat => f m *+ m) n); first by [].
  rewrite !dif_mulX.
  have f0 : forall m, dif f m = 0 by move=> m; apply: (fd m).
  by rewrite !f0 !mul0rn !add0r; apply: (fd n.+1).
rewrite difnSr.
have -> : difn d.+2 (dif (fun m : nat => f m *+ m)) n
        = difn d.+2 (fun m : nat => dif f m *+ m + f m.+1) n.
  by apply: difn_ext => m; rewrite dif_mulX.
apply: degleD; last by apply: degle_shift; apply: fd.
by apply: IH => m; rewrite -difnSr; apply: (fd m).
Qed.

(** Degree passes through a finite sum of terms. *)
Lemma degle_sum d (F : nat -> nat -> V) r :
  (forall j, j \in r -> degle d (F j)) ->
  degle d (fun n => \sum_(j <- r) F j n).
Proof.
move=> Fd n; rewrite difn_sum big1_seq // => j /andP[_ jr].
exact: (Fd j jr).
Qed.

(** A polynomial in Horner form, least significant coefficient first. *)
Fixpoint hpoly (c : seq V) : nat -> V :=
  if c is a :: c' then fun n => a + (hpoly c' n) *+ n else fun _ => 0.

Lemma degle_hpoly c : degle (size c) (hpoly c).
Proof.
elim: c => [|a c IH] n; first by apply: difn_eq0.
apply: degleD; last by apply: degle_mulX; apply: IH.
by apply: (degleW (leq0n _) (degle_const0 a)).
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

Lemma difn_scale i (a : R) f n : difn i (fun m => a * f m) n = a * difn i f n.
Proof. by elim: i n => [//|i IH] n; rewrite !difnS /dif !IH mulrBr. Qed.

Lemma degle_scale d (a : R) f : degle d f -> degle d (fun n => a * f n).
Proof. by move=> fd n; rewrite difn_scale fd mulr0. Qed.

Lemma mulrB1l (a b u : R) : a * (u + 1) - b * u = (a - b) * (u + 1) + b.
Proof. by rewrite mulrBl !mulrDr !mulr1 opprD addrA subrK. Qed.

Lemma dif_mulL (c : R) f n :
  dif (fun m => f m * (c + m%:R)) n = dif f n * (c + n.+1%:R) + f n.
Proof. by rewrite /dif -natr1 addrA; exact: mulrB1l. Qed.

Lemma degle_mulL d (c : R) f :
  degle d f -> degle d.+1 (fun n => f n * (c + n%:R)).
Proof.
elim: d c f => [|d IH] c f fd n.
  transitivity (dif (fun m => f m * (c + m%:R)) n.+1
              - dif (fun m => f m * (c + m%:R)) n); first by [].
  rewrite !dif_mulL.
  have f0 : forall m, dif f m = 0 by move=> m; apply: (fd m).
  by rewrite !f0 !mul0r !add0r; apply: (fd n).
rewrite difnSr.
have -> : difn d.+2 (dif (fun m => f m * (c + m%:R))) n
        = difn d.+2 (fun m => dif f m * (c + 1 + m%:R) + f m) n.
  apply: difn_ext => m; rewrite dif_mulL -natr1 addrA.
  by rewrite [(c + m%:R + 1)]addrAC.
apply: degleD; last exact: fd.
by apply: IH => m; rewrite -difnSr; apply: (fd m).
Qed.

(** A power of a monic linear factor has exactly that degree. *)
Lemma degle_linX k (c : R) : degle k (fun n => (c + n%:R) ^+ k).
Proof.
elim: k => [|k IH] n; first by rewrite /difn /= /dif !expr0 subrr.
have -> : difn k.+2 (fun m => (c + m%:R) ^+ k.+1) n
        = difn k.+2 (fun m => (c + m%:R) ^+ k * (c + m%:R)) n.
  by apply: difn_ext => m; rewrite exprSr.
by apply: degle_mulL.
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
Definition difh h f : nat -> V := fun n => f (n + h)%N - f n.

(** Written in the binomial basis, a shift by [h] is a combination of the
    differences of order [1] to [h]: the constant term is gone, which is
    why the degree drops. *)
Lemma difh_sumE h f n :
  difh h f n = \sum_(0 <= i < h) difn i.+1 f n *+ 'C(h, i.+1).
Proof.
rewrite /difh dif_shiftn big_nat_recl //= bin0 mulr1n.
by rewrite addrAC subrr add0r.
Qed.

Lemma difh_deg e h f : degle e.+1 f -> degle e (difh h f).
Proof.
move=> fe n.
have -> : difn e.+1 (difh h f) n
        = difn e.+1 (fun m => \sum_(0 <= i < h) difn i.+1 f m *+ 'C(h, i.+1)) n.
  by apply: difn_ext => m; rewrite difh_sumE.
rewrite difn_sum big1 // => i _.
rewrite difn_mulrn -difnD.
have -> : difn (e.+1 + i.+1)%N f n = 0.
  by apply: (degle_difn fe); rewrite addnS ltnS leq_addr.
by rewrite mul0rn.
Qed.

(** [e+1] shifts by [h] annihilate a polynomial of degree at most [e]. *)
Lemma difhn_deg e h f : degle e f -> forall n, iter e.+1 (difh h) f n = 0.
Proof.
elim: e f => [|e IH] f fe n.
  have fc : forall m, f m.+1 = f m.
    by move=> m; move: (fe m); rewrite /difn /= /dif => /eqP;
       rewrite subr_eq0 => /eqP.
  have fk : forall c m, f (m + c)%N = f m.
    by move=> c; elim: c => [m|c IHc m]; rewrite ?addn0 // addnS fc IHc.
  by rewrite /= /difh fk subrr.
by rewrite iterSr; apply: IH; apply: difh_deg.
Qed.

Variables (d N : nat) (P : nat -> V).
Hypothesis Pd : degle d P.

(** [acoef j k] is the [j]-th coefficient of [P (k N + .)] in the binomial
    basis, that is the [j]-th entry of the difference table of the [k]-th
    interval. *)
Definition acoef j k : V := difn j (fun m => P (k * N + m)%N) 0%N.

Lemma acoef_deg0 k : degle d (fun m => P (k * N + m)%N).
Proof. by move=> n; rewrite difn_shift. Qed.

(** The interpolation of Section 5: the [k]-th polynomial of the search,
    in the binomial basis, has the [a_j (k)] as coefficients. *)
Lemma hierarchicalE k m :
  P (k * N + m)%N = \sum_(j < d.+1) acoef j k *+ 'C(m, j).
Proof. exact: newton (acoef_deg0 k). Qed.

(** The difference table of the [k]-th interval is exactly the vector of
    the [a_j (k)], so running the shifts on the [a_j] produces every
    [P_k]. *)
Lemma dtab_acoef k :
  dtab d (fun m => P (k * N + m)%N) 0%N = mkseq (fun j => acoef j k) d.+1.
Proof. by []. Qed.

(** Stepping [k] by one turns [P] into its shift by [N]: that is the whole
    reason the [a_j] are again polynomials in [k]. *)
Lemma difn_acoef i j k :
  difn i (fun k' => difn j (fun m => P (k' * N + m)%N) 0%N) k
    = difn j (fun m => iter i (difh N) P (k * N + m)%N) 0%N.
Proof.
elim: i k => [//|i IH] k.
rewrite difnS /dif !IH -difn_sub; apply: difn_ext => m.
rewrite -[iter i.+1 _ _]/(difh N (iter i (difh N) P)) /difh.
have -> : (k.+1 * N + m = k * N + m + N)%N.
  by rewrite mulSn [(N + k * N)%N]addnC -addnA [(N + m)%N]addnC addnA.
by [].
Qed.

Lemma acoef_deg j : degle d (acoef j).
Proof.
move=> k; rewrite /acoef difn_acoef.
have -> : difn j (fun m => iter d.+1 (difh N) P (k * N + m)%N) 0%N
        = difn j (fun _ : nat => 0) 0%N.
  by apply: difn_ext => m; apply: difhn_deg.
by apply: difn_eq0.
Qed.

End Hierarchical.
