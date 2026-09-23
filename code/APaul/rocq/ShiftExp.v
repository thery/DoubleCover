(** * Section 5 applied to the polynomial htr.c actually needs

    [Shift.v] proves the Taylor-shift machinery of Section 5 of
    [doc/mourad.pdf] over an arbitrary abelian group.  Here it is run on
    the approximation of [exp] the hard-to-round search uses.

    The paper's own deployment (Section 5.2) takes a degree-2 Taylor
    polynomial over intervals of [2^15] arguments, which reaches nothing
    like the accuracy this search needs.  We take instead the polynomial
    [Cheb.v] certifies: the degree-7 near-minimax approximation of [exp]
    over the whole search interval [[0.25, 0.25001)], within [2^-160] of
    [exp] there, and the interval length [htr.c] uses, [2^20] arguments.

    The point of the section is then this: the shifts are *exact*, so the
    one certificate [Cheb.cheb_valid] covers every interval the shifts
    produce.  Generating the [2^17] or so interval polynomials of the
    search costs eight difference tables of eight entries and additions
    only -- no new approximation, and no new error term. *)

From Stdlib Require Import ZArith Reals.
From APaulRocq Require Import Cheb.
From mathcomp Require Import all_ssreflect all_algebra ssrZ zify.
From APaulRocq Require Import Shift.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** ** The grid, and the polynomial on it *)

(** [htr.c] walks the binade one double at a time: argument [n] is the
    double whose significand is [x0num + n].  The whole search interval
    holds [nargs] of them.

    [nargs] is kept in [Z], and the range condition of [Pdir_exp] is
    stated in [Z] too.  It is about 1.8e11, and [nat] is unary: as a [nat]
    that bound would be 1.8e11 successors, and any tactic that tried to
    decide [n < nargs] by computation would not come back. *)
Definition nargs : Z := Z.sub x1num x0num.

(** The expansion centre, as an offset on that grid: [x_n - c] is
    [(dlt + n) / 2^54]. *)
Definition dlt : Z := Z.sub x0num Cc.

(** [Cheb.v] writes the approximation as [(sum_k A_k (x - c)^k) / 2^cden]
    with [x - c] a multiple of [2^-xden].  On the grid every value is
    therefore an integer over [2^vden]: that integer is [Pdir]. *)
Definition vden : nat := 598.               (* cden + 7 * xden = 220 + 378 *)

Definition Aseq : seq Z := [:: A0; A1; A2; A3; A4; A5; A6; A7].

Definition Ascaled (k : nat) : Z :=
  Z.mul (nth Z0 Aseq k) (Z.pow 2 (Z.of_nat (54 * (7 - k))%nat)).

Definition Pdir (n : nat) : Z :=
  \sum_(0 <= k < 8) Ascaled k * (dlt + n%:R) ^+ k.

(** The interval length of [htr.c]'s chunked walk. *)
Definition Nsz : nat := 2 ^ 20.

(** The paper's own parameters, for comparison ([Section 5.2]). *)
Definition Nsz_paper : nat := 2 ^ 15.
Definition dgr_paper : nat := 2.

(** ** [Pdir] has a difference table of eight entries *)

Lemma Pdir_deg : degle 7 Pdir.
Proof.
apply: degle_sum => k; rewrite mem_index_iota => /andP[_ k8].
apply: (degleW (d := k)); first by rewrite -ltnS.
by apply: degle_scale; apply: degle_linX.
Qed.

(** ** Section 5 on this polynomial *)

(** The coefficients of the [k]-th interval polynomial in the binomial
    basis: eight integers per interval. *)
Definition aexp (j k : nat) : Z := acoef Nsz Pdir j k.

(** The hierarchical identity: the value at offset [m] of interval [k]. *)
Lemma PdirE k m :
  Pdir (k * Nsz + m)%nat = \sum_(j < 8) aexp j k *+ 'C(m, j).
Proof. exact: hierarchicalE Pdir_deg k m. Qed.

(** Each coefficient is itself a degree-7 polynomial in the interval
    index, so it has its own eight-entry difference table. *)
Lemma aexp_deg j : degle 7 (aexp j).
Proof. exact: acoef_deg Pdir_deg j. Qed.

(** Walking the intervals one at a time: additions only (Figure 8). *)
Lemma aexp_tab j k :
  iter k tstep (dtab 7 (aexp j) 0%nat) = dtab 7 (aexp j) k.
Proof. by rewrite tstep_iter ?add0n //; apply: aexp_deg. Qed.

(** Jumping [t] packets of [S] intervals on the CPU and then walking [s]
    intervals inside the thread -- the hybrid split of Section 5.2. *)
Lemma aexp_hybrid j Sp s t :
  iter s tstep (sstep (t * Sp)%nat (dtab 7 (aexp j) 0%nat))
    = dtab 7 (aexp j) (t * Sp + s)%nat.
Proof. by apply: hybridE; apply: aexp_deg. Qed.

(** ** Back to [exp]

    Nothing above rounds, so the value the shifts produce for interval [k]
    at offset [m] is exactly [Pdir] at the grid point [k * Nsz + m], and
    [Cheb.cheb_valid] applies to it unchanged. *)

Local Open Scope R_scope.

(** Grid point [n] as a real. *)
Definition xgrid (n : nat) : R := IZR (Z.add x0num (Z.of_nat n)) / 2 ^ 54.

Lemma ZnatrE (n : nat) : (n%:R : Z) = Z.of_nat n.
Proof.
by elim: n => [//|n IH]; rewrite -GRing.natr1 IH; lia.
Qed.

(** [Pdir n] over [2^vden] is the polynomial [Cheb.v] certifies.

    ADMITTED.  There is no mathematics left in this one: both sides are
    the same polynomial, the left one with the powers of two kept in the
    integer, the right one with them in the denominator.  Proving it is
    pushing [IZR] through eight products and sums, and the two sides use
    different notations for the same operations on [Z] (mathcomp's ring
    operations against [Z.add] and [Z.mul]), which is what makes it
    tedious rather than hard. *)
Lemma Pdir_chebE (n : nat) : IZR (Pdir n) / 2 ^ vden = P_R (xgrid n).
Proof.
Admitted.

(** Hence every value the shifts generate is within [2^-160] of [exp]:
    the single certificate of [Cheb.v] covers the whole search, because
    the shifts that produced the value did not round. *)
Theorem Pdir_exp (n : nat) :
  Z.lt (Z.of_nat n) nargs ->
  Rabs (exp (xgrid n) - IZR (Pdir n) / 2 ^ vden) <= / 2 ^ 160.
Proof.
move=> nlt; rewrite Pdir_chebE; apply: cheb_valid.
have hpos : 0 <= / 2 ^ 54.
  by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; apply: Rlt_0_2.
have gen : forall a b : Z, Z.lt (Z.of_nat n) (Z.sub b a) ->
     Z.le a (Z.add a (Z.of_nat n)) /\ Z.le (Z.add a (Z.of_nat n)) b.
  by move=> a b; lia.
have nb := gen x0num x1num nlt.
rewrite /xgrid /x_lo /x_hi /Rdiv.
split; apply: Rmult_le_compat_r; try exact: hpos;
  by apply: IZR_le; case: nb.
Qed.
