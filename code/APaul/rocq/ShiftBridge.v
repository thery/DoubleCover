(** * Moving the powers of two, over the reals

    [ShiftExp.v] carries the value of the approximation as an integer:
    everything is multiplied by [2^vden] so that no fraction is left.
    [Cheb.v] carries the same value as a real, with the powers of two in
    the denominator.  This file holds the one identity that relates them,
    for a single term of the sum.

    It is deliberately free of mathcomp.  The statement is about [Z] and
    [R] and nothing else, and with mathcomp loaded the rewriting lemmas on
    [pow] pick up the wrong subterms. *)

From Stdlib Require Import ZArith Reals Lia.

Open Scope R_scope.

Lemma pow2_neq0 (m : nat) : 2 ^ m <> 0.
Proof. apply pow_nonzero, Rgt_not_eq, Rlt_0_2. Qed.

(** One term.  The integer holds [54 (7 - k)] powers of two and the
    denominator [598]; what is left is [220 + 54 k], and the two counts
    add up to [598] whatever [k] is.  That is the whole content. *)
Lemma term_bridge (c D : Z) (k : nat) : (k <= 7)%nat ->
  IZR (Z.mul (Z.mul c (Z.pow 2 (Z.of_nat (54 * (7 - k)))))
             (Z.pow D (Z.of_nat k))) / 2 ^ 598
  = IZR c * (IZR D / 2 ^ 54) ^ k / 2 ^ 220.
Proof.
intros k7.
repeat rewrite mult_IZR.
repeat rewrite <- pow_IZR.
assert (e598 : (54 * (7 - k) + (220 + 54 * k) = 598)%nat) by lia.
rewrite <- e598.
rewrite pow_add.
assert (d54 : (IZR D / 2 ^ 54) ^ k = IZR D ^ k / 2 ^ (54 * k)).
{ unfold Rdiv. rewrite Rpow_mult_distr.
  rewrite pow_mult. rewrite <- Rinv_pow;
  [reflexivity | apply pow2_neq0]. }
rewrite d54.
rewrite pow_add.
field; repeat split; apply pow2_neq0.
Qed.

(** The eight terms of the sum, each put over the common denominator. *)
Lemma split8 (a0 a1 a2 a3 a4 a5 a6 a7 : R) :
  (a0 + (a1 + (a2 + (a3 + (a4 + (a5 + (a6 + (a7 + 0)))))))) / 2 ^ 598
  = a0 / 2 ^ 598 + a1 / 2 ^ 598 + a2 / 2 ^ 598 + a3 / 2 ^ 598
  + a4 / 2 ^ 598 + a5 / 2 ^ 598 + a6 / 2 ^ 598 + a7 / 2 ^ 598.
Proof. field; apply pow2_neq0. Qed.
