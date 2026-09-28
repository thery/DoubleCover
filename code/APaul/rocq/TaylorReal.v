(** * Zimmermann's search (doc/htr.md): from the reals to the scan

    [TaylorScan.scan_complete] says: if the integer polynomial [P] is
    within [E] of a multiple of [M] at [j], then [j] is a candidate.  This
    file proves the step before it, on the reals: if [y] (standing for
    [exp(x0 + j u) / v]) is within [eps] (standing for [2^-m]) of an
    integer, then [P j] is within [E] of a multiple of [M], under the three
    hypotheses of the note:
      (H_A) each [A_i] is within 1 of [M frac(a_i)];
      (H_T) [y] is within [rho] of [sum_i a_i j^i];
      (H_E) [E >= M (eps + rho) + (1 + n + ... + n^(k-1))].
    [exp] does not appear: it only enters through (H_A) and (H_T).

    Stdlib only, no mathcomp, so that the real arithmetic is not disturbed
    by mathcomp's notations. *)

From Stdlib Require Import ZArith Reals Lra Lia.

Open Scope R_scope.

(** [sum_(i < k) f i], by recursion on [k]. *)
Fixpoint sumR (k : nat) (f : nat -> R) : R :=
  match k with O => 0 | S k' => sumR k' f + f k' end.

(** The integer polynomial [sum_(i < k) A_i j^i]. *)
Fixpoint Pz (A : nat -> Z) (k j : nat) : Z :=
  match k with
  | O => 0%Z
  | S k' => (Pz A k' j + A k' * Z.of_nat j ^ Z.of_nat k')%Z
  end.

(** Extensionality of [sumR] below [k]. *)
Lemma sumR_ext (k : nat) (f g : nat -> R) :
  (forall i, (i < k)%nat -> f i = g i) -> sumR k f = sumR k g.
Proof.
induction k as [|k IH]; intros H; simpl; [reflexivity|].
rewrite IH by (intros i Hi; apply H; lia).
rewrite H by lia; reflexivity.
Qed.

(** [sumR] is additive. *)
Lemma sumR_plus (k : nat) (f g : nat -> R) :
  sumR k (fun i => f i + g i) = sumR k f + sumR k g.
Proof. induction k as [|k IH]; simpl; [lra|rewrite IH; lra]. Qed.

(** [sumR] commutes with a scalar factor. *)
Lemma sumR_scal (k : nat) (c : R) (f : nat -> R) :
  sumR k (fun i => c * f i) = c * sumR k f.
Proof. induction k as [|k IH]; simpl; [ring|rewrite IH; ring]. Qed.

(** The triangle inequality for [sumR]. *)
Lemma Rabs_sumR_le (k : nat) (f g : nat -> R) :
  (forall i, (i < k)%nat -> Rabs (f i) <= g i) ->
  Rabs (sumR k f) <= sumR k g.
Proof.
induction k as [|k IH]; intros H; simpl.
- rewrite Rabs_R0; lra.
- apply Rle_trans with (Rabs (sumR k f) + Rabs (f k)); [apply Rabs_triang|].
  apply Rplus_le_compat; [apply IH; intros i Hi; apply H; lia|apply H; lia].
Qed.

(** The integer polynomial, read in the reals. *)
Lemma IZR_Pz (A : nat -> Z) (k j : nat) :
  IZR (Pz A k j) = sumR k (fun i => IZR (A i) * INR j ^ i).
Proof.
induction k as [|k IH]; simpl; [reflexivity|].
rewrite plus_IZR, mult_IZR, IH, <- pow_IZR, <- INR_IZR_INZ.
reflexivity.
Qed.

Lemma real_lemma (k n j : nat) (M E : Z) (a : nat -> R) (A : nat -> Z)
    (rho eps y : R) :
  (0 < M)%Z -> (j <= n)%nat ->
  (forall i, (i < k)%nat -> Rabs (IZR (A i) - IZR M * frac_part (a i)) < 1) ->
  Rabs (y - sumR k (fun i => a i * INR j ^ i)) <= rho ->
  IZR M * (eps + rho) + sumR k (fun i => INR n ^ i) <= IZR E ->
  (exists z : Z, Rabs (y - IZR z) < eps) ->
  exists w : Z, (Z.abs (Pz A k j - M * w) <= E)%Z.
Proof.
intros HM Hjn HA HT HE [z Hz].
set (K := Pz (fun i => Int_part (a i)) k j).
set (S := sumR k (fun i => a i * INR j ^ i)).
set (D := sumR k (fun i =>
            (IZR (A i) - IZR M * frac_part (a i)) * INR j ^ i)).
assert (HP : IZR (Pz A k j) = D + IZR M * S - IZR M * IZR K).
{ unfold D, S, K; rewrite !IZR_Pz, <- !sumR_scal.
  transitivity (sumR k (fun i =>
    ((IZR (A i) - IZR M * frac_part (a i)) * INR j ^ i
     + IZR M * (a i * INR j ^ i))
    + (-1) * (IZR M * (IZR (Int_part (a i)) * INR j ^ i)))).
  { apply sumR_ext; intros i _; unfold frac_part; ring. }
  rewrite sumR_plus, sumR_scal, sumR_plus; ring. }
assert (HD : Rabs D <= sumR k (fun i => INR n ^ i)).
{ apply Rabs_sumR_le; intros i Hi.
  rewrite Rabs_mult, (Rabs_right (INR j ^ i))
    by (apply Rle_ge, pow_le, pos_INR).
  apply Rle_trans with (1 * INR j ^ i).
  - apply Rmult_le_compat_r; [apply pow_le, pos_INR|].
    apply Rlt_le, HA; exact Hi.
  - rewrite Rmult_1_l; apply pow_incr; split; [apply pos_INR|].
    apply le_INR; exact Hjn. }
exists (z - K)%Z.
apply le_IZR; rewrite abs_IZR.
rewrite minus_IZR, mult_IZR, minus_IZR, HP.
assert (HM' : 0 < IZR M) by (apply IZR_lt; exact HM).
replace (D + IZR M * S - IZR M * IZR K - IZR M * (IZR z - IZR K))
  with (D - IZR M * (y - S) + IZR M * (y - IZR z)) by ring.
apply Rle_trans
  with (Rabs D + IZR M * Rabs (y - S) + IZR M * Rabs (y - IZR z)).
{ apply Rle_trans
    with (Rabs (D - IZR M * (y - S)) + Rabs (IZR M * (y - IZR z)));
    [apply Rabs_triang|].
  rewrite Rabs_mult, (Rabs_right (IZR M)) by lra.
  apply Rplus_le_compat_r.
  unfold Rminus at 1; eapply Rle_trans; [apply Rabs_triang|].
  rewrite Rabs_Ropp, Rabs_mult, (Rabs_right (IZR M)) by lra; lra. }
assert (IZR M * Rabs (y - S) <= IZR M * rho)
  by (apply Rmult_le_compat_l; [lra|exact HT]).
assert (IZR M * Rabs (y - IZR z) <= IZR M * eps)
  by (apply Rmult_le_compat_l; lra).
lra.
Qed.
