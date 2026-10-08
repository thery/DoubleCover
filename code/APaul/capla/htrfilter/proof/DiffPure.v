(** * The forward differences by their recurrence

    Copied from ../../../vst/Fdiff.v (the pure part, on HtrDefs.v's
    [binom] and [fdiff]): [dif], the recurrence of the differences, its
    sum with the binomial coefficients, and [stage], what the
    coefficients hold after some passes of difftab. *)

From Stdlib Require Import ZArith List Lia.
From APaulRocq Require Import HtrDefs.
Import ListNotations.

Open Scope Z_scope.

(** ** Sums *)

(** The sum of [f t] for [t < m]. *)
Definition sumZ (f : nat -> Z) (m : nat) : Z :=
  fold_right Z.add 0 (map f (seq 0 m)).

Lemma fold_addZ (l : list Z) a :
  fold_right Z.add a l = fold_right Z.add 0 l + a.
Proof. induction l as [|x l IH]; simpl; lia. Qed.

Lemma sumZ_S0 f m : sumZ f (S m) = f 0%nat + sumZ (fun t => f (S t)) m.
Proof. unfold sumZ; simpl; rewrite <- seq_shift, map_map; reflexivity. Qed.

Lemma sumZ_Sr f m : sumZ f (S m) = sumZ f m + f m.
Proof.
  unfold sumZ; rewrite seq_S, map_app, fold_right_app; simpl.
  rewrite fold_addZ; lia.
Qed.

Lemma sumZ_ext f g m : (forall t, (t < m)%nat -> f t = g t) ->
  sumZ f m = sumZ g m.
Proof.
  intros H; unfold sumZ; f_equal; apply map_ext_in; intros t Ht.
  apply in_seq in Ht; apply H; lia.
Qed.

Lemma sumZ_add f g m :
  sumZ (fun t => f t + g t) m = sumZ f m + sumZ g m.
Proof. induction m as [|m IH]; [reflexivity|rewrite !sumZ_Sr, IH; lia]. Qed.

Lemma sumZ_opp f m : sumZ (fun t => - f t) m = - sumZ f m.
Proof. induction m as [|m IH]; [reflexivity|rewrite !sumZ_Sr, IH; lia]. Qed.

Lemma binom_gt n t : (n < t)%nat -> binom n t = 0.
Proof.
  revert t; induction n as [|n IH]; intros [|t] H; simpl; try lia.
  rewrite !IH; lia.
Qed.

Lemma binom0 n : binom n 0 = 1.
Proof. destruct n; reflexivity. Qed.

Lemma pow_m1S m : (-1) ^ Z.of_nat (S m) = - (-1) ^ Z.of_nat m.
Proof. rewrite Nat2Z.inj_succ, Z.pow_succ_r; lia. Qed.

(** ** The recurrence *)

(** The [a]-th difference of [x] at [n], by the recurrence. *)
Fixpoint dif (x : nat -> Z) (a n : nat) : Z :=
  match a with
  | O => x n
  | S a => dif x a (S n) - dif x a n
  end.

(** The recurrence gives the sum with the binomial coefficients. *)
Lemma dif_sum x a n :
  dif x a n =
  sumZ (fun t => (-1) ^ Z.of_nat (a - t) * binom a t * x (n + t)%nat) (S a).
Proof.
  revert n; induction a as [|a IH]; intros n.
  - unfold sumZ; simpl; rewrite Nat.add_0_r; destruct (x n); reflexivity.
  - cbn [dif]; rewrite !IH, (sumZ_S0 _ (S a)); cbv beta.
    set (C := fun t => (-1) ^ Z.of_nat (a - t) * binom a t * x (n + t)%nat).
    set (B := fun t =>
      (-1) ^ Z.of_nat (a - t) * binom a (S t) * x (n + S t)%nat).
    (* Pascal's rule splits the sum in two. *)
    assert (HG : sumZ (fun t => (-1) ^ Z.of_nat (S a - S t) *
                   binom (S a) (S t) * x (n + S t)%nat) (S a) =
                 sumZ (fun t => (-1) ^ Z.of_nat (a - t) * binom a t *
                   x (S n + t)%nat) (S a) + sumZ B (S a)).
    { rewrite <- sumZ_add; apply sumZ_ext; intros t Ht; unfold B.
      replace (S n + t)%nat with (n + S t)%nat by lia.
      replace (S a - S t)%nat with (a - t)%nat by lia.
      cbn [binom]; ring. }
    assert (HB : sumZ B (S a) = - sumZ (fun t => C (S t)) a).
    { rewrite sumZ_Sr; unfold B at 2; rewrite (binom_gt a (S a)) by lia.
      rewrite <- sumZ_opp; rewrite Z.mul_0_r, Z.mul_0_l, Z.add_0_r.
      apply sumZ_ext; intros t Ht; unfold B, C.
      replace (a - t)%nat with (S (a - S t)) by lia.
      rewrite pow_m1S; ring. }
    assert (HC : sumZ C (S a) = C 0%nat + sumZ (fun t => C (S t)) a)
      by apply sumZ_S0.
    assert (H0 : (-1) ^ Z.of_nat (S a - 0) * binom (S a) 0 * x (n + 0)%nat =
                 - C 0%nat).
    { unfold C; replace (S a - 0)%nat with (S a) by lia.
      replace (a - 0)%nat with a by lia.
      rewrite pow_m1S, !binom0; ring. }
    rewrite HG, HB, H0, HC; ring.
Qed.

(** [fdiff] is the difference of the recurrence. *)
Lemma fdiff_dif x k j : (j < k)%nat ->
  fdiff (map x (seq 0 k)) j = dif x j 0.
Proof.
  intros Hj; rewrite dif_sum; unfold fdiff; fold (sumZ
    (fun t => (-1) ^ Z.of_nat (j - t) * binom j t *
              nth t (map x (seq 0 k)) 0) (S j)).
  apply sumZ_ext; intros t Ht.
  rewrite (nth_indep _ 0 (x 0%nat)) by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia; reflexivity.
Qed.

(** ** The passes of difftab *)

(** After [a] passes, coefficient [p] holds the difference of order
    [min p a]. *)
Definition stage (x : nat -> Z) (a p : nat) : Z :=
  dif x (Nat.min p a) (p - Nat.min p a).

(** One step of pass [a + 1], at [p > a]. *)
Lemma stage_step x a p : (a < p)%nat ->
  stage x a p - stage x a (p - 1) = stage x (S a) p.
Proof.
  intros H; unfold stage.
  replace (Nat.min p a) with a by lia.
  replace (Nat.min (p - 1) a) with a by lia.
  replace (Nat.min p (S a)) with (S a) by lia.
  cbn [dif].
  replace (p - a)%nat with (S (p - S a)) by lia.
  replace (p - 1 - a)%nat with (p - S a)%nat by lia.
  reflexivity.
Qed.

(** Pass [a + 1] leaves coefficient [p] alone for [p <= a]. *)
Lemma stage_low x a p : (p <= a)%nat -> stage x (S a) p = stage x a p.
Proof.
  intros H; unfold stage.
  replace (Nat.min p a) with p by lia.
  replace (Nat.min p (S a)) with p by lia.
  reflexivity.
Qed.

(** Before any pass, coefficient [p] is [x p]. *)
Lemma stage0 x p : stage x 0 p = x p.
Proof. unfold stage; rewrite Nat.min_0_r, Nat.sub_0_r; reflexivity. Qed.

(** After [p] passes, coefficient [p] is the difference of order [p]. *)
Lemma stage_end x a p : (p <= a)%nat -> stage x a p = dif x p 0.
Proof.
  intros H; unfold stage.
  replace (Nat.min p a) with p by lia.
  rewrite Nat.sub_diag; reflexivity.
Qed.

