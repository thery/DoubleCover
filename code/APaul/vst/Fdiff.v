(** * The table of differences, on integers

    [fdiff], the forward difference of [code/APaul/rocq/HtrDefs.v] (copied
    here), its recurrence [dif], and [stage]: what the coefficients hold
    after some passes of [difftab].  Then the coefficients of a flat array
    of words. *)

From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist list_solver.
Require Import HtrVst.Words.
Import ListNotations.

Open Scope Z_scope.

(** ** The forward difference, as in HtrDefs.v *)

(** [C(n, t)]. *)
Fixpoint binom (n t : nat) : Z :=
  match n, t with
  | _, O => 1
  | O, S _ => 0
  | S n', S t' => binom n' t' + binom n' t
  end.

(** The [j]-th forward difference at 0 of the sequence [ds]:
    [sum_(t <= j) (-1)^(j - t) C(j, t) ds_t]. *)
Definition fdiff (ds : list Z) (j : nat) : Z :=
  fold_right Z.add 0
    (map (fun t => (-1) ^ Z.of_nat (j - t) * binom j t * nth t ds 0)
         (seq 0 (S j))).

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

(** ** Coefficients of a flat array

    A flat array of words holds the coefficients [B_0, B_1, ...], each of
    [l] words, the least significant first: [B_p] is the words
    [p l .. p l + l - 1]. *)

(** The number [B_p]. *)
Definition coef (xs : list Z) (l p : Z) : Z :=
  valZ (sublist (p * l) (p * l + l) xs).

(** The numbers [B_0 .. B_(k-1)]. *)
Definition coefs (xs : list Z) (l k : Z) : list Z :=
  map (fun j => coef xs l (Z.of_nat j)) (seq 0 (Z.to_nat k)).

(** [B_p] is a number of [l] words. *)
Lemma coef_bound xs l p : Forall word xs -> 0 <= p -> 0 <= l ->
  p * l + l <= Zlength xs -> 0 <= coef xs l p < baseZ l.
Proof.
  intros Hw Hp Hl Hpl; unfold coef.
  pose proof (valZ_bound (sublist (p * l) (p * l + l) xs)) as Hb.
  rewrite Zlength_sublist in Hb by nia.
  replace (p * l + l - p * l) with l in Hb by lia.
  apply Hb, Forall_sublist; auto.
Qed.

(** Two arrays that agree on the words of [B_p] have the same [B_p]. *)
Lemma coef_eq xs ys l p : 0 <= p -> 0 <= l ->
  p * l + l <= Zlength xs -> Zlength ys = Zlength xs ->
  (forall q, p * l <= q < p * l + l -> Znth q ys = Znth q xs) ->
  coef ys l p = coef xs l p.
Proof.
  intros Hp Hl Hpl Hlen H; unfold coef; f_equal.
  apply Znth_eq_ext.
  - rewrite !Zlength_sublist; nia.
  - intros q Hq; rewrite Zlength_sublist in Hq by nia.
    rewrite !Znth_sublist by nia; apply H; nia.
Qed.
