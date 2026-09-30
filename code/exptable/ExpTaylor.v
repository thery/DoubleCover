(** * The Taylor remainder of exp: condition 4, (H_T) *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Coquelicot Require Import Coquelicot.
From ExpTable Require Import ExpCheck.

Open Scope R_scope.

(* Every derivative of exp is exp. *)
Lemma Derive_n_exp (m : nat) (t : R) : Derive_n exp m t = exp t.
Proof.
revert t; induction m as [|m IH]; intros t; [reflexivity|].
simpl; rewrite (Derive_ext _ _ _ IH).
now apply is_derive_unique, is_derive_exp.
Qed.

(* exp is differentiable [m] times everywhere. *)
Lemma ex_derive_n_exp (m : nat) (t : R) : ex_derive_n exp m t.
Proof.
destruct m as [|m]; [exact I|simpl].
apply (ex_derive_ext exp); [intros s; now rewrite Derive_n_exp|].
eexists; apply is_derive_exp.
Qed.

(* [sumR] with [N + 1] terms is the Stdlib [sum_f_R0] up to [N]. *)
Lemma sumR_sum_f (f : nat -> R) (N : nat) : sumR f (S N) = sum_f_R0 f N.
Proof.
induction N as [|N IH]; [simpl; ring|].
change (sumR f (S N) + f (S N) = sum_f_R0 f N + f (S N)); now rewrite IH.
Qed.

(** For [h >= 0], the Taylor polynomial of degree [N-1] of [exp] at [x0]
    is below [exp (x0 + h)] by at most [exp (x0 + h) h^N / N!]. *)
Lemma taylor_exp (x0 h : R) (N : nat) : 0 <= h ->
  Rabs (exp (x0 + h) - sumR (fun i => exp x0 * h ^ i / INR (fact i)) N)
    <= exp (x0 + h) * h ^ N / INR (fact N).
Proof.
intros Hh.
destruct N as [|N].
  simpl; rewrite Rminus_0_r, Rabs_right by (left; apply exp_pos); lra.
destruct Hh as [Hh|<-].
2:{ (* At [h = 0] the sum is [exp x0] and the bound is [0]. *)
    rewrite Rplus_0_r, sumR_sum_f, pow_i by lia.
    replace (sum_f_R0 _ N) with (exp x0).
      rewrite Rminus_diag, Rabs_R0, Rmult_0_r; unfold Rdiv; lra.
    induction N as [|N IH]; [simpl; field|].
    rewrite tech5, <- IH, pow_i by lia; unfold Rdiv; ring. }
(* Lagrange: the remainder is [h^(N+1) / (N+1)! exp z], [z] in the range. *)
destruct (Taylor_Lagrange exp N x0 (x0 + h)) as [z [Hz Hz']]; [lra| |].
  intros t _ m _; apply ex_derive_n_exp.
rewrite sumR_sum_f.
replace (sum_f_R0 _ N) with
  (sum_f_R0 (fun m => (x0 + h - x0) ^ m / INR (fact m) * Derive_n exp m x0)
     N).
2:{ apply sum_eq; intros i _; rewrite Derive_n_exp.
    replace (x0 + h - x0) with h by ring; unfold Rdiv; ring. }
rewrite Hz' at 1; rewrite Derive_n_exp.
replace (x0 + h - x0) with h by ring.
assert (0 < INR (fact (S N))) by apply INR_fact_lt_0.
assert (0 < h ^ S N) by (apply pow_lt; lra).
rewrite Rplus_minus_l, Rabs_right.
2:{ apply Rle_ge; unfold Rdiv; apply Rmult_le_pos; [|left; apply exp_pos].
    apply Rmult_le_pos; [lra|left; apply Rinv_0_lt_compat; lra]. }
rewrite (Rmult_comm (exp _)); unfold Rdiv.
assert (exp z < exp (x0 + h)) by (apply exp_increasing; lra).
assert (0 < / INR (fact (S N))) by (apply Rinv_0_lt_compat; lra).
assert (0 < h ^ S N * / INR (fact (S N))) by (apply Rmult_lt_0_compat; lra).
nra.
Qed.

(* Two sums with equal terms are equal. *)
Lemma sumR_ext (f g : nat -> R) (N : nat) :
  (forall i, f i = g i) -> sumR f N = sumR g N.
Proof.
intros Hfg; induction N as [|N IH]; simpl; [easy|now rewrite IH, Hfg].
Qed.

(* A common divisor comes out of the sum. *)
Lemma sumR_div (f : nat -> R) (v : R) (N : nat) :
  sumR (fun i => f i / v) N = sumR f N / v.
Proof.
induction N as [|N IH]; simpl; [|rewrite IH]; unfold Rdiv; ring.
Qed.

(** Condition 4 of [line_ok], for [j] in [[0, n]]. *)
Lemma HT_ok (x0 v : R) (n j : Z) : 0 < v -> (0 <= j <= n)%Z ->
  Rabs (exp (x0 + IZR j * u) / v - sumR (fun i => a x0 i / v * IZR j ^ i) k)
    <= exp (x0 + IZR n * u) * (IZR n * u) ^ k / (INR (fact k) * v).
Proof.
intros Hv [Hj Hjn].
assert (Hu : 0 < u) by apply Flocq.Core.Raux.bpow_gt_0.
apply IZR_le in Hj; apply IZR_le in Hjn.
assert (Hh : 0 <= IZR j * u) by (apply Rmult_le_pos; lra).
(* The sum is the Taylor sum at [h = j u], divided by [v]. *)
rewrite (sumR_ext _ (fun i => exp x0 * (IZR j * u) ^ i / INR (fact i) / v)).
2:{ intros i; unfold a; rewrite Rpow_mult_distr; field.
    split; [apply not_0_INR, fact_neq_0|lra]. }
rewrite (sumR_div (fun i => exp x0 * (IZR j * u) ^ i / INR (fact i))).
set (Sj := sumR _ k).
replace (exp (x0 + IZR j * u) / v - Sj / v) with
  ((exp (x0 + IZR j * u) - Sj) / v) by (field; lra).
rewrite Rabs_div, (Rabs_right v) by lra.
assert (0 < INR (fact k)) by apply INR_fact_lt_0.
replace (_ / (INR (fact k) * v)) with
  (exp (x0 + IZR n * u) * (IZR n * u) ^ k / INR (fact k) / v)
  by (field; lra).
apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|].
eapply Rle_trans; [apply taylor_exp; lra|].
(* The bound grows with [j], so [j = n] is the worst case. *)
unfold Rdiv; apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; lra|].
apply Rmult_le_compat.
- left; apply exp_pos.
- now apply pow_le.
- destruct (Rle_lt_or_eq_dec _ _ Hjn) as [Hlt|Heq]; [|rewrite Heq; lra].
  left; apply exp_increasing; nra.
- apply pow_incr; split; [lra|]; nra.
Qed.
