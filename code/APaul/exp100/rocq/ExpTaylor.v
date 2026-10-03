(** * The Taylor remainder of exp

    For h >= 0, the Taylor polynomial of exp at x0 is below exp (x0 + h)
    by at most exp (x0 + h) h^N / N!. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

(** f 0 + ... + f (N-1). *)
Fixpoint sumR (f : nat -> R) (N : nat) : R :=
  match N with O => 0 | S N' => sumR f N' + f N' end.

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

