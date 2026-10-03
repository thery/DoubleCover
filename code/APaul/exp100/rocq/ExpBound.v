(** * S2: the enclosure of exp x

    When [core_Z xb] returns [(y, hN)], y 2^(hN - P) is within
    D 2^(hN - P) of exp x, for every x the bits [xb] stand for
    ([is_x xb x]).  The error budget is in ../README; its lines are the
    lemmas of ExpBudget.v. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Exp100 Require Import ExpTaylor ExpConsts ExpModel ExpBits ExpBudget.

Open Scope R_scope.

(** y is at least 2^P: T_j >= 2^P and the Horner value is >= C_0 = 2^P. *)
Theorem core_y_ge xb y hN : (0 <= xb < 2 ^ 64)%Z ->
  core_Z xb = inr (y, hN) -> (2 ^ P <= y)%Z.
Proof.
intros _ Hc.
destruct (core_relP xb y hN Hc) as (n & _ & Hq & _ & -> & _).
pose proof (horner_ge _ (rarg_ge0 xb n Hq)) as Hh.
pose proof (Tv_ge (Nu xb n mod TAB)
              (Z.mod_pos_bound _ TAB ltac:(reflexivity))) as Ht.
rewrite mulshrE; set (t := Tv _) in *; set (h := horner _) in *.
assert (H2 : (0 < 2 ^ P)%Z) by (unfold P; lia).
apply Z.div_le_lower_bound; nia.
Qed.

(* 2^P as a power of Flocq. *)
Lemma bpow_P : bpow radix2 P = IZR (2 ^ P).
Proof. reflexivity. Qed.

Theorem core_bound xb y hN x : (0 <= xb < 2 ^ 64)%Z ->
  core_Z xb = inr (y, hN) -> is_x xb x ->
  Rabs (exp x - IZR y * bpow radix2 (hN - P)) <=
    IZR D * bpow radix2 (hN - P).
Proof.
intros _ Hc [Hs1 [Hs2 Hx]]; rewrite bpow_P in Hx.
destruct (core_relP xb y hN Hc) as (n & Hbe & Hq & Hr & Hy & Hh).
destruct (n_bound n _ (xfix_lt xb Hbe) Hq) as [Hn0 Hn1].
pose proof (rarg_ge0 xb n Hq) as Hr0.
pose proof (ltZ_rmax _ Hr) as HR.
pose proof (red_arg_err xb n x Hs1 Hs2 Hx Hq Hn0 Hn1) as Hred.
set (r := rarg xb n) in *.
(* N + 2^17 = Nu, j = N mod 64 and hN = floor(N / 64) *)
assert (HNu : Nu xb n = (hN_bias * TAB + Nz xb n)%Z).
{ unfold Nu, Nz; destruct (xsign xb =? 0)%Z; reflexivity || lia. }
set (N := Nz xb n) in *.
rewrite HNu, Z.add_comm, Z_mod_plus_full in Hy.
rewrite HNu, Z.add_comm, Z_div_plus_full in Hh by (unfold TAB; lia).
replace hN with (N / TAB)%Z by lia; clear Hh.
set (j := (N mod TAB)%Z) in *.
assert (Hj : (0 <= j < TAB)%Z) by (apply Z.mod_pos_bound; reflexivity).
(* exp x = 2^hN 2^(j/64) exp(r* ) *)
rewrite (exp_split x N); fold j.
replace (exp (IZR (N / TAB) * ln 2)) with (bpow radix2 (N / TAB))
  by (rewrite bpow_exp; reflexivity).
unfold Z.sub; rewrite bpow_plus, bpow_opp, bpow_P; fold u.
set (B := bpow radix2 (N / TAB)).
assert (HB : 0 < B) by apply bpow_gt_0.
set (tau := Rpower 2 (IZR j / IZR TAB)).
set (rs := x - IZR N * (ln 2 / IZR TAB)) in *.
replace (B * tau * exp rs - IZR y * (B * u))
  with (B * (tau * exp rs - IZR y * u)) by ring.
replace (IZR D * (B * u)) with (B * (IZR D * u)) by ring.
rewrite Rabs_mult, (Rabs_pos_eq B) by lra.
apply Rmult_le_compat_l; [lra|].
(* the four lines of the budget *)
pose proof u_pos as Hu.
pose proof (Rpower_TAB_bounds j Hj) as Htau; fold tau in Htau.
pose proof (table_err j Hj) as Htab; fold tau in Htab.
pose proof (horner_err r Hr0 HR) as Hhor.
assert (HR0 : 0 <= IZR r * u)
  by (apply Rmult_le_pos; [apply IZR_le; lia|lra]).
pose proof (taylor_err (IZR r * u) (conj HR0 HR)) as Htay.
pose proof exp_rmax_ub as Hexp.
assert (HH0 : 0 <= IZR (horner r))
  by (apply IZR_le; pose proof (horner_ge r Hr0); unfold P in *; lia).
apply budget_total with (t := IZR (Tv j) * u) (h := IZR (horner r) * u)
  (p := sumR (fun i => (IZR r * u) ^ i / INR (fact i)) (S DEG))
  (eR := exp (IZR r * u)); auto; try lra.
- (* 0 <= h <= exp_bound: h <= p(r u) <= exp(r u) + 1.6122 u *)
  split; [apply Rmult_le_pos; lra|].
  pose proof (exp_mono (IZR r * u) (rmax + red_budget * u)
                ltac:(unfold red_budget; lra)).
  apply Rabs_le_inv in Htay; lra.
- (* the reduced argument, through exp(rmax + 2 u) <= exp_bound *)
  apply Rabs_le_inv in Hred.
  eapply Rle_trans; [apply (exp_diff _ _ (rmax + red_budget * u));
                     unfold red_budget in *; lra|].
  apply Rmult_le_compat; [left; apply exp_pos|apply Rabs_pos| |].
  + pose proof (exp_pos (rmax + red_budget * u)).
    pose proof (exp_pos (IZR r * u)); unfold taylor_budget in Hexp; lra.
  + apply Rabs_le; lra.
- (* the last floor *)
  rewrite Hy; apply mulshr_R.
Qed.
