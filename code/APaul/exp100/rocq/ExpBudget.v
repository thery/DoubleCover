(** * The error budget of exp100.c, line by line

    The lines of the table "Error budget" of ../README, one lemma each,
    on the integers [core_Z] computes (ExpModel.v), with u = 2^-P:
    - [red_arg_err]: the reduced argument, |r u - r*| <= 2 u;
    - [horner_err]: the Horner truncations, 0 <= p(r u) - h u <= 2.0219 u;
    - [taylor_err]: the Taylor remainder, |exp(r u) - p(r u)| <= 1.6122 u;
    - [table_err]: the table, |T_j u - 2^(j/64)| <= u/2;
    - [budget_total]: their sum, with the last floor, is at most D u.
    ExpBound.v applies them to [core_Z]. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From Exp100 Require Import ExpTaylor.
From Exp100 Require Import ExpConsts ExpModel.

Open Scope R_scope.

(** ** The integer side *)

(* C_i is nonnegative. *)
Lemma Cv_ge0 i : (i <= DEG)%nat -> (0 <= Cv i)%Z.
Proof.
intros Hi; rewrite CvE, C_ok by exact Hi.
apply Z.div_pos; [apply Z.pow_nonneg; lia|apply factN_gt0].
Qed.

(* C_0 = 2^P. *)
Lemma Cv0 : Cv 0 = (2 ^ P)%Z.
Proof. rewrite CvE, C_ok by (unfold DEG; lia); apply Z.div_1_r. Qed.

(* exp is nondecreasing. *)
Lemma exp_mono a b : a <= b -> exp a <= exp b.
Proof. intros [H|<-]; [left; apply exp_increasing, H|lra]. Qed.

(* 2^(j/64) is in [1, 2] for 0 <= j < 64. *)
Lemma Rpower_TAB_bounds j : (0 <= j < TAB)%Z ->
  1 <= Rpower 2 (IZR j / IZR TAB) <= 2.
Proof.
intros Hj.
assert (Hl : 0 < ln 2) by (rewrite <- ln_1; apply ln_increasing; lra).
assert (HT : 0 < IZR TAB) by (apply IZR_lt; unfold TAB; lia).
assert (H0 : 0 <= IZR j / IZR TAB <= 1).
{ split; [apply Rmult_le_pos; [apply IZR_le; lia|]; left;
          apply Rinv_0_lt_compat, HT|].
  apply Rmult_le_reg_r with (IZR TAB); [exact HT|].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Rmult_1_l by lra.
  apply IZR_le; lia. }
unfold Rpower; split.
- rewrite <- exp_0; apply exp_mono; nra.
- rewrite <- (exp_ln 2) at 2 by lra; apply exp_mono; nra.
Qed.

(* T_j >= 2^P. *)
Lemma Tv_ge j : (0 <= j < TAB)%Z -> (2 ^ P <= Tv j)%Z.
Proof.
intros Hj; rewrite TvE; generalize (T_ok j Hj).
set (t := valZ _); intros Ht.
destruct (Rpower_TAB_bounds j Hj) as [H1 _].
assert (H2 : 0 < IZR (2 ^ P)) by (apply IZR_lt; unfold P; lia).
apply Rabs_le_inv in Ht.
assert (H : IZR (2 ^ P) - 1 < IZR t) by nra.
rewrite <- minus_IZR in H; apply lt_IZR in H; lia.
Qed.

(* floor(a b / 2^P) >= 0 for a, b >= 0. *)
Lemma mulshr_ge0 a b : (0 <= a)%Z -> (0 <= b)%Z -> (0 <= mulshr a b)%Z.
Proof.
intros Ha Hb; rewrite mulshrE.
apply Z.div_pos; [nia|apply Z.pow_pos_nonneg; unfold P; lia].
Qed.

(* Every Horner value is >= 0, and the last one is >= C_0. *)
Lemma horner_from_ge r h k : (0 <= r)%Z -> (k <= DEG)%nat -> (0 <= h)%Z ->
  (k = O -> Cv 0 <= h)%Z -> (Cv 0 <= horner_from r h k)%Z.
Proof.
intros Hr; revert h; induction k as [|i IH]; intros h Hk Hh H0;
  [now apply H0|].
cbn [horner_from]; pose proof (mulshr_ge0 h r Hh Hr).
pose proof (Cv_ge0 i ltac:(lia)).
apply IH; [lia|lia|intros ->; lia].
Qed.

Lemma horner_ge r : (0 <= r)%Z -> (2 ^ P <= horner r)%Z.
Proof.
intros Hr; rewrite <- Cv0; apply horner_from_ge; auto.
- apply Cv_ge0; auto.
- unfold DEG; discriminate.
Qed.

(* r >= 0 once n is checked. *)
Lemma rarg_ge0 xb n : (q n <= xfix xb < q (n + 1))%Z -> (0 <= rarg xb n)%Z.
Proof. unfold rarg; destruct (xsign xb =? 0)%Z; lia. Qed.

(** ** Bounds on X and n: |x| < 1024 *)

(* X = floor(|x| 2^P) < 2^(P + 10). *)
Lemma xfix_lt xb : (xbexp xb < be_big)%Z -> (0 <= xfix xb < 2 ^ (P + 10))%Z.
Proof.
intros Hb.
assert (He : (0 <= xbexp xb)%Z).
{ rewrite xbexpE; apply Z.mod_pos_bound; reflexivity. }
assert (Hm : (0 <= xmant xb < 2 ^ 53)%Z).
{ unfold xmant; rewrite pow2E, xmant0E by discriminate.
  pose proof (Z.mod_pos_bound xb (2 ^ mant_bits) ltac:(reflexivity)).
  destruct (xbexp xb =? 0)%Z; unfold mant_bits in *; lia. }
assert (Hx : (1 <= xexpo xb <= 1032)%Z).
{ unfold xexpo; destruct (Z.eqb_spec (xbexp xb) 0); unfold be_big in Hb;
  lia. }
unfold xfix; rewrite scaleE.
set (e := (xexpo xb - expo_shift + P)%Z).
destruct (Z.leb_spec 0 e) as [He0|He0].
- assert (H1 : (2 ^ e <= 2 ^ 117)%Z).
  { apply Z.pow_le_mono_r; unfold e, expo_shift, P in *; lia. }
  assert (H2 : (0 < 2 ^ e)%Z) by (apply Z.pow_pos_nonneg; lia).
  change (2 ^ (P + 10))%Z with (2 ^ 53 * 2 ^ 117)%Z; nia.
- split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
  assert (H1 : (1 <= 2 ^ (- e))%Z).
  { apply (Z.pow_le_mono_r 2 0); lia. }
  apply Z.le_lt_trans with (xmant xb); [|change (2 ^ (P + 10))%Z with
    (2 ^ 53 * 2 ^ 117)%Z; lia].
  apply Z.div_le_upper_bound; nia.
Qed.

(* The checked n is in [0, 2^17 - 1]: q(2^17) >= 2^(P + 10). *)
Lemma n_bound n X : (0 <= X < 2 ^ (P + 10))%Z -> (q n <= X < q (n + 1))%Z ->
  (0 <= n /\ n + 1 <= N_bias)%Z.
Proof.
intros HX Hq; rewrite !qE in Hq.
assert (Hc : (2 ^ (P + 10) <= N_bias * valZ ExpTable.LN2 / 2 ^ limb_bits)%Z).
{ apply Z.leb_le; vm_compute; reflexivity. }
assert (HL : (0 < valZ ExpTable.LN2)%Z) by (vm_compute; reflexivity).
set (L := valZ ExpTable.LN2) in *.
assert (H2 : (0 < 2 ^ limb_bits)%Z) by reflexivity.
split.
- destruct (Z.le_gt_cases 0 n) as [|Hn]; [lia|exfalso].
  assert (H : ((n + 1) * L / 2 ^ limb_bits <= 0)%Z).
  { apply Z.div_le_upper_bound; nia. }
  lia.
- destruct (Z.le_gt_cases (n + 1) N_bias) as [|Hn]; [lia|exfalso].
  assert (H : (N_bias * L / 2 ^ limb_bits <= n * L / 2 ^ limb_bits)%Z).
  { apply Z.div_le_mono; [lia|apply Z.mul_le_mono_nonneg_r; lia]. }
  lia.
Qed.

(** ** Floors on the reals *)

Lemma u_pos : 0 < u.
Proof. apply Rinv_0_lt_compat, IZR_lt; unfold P; lia. Qed.

Lemma u_P : IZR (2 ^ P) * u = 1.
Proof. apply Rinv_r, not_0_IZR; unfold P; lia. Qed.

(* floor(a / b), on the reals. *)
Lemma Zdiv_R a b : (0 < b)%Z ->
  IZR (a / b) * IZR b <= IZR a < (IZR (a / b) + 1) * IZR b.
Proof.
intros Hb; pose proof (Z.div_mod a b ltac:(lia)) as Hd.
pose proof (Z.mod_pos_bound a b Hb) as [Hm0 Hm1].
apply IZR_le in Hm0; apply IZR_lt in Hm1.
replace (IZR a) with (IZR b * IZR (a / b) + IZR (a mod b))
  by (rewrite <- mult_IZR, <- plus_IZR; f_equal; exact (eq_sym Hd)).
lra.
Qed.

(* floor(a b / 2^P) u is at most u below (a u) (b u). *)
Lemma mulshr_R a b : IZR a * u * (IZR b * u) - u < IZR (mulshr a b) * u
                     <= IZR a * u * (IZR b * u).
Proof.
rewrite mulshrE.
destruct (Zdiv_R (a * b) (2 ^ P) ltac:(unfold P; lia)) as [H1 H2].
rewrite mult_IZR in H1, H2.
set (m := IZR (a * b / 2 ^ P)) in *.
pose proof u_pos as Hu.
assert (E : forall z, z * IZR (2 ^ P) * (u * u) = z * u).
{ intros z; rewrite Rmult_assoc, <- (Rmult_assoc (IZR _)), u_P; ring. }
apply Rmult_le_compat_r with (r := u * u) in H1; [|nra].
apply Rmult_lt_compat_r with (r := u * u) in H2; [|nra].
rewrite E in H1, H2; split; nra.
Qed.

(* C_i u is at most u below 1/i!. *)
Lemma Cv_R i : (i <= DEG)%nat ->
  IZR (Cv i) * u <= / INR (fact i) < IZR (Cv i) * u + u.
Proof.
intros Hi; pose proof (C_floor i Hi) as Hc; rewrite <- CvE in Hc.
replace (/ INR (fact i)) with (IZR (2 ^ P) / INR (fact i) * u).
2:{ unfold Rdiv; rewrite (Rmult_comm (IZR _)), Rmult_assoc, u_P; ring. }
pose proof u_pos; split; nra.
Qed.

(** ** Line 1: the reduced argument, |r u - r*| <= 2 u *)

Definition red_budget : R := 2.

(* N: n for x >= 0, -(n+1) for x < 0. *)
Definition Nz (xb n : Z) : Z :=
  if (xsign xb =? 0)%Z then n else (- (n + 1))%Z.

(* n LN2 / 2^32 is within n 2^-33 <= 2^-16 of n ln2/64 2^P. *)
Definition q_eps : R := / 65536.

Lemma q_err m : (0 <= m <= N_bias)%Z ->
  - 1 - q_eps < IZR (q m) - IZR m * (ln 2 / IZR TAB * IZR (2 ^ P)) <= q_eps.
Proof.
intros Hm; pose proof LN2_ok as HL; rewrite qE.
destruct (Zdiv_R (m * valZ ExpTable.LN2) (2 ^ limb_bits) ltac:(reflexivity))
  as [H1 H2].
rewrite Z.pow_add_r, mult_IZR in HL by (unfold P, limb_bits; lia).
rewrite mult_IZR in H1, H2.
change (2 ^ limb_bits)%Z with 4294967296%Z in H1, H2, HL |- *.
set (Q := IZR (m * valZ ExpTable.LN2 / 4294967296)) in *.
set (K := ln 2 / IZR TAB * IZR (2 ^ P)) in *.
set (M := IZR m) in *; set (L := IZR (valZ ExpTable.LN2)) in *.
assert (HM : 0 <= M <= 131072).
{ split; apply IZR_le; unfold N_bias in Hm; lia. }
replace (ln 2 / IZR TAB * (IZR (2 ^ P) * IZR 4294967296))
  with (K * 4294967296) in HL by (unfold K; ring).
apply Rabs_le_inv in HL.
(* M (LN2 - K 2^32) is within M / 2 of 0 *)
assert (HP : - (M / 2) <= M * (L - K * 4294967296) <= M / 2)
  by (split; nra).
unfold q_eps; split; nra.
Qed.

Lemma red_arg_err xb n x :
  (xsign xb = 0%Z -> 0 <= x) -> (xsign xb <> 0%Z -> x <= 0) ->
  IZR (xfix xb) <= Rabs x * IZR (2 ^ P) < IZR (xfix xb) + 1 ->
  (q n <= xfix xb < q (n + 1))%Z -> (0 <= n)%Z -> (n + 1 <= N_bias)%Z ->
  Rabs (IZR (rarg xb n) * u - (x - IZR (Nz xb n) * (ln 2 / IZR TAB)))
    <= red_budget * u.
Proof.
intros Hp Hn Hx Hq Hn0 Hn1.
pose proof u_pos as Hu.
assert (H2P : IZR (2 ^ P) <> 0) by (apply not_0_IZR; unfold P; lia).
set (K := ln 2 / IZR TAB * IZR (2 ^ P)).
unfold rarg, Nz; destruct (Z.eqb_spec (xsign xb) 0) as [Hs|Hs].
- rewrite Rabs_pos_eq in Hx by auto.
  pose proof (q_err n ltac:(lia)) as Hqn; fold K in Hqn.
  replace (IZR (xfix xb - q n) * u - (x - IZR n * (ln 2 / IZR TAB)))
    with ((IZR (xfix xb) - IZR (q n) - (x * IZR (2 ^ P) - IZR n * K)) * u)
    by (rewrite minus_IZR; unfold K, u; field; split; auto;
        apply not_0_IZR; unfold TAB; lia).
  rewrite Rabs_mult, (Rabs_pos_eq u) by lra.
  apply Rmult_le_compat_r; [lra|]; apply Rabs_le.
  unfold red_budget, q_eps in *; lra.
- rewrite Rabs_left1 in Hx by auto.
  pose proof (q_err (n + 1) ltac:(lia)) as Hqn; fold K in Hqn.
  replace (IZR (q (n + 1) - xfix xb) * u
           - (x - IZR (- (n + 1)) * (ln 2 / IZR TAB)))
    with ((IZR (q (n + 1)) - IZR (xfix xb)
           - (x * IZR (2 ^ P) + IZR (n + 1) * K)) * u)
    by (rewrite minus_IZR, opp_IZR; unfold K, u; field; split; auto;
        apply not_0_IZR; unfold TAB; lia).
  rewrite Rabs_mult, (Rabs_pos_eq u) by lra.
  apply Rmult_le_compat_r; [lra|]; apply Rabs_le.
  unfold red_budget, q_eps in *; lra.
Qed.

(** ** Line 2: the Horner truncations, 0 <= p(r u) - h u <= 2.0219 u

    Per step the error is e_i = e_(i+1) r u + 2 at most: one floor and
    the rounding down of 1/i!.  2.0219 rmax + 2 <= 2.0219. *)

Definition horner_budget : R := 20219 / 10000.

(* Horner's rule on the reals, the same loop as [horner_from]. *)
Fixpoint hornerR (x a : R) (k : nat) : R :=
  match k with
  | O => a
  | S i => hornerR x (a * x + / INR (fact i)) i
  end.

Lemma hornerR_sum x a k :
  hornerR x a k = sumR (fun i => x ^ i / INR (fact i)) k + a * x ^ k.
Proof.
revert a; induction k as [|i IH]; intros a; [simpl; ring|].
cbn [hornerR sumR]; rewrite IH; simpl; unfold Rdiv; ring.
Qed.

Lemma horner_from_err r h a k : (0 <= r)%Z -> IZR r * u <= rmax ->
  (k <= DEG)%nat -> 0 <= a - IZR h * u <= horner_budget * u ->
  0 <= hornerR (IZR r * u) a k - IZR (horner_from r h k) * u
    <= horner_budget * u.
Proof.
intros Hr HR; revert a h; induction k as [|i IH]; intros a h Hk Ha;
  [exact Ha|].
cbn [hornerR horner_from]; apply IH; [lia|].
pose proof (mulshr_R h r) as Hm.
pose proof (Cv_R i ltac:(lia)) as Hc.
pose proof u_pos as Hu; pose proof rmax_ub as Hb.
apply IZR_le in Hr.
assert (H0 : 0 <= IZR r * u) by nra.
rewrite plus_IZR.
set (R := IZR r * u) in *; set (H := IZR h * u) in *.
assert (Hp : 0 <= (a - H) * R <= horner_budget * u * rmax_bound).
{ split; [apply Rmult_le_pos; lra|apply Rmult_le_compat; lra]. }
unfold horner_budget, rmax_bound in *; split; nra.
Qed.

Lemma horner_err r : (0 <= r)%Z -> IZR r * u <= rmax ->
  0 <= sumR (fun i => (IZR r * u) ^ i / INR (fact i)) (S DEG)
       - IZR (horner r) * u <= horner_budget * u.
Proof.
intros Hr HR.
replace (sumR _ (S DEG)) with (hornerR (IZR r * u) (/ INR (fact DEG)) DEG)
  by (rewrite hornerR_sum; cbn [sumR]; unfold Rdiv; ring).
apply horner_from_err; auto.
pose proof (Cv_R DEG (le_n _)); pose proof u_pos.
unfold horner_budget; lra.
Qed.

(** ** Line 3: the Taylor remainder, |exp(r u) - p(r u)| <= 1.6122 u *)

Lemma taylor_err R : 0 <= R <= rmax ->
  Rabs (exp R - sumR (fun i => R ^ i / INR (fact i)) (S DEG))
    <= taylor_budget * u.
Proof.
intros HR; eapply Rle_trans; [|apply (taylor_rem_le R HR)].
pose proof (taylor_exp 0 R (S DEG) (proj1 HR)) as Ht.
rewrite Rplus_0_l, exp_0 in Ht.
rewrite (sumR_ext _ (fun i => R ^ i / INR (fact i))) in Ht
  by (intros i; unfold Rdiv; ring).
eapply Rle_trans; [exact Ht|].
rewrite factN_INR; right; unfold Rdiv; ring.
Qed.

(** ** Line 4: the table, |T_j u - 2^(j/64)| <= u/2 *)

Lemma table_err j : (0 <= j < TAB)%Z ->
  Rabs (IZR (Tv j) * u - Rpower 2 (IZR j / IZR TAB)) <= / 2 * u.
Proof.
intros Hj; pose proof (T_ok j Hj) as Ht; rewrite <- TvE in Ht.
pose proof u_pos as Hu.
replace (IZR (Tv j) * u - Rpower 2 (IZR j / IZR TAB))
  with ((IZR (Tv j) - Rpower 2 (IZR j / IZR TAB) * IZR (2 ^ P)) * u)
  by (rewrite Rmult_minus_distr_r, Rmult_assoc, u_P; ring).
rewrite Rabs_mult, (Rabs_pos_eq u) by lra.
apply Rmult_le_compat_r; lra.
Qed.

(** ** The sum *)

(* exp is Lipschitz with constant exp M below M. *)
Lemma exp_diff a b M : a <= M -> b <= M ->
  Rabs (exp a - exp b) <= exp M * Rabs (a - b).
Proof.
assert (Hk : forall a b, a <= b -> b <= M ->
          exp b - exp a <= exp M * (b - a)).
{ intros a' b' Hab HbM.
  pose proof (exp_ineq1_le (a' - b')) as H1.
  replace (exp a') with (exp b' * exp (a' - b'))
    by (rewrite <- exp_plus; f_equal; ring).
  pose proof (exp_pos b'); pose proof (exp_mono _ _ HbM); nra. }
intros Ha Hb; destruct (Rle_or_lt a b) as [Hab|Hab].
- rewrite Rabs_left1, Rabs_left1 by (try pose proof (exp_mono _ _ Hab); lra).
  pose proof (Hk a b Hab Hb); lra.
- rewrite Rabs_pos_eq, Rabs_pos_eq
    by (try pose proof (exp_increasing _ _ Hab); lra).
  pose proof (Hk b a (Rlt_le _ _ Hab) Ha); lra.
Qed.

(* exp(r) <= exp_bound for r <= rmax + 2u, with room for the Taylor
   remainder. *)
Definition exp_bound : R := 102 / 100.

Lemma exp_rmax_ub :
  exp (rmax + red_budget * u) + taylor_budget * u <= exp_bound.
Proof.
unfold rmax, red_budget, taylor_budget, exp_bound, u, TAB.
vm_compute (2 ^ P)%Z; interval.
Qed.

(* tau = 2^(j/64), t = T_j u, h = H_0 u, p = p(r u), eR = exp(r u),
   eRs = exp(r* ), Y = y u. *)
Lemma budget_total tau t h p eR eRs Y :
  0 <= tau <= 2 -> Rabs (t - tau) <= / 2 * u ->
  0 <= h <= exp_bound -> 0 <= p - h <= horner_budget * u ->
  Rabs (eR - p) <= taylor_budget * u ->
  Rabs (eR - eRs) <= exp_bound * (red_budget * u) ->
  t * h - u < Y <= t * h ->
  Rabs (tau * eRs - Y) <= IZR D * u.
Proof.
intros Htau Ht Hh Hp HeR HeRs HY; pose proof u_pos as Hu.
assert (A1 : Rabs ((t - tau) * h) <= / 2 * u * exp_bound).
{ rewrite Rabs_mult, (Rabs_pos_eq h) by lra.
  apply Rmult_le_compat; try lra; apply Rabs_pos. }
assert (A2 : Rabs (tau * (h - p)) <= 2 * (horner_budget * u)).
{ rewrite Rabs_mult, (Rabs_pos_eq tau) by lra.
  apply Rmult_le_compat; try lra; [apply Rabs_pos|apply Rabs_le; lra]. }
assert (A3 : Rabs (tau * (p - eR)) <= 2 * (taylor_budget * u)).
{ rewrite Rabs_mult, (Rabs_pos_eq tau), Rabs_minus_sym by lra.
  apply Rmult_le_compat; try lra; apply Rabs_pos. }
assert (A4 : Rabs (tau * (eR - eRs)) <= 2 * (exp_bound * (red_budget * u))).
{ rewrite Rabs_mult, (Rabs_pos_eq tau) by lra.
  apply Rmult_le_compat; try lra; apply Rabs_pos. }
apply Rabs_le_inv in A1, A2, A3, A4; apply Rabs_le.
unfold D, horner_budget, taylor_budget, exp_bound, red_budget in *; lra.
Qed.

(* exp x = 2^(N/64) 2^((N mod 64)/64) exp(x - N ln2/64). *)
Lemma exp_split x N : exp x =
  exp (IZR (N / TAB) * ln 2) * Rpower 2 (IZR (N mod TAB) / IZR TAB)
  * exp (x - IZR N * (ln 2 / IZR TAB)).
Proof.
assert (HT : IZR TAB <> 0) by (apply not_0_IZR; unfold TAB; lia).
assert (HN : IZR N = IZR TAB * IZR (N / TAB) + IZR (N mod TAB)).
{ rewrite <- mult_IZR, <- plus_IZR; f_equal; apply Z.div_mod.
  unfold TAB; lia. }
unfold Rpower; rewrite <- !exp_plus; f_equal; rewrite HN; field; exact HT.
Qed.
