(** * The constants of exp100, certified

    Step 3 of the proof plan of ../README.  The constants are the lists of
    ExpTable.v, copied from exp100_table.h.  A number is a list of limbs
    of 32 bits, the least significant first, standing for [valZ] (the
    shape of [valZ] in code/APaul/vst/Words.v, with limbs of 32 bits).

    - [T_ok]: [T_j] is within 1/2 of 2^(j/64) 2^160, by exact integer
      computation: (2 T_j - 1)^64 <= 2^64 2^j 2^(64 160) <= (2 T_j + 1)^64.
    - [C_ok]: [C_i] is 2^160 / i! rounded down, by computation.
    - [LN2_ok]: [LN2] is within 1/2 of ln2/64 2^192, by Interval.
    - [RMAX_ok]: [RMAX] is ceil(ln2/64 2^160) + 3, by Interval.
    - [rmax_ub], [taylor_rem_le]: the bound rmax on r and the Taylor
      remainder line of the error budget, by Interval.
    [INV] needs nothing: exp100.c checks the n it guesses. *)

From Stdlib Require Import Bool ZArith Reals Lia Lra List.
From Bignums Require Import BigZ.
From Interval Require Import Tactic.
From Exp100 Require Import ExpTable.
Import ListNotations.

Open Scope Z_scope.

(** ** Parameters, as in exp100.h *)

Definition limb_bits : Z := 32.  (* bits of a limb          *)
Definition NL : nat := 6.        (* limbs of a number       *)
Definition P : Z := 160.         (* bits after the point    *)
Definition TAB : Z := 64.        (* entries of the table T  *)
Definition DEG : nat := 16.      (* degree of the Taylor polynomial *)

(** ** Numbers *)

(** A limb: an integer in [0, 2^32). *)
Definition limb (x : Z) : Prop := 0 <= x < 2 ^ limb_bits.

(** The number a list of limbs stands for, least significant limb first. *)
Fixpoint valZ (ws : list Z) : Z :=
  match ws with
  | [] => 0
  | w :: r => w + 2 ^ limb_bits * valZ r
  end.

(** A number of exp100.c: [NL] limbs. *)
Definition num (ws : list Z) : Prop := length ws = NL /\ Forall limb ws.

Definition limbb (x : Z) : bool := (0 <=? x) && (x <? 2 ^ limb_bits).

Definition numb (ws : list Z) : bool :=
  Nat.eqb (length ws) NL && forallb limbb ws.

Lemma limbP x : limbb x = true -> limb x.
Proof. now unfold limbb, limb; rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. Qed.

Lemma numP ws : numb ws = true -> num ws.
Proof.
unfold numb, num; rewrite andb_true_iff, Nat.eqb_eq, forallb_forall.
intros [Hl Hw]; split; [exact Hl|].
apply Forall_forall; intros x Hx; apply limbP, Hw, Hx.
Qed.

(** i!, in integers (never in unary). *)
Fixpoint factN (n : nat) : Z :=
  match n with
  | O => 1
  | S m => Z.of_nat n * factN m
  end.

Lemma factN_INR n : IZR (factN n) = INR (fact n).
Proof.
induction n as [|n IH]; [reflexivity|].
cbn [factN fact]; rewrite mult_IZR, IH, mult_INR, <- INR_IZR_INZ; reflexivity.
Qed.

Lemma factN_gt0 n : 0 < factN n.
Proof. induction n as [|n IH]; cbn [factN]; lia. Qed.

(** ** The shape of the tables *)

Lemma length_T : length T = Z.to_nat TAB.
Proof. reflexivity. Qed.

Lemma length_C : length C = S DEG.
Proof. reflexivity. Qed.

Lemma num_T : Forall num T.
Proof.
apply Forall_forall; intros w Hw.
apply numP; revert w Hw; apply forallb_forall; vm_compute; reflexivity.
Qed.

Lemma num_C : Forall num C.
Proof.
apply Forall_forall; intros w Hw.
apply numP; revert w Hw; apply forallb_forall; vm_compute; reflexivity.
Qed.

Lemma num_LN2 : num LN2.
Proof. apply numP; vm_compute; reflexivity. Qed.

Lemma num_RMAX : num RMAX.
Proof. apply numP; vm_compute; reflexivity. Qed.

Lemma limb_INV : limb INV.
Proof. apply limbP; vm_compute; reflexivity. Qed.

(** ** C: 2^160 / i!, rounded down *)

Theorem C_ok i : (i <= DEG)%nat -> valZ (nth i C []) = 2 ^ P / factN i.
Proof.
intros Hi.
assert (H : forallb (fun i => valZ (nth i C []) =? 2 ^ P / factN i)
              (seq 0 (S DEG)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H; apply Z.eqb_eq, H, in_seq; lia.
Qed.

(** The same in the reals: [C_i] is at most 1 below 2^160 / i!. *)
Lemma C_floor i : (i <= DEG)%nat ->
  (IZR (valZ (nth i C [])) <= IZR (2 ^ P) / INR (fact i)
     < IZR (valZ (nth i C [])) + 1)%R.
Proof.
intros Hi; rewrite C_ok by exact Hi; rewrite <- factN_INR.
assert (Hf := factN_gt0 i).
assert (Hf' : (0 < IZR (factN i))%R) by (apply IZR_lt; exact Hf).
assert (Hd := Z.div_mod (2 ^ P) (factN i) ltac:(lia)).
assert (Hm := Z.mod_pos_bound (2 ^ P) (factN i) Hf).
set (q := 2 ^ P / factN i) in *; set (m := 2 ^ P mod factN i) in *.
rewrite Hd, plus_IZR, mult_IZR.
destruct Hm as [Hm0 Hm1]; apply IZR_le in Hm0; apply IZR_lt in Hm1.
split.
- apply (Rmult_le_reg_r (IZR (factN i))); [exact Hf'|].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; nra.
- apply (Rmult_lt_reg_r (IZR (factN i))); [exact Hf'|].
  unfold Rdiv; rewrite Rmult_assoc, Rinv_l by lra; nra.
Qed.

(** ** T: 2^(j/64) 2^160, to nearest

    [T_j] is within 1/2 of [a = 2^(j/64) 2^160] iff (2 T_j - 1) <= 2 a <=
    (2 T_j + 1); [a] and [2 T_j - 1] are positive, so this is the same on
    the 64th powers, where [(2 a)^64 = 2^(64 + j + 64 160)] is an
    integer. *)

Definition T_okZ (t j : Z) : bool :=
  (0 <=? 2 * t - 1) &&
  ((2 * t - 1) ^ TAB <=? 2 ^ (TAB + j + P * TAB)) &&
  (2 ^ (TAB + j + P * TAB) <=? (2 * t + 1) ^ TAB).

(** The same test computed with [BigZ]: in [Z] (bits in a list) the
    powers, of 10000 bits, take minutes. *)
Definition T_okb (t j : Z) : bool :=
  let b := BigZ.of_Z in
  let e := BigZ.pow (b 2) (b (TAB + j + P * TAB)) in
  (0 <=? 2 * t - 1) &&
  BigZ.leb (BigZ.pow (b (2 * t - 1)) (b TAB)) e &&
  BigZ.leb e (BigZ.pow (b (2 * t + 1)) (b TAB)).

Lemma T_okbE t j : T_okb t j = T_okZ t j.
Proof.
unfold T_okb, T_okZ.
now rewrite !BigZ.spec_leb, !BigZ.spec_pow, !BigZ.spec_of_Z.
Qed.

Open Scope R_scope.

(* Below 0 <= a, powers are strictly increasing. *)
Lemma pow_lt_compat a b n : 0 <= a < b -> (0 < n)%nat -> a ^ n < b ^ n.
Proof.
intros Hab Hn; induction n as [|n IH]; [lia|].
destruct n as [|n]; [simpl; lra|].
assert (0 <= a ^ S n) by (apply pow_le; lra).
assert (a ^ S n < b ^ S n) by (apply IH; lia).
change (a * a ^ S n < b * b ^ S n); nra.
Qed.

(* So the order of two nonnegative numbers is that of their powers. *)
Lemma pow_le_inv a b n :
  0 <= a -> 0 <= b -> (0 < n)%nat -> a ^ n <= b ^ n -> a <= b.
Proof.
intros Ha Hb Hn Hp; destruct (Rle_or_lt a b) as [|Hlt]; [easy|].
assert (b ^ n < a ^ n) by (apply pow_lt_compat; lra || lia); lra.
Qed.

(* 2^(j/64) to the 64th, j >= 0. *)
Lemma Rpower_TAB j : (0 <= j)%Z ->
  Rpower 2 (IZR j / IZR TAB) ^ Z.to_nat TAB = IZR (2 ^ j).
Proof.
intros Hj.
rewrite <- Rpower_pow by (apply exp_pos).
rewrite Rpower_mult, INR_IZR_INZ, Z2Nat.id by (unfold TAB; lia).
replace (IZR j / IZR TAB * IZR TAB) with (IZR j)
  by (field; unfold TAB; apply not_0_IZR; lia).
rewrite <- (Z2Nat.id j Hj) at 1 2; rewrite <- INR_IZR_INZ.
rewrite Rpower_pow, pow_IZR by lra; reflexivity.
Qed.

Lemma T_okbP t j : (0 <= j)%Z -> T_okb t j = true ->
  Rabs (IZR t - Rpower 2 (IZR j / IZR TAB) * IZR (2 ^ P)) <= / 2.
Proof.
intros Hj; rewrite T_okbE; unfold T_okZ.
rewrite !andb_true_iff, !Z.leb_le.
intros [[H0 Hlo] Hhi].
set (n := Z.to_nat TAB).
assert (Hn : (0 < n)%nat) by (unfold n, TAB; simpl; lia).
assert (HnZ : Z.of_nat n = TAB) by (unfold n, TAB; reflexivity).
set (x := 2 * (Rpower 2 (IZR j / IZR TAB) * IZR (2 ^ P))).
assert (Hx : 0 < x).
{ unfold x; assert (0 < Rpower 2 (IZR j / IZR TAB)) by apply exp_pos.
  assert (0 < IZR (2 ^ P)) by (apply IZR_lt; unfold P; lia); nra. }
(* x^64 is the integer 2^(64 + j + 64 160). *)
assert (Hxn : x ^ n = IZR (2 ^ (TAB + j + P * TAB))).
{ unfold x; rewrite !Rpow_mult_distr, Rpower_TAB by exact Hj.
  rewrite !pow_IZR, HnZ, <- !mult_IZR; f_equal.
  rewrite <- Z.pow_mul_r, <- !Z.pow_add_r; try (unfold P, TAB; lia).
  f_equal; lia. }
apply IZR_le in Hlo, Hhi, H0.
rewrite <- Hxn in Hlo, Hhi; rewrite <- HnZ, <- pow_IZR in Hlo, Hhi.
apply pow_le_inv in Hlo; try lra; try lia.
apply pow_le_inv in Hhi; try lra; try lia.
2: rewrite plus_IZR, minus_IZR in *; lra.
rewrite minus_IZR, mult_IZR in Hlo; rewrite plus_IZR, mult_IZR in Hhi.
unfold x in Hlo, Hhi; apply Rabs_le; lra.
Qed.

Theorem T_ok j : (0 <= j < TAB)%Z ->
  Rabs (IZR (valZ (nth (Z.to_nat j) T []))
        - Rpower 2 (IZR j / IZR TAB) * IZR (2 ^ P)) <= / 2.
Proof.
intros Hj; apply T_okbP; [lia|].
assert (H : forallb (fun i => T_okb (valZ (nth i T [])) (Z.of_nat i))
              (seq 0 (Z.to_nat TAB)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H.
rewrite <- (Z2Nat.id j) at 2 by lia.
apply H, in_seq; lia.
Qed.

(** ** LN2 and RMAX: ln2/64 at 2^192 and 2^160 *)

Ltac val_lit c :=
  let v := eval vm_compute in (valZ c) in change (valZ c) with v.

Theorem LN2_ok :
  Rabs (IZR (valZ LN2) - ln 2 / IZR TAB * IZR (2 ^ (P + limb_bits))) <= / 2.
Proof.
val_lit LN2; vm_compute (2 ^ (P + limb_bits))%Z; unfold TAB.
interval with (i_prec 300).
Qed.

(** [RMAX = ceil(ln2/64 2^160) + 3]. *)
Theorem RMAX_ok :
  IZR (valZ RMAX) - 4 < ln 2 / IZR TAB * IZR (2 ^ P) <= IZR (valZ RMAX) - 3.
Proof.
val_lit RMAX; vm_compute (2 ^ P)%Z; unfold TAB.
split; interval with (i_prec 300).
Qed.

Corollary RMAX_ge : ln 2 / IZR TAB * IZR (2 ^ P) + 3 <= IZR (valZ RMAX).
Proof. generalize RMAX_ok; lra. Qed.

(** The bound on the reduced argument r of the budget, ln2/64 + 3 u. *)
Definition u : R := / IZR (2 ^ P).
Definition rmax : R := ln 2 / IZR TAB + 3 * u.

(** exp100.c checks r < RMAX, so r u <= rmax. *)
Lemma ltZ_rmax (r : Z) : (r < valZ RMAX)%Z -> IZR r * u <= rmax.
Proof.
intros Hr; apply Zlt_le_succ, IZR_le in Hr; rewrite succ_IZR in Hr.
generalize RMAX_ok; unfold rmax, u; intros [H _].
assert (Hp : 0 < IZR (2 ^ P)) by (apply IZR_lt; unfold P; lia).
assert (Hp' : 0 < / IZR (2 ^ P)) by (apply Rinv_0_lt_compat, Hp).
assert (HT : IZR TAB <> 0) by (apply not_0_IZR; unfold TAB; lia).
replace (ln 2 / IZR TAB + 3 * / IZR (2 ^ P))
  with ((ln 2 / IZR TAB * IZR (2 ^ P) + 3) * / IZR (2 ^ P))
  by (field; lra).
apply Rmult_le_compat_r; lra.
Qed.

(** The budget prints rmax = 0.010830 (to nearest); an upper bound is
    0.010831. *)
Definition rmax_bound : R := 10831 / 1000000.

Lemma rmax_ub : rmax <= rmax_bound.
Proof.
unfold rmax, rmax_bound, u, TAB; vm_compute (2 ^ P)%Z; interval.
Qed.

(** ** The Taylor remainder line of the budget

    rmax^17/17! e^rmax <= 1.6122 u, and the same for every r in
    [0, rmax]. *)

Definition taylor_budget : R := 16122 / 10000.

Theorem taylor_rem_le r : 0 <= r <= rmax ->
  r ^ S DEG / IZR (factN (S DEG)) * exp r <= taylor_budget * u.
Proof.
intros Hr; unfold rmax, u, TAB in Hr; unfold taylor_budget, u, DEG.
vm_compute (factN 17); vm_compute (2 ^ P)%Z in Hr |- *.
interval with (i_prec 80).
Qed.
