(** * Pure lemmas for mul_ln2 and guess_n (no WP)

    mul_ln2 copies p[1..6] of p = n LN2 (7 limbs) into q; guess_n reads
    bits 185 .. 223 of p = X INV from limbs 5 and 6 of p. *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge Exp100Capla.Specs.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpTable ExpConsts ExpModel.
Require Import WP ZifyIntegers ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(** ** The constant INV *)

(* The word 3098164009 of guess_n is INV, a limb. *)
Lemma INV_word : Int64.unsigned (Int64.repr 3098164009) = ExpTable.INV /\
  (ExpTable.INV < 2 ^ limb_bits)%Z.
Proof. by split; [|rewrite /ExpTable.INV /limb_bits; lia]. Qed.

(** ** mul_ln2: dropping the low limb *)

(* Dropping the low limb divides by 2^32. *)
Lemma val32_drop1 p : limbs p -> val32 (skipn 1 p) = (val32 p / 2 ^ 32)%Z.
Proof.
  case: p => [|x t] Hp; first by [].
  have Hx := Hp 0%nat; cbn [List.nth] in Hx.
  have := Int64.unsigned_range x => Hr.
  cbn [skipn val32].
  rewrite Z.add_comm Z.mul_comm Z.div_add_l; first lia.
  rewrite Z.div_small; lia.
Qed.

(* The limbs after the first are limbs. *)
Lemma limbs_skipn1 p : limbs p -> limbs (skipn 1 p).
Proof.
  case: p => [|x t] Hp q; first by cbn [skipn]; exact: Hp.
  exact: (Hp (S q)).
Qed.

(* The copy loop q[i] = p[i + 1], i < 6, gives q = p[1..6]. *)
Lemma copy_shift (qs ps : list int64) :
  length qs = 6%nat -> length ps = 7%nat ->
  (forall j, (j < 6)%coq_nat ->
     List.nth j qs Int64.zero = List.nth (S j) ps Int64.zero) ->
  qs = skipn 1 ps.
Proof.
  move=> Hq Hp H.
  apply: (List.nth_ext _ _ Int64.zero Int64.zero).
  - rewrite length_skipn; lia.
  - move=> j Hj; rewrite List.nth_skipn; apply: H; lia.
Qed.

(* q = floor(n LN2 / 2^32) from p = LN2 n. *)
Lemma mul_ln2_value (ps : list int64) (n : int64) :
  limbs ps -> val32 ps = (val32 LN2w * Int64.unsigned n)%Z ->
  val32 (skipn 1 ps) = ExpModel.q (Int64.unsigned n).
Proof.
  move=> Lp Hv.
  have [_ [_ HL]] := LN2w_num.
  rewrite val32_drop1 // Hv HL ExpModel.qE ExpModel.LN2vE.
  by rewrite Z.mul_comm.
Qed.

(** ** guess_n: bits 185 .. 223 *)

(* Two pieces without common bits: their or is their sum. *)
Lemma lor7 a b : (0 <= a < 2 ^ 7)%Z ->
  Z.lor a (b * 2 ^ 7) = (a + b * 2 ^ 7)%Z.
Proof.
  move=> Ha.
  have Hl : Z.land a (b * 2 ^ 7) = 0%Z.
  { apply: Z.bits_inj' => k Hk.
    rewrite Z.land_spec Z.bits_0.
    case: (Z.lt_ge_cases k 7) => Hk7.
    - by rewrite Z.mul_pow2_bits_low // Bool.andb_false_r.
    - rewrite -(Z.mod_small a (2 ^ 7)) //.
      by rewrite Z.mod_pow2_bits_high //; lia. }
  by rewrite -Z.lxor_lor // -Z.add_nocarry_lxor.
Qed.

Section Words.
Transparent Int64.repr Int64.unsigned Int.repr Int.unsigned Int.modu.

(* (p[5] >> 25) | (p[6] << 7) for a number p of 7 limbs. *)
Lemma bits185w (ps : list int64) : length ps = 7%nat -> limbs ps ->
  Int64.or (Int64.shru' (List.nth 5 ps Int64.zero)
              (Int.modu (Int.repr 25) Int64.iwordsize'))
           (Int64.shl' (List.nth 6 ps Int64.zero)
              (Int.modu (Int.repr 7) Int64.iwordsize')) =
  Int64.repr (val32 ps / 2 ^ 185).
Proof.
  case: ps => [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|? ?]]]]]]]] Hl Lp;
    try discriminate Hl.
  move: (Lp 0%nat) (Lp 1%nat) (Lp 2%nat) (Lp 3%nat) (Lp 4%nat) (Lp 5%nat)
    (Lp 6%nat); cbn [List.nth] => L0 L1 L2 L3 L4 L5 L6.
  have R0 := Int64.unsigned_range a0; have R1 := Int64.unsigned_range a1;
  have R2 := Int64.unsigned_range a2; have R3 := Int64.unsigned_range a3;
  have R4 := Int64.unsigned_range a4; have R5 := Int64.unsigned_range a5;
  have R6 := Int64.unsigned_range a6.
  have E25 : Int.unsigned (Int.modu (Int.repr 25) Int64.iwordsize') = 25%Z by [].
  have E7 : Int.unsigned (Int.modu (Int.repr 7) Int64.iwordsize') = 7%Z by [].
  rewrite /Int64.or /Int64.shru' /Int64.shl' E25 E7.
  rewrite Z.shiftr_div_pow2 // Z.shiftl_mul_pow2 //.
  have Hd := Z.div_mod (Int64.unsigned a5) (2 ^ 25) ltac:(lia).
  have Hm := Z.mod_pos_bound (Int64.unsigned a5) (2 ^ 25) ltac:(lia).
  have Hq : (0 <= Int64.unsigned a5 / 2 ^ 25 < 2 ^ 7)%Z.
  { split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; lia. }
  rewrite (Int64.unsigned_repr (Int64.unsigned a5 / 2 ^ 25)); first
    by change Int64.max_unsigned with 18446744073709551615%Z; lia.
  rewrite (Int64.unsigned_repr (Int64.unsigned a6 * 2 ^ 7)); first
    by change Int64.max_unsigned with 18446744073709551615%Z; lia.
  rewrite lor7 //.
  congr Int64.repr.
  cbn [val32].
  set q := (Int64.unsigned a5 / 2 ^ 25)%Z in Hd Hq *.
  set r := (Int64.unsigned a5 mod 2 ^ 25)%Z in Hd Hm *.
  apply: (Z.div_unique _ _ _
    (Int64.unsigned a0 + 2 ^ 32 * (Int64.unsigned a1 + 2 ^ 32 *
      (Int64.unsigned a2 + 2 ^ 32 * (Int64.unsigned a3 + 2 ^ 32 *
        (Int64.unsigned a4 + 2 ^ 32 * r)))))).
  - left; lia.
  - rewrite {1}Hd; ring.
Qed.

End Words.

(* The guess from p = X INV. *)
Lemma guess_value (ps xs : list int64) :
  val32 ps = (val32 xs * ExpTable.INV)%Z ->
  ExpModel.guess (val32 xs) = (val32 ps / 2 ^ 185)%Z.
Proof. by move=> Hv; rewrite ExpModel.guessE Hv. Qed.
