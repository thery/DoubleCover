(** * Pure lemmas for maybe_hard_bits and exp_encl_bits (no WP)

    exp_encl_bits packs the 6 limbs of y into 3 words,
    M[i] = y[2i] | (y[2i+1] << 32), and sets s = hN - 160; maybe_hard_bits
    passes y and hN to decide.  Both read core_Z through exp_core's spec. *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers.
Require Import BValues.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge Exp100Capla.Specs.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpTable ExpConsts ExpModel ExpModelBounds.
Require Import WP ZifyIntegers ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

(** ** The model *)

(* exp_encl_Z on a failure of core_Z. *)
Lemma encl_fail xb rc : ExpModel.core_Z xb = inl rc ->
  ExpModel.exp_encl_Z xb = inl rc.
Proof. by rewrite /ExpModel.exp_encl_Z => ->. Qed.

(* exp_encl_Z on a success of core_Z: s = hN - 160. *)
Lemma encl_ok xb y hN : ExpModel.core_Z xb = inr (y, hN) ->
  ExpModel.exp_encl_Z xb = inr (y, (hN - 160)%Z).
Proof. by rewrite /ExpModel.exp_encl_Z => ->. Qed.

(* maybe_hard_Z on a failure of core_Z. *)
Lemma hard_fail xb rc : ExpModel.core_Z xb = inl rc ->
  ExpModel.maybe_hard_Z xb = 1%Z.
Proof. by rewrite /ExpModel.maybe_hard_Z => ->. Qed.

(* maybe_hard_Z on a success of core_Z: the decision. *)
Lemma hard_ok xb y hN : ExpModel.core_Z xb = inr (y, hN) ->
  ExpModel.maybe_hard_Z xb = ExpModel.decide_Z y hN.
Proof. by rewrite /ExpModel.maybe_hard_Z => ->. Qed.

(* A failure code of core_Z is 1, 2 or 3. *)
Lemma core_rc_range xb rc : ExpModel.core_Z xb = inl rc -> (1 <= rc <= 3)%Z.
Proof. exact: ExpModelBounds.core_Z_rc. Qed.

(** ** s = hN - 160 *)

Section Words.
Transparent Int64.repr Int64.unsigned Int64.signed Int64.sub Int.repr
  Int.unsigned Int.modu.

(* hN - 160 does not wrap, for |hN| <= 2^12. *)
Lemma signed_sub160 hN :
  (- 2 ^ ExpModelBounds.hN_bits <= Int64.signed hN <= 2 ^ ExpModelBounds.hN_bits)%Z ->
  Int64.signed (Int64.sub hN (Int64.repr 160)) = (Int64.signed hN - 160)%Z.
Proof.
  rewrite /ExpModelBounds.hN_bits => H.
  rewrite Int64.sub_signed.
  change (Int64.signed (Int64.repr 160)) with 160%Z.
  rewrite Int64.signed_repr //.
  change Int64.min_signed with (-9223372036854775808)%Z.
  change Int64.max_signed with 9223372036854775807%Z; lia.
Qed.

(** ** M[i] = y[2i] | (y[2i+1] << 32) *)

(* Two limbs in one word. *)
Lemma or_shl32 a b : (Int64.unsigned a < 2 ^ 32)%Z -> (Int64.unsigned b < 2 ^ 32)%Z ->
  Int64.unsigned (Int64.or a (Int64.shl' b (Int.modu (Int.repr 32) Int64.iwordsize'))) =
  (Int64.unsigned a + 2 ^ 32 * Int64.unsigned b)%Z.
Proof.
  move=> Ha Hb.
  have Ra := Int64.unsigned_range a; have Rb := Int64.unsigned_range b.
  have E32 : Int.unsigned (Int.modu (Int.repr 32) Int64.iwordsize') = 32%Z by [].
  rewrite /Int64.or /Int64.shl' E32 Z.shiftl_mul_pow2 //.
  rewrite (Int64.unsigned_repr (Int64.unsigned b * 2 ^ 32)); first
    by change Int64.max_unsigned with 18446744073709551615%Z; lia.
  have -> : Z.lor (Int64.unsigned a) (Int64.unsigned b * 2 ^ 32) =
            (Int64.unsigned a + Int64.unsigned b * 2 ^ 32)%Z.
  { have Hl : Z.land (Int64.unsigned a) (Int64.unsigned b * 2 ^ 32) = 0%Z.
    { apply: Z.bits_inj' => k Hk.
      rewrite Z.land_spec Z.bits_0.
      case: (Z.lt_ge_cases k 32) => Hk32.
      - by rewrite Z.mul_pow2_bits_low // Bool.andb_false_r.
      - rewrite -(Z.mod_small (Int64.unsigned a) (2 ^ 32)); first lia.
        by rewrite Z.mod_pow2_bits_high //; lia. }
    by rewrite -Z.lxor_lor // -Z.add_nocarry_lxor. }
  rewrite Int64.unsigned_repr; first
    by change Int64.max_unsigned with 18446744073709551615%Z; lia.
  lia.
Qed.

End Words.

(* The 3 words written by the packing loop hold the number y. *)
Lemma pack_value (ms ys : list int64) :
  length ms = 3%nat -> length ys = 6%nat ->
  (forall i, (i < 3)%coq_nat ->
     Int64.unsigned (List.nth i ms Int64.zero) =
     (Int64.unsigned (List.nth (2 * i) ys Int64.zero) +
      2 ^ 32 * Int64.unsigned (List.nth (2 * i + 1) ys Int64.zero))%Z) ->
  valW (map Int64.unsigned ms) = val32 ys.
Proof.
  move=> Hm Hy H.
  have H0 : Int64.unsigned (List.nth 0 ms Int64.zero) =
    (Int64.unsigned (List.nth 0 ys Int64.zero) +
     2 ^ 32 * Int64.unsigned (List.nth 1 ys Int64.zero))%Z := H 0%nat ltac:(lia).
  have H1 : Int64.unsigned (List.nth 1 ms Int64.zero) =
    (Int64.unsigned (List.nth 2 ys Int64.zero) +
     2 ^ 32 * Int64.unsigned (List.nth 3 ys Int64.zero))%Z := H 1%nat ltac:(lia).
  have H2 : Int64.unsigned (List.nth 2 ms Int64.zero) =
    (Int64.unsigned (List.nth 4 ys Int64.zero) +
     2 ^ 32 * Int64.unsigned (List.nth 5 ys Int64.zero))%Z := H 2%nat ltac:(lia).
  clear H.
  case: ms Hm H0 H1 H2 => [|m0 [|m1 [|m2 [|? ?]]]] Hm H0 H1 H2;
    try discriminate Hm.
  case: ys Hy H0 H1 H2 => [|y0 [|y1 [|y2 [|y3 [|y4 [|y5 [|? ?]]]]]]] Hy H0 H1 H2;
    try discriminate Hy.
  move: H0 H1 H2; cbn [List.nth map valW val32] => H0 H1 H2.
  rewrite H0 H1 H2 /word_bits.
  change (2 ^ 64)%Z with (2 ^ 32 * 2 ^ 32)%Z; ring.
Qed.

(** ** The scratch arrays *)

(* An array of 6 words, as exp_core leaves its scratch arrays. *)
Lemma arr6_inv v : arr6 v ->
  exists l, v = Some (Varr (map Vint64 l)) /\ length l = 6%nat.
Proof. by []. Qed.
