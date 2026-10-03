(** * S1: the real x of the bits xb

    [xreal xb] is the double whose bits are [xb] (Flocq's [b64_of_bits]).
    For a finite x with |x| < 1024 ([xbexp xb < be_big]), [is_x xb x]:
    the sign bit gives the sign of x and [xfix xb] = floor(|x| 2^P). *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Exp100 Require Import ExpConsts ExpModel.

Open Scope R_scope.

(** The double of the bits [xb]. *)
Definition xreal (xb : Z) : R := @B2R 53 1024 (b64_of_bits xb).

(** What the model reads of x: the sign, then floor(|x| 2^P). *)
Definition is_x (xb : Z) (x : R) : Prop :=
  (xsign xb = 0%Z -> 0 <= x) /\ (xsign xb <> 0%Z -> x <= 0) /\
  IZR (xfix xb) <= Rabs x * bpow radix2 P < IZR (xfix xb) + 1.

(** [scale v e] = floor(v 2^e), for any e. *)
Lemma scale_floor v e :
  IZR (scale v e) <= IZR v * bpow radix2 e < IZR (scale v e) + 1.
Proof.
rewrite scaleE; destruct (Z.leb_spec 0 e) as [He|He].
- rewrite mult_IZR, <- (IZR_Zpower radix2) by exact He; simpl; lra.
- assert (H2 : (2 ^ (- e) <> 0)%Z) by (apply Z.pow_nonzero; lia).
  replace (IZR v * bpow radix2 e) with (IZR v / IZR (2 ^ (- e))).
  + rewrite <- (Zfloor_div v _ H2); split; [apply Zfloor_lb|apply Zfloor_ub].
  + rewrite (IZR_Zpower radix2) by lia; rewrite bpow_opp; unfold Rdiv.
    rewrite Rinv_inv; reflexivity.
Qed.

Theorem xreal_is_x xb : (0 <= xb < 2 ^ 64)%Z -> (xbexp xb < be_big)%Z ->
  is_x xb (xreal xb).
Proof.
intros Hxb Hbe.
unfold xreal, b64_of_bits, binary_float_of_bits; rewrite B2R_FF2B.
unfold binary_float_of_bits_aux, split_bits, is_x, xfix, xexpo, xmant.
rewrite xsignE, xbexpE in *; rewrite xmant0E, pow2E by discriminate.
(* Flocq's field widths are ours *)
change (2 ^ 52)%Z with (2 ^ mant_bits)%Z.
change (2 ^ 11)%Z with (2 ^ expo_bits)%Z.
(* Flocq's sign test is the sign bit *)
assert (Hs : (2 ^ mant_bits * 2 ^ expo_bits <=? xb)%Z =
             negb (xb / 2 ^ sign_bit =? 0)%Z).
{ change (2 ^ mant_bits * 2 ^ expo_bits)%Z with (2 ^ sign_bit)%Z.
  destruct (Z.leb_spec (2 ^ sign_bit) xb) as [H1|H1].
  - assert (1 <= xb / 2 ^ sign_bit)%Z
      by (apply Z.div_le_lower_bound; [reflexivity|lia]).
    destruct (Z.eqb_spec (xb / 2 ^ sign_bit) 0); lia || reflexivity.
  - rewrite Z.div_small by lia; reflexivity. }
rewrite Hs; clear Hs.
set (sg := (xb / 2 ^ sign_bit =? 0)%Z).
(* Flocq's smallest exponent *)
change (SpecFloat.emin (52 + 1) (2 ^ (11 - 1))) with (1 - expo_shift)%Z.
assert (Hm : (0 <= xb mod 2 ^ mant_bits < 2 ^ mant_bits)%Z)
  by (apply Z.mod_pos_bound; reflexivity).
assert (He : (0 <= (xb / 2 ^ mant_bits) mod 2 ^ expo_bits < 2 ^ expo_bits)%Z)
  by (apply Z.mod_pos_bound; reflexivity).
set (m := (xb mod 2 ^ mant_bits)%Z) in *.
set (be := ((xb / 2 ^ mant_bits) mod 2 ^ expo_bits)%Z) in *.
clearbody m be.
set (v := if (be =? 0)%Z then m else (m + 2 ^ mant_bits)%Z).
set (e := ((if (be =? 0)%Z then 1%Z else be) - expo_shift)%Z).
match goal with |- context [FF2R radix2 ?f] => set (x := FF2R radix2 f) end.
assert (Hv : (0 <= v)%Z) by (unfold v; destruct (be =? 0)%Z; lia).
(* x = +- v 2^e, zero and subnormal included *)
assert (Hx : x = if sg then IZR v * bpow radix2 e
                 else - (IZR v * bpow radix2 e)).
{ unfold x, v, e; destruct (Z.eqb_spec be 0) as [Hb|Hb].
  - destruct m as [|p|p]; [| |lia]; destruct sg;
      cbn [FF2R negb cond_Zopp]; unfold F2R; cbn [Fnum Fexp];
      rewrite ?opp_IZR; ring.
  - (* not infinity nor NaN *)
    assert (Hb2 : (be =? 2 ^ expo_bits - 1)%Z = false).
    { assert (be_big < 2 ^ expo_bits - 1)%Z by reflexivity.
      apply Z.eqb_neq; lia. }
    rewrite Hb2.
    replace (be + (1 - expo_shift) - 1)%Z with (be - expo_shift)%Z by ring.
    assert (Hp : (0 < m + 2 ^ mant_bits)%Z).
    { assert (0 < 2 ^ mant_bits)%Z by reflexivity; lia. }
    destruct (m + 2 ^ mant_bits)%Z as [|p|p]; try lia.
    destruct sg; cbn [FF2R negb cond_Zopp]; unfold F2R; cbn [Fnum Fexp];
      rewrite ?opp_IZR; ring. }
clearbody x; subst x.
assert (Hr : 0 <= IZR v * bpow radix2 e)
  by (apply Rmult_le_pos; [apply IZR_le, Hv|apply bpow_ge_0]).
assert (Ha : Rabs (if sg then IZR v * bpow radix2 e
                   else - (IZR v * bpow radix2 e)) * bpow radix2 P =
             IZR v * bpow radix2 (e + P)).
{ rewrite bpow_plus; destruct sg;
    rewrite ?Rabs_Ropp, Rabs_pos_eq by exact Hr; ring. }
rewrite Ha; split; [|split; [|apply scale_floor]];
  unfold sg; destruct (Z.eqb_spec (xb / 2 ^ sign_bit) 0); intros H;
  try lra; contradiction.
Qed.
