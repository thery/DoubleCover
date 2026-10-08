(** * The doubles of a line and their bits; the two notions of hard

    A line of the table has [x0 = S0 2^(ex - 52)] with
    [2^52 <= |S0| < 2^53] (ExpParse / line_ok of code/exptablekl); its
    inputs are [x0 + j u = (S0 + j) 2^(ex - 52)].  When [x0] is a normal
    double ([-1022 <= ex <= 1023]), the bits of [S 2^(ex - 52)] are
    [enc S ex]: the sign bit, the biased exponent [ex + 1023], the 52 low
    bits of [|S|].  Along a line the sign and [ex] do not change
    (condition 1 of line_ok), so the bits of [x0 + j u] are
    [enc S0 ex + j] ([x0 > 0]) or [enc S0 ex - j] ([x0 < 0]).

    [hard] of the table (m = 43, ExpTableKL.ExpHard) and [hard] of exp100
    (m_hard = 42, Exp100.ExpHard) have the same shape and the same [v]
    (half an ulp of [exp x]): the first implies the second. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
Require Exp100.ExpModel Exp100.ExpBits Exp100.ExpHard.
Require ExpTableKL.ExpCheck ExpTableKL.ExpHard.

Local Notation line_ok := ExpTableKL.ExpCheck.line_ok.
Local Notation bp := ExpTableKL.ExpCheck.bp.
Local Notation uexp := ExpTableKL.ExpCheck.uexp.
Local Notation xreal := Exp100.ExpBits.xreal.

Open Scope Z_scope.

(** ** The bits of a normal double *)

(** The bits of [S 2^(ex - 52)], for [2^52 <= |S| < 2^53] and
    [-1022 <= ex <= 1023]. *)
Definition enc (S ex : Z) : Z :=
  (if S <? 0 then 2 ^ 63 else 0) + (ex + 1022) * 2 ^ 52 + Z.abs S.

Lemma enc_join S ex : 2 ^ 52 <= Z.abs S < 2 ^ 53 ->
  enc S ex = join_bits 52 11 (S <? 0) (Z.abs S - 2 ^ 52) (ex + 1023).
Proof.
  intros HS; unfold enc, join_bits.
  rewrite !Z.shiftl_mul_pow2 by lia.
  destruct (S <? 0); cbn [Z.pow Z.pow_pos Pos.iter Z.mul]; lia.
Qed.

Theorem xreal_enc S ex : 2 ^ 52 <= Z.abs S < 2 ^ 53 -> -1022 <= ex <= 1023 ->
  Exp100.ExpBits.xreal (enc S ex) = (IZR S * bpow radix2 (ex - 52))%R.
Proof.
  intros HS He.
  unfold Exp100.ExpBits.xreal, b64_of_bits, binary_float_of_bits.
  rewrite B2R_FF2B; unfold binary_float_of_bits_aux.
  rewrite enc_join, split_join_bits by (try split; cbn; lia).
  assert (Hz : Zeq_bool (ex + 1023) 0 = false)
    by (apply Zeq_bool_false; lia).
  assert (Hi : Zeq_bool (ex + 1023) (2 ^ 11 - 1) = false)
    by (apply Zeq_bool_false; cbn; lia).
  rewrite Hz, Hi.
  replace (Z.abs S - 2 ^ 52 + 2 ^ 52) with (Z.abs S) by ring.
  change (SpecFloat.emin (52 + 1) (2 ^ (11 - 1))) with (-1074).
  replace (ex + 1023 + -1074 - 1) with (ex - 52) by ring.
  destruct S as [|p|p]; cbn in HS; try lia; cbn [Z.abs Z.ltb Z.compare];
    cbn [FF2R cond_Zopp]; unfold F2R; cbn [Fnum Fexp];
    rewrite ?opp_IZR; reflexivity.
Qed.

(** The double [S 2^(ex - 52)] has no other bits. *)
Theorem enc_unique xb S ex : 0 <= xb < 2 ^ 64 ->
  2 ^ 52 <= Z.abs S < 2 ^ 53 -> -1022 <= ex <= 1023 ->
  Exp100.ExpBits.xreal xb = (IZR S * bpow radix2 (ex - 52))%R ->
  xb = enc S ex.
Proof.
  intros Hxb HS He Hx.
  assert (He0 : 0 <= enc S ex < 2 ^ 64)
    by (unfold enc; destruct (S <? 0); lia).
  rewrite <- (xreal_enc S ex HS He) in Hx.
  unfold Exp100.ExpBits.xreal, b64_of_bits in Hx.
  set (f := binary_float_of_bits 52 11 eq_refl eq_refl eq_refl xb) in Hx.
  set (g := binary_float_of_bits 52 11 eq_refl eq_refl eq_refl (enc S ex))
    in Hx.
  (* both are finite and not zero: their real is S 2^(ex - 52) <> 0 *)
  assert (Hg : B2R _ _ g <> 0%R).
  { unfold g; fold (b64_of_bits (enc S ex)).
    change (B2R _ _ (b64_of_bits (enc S ex)))
      with (Exp100.ExpBits.xreal (enc S ex)).
    rewrite (xreal_enc S ex HS He).
    apply Rmult_integral_contrapositive; split;
      [apply IZR_neq; lia|apply Rgt_not_eq, bpow_gt_0]. }
  assert (Hfs : is_finite_strict _ _ f = true).
  { destruct f; cbn in Hx |- *; auto; elim Hg; rewrite <- Hx; reflexivity. }
  assert (Hgs : is_finite_strict _ _ g = true).
  { destruct g; cbn in Hg |- *; auto; elim Hg; reflexivity. }
  assert (Hfg : f = g) by (apply B2R_inj; auto).
  rewrite <- (bits_of_binary_float_of_bits 52 11 eq_refl eq_refl eq_refl
                xb) by (cbn; lia).
  rewrite <- (bits_of_binary_float_of_bits 52 11 eq_refl eq_refl eq_refl
                (enc S ex)) by (cbn; lia).
  fold f g; rewrite Hfg; reflexivity.
Qed.

(** Along a line: [S] and [S + j] of the same sign, both of 53 bits. *)
Theorem enc_step S ex j : 2 ^ 52 <= Z.abs S < 2 ^ 53 ->
  2 ^ 52 <= Z.abs (S + j) < 2 ^ 53 -> 0 < S * (S + j) ->
  enc (S + j) ex = if S <? 0 then enc S ex - j else enc S ex + j.
Proof.
  intros HS HSj Hs; unfold enc.
  destruct (Z.ltb_spec S 0) as [Hn|Hp].
  - assert (S + j < 0) by nia.
    rewrite (proj2 (Z.ltb_lt (S + j) 0)) by lia.
    rewrite !Z.abs_neq by lia; lia.
  - assert (0 < S) by nia. assert (0 < S + j) by nia.
    rewrite (proj2 (Z.ltb_ge (S + j) 0)) by lia.
    rewrite !Z.abs_eq by lia; lia.
Qed.

(** ** Hard with m = 43 is hard with m_hard = 42 *)

Theorem hard_43_42 x : ExpTableKL.ExpHard.hard x -> Exp100.ExpHard.hard x.
Proof.
  intros [z Hz]; exists z.
  assert (Hv : Exp100.ExpHard.vof x = ExpTableKL.ExpHard.vof x)
    by reflexivity.
  rewrite Hv; eapply Rlt_trans; [exact Hz|].
  apply bpow_lt; reflexivity.
Qed.

(** ** The bits of the inputs of a line *)

(** On a line, with [x0] a normal double of bits [xb0] and [neg = 0]
    exactly when [x0 > 0], the bits given to [maybe_hard_bits] for [j],
    [xb0 + j] or [xb0 - j] as a word of 64 bits ([xbj] of FilterProof.v),
    are those of [x0 + j u]. *)
Theorem line_bits S0 ex n k l B xb0 neg :
  line_ok S0 ex n k l B ->
  -1022 <= ex <= 1023 -> 0 <= xb0 < 2 ^ 64 ->
  xreal xb0 = (IZR S0 * bp (uexp ex))%R ->
  (neg = 0 <-> 0 < S0) ->
  forall j, 0 <= j < n ->
  xreal ((if Z.eqb neg 0 then xb0 + j else xb0 - j) mod 2 ^ 64) =
    (IZR (S0 + j) * bp (uexp ex))%R.
Proof.
  intros hok He Hxb Hx Hneg j Hj.
  destruct hok as (e & Hdrop & HS0 & HSL & Hsg & _).
  change ExpTableKL.ExpCheck.drop with 1 in *.
  assert (Hu : bp (uexp ex) = Flocq.Core.Raux.bpow Flocq.Core.Zaux.radix2
                                (ex - 52))
    by (unfold ExpTableKL.ExpCheck.bp, ExpTableKL.ExpCheck.uexp, ExpTableKL.ExpCheck.prec; f_equal; lia).
  rewrite Hu in *.
  (* S0 + j is between S0 and SL = S0 + n - 1: 53 bits, the sign of S0 *)
  assert (HSj : 2 ^ 52 <= Z.abs (S0 + j) < 2 ^ 53 /\ 0 < S0 * (S0 + j)).
  { destruct (Z.ltb_spec S0 0).
    - assert (S0 + n - 1 < 0) by nia.
      rewrite !Z.abs_neq in * by lia; split; [lia|nia].
    - assert (0 < S0) by (destruct (Z.eq_dec S0 0); [subst; lia|lia]).
      assert (0 < S0 + n - 1) by nia.
      rewrite !Z.abs_eq in * by lia; split; [lia|nia]. }
  destruct HSj as [HSj Hs].
  assert (Hxe : xb0 = enc S0 ex)
    by (apply enc_unique; auto).
  rewrite <- xreal_enc by auto.
  f_equal.
  assert (He0 : 0 <= enc (S0 + j) ex < 2 ^ 64)
    by (unfold enc; destruct (S0 + j <? 0); lia).
  rewrite enc_step in He0 |- * by auto.
  rewrite Hxe.
  destruct (Z.ltb_spec S0 0); destruct (Z.eqb_spec neg 0);
    try (exfalso; lia); apply Z.mod_small; lia.
Qed.

(** [maybe_hard_bits] answers 0 or 1. *)
Lemma maybe_hard_Z_range xb : 0 <= Exp100.ExpModel.maybe_hard_Z xb <= 1.
Proof.
  unfold Exp100.ExpModel.maybe_hard_Z.
  destruct (Exp100.ExpModel.core_Z xb) as [r|[y hN]]; [lia|].
  unfold Exp100.ExpModel.decide_Z; cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    lia.
Qed.

