(** * S3: the filter

    When [decide_Z y hN] returns 0 (and y > D), no z within D 2^(hN - P) of
    y 2^(hN - P) is hard: z / v is at distance at least 2^-m_hard from every
    integer, v being half an ulp of z ([vexp] of its binade), as [hard]
    of ExpHard.v takes it. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Exp100 Require Import ExpConsts ExpModel ExpModelBounds ExpHard.

Open Scope R_scope.

(** 2^e as a real, for 0 <= e. *)
Lemma IZR_pow2 e : (0 <= e)%Z -> IZR (2 ^ e) = bpow radix2 e.
Proof.
intros He; rewrite <- IZR_Zpower by exact He; destruct e; reflexivity.
Qed.

(** The distance of y to the multiples of 2^f is at least
    min (y mod 2^f, 2^f - y mod 2^f). *)
Lemma dist_mult y f k a : (0 <= f)%Z ->
  (a < y mod 2 ^ f)%Z -> (a < 2 ^ f - y mod 2 ^ f)%Z ->
  (a < Z.abs (y - k * 2 ^ f))%Z.
Proof.
intros Hf Hlo Hhi.
assert (Hp : (0 < 2 ^ f)%Z) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.div_mod y (2 ^ f) ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound y (2 ^ f) Hp).
set (q := (y / 2 ^ f)%Z) in *; set (lo := (y mod 2 ^ f)%Z) in *.
destruct (Z.le_gt_cases k q).
- assert (0 <= (q - k) * 2 ^ f)%Z by nia; lia.
- assert ((k - q) * 2 ^ f >= 2 ^ f)%Z by nia; lia.
Qed.

Theorem decide_ok y hN z : (D < y)%Z -> decide_Z y hN = 0%Z ->
  Rabs (z - IZR y * bpow radix2 (hN - P)) <= IZR D * bpow radix2 (hN - P) ->
  forall k : Z, bp (- m_hard) <= Rabs (z / bp (vexp (binade z)) - IZR k).
Proof.
intros Hy Hd Hz k; unfold decide_Z in Hd.
set (s := (hN - P)%Z) in *; set (b := bitlen y) in *.
destruct (Z.eqb_spec (bitlen (y - D)) b) as [Hb1|]; [|discriminate].
destruct (Z.eqb_spec (bitlen (y + D)) b) as [Hb2|]; [|discriminate].
cbn [andb negb] in Hd.
set (f := (Z.max (s + b - 1) emin - prec - s)%Z) in *.
destruct (Z.ltb_spec f f_min) as [|Hf1]; [discriminate|].
destruct (Z.ltb_spec f_max f) as [|Hf2]; [discriminate|].
cbn [orb] in Hd.
(* f - m_hard and f are not negative *)
assert (Hfm : (0 <= f - m_hard)%Z) by (unfold f_min, m_hard in *; lia).
assert (Hf : (0 <= f)%Z) by (unfold m_hard in Hfm; lia).
rewrite !lowE, !pow2E in Hd by assumption.
(* y is far from every multiple of 2^f *)
assert (Hdist : (2 ^ (f - m_hard) + D < Z.abs (y - k * 2 ^ f))%Z).
{ apply dist_mult; [exact Hf| |];
  destruct (Z.ltb_spec (y mod 2 ^ f) (2 ^ f - y mod 2 ^ f));
  match type of Hd with context [Z.ltb ?a ?c] =>
    destruct (Z.ltb_spec a c) end; try discriminate; lia. }
clear Hd.
destruct (bitlen_range y b Hy Hb1 Hb2) as (Hb0 & Hbl & Hbh).
(* z is in the binade s + b - 1 *)
assert (Hs : 0 < bpow radix2 s) by apply bpow_gt_0.
apply Rabs_le_inv in Hz.
assert (Hlo : IZR (2 ^ (b - 1)) <= IZR (y - D)) by (apply IZR_le; lia).
assert (Hhi : IZR (y + D) < IZR (2 ^ b)) by (apply IZR_lt; lia).
rewrite IZR_pow2 in Hlo, Hhi by lia.
rewrite minus_IZR in Hlo; rewrite plus_IZR in Hhi.
assert (Hzb : bpow radix2 (s + b - 1) <= z < bpow radix2 (s + b)).
{ replace (s + b - 1)%Z with ((b - 1) + s)%Z by ring.
  rewrite !bpow_plus; split; nra. }
assert (Hv : vexp (binade z) = (f + s)%Z).
{ unfold binade; rewrite (mag_unique_pos radix2 z (s + b) Hzb).
  unfold vexp, f; lia. }
rewrite Hv; unfold bp.
(* w = z 2^-s - y is at most D *)
set (w := z * bpow radix2 (- s) - IZR y).
assert (Hw : Rabs w <= IZR D).
{ assert (Hinv : bpow radix2 (- s) * bpow radix2 s = 1)
    by (rewrite <- bpow_plus, Z.add_opp_diag_l; reflexivity).
  assert (Hwe : w = (z - IZR y * bpow radix2 s) * bpow radix2 (- s))
    by (unfold w; rewrite Rmult_minus_distr_r, Rmult_assoc,
          (Rmult_comm (bpow radix2 s)), Hinv, Rmult_1_r; reflexivity).
  rewrite Hwe, Rabs_mult, (Rabs_pos_eq (bpow _ (- s))) by apply bpow_ge_0.
  pose proof (bpow_gt_0 radix2 (- s)).
  apply Rabs_le in Hz.
  apply Rle_trans with (IZR D * bpow radix2 s * bpow radix2 (- s)).
  { apply Rmult_le_compat_r; lra. }
  rewrite Rmult_assoc, (Rmult_comm (bpow radix2 s)), Hinv; lra. }
(* z / 2^(f+s) - k = (y - k 2^f + w) 2^-f *)
assert (Hsplit : z / bpow radix2 (f + s) - IZR k =
  (IZR (y - k * 2 ^ f) + w) * bpow radix2 (- f)).
{ unfold w; rewrite minus_IZR, mult_IZR, IZR_pow2 by exact Hf.
  rewrite bpow_plus, !bpow_opp.
  pose proof (bpow_gt_0 radix2 f); field; lra. }
rewrite Hsplit, Rabs_mult, (Rabs_pos_eq (bpow _ (- f))) by apply bpow_ge_0.
assert (Hn : bpow radix2 (f - m_hard) + IZR D < Rabs (IZR (y - k * 2 ^ f))).
{ rewrite Rabs_Zabs, <- IZR_pow2 by exact Hfm.
  rewrite <- plus_IZR; apply IZR_lt; exact Hdist. }
assert (Htri := Rabs_triang_inv (IZR (y - k * 2 ^ f)) (- w)).
rewrite Rabs_Ropp in Htri; unfold Rminus in Htri.
rewrite Ropp_involutive in Htri.
replace (- m_hard)%Z with ((f - m_hard) + - f)%Z by ring.
rewrite bpow_plus.
pose proof (bpow_gt_0 radix2 (- f)).
apply Rmult_le_compat_r; lra.
Qed.
