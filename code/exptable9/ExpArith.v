(** * The integer tests of the checker, read in the reals *)

From Stdlib Require Import ZArith Reals Lia Lra List.
From Flocq Require Import Core.
From ExpTable9 Require Import ExpCheck.

Open Scope R_scope.

(** [flr] is the floor it is named after. *)
Lemma flrE p g fk h : (0 < fk)%Z -> (0 <= h)%Z ->
  flr p g fk h = Zfloor (IZR p * bp g / IZR fk + IZR h / 2).
Proof.
intros Hfk Hh; unfold flr, bp.
assert (Hfk' : IZR fk <> 0) by (apply not_0_IZR; lia).
destruct (Z.leb_spec 0 g) as [Hg | Hg].
- rewrite <- Zfloor_div by lia; f_equal.
  rewrite <- (IZR_Zpower radix2 g) by lia; simpl radix_val.
  rewrite !mult_IZR, plus_IZR, !mult_IZR; field; auto.
- rewrite <- Zfloor_div.
  2: { apply Z.neq_mul_0; split; [lia|]; apply Z.pow_nonzero; lia. }
  f_equal.
  (* a negative power of two is the inverse of an integer *)
  assert (Hq : bpow radix2 g = / IZR (2 ^ (- g))).
  { rewrite (IZR_Zpower radix2) by lia; rewrite bpow_opp, Rinv_inv; easy. }
  assert (H2 : IZR (2 ^ (- g)) <> 0).
  { apply not_0_IZR; apply Z.pow_nonzero; lia. }
  rewrite Hq, !mult_IZR, plus_IZR, !mult_IZR; field; auto.
Qed.

Lemma lt2_ok p f g : (1 <= p)%Z -> lt2 p f g = true -> IZR p * bp f < bp g.
Proof.
intros Hp; unfold lt2, bp.
destruct (Z.leb_spec g f) as [Hgf | Hgf]; [discriminate|].
intros Hlt; apply Z.ltb_lt in Hlt.
replace (bpow radix2 g) with (bpow radix2 ((g - f) + f)) by (f_equal; ring).
rewrite bpow_plus; apply Rmult_lt_compat_r; [apply bpow_gt_0|].
rewrite <- (IZR_Zpower radix2) by lia; apply IZR_lt; exact Hlt.
Qed.

Lemma log2_le p f : (0 < p)%Z -> bp (Z.log2 p + f) <= IZR p * bp f.
Proof.
intros Hp; unfold bp; rewrite bpow_plus.
apply Rmult_le_compat_r; [apply Rlt_le, bpow_gt_0|].
rewrite <- (IZR_Zpower radix2) by (apply Z.log2_nonneg).
apply IZR_le; destruct (Z.log2_spec p Hp) as [H _]; exact H.
Qed.

(** [beta^l] is the power of two of exponent [lbits]. *)
Lemma beta_lE : beta_l = (2 ^ lbits)%Z.
Proof. vm_compute; reflexivity. Qed.

Lemma lbits_ge0 : (0 <= lbits)%Z.
Proof. vm_compute; discriminate. Qed.

Lemma beta_lR : IZR beta_l = bp lbits.
Proof.
rewrite beta_lE; unfold bp; rewrite (IZR_Zpower radix2); [easy|].
exact lbits_ge0.
Qed.

(** A power of a power of two. *)
Lemma bp_pow a i : bp a ^ i = bp (a * Z.of_nat i).
Proof.
induction i as [|i IH]; [now rewrite Z.mul_0_r|].
rewrite Nat2Z.inj_succ, <- Z.add_1_r, Z.mul_add_distr_l, Z.mul_1_r.
unfold bp in *; rewrite bpow_plus, <- IH; simpl; ring.
Qed.

(** Moving the start of an integer sum. *)
Lemma fold_addE (s : list Z) a :
  fold_right Z.add a s = (fold_right Z.add 0 s + a)%Z.
Proof. induction s as [|x s IH]; simpl; lia. Qed.

(** [sumR] of powers of an integer, in integers. *)
Lemma sumR_powE n N : sumR (fun i => IZR n ^ i) N =
  IZR (fold_right Z.add 0 (map (fun i => n ^ Z.of_nat i) (seq 0 N)))%Z.
Proof.
induction N as [|N IH]; [easy|].
rewrite seq_S, map_app, fold_right_app; simpl.
rewrite fold_addE, plus_IZR, <- IH, Z.add_0_r, pow_IZR; easy.
Qed.

(** A power of two, as an integer. *)
Lemma bp_IZR g : (0 <= g)%Z -> bp g = IZR (2 ^ g).
Proof.
intros Hg; unfold bp; rewrite <- (IZR_Zpower radix2) by exact Hg; easy.
Qed.

(** A negative power of two, as the inverse of an integer. *)
Lemma bp_IZRN g : (g < 0)%Z -> bp g = / IZR (2 ^ (- g)).
Proof.
intros Hg; unfold bp; rewrite (IZR_Zpower radix2) by lia.
rewrite bpow_opp, Rinv_inv; easy.
Qed.

(** [window_ok] in the reals, before the bound on [exp x1]. *)
Lemma window_okR mU fU ve ue n : window_ok mU fU ve ue n = true ->
  IZR (2 ^ (lbits - m) + sumn n) + IZR (mU * n ^ Z.of_nat k) *
    bp (fU + lbits + ue * Z.of_nat k - ve) / IZR (Z.of_nat (fact k))
    <= IZR E.
Proof.
unfold window_ok; cbv zeta.
set (X := (mU * n ^ Z.of_nat k)%Z).
set (g := (fU + lbits + ue * Z.of_nat k - ve)%Z).
set (C := (2 ^ (lbits - m) + sumn n)%Z).
set (kf := Z.of_nat (fact k)).
assert (Hkf : (0 < kf)%Z) by (pose proof (lt_O_fact k); lia).
assert (HkfR : 0 < IZR kf) by (apply IZR_lt; exact Hkf).
clearbody X g C kf; generalize E; intros EE.
destruct (Z.leb_spec 0 g) as [Hg | Hg]; intros H; apply Z.leb_le, IZR_le in H;
  rewrite ?plus_IZR, ?mult_IZR, ?plus_IZR, ?mult_IZR in H.
- rewrite bp_IZR by exact Hg.
  (* field and lra only see real variables, or the kernel check is slow *)
  generalize (IZR X) (IZR C) (IZR (2 ^ g)) (IZR EE) H.
  generalize (IZR kf) HkfR; clear; intros kr Hk xr cr pr er H.
  apply Rmult_le_reg_r with (1 := Hk).
  replace ((cr + xr * pr / kr) * kr) with (xr * pr + cr * kr) by (field; lra).
  exact H.
- rewrite bp_IZRN by exact Hg.
  assert (HP : 0 < IZR (2 ^ (- g))).
  { apply IZR_lt; apply Z.pow_pos_nonneg; lia. }
  generalize (IZR X) (IZR C) (IZR (2 ^ (- g))) (IZR EE) H HP.
  generalize (IZR kf) HkfR; clear; intros kr Hk xr cr pr er H Hp.
  apply Rmult_le_reg_r with (r := kr * pr); [now apply Rmult_lt_0_compat|].
  replace ((cr + xr * / pr / kr) * (kr * pr))
    with (xr + cr * kr * pr) by (field; lra).
  lra.
Qed.

(** (H_E), from an upper bound [mU 2^fU] of [y = exp x1]. *)
Lemma window_okP mU fU ve ue n y :
  (m <= lbits)%Z -> (0 <= n)%Z -> 0 <= y <= IZR mU * bp fU ->
  window_ok mU fU ve ue n = true ->
  IZR beta_l * (bp (- m) + y * (IZR n * bp ue) ^ k / (INR (fact k) * bp ve))
    + sumR (fun i => IZR n ^ i) k <= IZR E.
Proof.
intros Hm Hn Hy Hw.
eapply Rle_trans; [| exact (window_okR _ _ _ _ _ Hw)].
rewrite sumR_powE; fold (sumn n).
rewrite plus_IZR, mult_IZR, <- pow_IZR, <- INR_IZR_INZ.
rewrite <- bp_IZR by lia.
rewrite beta_lR.
rewrite Rpow_mult_distr, bp_pow.
replace (bp (lbits - m)) with (bp lbits * bp (- m))
  by (unfold bp; rewrite <- bpow_plus; f_equal; ring).
replace (bp (fU + lbits + ue * Z.of_nat k - ve))
  with (bp fU * bp lbits * bp (ue * Z.of_nat k) / bp ve)
  by (unfold bp, Rdiv; rewrite <- bpow_opp, <- !bpow_plus; f_equal; ring).
assert (HB : 0 < bp lbits) by apply bpow_gt_0.
assert (HU : 0 < bp (ue * Z.of_nat k)) by apply bpow_gt_0.
assert (HV : 0 < bp ve) by apply bpow_gt_0.
assert (HK : 0 < INR (fact k)) by apply INR_fact_lt_0.
assert (HN : 0 <= IZR n ^ k) by (apply pow_le, IZR_le; exact Hn).
(* only real variables are left *)
revert Hy HB HU HV HK HN.
generalize (bp lbits) (bp (- m)) (bp (ue * Z.of_nat k)) (bp ve).
generalize (INR (fact k)) (IZR n ^ k) (IZR (sumn n)) (IZR mU) (bp fU).
clear; intros K N S F1 F2 B M U V Hy HB HU HV HK HN.
assert (Hc : 0 <= N * U * B / (K * V)).
{ unfold Rdiv; apply Rmult_le_pos.
  - apply Rmult_le_pos; [apply Rmult_le_pos|]; lra.
  - apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; easy. }
replace (B * (M + y * (N * U) / (K * V)) + S)
  with (B * M + S + y * (N * U * B / (K * V))) by (field; lra).
replace (B * M + S + F1 * N * (F2 * B * U / V) / K)
  with (B * M + S + (F1 * F2) * (N * U * B / (K * V))) by (field; lra).
apply Rplus_le_compat_l, Rmult_le_compat_r; [exact Hc | apply Hy].
Qed.

(** A floor that is the same at both ends is the same in between. *)
Lemma Zfloor_mid a b d : a <= b <= d -> Zfloor a = Zfloor d ->
  Zfloor b = Zfloor a.
Proof.
intros [Hab Hbd] Had.
apply Zfloor_le in Hab; apply Zfloor_le in Hbd; lia.
Qed.

(** (H_A) for one coefficient, from an enclosure of [y = exp x0]. *)
Lemma coefA_ok mL fL mU fU ve ue i fk Ai y :
  fk = Z.of_nat (fact i) ->
  IZR mL * bp fL <= y <= IZR mU * bp fU ->
  coefA mL fL mU fU ve ue i fk = Some Ai ->
  (0 <= Ai < beta_l)%Z /\
  Rabs (IZR Ai - IZR beta_l *
        fracR (y * bp ue ^ i / INR (fact i) / bp ve)) < 1.
Proof.
intros Hfk Hy H.
assert (Hfk0 : (0 < fk)%Z) by (pose proof (lt_O_fact i); lia).
unfold coefA in H; cbv zeta in H.
set (gi := (lbits + ue * Z.of_nat i - ve)%Z) in H.
set (r := flr mL (fL + gi) fk 1) in H.
set (q := flr mL (fL + gi - lbits) fk 0) in H.
destruct (_ && _) eqn:Hb; [|discriminate].
injection H as <-.
rewrite !Bool.andb_true_iff, Z.eqb_eq, Z.eqb_eq, Z.leb_le, Z.ltb_lt in Hb.
destruct Hb as [[[H1 H2] H3] H4].
split; [lia|].
unfold r, q in *.
rewrite !flrE in H1, H2 by lia.
rewrite !flrE by lia.
clear H3 H4.
assert (HfkR : 0 < IZR fk) by (apply IZR_lt; exact Hfk0).
assert (HB : 0 < bp lbits) by apply bpow_gt_0.
(* the argument of fracR is y (2^gi / i!) / beta^l *)
assert (Hc : y * bp ue ^ i / INR (fact i) / bp ve =
             y * (bp gi / IZR fk) / bp lbits).
{ rewrite INR_IZR_INZ, <- Hfk; rewrite bp_pow.
  unfold gi; replace (lbits + ue * Z.of_nat i - ve)%Z
    with (lbits + ue * Z.of_nat i + - ve)%Z by ring.
  assert (HV : 0 < bp ve) by apply bpow_gt_0.
  unfold bp in *; rewrite !bpow_plus, bpow_opp; field; lra. }
rewrite Hc; clear Hc; clearbody gi.
assert (Ha : forall z f, IZR z * bp (f + gi) / IZR fk =
                       IZR z * bp f * (bp gi / IZR fk)).
{ intros z f; unfold bp; rewrite bpow_plus; field; lra. }
assert (Hb : forall z f, IZR z * bp (f + gi - lbits) / IZR fk + 0 / 2 =
                       IZR z * bp f * (bp gi / IZR fk) / bp lbits).
{ intros z f; replace (f + gi - lbits)%Z with (f + gi + - lbits)%Z by ring.
  unfold bp; rewrite !bpow_plus, bpow_opp.
  unfold bp in HB; field; lra. }
rewrite !Ha, !Hb in *; clear Ha Hb.
assert (Hc : 0 < bp gi / IZR fk).
{ apply Rdiv_lt_0_compat; [apply bpow_gt_0 | exact HfkR]. }
rewrite minus_IZR, mult_IZR, beta_lR.
unfold fracR.
(* only real variables are left *)
revert Hy H1 H2 HB Hc.
generalize (IZR mL * bp fL) (IZR mU * bp fU) (bp gi / IZR fk) (bp lbits).
clear; intros lo hi c B Hy H1 H2 HB Hc.
assert (Hlo : lo * c <= y * c) by (apply Rmult_le_compat_r; lra).
assert (Hhi : y * c <= hi * c) by (apply Rmult_le_compat_r; lra).
rewrite <- (Zfloor_mid (lo * c / B) (y * c / B) (hi * c / B));
  [| | exact H2].
2: { unfold Rdiv; split; apply Rmult_le_compat_r; try lra;
     apply Rlt_le, Rinv_0_lt_compat; exact HB. }
rewrite <- (Zfloor_mid (lo * c + 1 / 2) (y * c + 1 / 2) (hi * c + 1 / 2));
  [| lra | exact H1].
pose proof (Zfloor_lb (y * c + 1 / 2)).
pose proof (Zfloor_ub (y * c + 1 / 2)).
replace (B * (y * c / B - IZR (Zfloor (y * c / B))))
  with (y * c - IZR (Zfloor (y * c / B)) * B) by (field; lra).
apply Rabs_def1; lra.
Qed.

(** (H_A) for the [c] coefficients from the [i]-th on. *)
Lemma coefs_ok mL fL mU fU ve ue y c i fk As :
  fk = Z.of_nat (fact i) ->
  IZR mL * bp fL <= y <= IZR mU * bp fU ->
  coefs mL fL mU fU ve ue i fk c = Some As ->
  length As = c /\
  forall j, (j < c)%nat ->
    (0 <= nth j As 0%Z < beta_l)%Z /\
    Rabs (IZR (nth j As 0%Z) - IZR beta_l *
          fracR (y * bp ue ^ (i + j) / INR (fact (i + j)) / bp ve)) < 1.
Proof.
intros Hfk Hy; revert i fk As Hfk.
induction c as [|c IH]; intros i fk As Hfk H; cbn [coefs] in H.
- injection H as <-; split; [easy | intros j Hj; lia].
- destruct (coefA mL fL mU fU ve ue i fk) as [Ai|] eqn:HA; [|discriminate].
  destruct (coefs mL fL mU fU ve ue (S i) (fk * Z.of_nat (S i)) c) as [As'|]
    eqn:HAs; [|discriminate].
  injection H as <-.
  (* the next factorial *)
  assert (Hfk' : (fk * Z.of_nat (S i))%Z = Z.of_nat (fact (S i))).
  { change (fact (S i)) with (S i * fact i)%nat.
    rewrite Nat2Z.inj_mul, Hfk; ring. }
  destruct (IH _ _ _ Hfk' HAs) as [Hl HAs'].
  split; [simpl; lia|].
  intros [|j] Hj.
  + rewrite Nat.add_0_r; exact (coefA_ok _ _ _ _ _ _ _ _ _ _ Hfk Hy HA).
  + replace (i + S j)%nat with (S i + j)%nat by lia.
    apply HAs'; lia.
Qed.
