(** * Task T4: mul_ln2, guess_n *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

(* Dropping the low limb of a number divides it by 2^32. *)
Lemma valZ_drop1 p : Zlength p = NP -> Forall limb p ->
  valZ (sublist 1 NP p) = valZ p / 2 ^ limb_bits.
Proof.
  intros Hl Hf.
  assert (H0 : limb (Znth 0 p)) by (apply Forall_Znth; auto; lia).
  rewrite <- (sublist_same 0 NP p) at 2 by lia.
  rewrite (sublist_split 0 1 NP) by lia.
  rewrite valZ_app, sublist_len_1 by lia.
  change (Zlength [Znth 0 p]) with 1.
  cbn [Exp100.ExpNum.valZ].
  unfold Exp100.ExpNum.limb, Exp100.ExpNum.limb_bits in *.
  rewrite Z.mul_1_r.
  rewrite Z.add_0_r, Z.add_comm, Z.mul_comm, Z.div_add_l by lia.
  rewrite Z.div_small by lia; lia.
Qed.

Lemma body_mul_ln2 : semax_body Vprog Gprog f_mul_ln2 mul_ln2_spec.
Proof.
  start_function.
  rename H into Hn.
  destruct LN2_num as [HlL HfL].
  forward_call (Tsh, Ers, v_p, gv _LN2, Exp100.ExpTable.LN2, n).
  Intros p.
  rename H into Hlp, H0 into Hfp, H1 into Hvp.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z,
     PROP ()
     LOCAL (temp _q pq; lvar _p (tarray tulong 7) v_p; gvars gv)
     SEP (data_at Tsh (tarray tulong NP) (vwords p) v_p;
          data_at sh (tarray tulong NL)
            (vwords (sublist 1 (i + 1) p) ++ Zrepeat Vundef (NL - i)) pq;
          num Ers Exp100.ExpTable.LN2 (gv _LN2))).
  - change (0 + 1) with 1; rewrite sublist_nil. entailer!.
  - forward.
    { rewrite Znth_vwords by lia. entailer!. }
    rewrite Znth_vwords by lia.
    forward.
    entailer!.
    apply derives_refl'; f_equal. unfold vwords; list_solve.
  - Exists (sublist 1 7 p).
    rewrite Z.sub_diag, app_nil_r.
    assert (Hq : valZ (sublist 1 7 p) = Exp100.ExpModel.q n)
      by (rewrite valZ_drop1, Exp100.ExpModel.qE, Hvp by auto; f_equal; lia).
    unfold num; entailer!.
    split; [list_solve|apply Forall_sublist; auto].
Qed.

(* Two pieces without common bits: their or is their sum. *)
Lemma lor_shift7 a b : 0 <= a < 2 ^ 7 -> Z.lor a (b * 2 ^ 7) = a + b * 2 ^ 7.
Proof.
  intros Ha.
  assert (Hl : Z.land a (b * 2 ^ 7) = 0).
  { apply Z.bits_inj'; intros k Hk.
    rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases k 7).
    - rewrite Z.mul_pow2_bits_low by lia; apply andb_false_r.
    - rewrite <- (Z.mod_small a (2 ^ 7)) by lia.
      rewrite Z.mod_pow2_bits_high by lia; reflexivity. }
  rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact Hl; reflexivity.
Qed.

(* Bits 185 .. 223 of a number of 7 limbs, from its limbs 5 and 6. *)
Lemma bits185 p : Zlength p = NP -> Forall limb p ->
  Int64.or (Int64.shru (Int64.repr (Znth 5 p)) (Int64.repr 25))
           (Int64.shl (Int64.repr (Znth 6 p)) (Int64.repr 7)) =
  Int64.repr (valZ p / 2 ^ 185).
Proof.
  intros Hl Hf.
  assert (Ha : limb (Znth 5 p)) by (apply Forall_Znth; auto; lia).
  assert (Hb : limb (Znth 6 p)) by (apply Forall_Znth; auto; lia).
  assert (HL := valZ_bounds (sublist 0 5 p) (Forall_sublist _ _ _ _ Hf)).
  assert (Ep : valZ p = valZ (sublist 0 5 p) +
                        2 ^ 160 * (Znth 5 p + 2 ^ 32 * Znth 6 p)).
  { rewrite <- (sublist_same 0 NP p) at 1 by lia.
    rewrite (sublist_split 0 5 NP), valZ_app by lia.
    replace (sublist 5 NP p) with [Znth 5 p; Znth 6 p] by list_solve.
    rewrite Zlength_sublist by lia.
    cbn [Exp100.ExpNum.valZ]; unfold Exp100.ExpNum.limb_bits.
    replace (32 * (5 - 0)) with 160 by lia; ring. }
  rewrite Zlength_sublist in HL by lia.
  unfold Exp100.ExpNum.limb, Exp100.ExpNum.limb_bits in *.
  replace (32 * (5 - 0)) with 160 in HL by lia.
  set (a := Znth 5 p) in *; set (b := Znth 6 p) in *.
  set (L := valZ (sublist 0 5 p)) in *.
  clearbody a b L.
  rewrite Int64.shru_div_two_p, Int64.shl_mul_two_p.
  rewrite !Int64.unsigned_repr by rep_lia.
  change (two_p 25) with (2 ^ 25); change (two_p 7) with (2 ^ 7).
  unfold Int64.or, Int64.mul.
  rewrite (Int64.unsigned_repr b), (Int64.unsigned_repr (2 ^ 7)) by rep_lia.
  assert (Hd := Z.div_mod a (2 ^ 25) ltac:(lia)).
  assert (Hm := Z.mod_pos_bound a (2 ^ 25) ltac:(lia)).
  set (a1 := a / 2 ^ 25) in *; set (a0 := a mod 2 ^ 25) in *.
  clearbody a1 a0.
  rewrite !Int64.unsigned_repr by rep_lia.
  rewrite lor_shift7 by lia.
  f_equal; rewrite Ep.
  apply Z.div_unique with (r := L + 2 ^ 160 * a0); lia.
Qed.

Lemma body_guess_n : semax_body Vprog Gprog f_guess_n guess_n_spec.
Proof.
  start_function.
  forward.
  rename H into Hlx, H0 into Hfx.
  forward_call (Tsh, sh, v_p, px, X, Exp100.ExpTable.INV).
  { exact INV_limb. }
  Intros p.
  rename H into Hlp, H0 into Hfp, H1 into Hvp.
  forward.
  { rewrite Znth_vwords by lia. entailer!. }
  rewrite Znth_vwords by lia.
  forward.
  { rewrite Znth_vwords by lia. entailer!. }
  rewrite Znth_vwords by lia.
  assert (Hg : Exp100.ExpModel.guess (valZ X) = valZ p / 2 ^ 185)
    by (rewrite Exp100.ExpModel.guessE, Hvp; reflexivity).
  forward.
  rewrite bits185, Hg by auto.
  entailer!.
Qed.
