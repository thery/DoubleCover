(** * Task T3: num_mulshr *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

(** Writing [v] at [k] changes the value by (v - old) 2^(32 k). *)
Lemma valZ_upd xs k v : 0 <= k < Zlength xs ->
  valZ (upd_Znth k xs v) =
  valZ xs + (v - Znth k xs) * 2 ^ (limb_bits * k).
Proof.
  intros Hk.
  rewrite upd_Znth_unfold by lia.
  assert (E : valZ xs = valZ (sublist 0 k xs ++ [Znth k xs] ++
                               sublist (k + 1) (Zlength xs) xs))
    by (f_equal; list_solve).
  rewrite E.
  rewrite !valZ_app; simpl Exp100.ExpConsts.valZ.
  rewrite !Zlength_sublist, !Zlength_cons, Zlength_nil by lia.
  replace (k - 0) with k by lia; ring.
Qed.

(** Limbs 5..10 of a product of 12 limbs below 2^352 are its top part. *)
Lemma valZ_shift ps : Zlength ps = 12 -> Forall limb ps ->
  valZ ps < 2 ^ 352 -> valZ (sublist 5 11 ps) = valZ ps / 2 ^ 160.
Proof.
  intros Hl Hp Hv.
  assert (E : ps = sublist 0 5 ps ++ sublist 5 11 ps ++ sublist 11 12 ps)
    by list_solve.
  assert (B0 := valZ_bounds (sublist 0 5 ps)
                  ltac:(apply Forall_sublist; auto)).
  assert (B1 := valZ_bounds (sublist 5 11 ps)
                  ltac:(apply Forall_sublist; auto)).
  assert (B2 := valZ_bounds (sublist 11 12 ps)
                  ltac:(apply Forall_sublist; auto)).
  set (x0 := valZ (sublist 0 5 ps)) in *.
  set (x1 := valZ (sublist 5 11 ps)) in *.
  set (x2 := valZ (sublist 11 12 ps)) in *.
  assert (Ev : valZ ps = x0 + 2 ^ 160 * (x1 + 2 ^ 192 * x2)).
  { rewrite E at 1; rewrite !valZ_app, !Zlength_sublist by lia.
    reflexivity. }
  rewrite !Zlength_sublist in B0, B1, B2 by lia.
  unfold Exp100.ExpConsts.limb_bits in *.
  assert (x2 = 0).
  { assert (2 ^ 160 * (2 ^ 192 * x2) < 2 ^ 352) by nia.
    rewrite Z.mul_assoc, <- Z.pow_add_r in H by lia; simpl Z.add in H; nia. }
  rewrite Ev, H, Z.mul_0_r, Z.add_0_r.
  apply Z.div_unique with x0; [|lia].
  replace (5 - 0) with 5 in B0 by lia; simpl Z.mul in B0; lia.
Qed.

Lemma body_num_mulshr : semax_body Vprog Gprog f_num_mulshr num_mulshr_spec.
Proof.
  start_function.
  rename H into Hla, H0 into Hlb, H1 into Ha, H2 into Hb, H3 into Hfit.
  unfold num.
  (* p = 0 *)
  forward_for_simple_bound 12   (* 2 NL limbs of the product *)
    (EX i : Z,
     PROP ()
     LOCAL (lvar _p (tarray tulong 12) v_p; temp _r pr;
            temp _a pa; temp _b pb)
     SEP (data_at Tsh (tarray tulong 12)
            (vwords (Zrepeat 0 i) ++ Zrepeat Vundef (12 - i)) v_p;
          data_at_ shr (tarray tulong 6) pr;
          data_at sha (tarray tulong NL) (vwords a) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - entailer!.
  - forward.
    entailer!.
    apply derives_refl'; f_equal; unfold vwords; list_solve.
  (* p = (first i limbs of a) b, limbs i + 6 .. 11 still 0 *)
  - forward_for_simple_bound 6   (* NL *)
      (EX i : Z, EX ps : list Z,
       PROP (Zlength ps = 12; Forall limb ps;
             (forall k, i + 6 <= k < 12 -> Znth k ps = 0)%Z;
             (valZ ps = valZ (sublist 0 i a) * valZ b)%Z)
       LOCAL (lvar _p (tarray tulong 12) v_p; temp _r pr;
              temp _a pa; temp _b pb)
       SEP (data_at Tsh (tarray tulong 12) (vwords ps) v_p;
            data_at_ shr (tarray tulong 6) pr;
            data_at sha (tarray tulong NL) (vwords a) pa;
            data_at shb (tarray tulong NL) (vwords b) pb)).
    + Exists (Zrepeat 0 12). entailer!.
      split; [|intros k Hk; list_solve].
      unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits.
      repeat constructor; lia.
    + Intros. rename ps into ps0, H0 into Hl0, H1 into Hp0, H2 into Hz0,
        H3 into Hv0.
      forward.
      (* p + c 2^(32 (i + j)) = p0 + a_i (first j limbs of b) 2^(32 i) *)
      forward_for_simple_bound 6   (* NL *)
        (EX j : Z, EX ps : list Z, EX c : Z,
         PROP (Zlength ps = 12; Forall limb ps; (0 <= c < 2 ^ 32)%Z;
               (forall k, i + 6 <= k < 12 -> Znth k ps = 0)%Z;
               (valZ ps + c * 2 ^ (limb_bits * (i + j)) =
                valZ ps0 + Znth i a * valZ (sublist 0 j b) *
                           2 ^ (limb_bits * i))%Z)
         LOCAL (temp _c (Vlong (Int64.repr c));
                temp _i__1 (Vint (Int.repr i));
                lvar _p (tarray tulong 12) v_p; temp _r pr;
                temp _a pa; temp _b pb)
         SEP (data_at Tsh (tarray tulong 12) (vwords ps) v_p;
              data_at_ shr (tarray tulong 6) pr;
              data_at sha (tarray tulong NL) (vwords a) pa;
              data_at shb (tarray tulong NL) (vwords b) pb)).
      * Exists ps0 0. entailer!.
        simpl Exp100.ExpConsts.valZ; ring.
      * Intros. rename i0 into j, H0 into Hj, H1 into Hl, H2 into Hp,
          H3 into Hc, H4 into Hz, H5 into Hv.
        assert (Lx : limb (Znth i a)) by (apply Forall_Znth; auto; lia).
        assert (Ly : limb (Znth j b)) by (apply Forall_Znth; auto; lia).
        assert (Lp : limb (Znth (i + j) ps)) by (apply Forall_Znth; auto; lia).
        unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits in Lx, Ly, Lp.
        assert (Ea : @Znth val Vundef i (vwords a) =
                     Vlong (Int64.repr (Znth i a))) by (apply Znth_vwords; lia).
        assert (Eb : @Znth val Vundef j (vwords b) =
                     Vlong (Int64.repr (Znth j b))) by (apply Znth_vwords; lia).
        assert (Ep : @Znth val Vundef (i + j) (vwords ps) =
                     Vlong (Int64.repr (Znth (i + j) ps)))
          by (apply Znth_vwords; lia).
        forward. { rewrite Ea; entailer!. } rewrite Ea.
        forward. { rewrite Eb; entailer!. } rewrite Eb.
        forward. { rewrite Ep; entailer!. } rewrite Ep.
        forward.
        rewrite mul64_repr, !add64_repr.
        set (s := Znth i a * Znth j b + Znth (i + j) ps + c).
        assert (Es : s = Znth i a * Znth j b + Znth (i + j) ps + c)
          by reflexivity.
        clearbody s.
        (* the bound of the C comment *)
        assert (Hs : 0 <= s < 2 ^ 64).
        { rewrite Es; split; [nia|].
          assert (Znth i a * Znth j b <= (2 ^ 32 - 1) * (2 ^ 32 - 1)) by nia.
          lia. }
        forward.
        rewrite and_mask32 by lia.
        forward.
        rewrite shru32 by lia.
        Exists (upd_Znth (i + j) ps (s mod 2 ^ 32)) (s / 2 ^ 32).
        assert (Hd := Z.div_mod s (2 ^ 32) ltac:(lia)).
        assert (Hm := Z.mod_pos_bound s (2 ^ 32) ltac:(lia)).
        assert (Hq : 0 <= s / 2 ^ 32 < 2 ^ 32).
        { split; [apply Z.div_pos; lia|].
          apply Z.div_lt_upper_bound; lia. }
        entailer!.
        { split; [list_solve|]. split; [apply Forall_upd_Znth; auto; lia|].
          split.
          { intros k Hk. rewrite upd_Znth_diff by lia. auto. }
          rewrite valZ_upd by lia.
          rewrite valZ_sublist_succ by lia.
          unfold Exp100.ExpConsts.limb_bits in *.
          replace (32 * (i + (j + 1))) with (32 * (i + j) + 32) by lia.
          replace (32 * (i + j)) with (32 * i + 32 * j) in * by lia.
          rewrite !Z.pow_add_r in * by lia.
          set (Q := 2 ^ (32 * i)) in *. set (R := 2 ^ (32 * j)) in *.
          remember (Znth i a * Znth j b + Znth (i + j) ps + c) as s eqn:Es.
          rewrite (Z.mod_eq s (2 ^ 32)) by lia.
          assert (Hv' : valZ ps = valZ ps0 +
                    Znth i a * valZ (sublist 0 j b) * Q - c * (Q * R))
            by lia.
          rewrite Hv', Es; ring. }
        rewrite upd_vwords by lia.
        rewrite Int64.unsigned_repr by rep_lia.
        apply derives_refl.
      * Intros ps c. rename H0 into Hl, H1 into Hp, H2 into Hc, H3 into Hz,
          H4 into Hv.
        forward.
        Exists (upd_Znth (i + 6) ps c).
        entailer!.
        { split; [list_solve|].
          split; [apply Forall_upd_Znth; auto; unfold limb; rep_lia|].
          split.
          { intros k Hk. rewrite upd_Znth_diff by lia. apply Hz; lia. }
          rewrite valZ_upd, Hz by lia.
          rewrite valZ_sublist_succ by lia.
          rewrite sublist_same in Hv by lia.
          lia. }
        rewrite upd_vwords by lia.
        rewrite Int64.unsigned_repr by rep_lia.
        apply derives_refl.
    + Intros ps. rename H into Hl, H0 into Hp, H1 into Hz, H2 into Hv.
      rewrite sublist_same in Hv by lia.
      (* r = limbs 5 .. 5 + k - 1 of p *)
      forward_for_simple_bound 6   (* NL *)
        (EX k : Z,
         PROP ()
         LOCAL (lvar _p (tarray tulong 12) v_p; temp _r pr;
                temp _a pa; temp _b pb)
         SEP (data_at Tsh (tarray tulong 12) (vwords ps) v_p;
              data_at shr (tarray tulong 6)
                (vwords (sublist 5 (5 + k) ps) ++ Zrepeat Vundef (6 - k)) pr;
              data_at sha (tarray tulong NL) (vwords a) pa;
              data_at shb (tarray tulong NL) (vwords b) pb)).
      * entailer!.
        rewrite data_at__eq, sublist_nil; apply derives_refl.
      * assert (Ed : Int.add (Int.repr i) (Int.divs (Int.repr 160)
                       (Int.repr 32)) = Int.repr (i + 5)).
        { change (Int.divs (Int.repr 160) (Int.repr 32)) with (Int.repr 5).
          apply add_repr. }
        assert (Eq : @Znth val Vundef (i + 5) (vwords ps) =
                     Vlong (Int64.repr (Znth (i + 5) ps)))
          by (apply Znth_vwords; lia).
        forward.
        1-3: rewrite ?Ed, ?Int.signed_repr by rep_lia; rewrite ?Eq; entailer!.
        { change (Int.divs (Int.repr 160) (Int.repr 32)) with (Int.repr 5).
          rewrite Int.signed_repr by rep_lia; rep_lia. }
        forward.
        entailer!.
        rewrite Ed, Int.signed_repr, Eq by rep_lia.
        apply derives_refl'; f_equal; unfold vwords; list_solve.
      * Exists (sublist 5 11 ps).
        assert (Hs : valZ (sublist 5 11 ps) = valZ ps / 2 ^ 160).
        { apply valZ_shift; auto.
          unfold Exp100.ExpConsts.P, num_bits, Exp100.ExpConsts.limb_bits
            in Hfit; lia. }
        unfold num; entailer!.
        { split; [list_solve|]. split; [apply Forall_sublist; auto|].
          rewrite Hs, Hv, Exp100.ExpModel.mulshrE; reflexivity. }
        rewrite app_nil_r; apply derives_refl.
Qed.
