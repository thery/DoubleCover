(** * Task T1: num_zero, num_copy, num_add, num_sub, num_mul_small *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

Lemma body_num_zero : semax_body Vprog Gprog f_num_zero num_zero_spec.
Proof.
  start_function.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z,
     PROP () LOCAL (temp _a p)
     SEP (data_at sh (tarray tulong NL)
            (vwords (Zrepeat 0 i) ++ Zrepeat Vundef (NL - i)) p)).
  - entailer!.
  - forward.
    entailer!.
    apply derives_refl'; f_equal; unfold vwords; list_solve.
  - unfold num; entailer!.
Qed.

Lemma body_num_copy : semax_body Vprog Gprog f_num_copy num_copy_spec.
Proof.
  start_function.
  rename H into Hlb.
  unfold num.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z,
     PROP () LOCAL (temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL)
            (sublist 0 i (vwords b) ++ Zrepeat Vundef (NL - i)) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - entailer!.
  - forward.
    { rewrite Znth_vwords by lia. entailer!. }
    rewrite Znth_vwords by lia.
    forward.
    entailer!.
    apply derives_refl'; f_equal.
    rewrite <- Znth_vwords by lia. list_solve.
  - rewrite sublist_same, app_nil_r by (rewrite ?Zlength_vwords; lia).
    unfold num; entailer!.
Qed.

Lemma body_num_add : semax_body Vprog Gprog f_num_add num_add_spec.
Proof.
  start_function.
  rename H into Hla, H0 into Hlb, H1 into Ha, H2 into Hb, H3 into Hfit.
  unfold num.
  forward.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z, EX r : list Z, EX c : Z,
     PROP (Zlength r = i; Forall limb r; 0 <= c <= 1;
           (valZ r + c * 2 ^ (limb_bits * i) =
              valZ (sublist 0 i a) + valZ (sublist 0 i b))%Z)
     LOCAL (temp _c (Vlong (Int64.repr c)); temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL) (vwords (r ++ sublist i NL a)) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - Exists (@nil Z) 0. entailer!.
    rewrite sublist_same by lia. cancel.
  - Intros.
    rename H0 into Hr, H1 into Hrl, H2 into Hc, H3 into Hv. subst i.
    assert (Lx : limb (Znth (Zlength r) a)) by (apply Forall_Znth; auto; lia).
    assert (Ly : limb (Znth (Zlength r) b)) by (apply Forall_Znth; auto; lia).
    unfold Exp100.ExpNum.limb, Exp100.ExpNum.limb_bits in *.
    assert (Ex : @Znth val Vundef (Zlength r)
                   (vwords (r ++ sublist (Zlength r) NL a)) =
                 Vlong (Int64.repr (Znth (Zlength r) a))).
    { unfold vwords. rewrite Znth_map, Znth_map. f_equal. f_equal.
      rewrite Znth_app2 by lia. replace (Zlength r - Zlength r) with 0 by lia.
      rewrite Znth_sublist by lia. f_equal; lia.
      all: rewrite ?Zlength_map, Zlength_app, Zlength_sublist; lia. }
    forward.
    { rewrite Ex. entailer!. }
    rewrite Ex.
    forward.
    { rewrite Znth_vwords by lia. entailer!. }
    rewrite Znth_vwords by lia.
    forward.
    rewrite !add64_repr.
    set (s := c + Znth (Zlength r) a + Znth (Zlength r) b).
    assert (Hs : 0 <= s < 2 ^ 64) by (unfold s; rep_lia).
    forward.
    forward.
    rewrite and_mask32 by lia.
    Exists (r ++ [s mod 2 ^ 32]) (s / 2 ^ 32).
    entailer!.
    + assert (Hd := Z.div_mod s (2 ^ 32) ltac:(lia)).
      assert (Hm := Z.mod_pos_bound s (2 ^ 32) ltac:(lia)).
      repeat split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      * apply Forall_app; split; [exact Hrl|constructor; [lia|constructor]].
      * apply Z.div_pos; lia.
      * assert (s / 2 ^ 32 < 2)
          by (apply Z.div_lt_upper_bound; unfold s; rep_lia); lia.
      * rewrite valZ_app; simpl Exp100.ExpNum.valZ.
        rewrite !valZ_sublist_succ by lia.
        unfold Exp100.ExpNum.limb_bits.
        replace (32 * (Zlength r + 1)) with (32 * Zlength r + 32) by lia.
        rewrite Z.pow_add_r by rep_lia.
        set (P := 2 ^ (32 * Zlength r)) in *.
        assert (E : P * s = P * c + P * Znth (Zlength r) a +
                            P * Znth (Zlength r) b)
          by (unfold s; ring).
        rewrite Hd in E at 1. nia.
      * rewrite shru32 by lia; reflexivity.
    + apply derives_refl'; f_equal. unfold vwords; list_solve.
  - Intros r c.
    rename H into Hr, H0 into Hrl, H1 into Hc, H2 into Hv.
    rewrite !sublist_same in Hv by lia.
    assert (c = 0).
    { pose proof (valZ_bounds r Hrl).
      unfold num_bits, Exp100.ExpNum.limb_bits in *. nia. }
    subst c.
    Exists r. unfold num. rewrite sublist_nil, app_nil_r. entailer!.
Qed.

Lemma body_num_sub : semax_body Vprog Gprog f_num_sub num_sub_spec.
Proof.
  start_function.
  rename H into Hla, H0 into Hlb, H1 into Ha, H2 into Hb, H3 into Hle.
  unfold num.
  forward.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z, EX r : list Z, EX c : Z,
     PROP (Zlength r = i; Forall limb r; 0 <= c <= 1;
           (valZ r - c * 2 ^ (limb_bits * i) =
              valZ (sublist 0 i a) - valZ (sublist 0 i b))%Z)
     LOCAL (temp _c (Vlong (Int64.repr c)); temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL) (vwords (r ++ sublist i NL a)) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - Exists (@nil Z) 0. entailer!.
    rewrite sublist_same by lia. cancel.
  - Intros.
    rename H0 into Hr, H1 into Hrl, H2 into Hc, H3 into Hv. subst i.
    assert (Lx : limb (Znth (Zlength r) a)) by (apply Forall_Znth; auto; lia).
    assert (Ly : limb (Znth (Zlength r) b)) by (apply Forall_Znth; auto; lia).
    unfold Exp100.ExpNum.limb, Exp100.ExpNum.limb_bits in *.
    assert (Ex : @Znth val Vundef (Zlength r)
                   (vwords (r ++ sublist (Zlength r) NL a)) =
                 Vlong (Int64.repr (Znth (Zlength r) a))).
    { unfold vwords. rewrite Znth_map, Znth_map. f_equal. f_equal.
      rewrite Znth_app2 by lia. replace (Zlength r - Zlength r) with 0 by lia.
      rewrite Znth_sublist by lia. f_equal; lia.
      all: rewrite ?Zlength_map, Zlength_app, Zlength_sublist; lia. }
    forward.
    { rewrite Znth_vwords by lia. entailer!. }
    rewrite Znth_vwords by lia.
    forward.
    forward.
    { rewrite Ex. entailer!. }
    rewrite Ex, add64_repr.
    set (t := Znth (Zlength r) b + c).
    set (x := Znth (Zlength r) a) in *.
    remember (if x >=? t then 0 else 1) as d eqn:Ed.
    remember (x + d * 2 ^ 32 - t) as y eqn:Ey0.
    assert (Hy : 0 <= y < 2 ^ 32)
      by (subst y d; destruct (Z.geb_spec x t); unfold t in *; lia).
    forward_if
      (PROP () LOCAL (temp _c (Vlong (Int64.repr d)); temp _i
                      (Vint (Int.repr (Zlength r))); temp _a pa; temp _b pb)
       SEP (data_at sha (tarray tulong NL)
              (vwords ((r ++ [y]) ++ sublist (Zlength r + 1) NL a)) pa;
            data_at shb (tarray tulong NL) (vwords b) pb)).
    + assert (Hd : d = 0) by (rewrite Ed; destruct (Z.geb_spec x t); lia).
      assert (Ey : y = x - t) by (rewrite Ey0, Hd; ring).
      forward.
      { rewrite Ex. entailer!. }
      rewrite Ex.
      forward.
      forward.
      rewrite Hd, Ey.
      entailer!.
      apply derives_refl'; f_equal.
      unfold vwords; list_solve.
    + assert (Hd : d = 1) by (rewrite Ed; destruct (Z.geb_spec x t); lia).
      assert (Ey : y = x + 2 ^ 32 - t) by (rewrite Ey0, Hd; ring).
      forward.
      { rewrite Ex. entailer!. }
      rewrite Ex.
      forward.
      forward.
      rewrite Hd, Ey.
      entailer!.
      apply derives_refl'; f_equal.
      replace (x + (4294967295 + 1) - t) with (x + 2 ^ 32 - t) by lia.
      unfold vwords; list_solve.
    + assert (Hd : 0 <= d <= 1) by (rewrite Ed; destruct (x >=? t); lia).
      assert (Hk : y - d * 2 ^ 32 = x - t) by (rewrite Ey0; ring).
      clear Ed Ey0.
      Exists (r ++ [y]) d.
      entailer!.
      repeat split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      * apply Forall_app; split; [exact Hrl|constructor; [lia|constructor]].
      * rewrite valZ_app; simpl Exp100.ExpNum.valZ.
        rewrite !valZ_sublist_succ by lia.
        unfold Exp100.ExpNum.limb_bits.
        replace (32 * (Zlength r + 1)) with (32 * Zlength r + 32) by lia.
        rewrite Z.pow_add_r by rep_lia.
        set (P := 2 ^ (32 * Zlength r)) in *.
        unfold t, x in *.
        assert (E : P * (y - d * 2 ^ 32) = P * (Znth (Zlength r) a -
                      (Znth (Zlength r) b + c))) by (rewrite Hk; reflexivity).
        nia.
  - Intros r c.
    rename H into Hr, H0 into Hrl, H1 into Hc, H2 into Hv.
    rewrite !sublist_same in Hv by lia.
    assert (c = 0).
    { pose proof (valZ_bounds r Hrl).
      unfold Exp100.ExpNum.limb_bits in *. rewrite Hr in *. nia. }
    subst c.
    Exists r. unfold num. rewrite sublist_nil, app_nil_r. entailer!.
Qed.

Lemma body_num_mul_small :
  semax_body Vprog Gprog f_num_mul_small num_mul_small_spec.
Proof.
  start_function.
  rename H into Hla, H0 into Ha, H1 into Hw.
  unfold num.
  forward.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z, EX r : list Z, EX c : Z,
     PROP (Zlength r = i; Forall limb r; 0 <= c < 2 ^ limb_bits;
           (valZ r + c * 2 ^ (limb_bits * i) = valZ (sublist 0 i a) * w)%Z)
     LOCAL (temp _c (Vlong (Int64.repr c)); temp _p pp; temp _a pa;
            temp _w (Vlong (Int64.repr w)))
     SEP (data_at shp (tarray tulong NP)
            (vwords r ++ Zrepeat Vundef (NP - i)) pp;
          data_at sha (tarray tulong NL) (vwords a) pa)).
  - Exists (@nil Z) 0. entailer!.
    unfold Exp100.ExpNum.limb_bits; lia.
  - Intros.
    rename H0 into Hr, H1 into Hrl, H2 into Hc, H3 into Hv. subst i.
    assert (Lx : limb (Znth (Zlength r) a)) by (apply Forall_Znth; auto; lia).
    unfold Exp100.ExpNum.limb, Exp100.ExpNum.limb_bits in *.
    forward.
    { rewrite Znth_vwords by lia. entailer!. }
    rewrite Znth_vwords by lia.
    forward.
    rewrite mul64_repr, add64_repr.
    set (s := Znth (Zlength r) a * w + c).
    assert (Hs : 0 <= s < 2 ^ 64) by (unfold s; nia).
    forward.
    forward.
    rewrite and_mask32, shru32 by lia.
    Exists (r ++ [s mod 2 ^ 32]) (s / 2 ^ 32).
    entailer!.
    + assert (Hd := Z.div_mod s (2 ^ 32) ltac:(lia)).
      assert (Hm := Z.mod_pos_bound s (2 ^ 32) ltac:(lia)).
      repeat split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      * apply Forall_app; split; [exact Hrl|constructor; [lia|constructor]].
      * apply Z.div_pos; lia.
      * apply Z.div_lt_upper_bound; lia.
      * assert (Es : s = Znth (Zlength r) a * w + c) by reflexivity.
        clearbody s.
        set (q := s / 2 ^ 32) in *. set (m := s mod 2 ^ 32) in *.
        clearbody q m.
        rewrite valZ_app, !valZ_sublist_succ by lia.
        cbn [Exp100.ExpNum.valZ].
        unfold Exp100.ExpNum.limb_bits.
        replace (32 * (Zlength r + 1)) with (32 * Zlength r + 32) by lia.
        rewrite Z.pow_add_r by rep_lia.
        set (P := 2 ^ (32 * Zlength r)) in *.
        assert (E : P * s = P * c + P * Znth (Zlength r) a * w)
          by (rewrite Es; ring).
        rewrite Hd in E.
        rewrite Z.mul_add_distr_r, <- Hv. lia.
    + apply derives_refl'; f_equal. unfold vwords; list_solve.
  - Intros r c.
    rename H into Hr, H0 into Hrl, H1 into Hc, H2 into Hv.
    rewrite !sublist_same in Hv by lia.
    forward.
    Exists (r ++ [c]).
    entailer!.
    + unfold Exp100.ExpNum.limb, Exp100.ExpNum.limb_bits in *.
      repeat split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      * apply Forall_app; split; [exact Hrl|constructor; [lia|constructor]].
      * rewrite valZ_app, Hr; cbn [Exp100.ExpNum.valZ].
        unfold Exp100.ExpNum.limb_bits; lia.
    + apply derives_refl'; f_equal. unfold vwords; list_solve.
Qed.
