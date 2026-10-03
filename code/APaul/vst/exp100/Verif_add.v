Require Import VST.floyd.proofauto.
Require Import E.Limbs E.exp100_clight E.Common E.Spec.
Definition Gprog : funspecs := [num_add_spec].

Lemma and_mask z : 0 <= z < 2 ^ 64 ->
  Int64.and (Int64.repr z) (Int64.repr 4294967295) = Int64.repr (z mod 2 ^ 32).
Proof.
  intros Hz.
  change 4294967295 with (Z.ones 32).
  apply Int64.same_bits_eq; intros k Hk.
  rewrite Int64.bits_and by lia.
  rewrite !Int64.testbit_repr by lia.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_spec; reflexivity.
Qed.

Lemma shr32 z : 0 <= z < 2 ^ 64 ->
  Int64.shru (Int64.repr z) (Int64.repr 32) = Int64.repr (z / 2 ^ 32).
Proof.
  intros Hz.
  rewrite Int64.shru_div_two_p.
  rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
  reflexivity.
Qed.

Lemma body_num_add : semax_body Vprog Gprog f_num_add num_add_spec.
Proof.
  start_function.
  rename H into Hla, H0 into Hlb, H1 into Ha, H2 into Hb, H3 into Hfit.
  unfold num.
  forward.
  forward_for_simple_bound 6
    (EX i : Z, EX r : list Z, EX c : Z,
     PROP (Zlength r = i; Forall limb r; 0 <= c <= 1;
           (valL r + c * 2 ^ (lbits * i) =
              valL (sublist 0 i a) + valL (sublist 0 i b))%Z)
     LOCAL (temp _c (Vlong (Int64.repr c)); temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL) (vwords (r ++ sublist i NL a)) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - Exists (@nil Z) 0. entailer!.
    rewrite sublist_same by (unfold NL in *; lia). cancel.
  - Intros.
    rename H0 into Hr, H1 into Hrl, H2 into Hc, H3 into Hv. subst i.
    assert (Lx : limb (Znth (Zlength r) a)) by (apply Forall_Znth; auto; unfold NL in *; lia).
    assert (Ly : limb (Znth (Zlength r) b)) by (apply Forall_Znth; auto; unfold NL in *; lia).
    unfold limb, lbits in *.
    assert (Ex : @Znth val Vundef (Zlength r) (vwords (r ++ sublist (Zlength r) NL a)) = Vlong (Int64.repr (Znth (Zlength r) a))).
    { unfold vwords. rewrite Znth_map, Znth_map. f_equal. f_equal.
      rewrite Znth_app2 by lia. replace (Zlength r - Zlength r) with 0 by lia.
      rewrite Znth_sublist by (unfold NL in *; lia). f_equal; lia.
      all: unfold NL in *; rewrite ?Zlength_map, Zlength_app, Zlength_sublist; lia. }
    forward.
    { rewrite Ex. entailer!. }
    rewrite Ex.
    forward.
    { rewrite Znth_vwords by (unfold NL in *; lia). entailer!. }
    rewrite Znth_vwords by (unfold NL in *; lia).
    forward.
    rewrite !add64_repr.
    set (s := c + Znth (Zlength r) a + Znth (Zlength r) b).
    assert (Hs : 0 <= s < 2 ^ 64) by (unfold s; rep_lia).
    forward.
    forward.
    rewrite and_mask by lia.
    Exists (r ++ [s mod 2 ^ 32]) (s / 2 ^ 32).
    entailer!.
    + assert (Hd := Z.div_mod s (2 ^ 32) ltac:(lia)).
      assert (Hm := Z.mod_pos_bound s (2 ^ 32) ltac:(lia)).
      repeat split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil; lia.
      * apply Forall_app; split; [exact Hrl|constructor; [lia|constructor]].
      * apply Z.div_pos; lia.
      * assert (s / 2 ^ 32 < 2) by (apply Z.div_lt_upper_bound; unfold s; rep_lia); lia.
      * rewrite valL_app; simpl valL. unfold lbits in *.
        rewrite !valL_sublist_succ by (unfold NL in *; lia).
        unfold lbits.
        replace (32 * (Zlength r + 1)) with (32 * Zlength r + 32) by lia.
        rewrite Z.pow_add_r by rep_lia.
        set (P := 2 ^ (32 * Zlength r)) in *.
        assert (E : P * s = P * c + P * Znth (Zlength r) a + P * Znth (Zlength r) b)
          by (unfold s; ring).
        rewrite Hd in E at 1. nia.
      * rewrite shr32 by lia; reflexivity.
    + apply derives_refl'; f_equal. unfold vwords, NL in *; list_solve.
  - Intros r c.
    rename H into Hr, H0 into Hrl, H1 into Hc, H2 into Hv.
    unfold NL in *.
    rewrite !sublist_same in Hv by lia.
    assert (c = 0).
    { unfold lbits in *. assert (0 <= valL r).
      { clear - Hrl. induction Hrl; simpl; unfold limb, lbits in *; nia. }
      nia. }
    subst c.
    Exists r. unfold num, NL. rewrite sublist_nil, app_nil_r. entailer!.
Qed.
