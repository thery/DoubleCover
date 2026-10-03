(** * Task T2: num_lt, num_bitlen, num_pow2, num_low, num_scale *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.
Require Exp100.ExpModel.

(** ** Helpers *)

(* Signed division of non-negative ints. *)
Lemma divs_repr a b : 0 <= a <= Int.max_signed -> 0 < b <= Int.max_signed ->
  Int.divs (Int.repr a) (Int.repr b) = Int.repr (a / b).
Proof.
  intros Ha Hb; unfold Int.divs.
  rewrite !Int.signed_repr by rep_lia.
  rewrite Zquot.Zquot_Zdiv_pos by lia; reflexivity.
Qed.

(* A shift of one is a power of two. *)
Lemma shl1 m : 0 <= m < 64 ->
  Int64.shl (Int64.repr 1) (Int64.repr m) = Int64.repr (2 ^ m).
Proof.
  intros Hm; rewrite Int64.shl_mul_two_p.
  rewrite Int64.unsigned_repr by rep_lia.
  rewrite two_p_equiv, Int64.mul_commut, Int64.mul_one; reflexivity.
Qed.

(* The load of cell i. *)
Lemma Znth_vwords' xs k : 0 <= k < Zlength xs ->
  @Znth val Vundef k (vwords xs) = Vlong (Int64.repr (Znth k xs)).
Proof. apply Znth_vwords. Qed.

(* A left shift is a product. *)
Lemma shl_mul x m : 0 <= m < 64 ->
  Int64.shl (Int64.repr x) (Int64.repr m) = Int64.repr (x * 2 ^ m).
Proof.
  intros Hm; rewrite Int64.shl_mul_two_p, Int64.unsigned_repr by rep_lia.
  rewrite two_p_equiv, mul64_repr; reflexivity.
Qed.

(* The m low bits of a word. *)
Lemma and_low z m : 0 <= z < 2 ^ 64 -> 0 <= m < 64 ->
  Int64.and (Int64.repr z) (Int64.repr (2 ^ m - 1)) =
  Int64.repr (z mod 2 ^ m).
Proof.
  intros Hz Hm.
  replace (2 ^ m - 1) with (Z.ones m) by (rewrite Z.ones_equiv; lia).
  apply Int64.same_bits_eq; intros k Hk.
  rewrite Int64.bits_and by lia.
  rewrite !Int64.testbit_repr by lia.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_spec; reflexivity.
Qed.

(* Zeros add nothing. *)
Lemma valZ_zeros n : valZ (Zrepeat 0 n) = 0.
Proof.
  unfold Zrepeat; induction (Z.to_nat n) as [|k IH]; simpl; lia.
Qed.

Lemma valZ_app3 a w c : valZ (a ++ w :: c) =
  valZ a + 2 ^ (limb_bits * Zlength a) * (w + 2 ^ limb_bits * valZ c).
Proof. rewrite valZ_app; reflexivity. Qed.

(* Dividing by 32 does not overflow. *)
Ltac no_ovf := try intro;
  match goal with X : _ /\ Int.repr 32 = Int.mone |- _ =>
    destruct X as [_ X]; apply (f_equal Int.unsigned) in X;
    vm_compute in X; discriminate end.

(* A shift by f mod 32 is defined. *)
Ltac shift_ok := rewrite ?mods_repr by rep_lia; repeat split; try no_ovf;
  change (Int.unsigned Int64.iwordsize') with 64;
  try rewrite Int.unsigned_repr by rep_lia; rep_lia.

Lemma limb_zeros n : Forall limb (Zrepeat 0 n).
Proof.
  apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x.
  unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits; lia.
Qed.

(* One word at q in a row of zeros. *)
Lemma upd_zeros n q w : 0 <= q < n ->
  upd_Znth q (Zrepeat 0 n) w = Zrepeat 0 q ++ w :: Zrepeat 0 (n - q - 1).
Proof. intros Hq; list_solve. Qed.

Lemma valZ_one q w r : 0 <= q ->
  valZ (Zrepeat 0 q ++ w :: Zrepeat 0 r) = 2 ^ (limb_bits * q) * w.
Proof.
  intros Hq; rewrite valZ_app3, !valZ_zeros, Zlength_Zrepeat by lia; ring.
Qed.

Lemma limb_one q w r : limb w -> Forall limb (Zrepeat 0 q ++ w :: Zrepeat 0 r).
Proof.
  intros Hw; apply Forall_app; split; [|constructor]; auto using limb_zeros.
Qed.

(** ** num_lt *)

(* A number split at limb i. *)
Lemma valZ_split a i : 0 <= i < Zlength a ->
  valZ a = valZ (sublist 0 i a) + 2 ^ (limb_bits * i) *
    (Znth i a + 2 ^ limb_bits * valZ (sublist (i + 1) (Zlength a) a)).
Proof.
  intros Hi.
  assert (Ea : a = sublist 0 i a ++ Znth i a ::
                   sublist (i + 1) (Zlength a) a) by list_solve.
  rewrite Ea at 1; rewrite valZ_app3, Zlength_sublist by lia.
  do 3 f_equal; lia.
Qed.

(* Equal top limbs, then a smaller limb at i: a smaller number. *)
Lemma valZ_lt_top a b i : Zlength a = Zlength b ->
  Forall limb a -> Forall limb b -> 0 <= i < Zlength a ->
  sublist (i + 1) (Zlength a) a = sublist (i + 1) (Zlength b) b ->
  Znth i a < Znth i b -> valZ a < valZ b.
Proof.
  intros Hl Ha Hb Hi Ht Hab.
  rewrite (valZ_split a i), (valZ_split b i) by lia; rewrite Ht.
  assert (HA := valZ_bounds (sublist 0 i a)
                  ltac:(apply Forall_sublist; auto)).
  assert (HB := valZ_bounds (sublist 0 i b)
                  ltac:(apply Forall_sublist; auto)).
  rewrite Zlength_sublist in HA, HB by lia.
  replace (i - 0) with i in HA, HB by lia.
  set (P := 2 ^ (limb_bits * i)) in *.
  set (T := 2 ^ limb_bits * valZ (sublist (i + 1) (Zlength b) b)).
  nia.
Qed.

Lemma body_num_lt : semax_body Vprog Gprog f_num_lt num_lt_spec.
Proof.
  start_function.
  rename H into Hla, H0 into Hlb, H1 into Ha, H2 into Hb.
  unfold num.
  forward_loop
    (EX i : Z,
     PROP (-1 <= i < NL; sublist (i + 1) NL a = sublist (i + 1) NL b)
     LOCAL (temp _i (Vint (Int.repr i)); temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL) (vwords a) pa;
          data_at shb (tarray tulong NL) (vwords b) pb))
  continue:
    (EX i : Z,
     PROP (0 <= i < NL; sublist i NL a = sublist i NL b)
     LOCAL (temp _i (Vint (Int.repr i)); temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL) (vwords a) pa;
          data_at shb (tarray tulong NL) (vwords b) pb))
  break:
    (PROP (a = b)
     LOCAL (temp _a pa; temp _b pb)
     SEP (data_at sha (tarray tulong NL) (vwords a) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - forward. Exists 5. entailer!. rewrite !sublist_nil; auto.
  - Intros i. rename H into Hi, H0 into Ht.
    forward_if.
    +
      assert (Hai : limb (Znth i a)) by (apply Forall_Znth; auto; lia).
      assert (Hbi : limb (Znth i b)) by (apply Forall_Znth; auto; lia).
      unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits in Hai, Hbi.
      forward.
      { entailer!. rewrite Znth_vwords' by lia; exact I. }
      forward.
      { entailer!. rewrite Znth_vwords' by lia; exact I. }
      rewrite !Znth_vwords' by lia.
      forward_if.
      * forward.
        assert (valZ a < valZ b)
          by (apply (valZ_lt_top a b i); auto; try lia;
              rewrite Hla, Hlb; auto).
        entailer!.
        destruct (Z.ltb_spec (valZ a) (valZ b)); [auto|lia].
      * forward.
        { entailer!. rewrite Znth_vwords' by lia; exact I. }
        forward.
        { entailer!. rewrite Znth_vwords' by lia; exact I. }
        rewrite !Znth_vwords' by lia.
        forward_if.
        -- forward.
           assert (valZ b < valZ a)
             by (apply (valZ_lt_top b a i); auto; try lia;
                 rewrite Hla, Hlb; auto).
           entailer!.
           destruct (Z.ltb_spec (valZ a) (valZ b)); [lia|auto].
        -- assert (Eab : Znth i a = Znth i b) by lia.
           forward. Exists i. entailer!.
           rewrite (sublist_split i (i + 1) 6 a), !sublist_len_1, Ht
             by lia.
           rewrite (sublist_split i (i + 1) 6 b), !sublist_len_1, Eab
             by lia; reflexivity.
    + forward. entailer!.
      assert (i = -1) by lia; subst i.
      rewrite !sublist_same in Ht by lia; auto.
  - Intros i. forward. Exists (i - 1). entailer!.
    replace (i - 1 + 1) with i by lia; auto.
  - forward.
    entailer!.
    rewrite Z.ltb_irrefl; auto.
Qed.

(** ** num_bitlen *)

Notation bitlen := Exp100.ExpModel.bitlen.

(* Bit k of a word. *)
Lemma bit_word w k : 0 <= w < 2 ^ 64 -> 0 <= k < 64 ->
  Int64.and (Int64.shru (Int64.repr w) (Int64.repr k)) (Int64.repr 1) =
  Int64.repr ((w / 2 ^ k) mod 2).
Proof.
  intros Hw Hk.
  rewrite Int64.shru_div_two_p, !Int64.unsigned_repr, two_p_equiv
    by rep_lia.
  assert (0 <= w / 2 ^ k <= w)
    by (split; [apply Z.div_pos|apply Z.div_le_upper_bound]; try lia;
        assert (1 <= 2 ^ k) by (change 1 with (2 ^ 0);
          apply Z.pow_le_mono_r; lia); nia).
  change (Int64.repr 1) with (Int64.repr (2 ^ 1 - 1)).
  rewrite and_low by lia; reflexivity.
Qed.

(* A number of n bits plus 2^n has n + 1 bits. *)
Lemma bitlen_top Y n : 0 <= n -> 0 <= Y < 2 ^ n -> bitlen (Y + 2 ^ n) = n + 1.
Proof.
  intros Hn HY; unfold Exp100.ExpModel.bitlen.
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  destruct (Z.leb_spec (Y + 2 ^ n) 0); [lia|].
  rewrite (Z.log2_unique (Y + 2 ^ n) n); auto.
  rewrite Z.pow_succ_r by lia; lia.
Qed.

(* Scanning bit k of limb i. *)
Lemma bitlen_step X i w k : 0 <= i -> 0 <= k -> 0 <= X < 2 ^ (32 * i) ->
  bitlen (X + 2 ^ (32 * i) * (w mod 2 ^ (k + 1))) =
  if (w / 2 ^ k) mod 2 =? 0 then bitlen (X + 2 ^ (32 * i) * (w mod 2 ^ k))
  else 32 * i + k + 1.
Proof.
  intros Hi Hk HX.
  assert (Hk2 : 0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
  rewrite Z.pow_add_r, Z.pow_1_r, Z.rem_mul_r by lia.
  assert (Hb := Z.mod_pos_bound (w / 2 ^ k) 2 ltac:(lia)).
  assert (Hr := Z.mod_pos_bound w (2 ^ k) Hk2).
  destruct (Z.eqb_spec ((w / 2 ^ k) mod 2) 0) as [E|E].
  - rewrite E; f_equal; ring.
  - replace ((w / 2 ^ k) mod 2) with 1 by lia.
    replace (X + 2 ^ (32 * i) * (w mod 2 ^ k + 2 ^ k * 1)) with
      (X + 2 ^ (32 * i) * (w mod 2 ^ k) + 2 ^ (32 * i + k))
      by (rewrite Z.pow_add_r by lia; ring).
    apply bitlen_top; [lia|].
    rewrite Z.pow_add_r by lia; nia.
Qed.

Lemma body_num_bitlen : semax_body Vprog Gprog f_num_bitlen num_bitlen_spec.
Proof.
  start_function.
  rename H into Hl, H0 into Ha.
  unfold num.
  forward.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z,
     PROP ()
     LOCAL (temp _b (Vint (Int.repr (bitlen (valZ (sublist 0 i a)))));
            temp _a pa)
     SEP (data_at sha (tarray tulong NL) (vwords a) pa)).
  - entailer!.
  - assert (Hai : limb (Znth i a)) by (apply Forall_Znth; auto; lia).
    unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits in Hai.
    assert (HX := valZ_bounds (sublist 0 i a)
                    ltac:(apply Forall_sublist; auto)).
    rewrite Zlength_sublist in HX by lia; replace (i - 0) with i in HX by lia.
    unfold Exp100.ExpConsts.limb_bits in HX.
    forward_for_simple_bound 32   (* bits of a limb *)
      (EX k : Z,
       PROP ()
       LOCAL (temp _b (Vint (Int.repr (bitlen (valZ (sublist 0 i a) +
                2 ^ (32 * i) * (Znth i a mod 2 ^ k)))));
              temp _i (Vint (Int.repr i)); temp _a pa)
       SEP (data_at sha (tarray tulong NL) (vwords a) pa)).
    + entailer!.
      rewrite Z.pow_0_r, Z.mod_1_r, Z.mul_0_r, Z.add_0_r; reflexivity.
    + rename i0 into k.
      forward.
      { entailer!. rewrite Znth_vwords' by lia; exact I. }
      rewrite Znth_vwords' by lia.
      forward_if.
      { entailer!; shift_ok. }
      * rewrite Int.unsigned_repr, bit_word in H1 by rep_lia.
        assert (Hbit : (Znth i a / 2 ^ k) mod 2 <> 0)
          by (intro E; apply H1; rewrite E; reflexivity).
        forward.
        entailer!.
        rewrite bitlen_step by lia.
        destruct (Z.eqb_spec ((Znth i a / 2 ^ k) mod 2) 0); [lia|].
        reflexivity.
      * rewrite Int.unsigned_repr, bit_word in H1 by rep_lia.
        assert (Hbit := Z.mod_pos_bound (Znth i a / 2 ^ k) 2 ltac:(lia)).
        apply (f_equal Int64.unsigned) in H1.
        rewrite Int64.unsigned_repr in H1 by rep_lia.
        forward.
        entailer!.
        rewrite bitlen_step by lia.
        rewrite H1, Z.eqb_refl; reflexivity.
    + entailer!.
      rewrite Z.mod_small, valZ_sublist_succ by lia; reflexivity.
  - forward.
    entailer!.
    rewrite sublist_same by lia; reflexivity.
Qed.

(** ** num_pow2 *)

Lemma body_num_pow2 : semax_body Vprog Gprog f_num_pow2 num_pow2_spec.
Proof.
  start_function.
  rename H into Hf.
  unfold num_bits, Exp100.ExpConsts.limb_bits in Hf.
  forward_call (sha, pa).
  unfold num.
  assert (Hq : 0 <= f / 32 < 6) by (split; [apply Z.div_pos|
    apply Z.div_lt_upper_bound]; lia).
  assert (Hm : 0 <= f mod 32 < 32) by (apply Z.mod_pos_bound; lia).
  forward.
  all: rewrite ?divs_repr, ?mods_repr by rep_lia.
  { entailer!; shift_ok. }
  { entailer!. }
  rewrite Int.signed_repr, Int.unsigned_repr, Int.signed_repr by rep_lia.
  rewrite shl1 by lia.
  rewrite upd_vwords by (rewrite Zlength_Zrepeat; lia).
  assert (Hp : 0 < 2 ^ (f mod 32) < 2 ^ 32) by
    (split; [apply Z.pow_pos_nonneg|apply Z.pow_lt_mono_r]; lia).
  rewrite Int64.unsigned_repr by rep_lia.
  Exists (upd_Znth (f / 32) (Zrepeat 0 6) (2 ^ (f mod 32))).
  unfold num; entailer!.
  rewrite upd_zeros by lia.
  split3; [list_solve|apply limb_one;
    unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits; lia|].
  rewrite valZ_one, Exp100.ExpModel.pow2E by lia.
  unfold Exp100.ExpConsts.limb_bits; rewrite <- Z.pow_add_r by lia.
  f_equal; pose proof (Z.div_mod f 32); lia.
Qed.

(** ** num_low *)

(* (A + 2^n B) mod 2^(n+m), for A < 2^n. *)
Lemma mod_shift A B n m : 0 <= n -> 0 <= m -> 0 <= A < 2 ^ n ->
  (A + 2 ^ n * B) mod 2 ^ (n + m) = A + 2 ^ n * (B mod 2 ^ m).
Proof.
  intros Hn Hm HA.
  assert (Hp : 0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (HB := Z.mod_pos_bound B (2 ^ m) Hp).
  symmetry; apply Z.mod_unique with (B / 2 ^ m); [left|].
  - rewrite Z.pow_add_r by lia; nia.
  - rewrite Z.pow_add_r by lia.
    rewrite (Z.div_mod B (2 ^ m)) at 1 by lia; ring.
Qed.

(* The limbs of b mod 2^(32 q + m). *)
Definition low_list (b : list Z) (q m : Z) : list Z :=
  sublist 0 q b ++ Znth q b mod 2 ^ m :: Zrepeat 0 (NL - q - 1).

Lemma valZ_low_list b q m : Zlength b = NL -> Forall limb b ->
  0 <= q < NL -> 0 <= m < limb_bits ->
  valZ (low_list b q m) = valZ b mod 2 ^ (limb_bits * q + m).
Proof.
  intros Hl Hb Hq Hm; unfold low_list.
  rewrite valZ_app3, valZ_zeros, Zlength_sublist by lia.
  assert (Eb : b = sublist 0 q b ++ Znth q b :: sublist (q + 1) NL b)
    by list_solve.
  assert (Ev : valZ b = valZ (sublist 0 q b) + 2 ^ (limb_bits * q) *
                 (Znth q b + 2 ^ limb_bits * valZ (sublist (q + 1) NL b))).
  { rewrite Eb at 1; rewrite valZ_app3, Zlength_sublist by lia.
    do 3 f_equal; lia. }
  rewrite Ev; replace (q - 0) with q by lia.
  assert (Hs := valZ_bounds (sublist 0 q b)
                  ltac:(apply Forall_sublist; auto)).
  rewrite Zlength_sublist in Hs by lia; replace (q - 0) with q in Hs by lia.
  unfold Exp100.ExpConsts.limb_bits in *.
  rewrite mod_shift by lia.
  rewrite Z.mul_0_r, Z.add_0_r; f_equal; f_equal.
  rewrite <- Z.add_mod_idemp_r, Z.mul_comm by (apply Z.pow_nonzero; lia).
  replace (2 ^ 32) with (2 ^ (32 - m) * 2 ^ m)
    by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
  rewrite Z.mul_assoc, Z.mod_mul, Z.add_0_r by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.

Lemma Zlength_low_list b q m : Zlength b = NL -> 0 <= q < NL ->
  Zlength (low_list b q m) = NL.
Proof. intros; unfold low_list; list_solve. Qed.

Lemma Znth_low_list b q m i : Zlength b = NL -> 0 <= q < NL ->
  0 <= i < NL ->
  Znth i (low_list b q m) =
  if i <? q then Znth i b else if i =? q then Znth q b mod 2 ^ m else 0.
Proof.
  intros Hb Hq Hi; unfold low_list.
  destruct (Z.ltb_spec i q); [list_solve|].
  destruct (Z.eqb_spec i q); [subst; list_solve|list_solve].
Qed.

(* Writing cell i of a list filled up to i. *)
Lemma upd_step L i x : Zlength L = NL -> 0 <= i < NL -> Znth i L = x ->
  upd_Znth i (vwords (sublist 0 i L) ++ Zrepeat Vundef (NL - i))
    (Vlong (Int64.repr x)) =
  vwords (sublist 0 (i + 1) L) ++ Zrepeat Vundef (NL - (i + 1)).
Proof. intros Hl Hi Hx; subst x; unfold vwords; list_solve. Qed.

Lemma body_num_low : semax_body Vprog Gprog f_num_low num_low_spec.
Proof.
  start_function.
  rename H into Hl, H0 into Hb, H1 into Hf.
  unfold num_bits, Exp100.ExpConsts.limb_bits in Hf.
  assert (Hq : 0 <= f / 32 < 6) by (split; [apply Z.div_pos|
    apply Z.div_lt_upper_bound]; lia).
  assert (Hm : 0 <= f mod 32 < 32) by (apply Z.mod_pos_bound; lia).
  unfold num.
  forward_for_simple_bound 6   (* NL: a notation is refused here *)
    (EX i : Z,
     PROP ()
     LOCAL (temp _a pa; temp _b pb; temp _f (Vint (Int.repr f)))
     SEP (data_at sha (tarray tulong NL)
            (vwords (sublist 0 i (low_list b (f / 32) (f mod 32))) ++
             Zrepeat Vundef (NL - i)) pa;
          data_at shb (tarray tulong NL) (vwords b) pb)).
  - entailer!.
  - assert (Hbi : limb (Znth i b)) by (apply Forall_Znth; auto; lia).
    unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits in Hbi.
    forward_if.
    { entailer!; no_ovf. }
    + rewrite divs_repr, Int.signed_repr in H0 by rep_lia.
      forward.
      { entailer!. rewrite Znth_vwords' by lia; exact I. }
      rewrite Znth_vwords' by lia.
      forward.
      entailer!.
      rewrite upd_step; auto; [rewrite Zlength_low_list; auto; lia|].
      rewrite Znth_low_list by lia.
      destruct (Z.ltb_spec i (f / 32)); [auto|lia].
    + rewrite divs_repr, Int.signed_repr in H0 by rep_lia.
      forward_if.
      { entailer!; no_ovf. }
      * forward.
        { entailer!. rewrite Znth_vwords' by lia; exact I. }
        rewrite Znth_vwords' by lia.
        forward.
        { entailer!; shift_ok. }
        rewrite divs_repr in H1 by rep_lia.
        apply repr_inj_signed in H1; [|rep_lia|rep_lia]; subst i.
        rewrite mods_repr, Int.unsigned_repr, !Int.signed_repr by rep_lia.
        rewrite shl1, sub64_repr, and_low by lia.
        entailer!.
        rewrite upd_step; auto; [rewrite Zlength_low_list; auto; lia|].
        rewrite Znth_low_list by lia.
        rewrite Z.ltb_irrefl, Z.eqb_refl; reflexivity.
      * rewrite divs_repr in H1 by rep_lia.
        assert (i <> f / 32) by (intro E; apply H1; rewrite E; reflexivity).
        forward.
        entailer!.
        change (Int64.repr (Int.signed (Int.repr 0))) with (Int64.repr 0).
        rewrite upd_step; auto; [rewrite Zlength_low_list; auto; lia|].
        rewrite Znth_low_list by lia.
        destruct (Z.ltb_spec i (f / 32)); [lia|].
        destruct (Z.eqb_spec i (f / 32)); [lia|reflexivity].
  - Exists (low_list b (f / 32) (f mod 32)).
    rewrite sublist_same, Zrepeat_0, app_nil_r
      by (rewrite ?Zlength_low_list; auto; lia).
    unfold num; entailer!.
    split3.
    + apply Zlength_low_list; auto; lia.
    + unfold low_list; apply Forall_app; split;
        [apply Forall_sublist; auto|constructor; [|apply limb_zeros]].
      assert (Hp : 0 < 2 ^ (f mod 32) <= 2 ^ 32) by
        (split; [apply Z.pow_pos_nonneg|apply Z.pow_le_mono_r]; lia).
      assert (Hr := Z.mod_pos_bound (Znth (f / 32) b) (2 ^ (f mod 32))).
      unfold Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits; lia.
    + rewrite Exp100.ExpModel.lowE, valZ_low_list by
        (auto; unfold Exp100.ExpConsts.limb_bits; lia).
      unfold Exp100.ExpConsts.limb_bits.
      f_equal; f_equal; pose proof (Z.div_mod f 32); lia.
Qed.

(** ** num_scale *)

(* Three words written at q, q + 1, q + 2 in a row of zeros. *)
Lemma upd3_zeros q x0 x1 x2 : 0 <= q <= NL - 3 ->
  upd_Znth (q + 2)
    (upd_Znth (q + 1)
       (upd_Znth q (vwords (Zrepeat 0 NL)) (Vlong (Int64.repr x0)))
       (Vlong (Int64.repr x1)))
    (Vlong (Int64.repr x2)) =
  vwords (Zrepeat 0 q ++ [x0; x1; x2] ++ Zrepeat 0 (NL - 3 - q)).
Proof. intros Hq; unfold vwords; list_solve. Qed.

Lemma body_num_scale : semax_body Vprog Gprog f_num_scale num_scale_spec.
Proof.
  start_function.
  rename H into Hv, H0 into He.
  unfold mant_bits, scale_emax in Hv, He.
  forward_call (sha, pa).
  unfold num.
  forward_if.
  - forward_if
      (PROP ()
       LOCAL (temp _v (Vlong (Int64.repr (v / 2 ^ (- e))));
              temp _a pa; temp _e (Vint (Int.repr e)))
       SEP (data_at sha (tarray tulong NL) (vwords (Zrepeat 0 NL)) pa)).
    + rewrite Int.neg_repr, Int.signed_repr in H0 by rep_lia.
      forward.
      { entailer!. change (Int.unsigned Int64.iwordsize') with 64.
        change (Int.signed Int.zero) with 0; rep_lia. }
      entailer!.
      rewrite Int64.shru_div_two_p, !Int64.unsigned_repr, two_p_equiv
        by rep_lia.
      reflexivity.
    + rewrite Int.neg_repr, Int.signed_repr in H0 by rep_lia.
      forward. entailer!.
      rewrite Z.div_small; auto.
      split; [lia|].
      apply Z.lt_le_trans with (2 ^ 53); [lia|apply Z.pow_le_mono_r; lia].
    + assert (Hp : 1 <= 2 ^ (- e))
        by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
      set (w := v / 2 ^ (- e)).
      assert (Hw : 0 <= w < 2 ^ 53).
      { split; [apply Z.div_pos; lia|].
        apply Z.le_lt_trans with v; [apply Z.div_le_upper_bound|]; nia. }
      forward.
      forward.
      rewrite and_mask32, shru32 by rep_lia.
      assert (Hd := Z.div_mod w (2 ^ 32) ltac:(lia)).
      assert (Hm := Z.mod_pos_bound w (2 ^ 32) ltac:(lia)).
      assert (Hq : 0 <= w / 2 ^ 32 < 2 ^ 32)
        by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
      Exists [w mod 2 ^ 32; w / 2 ^ 32; 0; 0; 0; 0].
      unfold num; entailer!.
      + split.
        * repeat constructor; unfold Exp100.ExpConsts.limb,
            Exp100.ExpConsts.limb_bits; lia.
        * rewrite Exp100.ExpModel.scaleE.
          destruct (Z.leb_spec 0 e); [lia|].
          cbn [Exp100.ExpConsts.valZ]; unfold Exp100.ExpConsts.limb_bits.
          lia.
  - assert (Hq : 0 <= e / 32 < 4) by (split; [apply Z.div_pos|
      apply Z.div_lt_upper_bound]; lia).
    assert (Hm : 0 <= e mod 32 < 32) by (apply Z.mod_pos_bound; lia).
    forward.
    { entailer!; no_ovf. }
    rewrite divs_repr by rep_lia.
    forward.
    { entailer!; no_ovf. }
    rewrite mods_repr by rep_lia.
    forward.
    { entailer!; shift_ok. }
    forward.
    { entailer!; shift_ok. }
    rewrite !Int.unsigned_repr by rep_lia.
    rewrite and_mask32, shru32, !shl_mul by rep_lia.
    assert (Hp : 1 <= 2 ^ (e mod 32) <= 2 ^ 31)
      by (split; [change 1 with (2 ^ 0)|]; apply Z.pow_le_mono_r; lia).
    assert (Hv0 := Z.mod_pos_bound v (2 ^ 32) ltac:(lia)).
    assert (Hv1 : 0 <= v / 2 ^ 32 < 2 ^ 21)
      by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
    assert (Hlo : 0 <= v mod 2 ^ 32 * 2 ^ (e mod 32) < 2 ^ 63) by nia.
    assert (Hhi : 0 <= v / 2 ^ 32 * 2 ^ (e mod 32) < 2 ^ 52) by nia.
    assert (Ee := Z.div_mod e 32 ltac:(lia)).
    remember (e / 32) as q eqn:Eq; remember (e mod 32) as m eqn:Em.
    remember (v mod 2 ^ 32 * 2 ^ m) as lo eqn:Elo.
    remember (v / 2 ^ 32 * 2 ^ m) as hi eqn:Ehi.
    forward.
    rewrite and_mask32 by rep_lia.
    forward.
    rewrite Int.unsigned_repr, shru32, add64_repr by rep_lia.
    assert (Hlh : 0 <= lo / 2 ^ 32 < 2 ^ 31)
      by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
    remember (hi + lo / 2 ^ 32) as h2 eqn:Eh2.
    forward.
    rewrite and_mask32 by rep_lia.
    forward.
    rewrite Int.unsigned_repr, shru32 by rep_lia.
    rewrite upd3_zeros by lia.
    assert (Hh2 : 0 <= h2 / 2 ^ 32 < 2 ^ 32)
      by (split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; lia).
    assert (Hd0 := Z.div_mod lo (2 ^ 32) ltac:(lia)).
    assert (Hd1 := Z.div_mod h2 (2 ^ 32) ltac:(lia)).
    assert (Hd2 := Z.div_mod v (2 ^ 32) ltac:(lia)).
    assert (Hm0 := Z.mod_pos_bound lo (2 ^ 32) ltac:(lia)).
    assert (Hm1 := Z.mod_pos_bound h2 (2 ^ 32) ltac:(lia)).
    assert (Ev : lo mod 2 ^ 32 + 2 ^ 32 * (h2 mod 2 ^ 32 +
                   2 ^ 32 * (h2 / 2 ^ 32)) = v * 2 ^ m).
    { replace (h2 mod 2 ^ 32 + 2 ^ 32 * (h2 / 2 ^ 32)) with h2 by lia.
      rewrite Eh2.
      replace (lo mod 2 ^ 32 + 2 ^ 32 * (hi + lo / 2 ^ 32))
        with (lo + 2 ^ 32 * hi) by lia.
      rewrite Elo, Ehi.
      transitivity ((2 ^ 32 * (v / 2 ^ 32) + v mod 2 ^ 32) * 2 ^ m);
        [ring|rewrite <- Hd2; reflexivity]. }
    Exists (Zrepeat 0 q ++ [lo mod 2 ^ 32; h2 mod 2 ^ 32; h2 / 2 ^ 32] ++
            Zrepeat 0 (NL - 3 - q)).
    unfold num; entailer!.
    split3.
    + list_solve.
    + apply Forall_app; split; [apply limb_zeros|].
      apply Forall_app; split; [|apply limb_zeros].
      repeat constructor; unfold Exp100.ExpConsts.limb,
        Exp100.ExpConsts.limb_bits; lia.
    + rewrite valZ_app, valZ_app, !valZ_zeros, Zlength_Zrepeat by lia.
      cbn [Exp100.ExpConsts.valZ]; unfold Exp100.ExpConsts.limb_bits.
      rewrite Exp100.ExpModel.scaleE.
      rewrite !Z.mul_0_r, !Z.add_0_r, Z.add_0_l, Ev.
      destruct (Z.leb_spec 0 (32 * q + m)); [|lia].
      rewrite Z.pow_add_r by lia; ring.
Qed.
