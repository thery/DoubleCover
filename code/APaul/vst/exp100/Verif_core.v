(** * Task T5: exp_core *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec E.Rows E.CoreBounds.
Require Exp100.ExpConsts Exp100.ExpModel.

Module M := Exp100.ExpModel.

(** ** Word lemmas *)

(* the k low bits of z *)
Lemma and_ones z k : 0 <= z <= Int64.max_unsigned -> 0 <= k <= 64 ->
  Int64.and (Int64.repr z) (Int64.repr (2 ^ k - 1)) = Int64.repr (z mod 2 ^ k).
Proof.
  intros Hz Hk.
  replace (2 ^ k - 1) with (Z.ones k) by (rewrite Z.ones_equiv; lia).
  apply Int64.same_bits_eq; intros i Hi.
  rewrite Int64.bits_and by lia.
  rewrite !Int64.testbit_repr by lia.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_spec; reflexivity.
Qed.

(* z shifted right by k *)
Lemma shru_repr z k : 0 <= z <= Int64.max_unsigned -> 0 <= k < 64 ->
  Int64.shru (Int64.repr z) (Int64.repr k) = Int64.repr (z / 2 ^ k).
Proof.
  intros Hz Hk.
  rewrite Int64.shru_div_two_p, !Int64.unsigned_repr by rep_lia.
  rewrite two_p_equiv; reflexivity.
Qed.

(* setting bit k of v < 2^k *)
Lemma or_top v k : 0 <= v < 2 ^ k -> 0 <= k < 64 ->
  Int64.or (Int64.repr v) (Int64.repr (2 ^ k)) = Int64.repr (v + 2 ^ k).
Proof.
  intros Hv Hk.
  rewrite <- Int64.add_is_or, add64_repr; [reflexivity|].
  apply Int64.same_bits_eq; intros i Hi.
  rewrite Int64.bits_and, Int64.bits_zero by lia.
  rewrite !Int64.testbit_repr by lia.
  rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec k i) as [<-|]; [|apply andb_false_r].
  rewrite <- (Z.mod_small v (2 ^ k)) by lia.
  rewrite Z.mod_pow2_bits_high by lia; reflexivity.
Qed.

(* the C test n > 0 on an unsigned n *)
Lemma gt0_val g : 0 <= g <= Int64.max_unsigned ->
  bool2val (Int64.cmpu Cgt (Int64.repr g) (Int64.repr 0)) =
  Vint (Int.repr (if 0 <? g then 1 else 0)).
Proof.
  intros Hg; unfold Int64.cmpu, Int64.ltu.
  rewrite !Int64.unsigned_repr by rep_lia.
  destruct (zlt 0 g), (Z.ltb_spec 0 g); try lia; reflexivity.
Qed.

(* a number can be overwritten *)
Lemma num_data_at_ sh xs p : num sh xs p |-- data_at_ sh (tarray tulong NL) p.
Proof. unfold num; apply data_at_data_at_. Qed.

(** ** The tables *)

(* a table without its row i *)
Definition rows_but sh m (rows : list (list val)) i p : mpred :=
  (data_at sh (tarray (tarray tulong NL) i) (sublist 0 i rows) p *
   data_at sh (tarray (tarray tulong NL) (m - (i + 1)))
     (sublist (i + 1) m rows)
     (field_address0 (tarray (tarray tulong NL) m) [ArraySubsc (i + 1)] p))%logic.

(* row i of a table of numbers, as a number *)
Lemma table_row sh m tab i p : 0 <= i < m -> Zlength tab = m ->
  field_compatible (tarray (tarray tulong NL) m) [] p ->
  data_at sh (tarray (tarray tulong NL) m) (map vwords tab) p =
  (num sh (Znth i tab) (offset_val (48 * i) p) *
   rows_but sh m (map vwords tab) i p)%logic.
Proof.
  intros Hi Hl Hc.
  rewrite (row_split sh m (map vwords tab) i p Hi)
    by (rewrite Zlength_map; exact Hl).
  rewrite (row_addr m i p Hi Hc).
  unfold num, rows_but; rewrite Znth_map by lia.
  apply pred_ext; cancel.
Qed.


Lemma Zlength_T : Zlength Exp100.ExpTable.T = NT.
Proof. reflexivity. Qed.

Lemma Zlength_C : Zlength Exp100.ExpTable.C = NC.
Proof. reflexivity. Qed.

(* C_i and T_j as rows of the tables *)
Lemma Cv_Znth i : 0 <= i < NC -> M.Cv (Z.to_nat i) = valZ (Znth i Exp100.ExpTable.C).
Proof.
  intros Hi; rewrite M.CvE, <- nth_Znth by (rewrite Zlength_C; lia).
  reflexivity.
Qed.

Lemma Tv_Znth j : 0 <= j < NT -> M.Tv j = valZ (Znth j Exp100.ExpTable.T).
Proof.
  intros Hj; rewrite M.TvE, <- nth_Znth by (rewrite Zlength_T; lia).
  reflexivity.
Qed.

(* VST tactics compute with whatever they can unfold: keep the model
   functions and the tables shut *)
Local Opaque M.xbexp M.xsign M.xmant0 M.xmant M.xexpo M.xfix M.scale
  M.guess M.q M.mulshr M.horner M.horner_from M.Tv M.Cv M.core_Z M.rarg
  M.Nu M.jidx M.hidx M.reduce M.LN2v M.RMAXv M.Ts M.Cs
  Exp100.ExpTable.T Exp100.ExpTable.C Exp100.ExpTable.LN2
  Exp100.ExpTable.RMAX.

Lemma body_exp_core : semax_body Vprog Gprog f_exp_core exp_core_spec.
Proof.
  start_function.
  unfold consts; Intros.
  rename H into Hxb.
  assert_PROP (field_compatible (tarray (tarray tulong NL) NT) [] (gv _T))
    as FcT by entailer!.
  assert_PROP (field_compatible (tarray (tarray tulong NL) NC) [] (gv _C))
    as FcC by entailer!.
  freeze FT := (data_at Ers (tarray (tarray tulong 6) 64) _ (gv _T))
    (data_at Ers (tarray (tarray tulong 6) 17) _ (gv _C)).
  forward.
  forward.
  forward.
  (* the sign, the biased exponent, the stored mantissa *)
  pose proof (xbexp_bound xb) as Bbe.
  pose proof (xmant0_bound xb) as Bm.
  assert (Eneg : Int64.shru (Int64.repr xb)
                   (Int64.repr (Int.unsigned (Int.repr 63))) =
                 Int64.repr (M.xsign xb)).
  { change (Int.unsigned (Int.repr 63)) with 63.
    rewrite M.xsignE, shru_repr by rep_lia; reflexivity. }
  assert (Ebe : Int64.unsigned
                  (Int64.and (Int64.shru (Int64.repr xb)
                     (Int64.repr (Int.unsigned (Int.repr 52))))
                     (Int64.repr (Int.signed (Int.repr 2047)))) =
                M.xbexp xb).
  { change (Int.unsigned (Int.repr 52)) with 52.
    change (Int.signed (Int.repr 2047)) with (2 ^ 11 - 1).
    assert (0 <= xb / 2 ^ 52 < 2 ^ 12).
    { split; [apply Z.div_pos|apply Z.div_lt_upper_bound]; zpow; rep_lia. }
    rewrite shru_repr by rep_lia.
    rewrite and_ones by (zpow; rep_lia).
    rewrite M.xbexpE, Int64.unsigned_repr; [reflexivity|].
    rewrite <- M.xbexpE; zpow; rep_lia. }
  assert (Emx : Int64.and (Int64.repr xb)
                  (Int64.sub (Int64.shl (Int64.repr (Int.signed (Int.repr 1)))
                                (Int64.repr (Int.unsigned (Int.repr 52))))
                     (Int64.repr (Int.signed (Int.repr 1)))) =
                Int64.repr (M.xmant0 xb)).
  { change (Int64.sub (Int64.shl (Int64.repr (Int.signed (Int.repr 1)))
                         (Int64.repr (Int.unsigned (Int.repr 52))))
              (Int64.repr (Int.signed (Int.repr 1)))) with
      (Int64.repr (2 ^ 52 - 1)).
    rewrite and_ones, M.xmant0E by rep_lia; reflexivity. }
  rewrite Eneg, Ebe, Emx; clear Eneg Ebe Emx.
  forward_if.
  { (* |x| >= 1024 *)
    forward.
    Exists 1 (@nil Z) 0.
    assert (Hc : M.core_Z xb = inl 1).
    { apply core_Z_big; unfold M.be_big; lia. }
    rewrite Hc.
    entailer!.
    thaw FT; unfold consts; cbn [Z.eqb]; cancel. }
  forward_if [temp _be (Vint (Int.repr (M.xexpo xb)));
              temp _mx (Vlong (Int64.repr (M.xmant xb)))].
  { forward.
    destruct (xexpo_0 xb H0) as [-> ->].
    entailer!. }
  { forward.
    destruct (xexpo_n xb H0) as [-> ->].
    change (Int64.shl (Int64.repr (Int.signed (Int.repr 1)))
              (Int64.repr (Int.unsigned (Int.repr 52)))) with
      (Int64.repr (2 ^ 52)).
    rewrite or_top by (try lia; discriminate).
    entailer!. }
  pose proof (xmant_bound xb) as Bv.
  assert (Bx : M.xbexp xb < M.be_big) by (unfold M.be_big; lia).
  pose proof (xexpo_bound xb Bx) as Be.
  unfold M.be_big in Be.
  forward_call (Tsh, v_X, M.xmant xb, M.xexpo xb - 1075 + 160).
  { unfold mant_bits, scale_emax; zpow; rep_lia. }
  Intros Xl.
  rename H0 into HlX, H1 into HfX, H2 into HX.
  rewrite <- xfixE in HX.
  pose proof (xfix_bound xb Bx) as BX.
  set (X := M.xfix xb) in *.
  (* the guess, lowered once *)
  forward_call (gv, Tsh, v_X, Xl).
  rewrite HX.
  set (g := M.guess X).
  assert (Bg : 0 <= g < 2 ^ n_bits) by (apply guess_bound; exact BX).
  unfold n_bits in Bg.
  forward_call (gv, Tsh, v_q, g).
  { unfold limb, Exp100.ExpConsts.limb_bits; zpow; lia. }
  Intros ql.
  rename H0 into Hlq, H1 into Hfq, H2 into Hq.
  forward_call (Tsh, Tsh, v_X, v_q, Xl, ql).
  rewrite HX, Hq.
  forward_if (temp _t'3
    (Vint (Int.repr (if andb (X <? M.q g) (0 <? g) then 1 else 0)))).
  { forward. entailer!.
    destruct (M.xfix xb <? M.q g); [|contradiction].
    rewrite gt0_val by rep_lia; reflexivity. }
  { forward. destruct (X <? M.q g); [discriminate|]. entailer!. }
  forward_if (temp _n (Vlong (Int64.repr (red1 X g)))).
  { forward. entailer!.
    unfold red1; destruct (andb _ _); [|contradiction].
    reflexivity. }
  { forward. entailer!.
    unfold red1; destruct (andb _ _); [discriminate|reflexivity]. }
  (* raised once *)
  set (n1 := red1 X g).
  assert (B1 : 0 <= n1 < 2 ^ 17) by (apply (red1_bound X g Bg)).
  forward_call (gv, Tsh, v_q1, n1 + 1).
  { unfold limb, Exp100.ExpConsts.limb_bits; zpow; lia. }
  Intros q1l.
  rename H0 into Hlq1, H1 into Hfq1, H2 into Hq1.
  forward_call (Tsh, Tsh, v_X, v_q1, Xl, q1l).
  rewrite HX, Hq1.
  forward_if (temp _n (Vlong (Int64.repr (red2 X n1)))).
  { forward. entailer!.
    unfold red2; destruct (_ <? _); [discriminate|].
    rewrite ?add64_repr; reflexivity. }
  { forward. entailer!.
    unfold red2; destruct (_ <? _); [reflexivity|].
    exfalso; apply H0; reflexivity. }
  (* the check q(n) <= X < q(n+1) *)
  assert (En : red2 X n1 = red_n X) by reflexivity.
  rewrite En; clear En.
  set (n := red_n X).
  assert (Bn : 0 <= n <= 2 ^ 17).
  { apply red_n_bound; unfold X_bits in BX; exact BX. }
  sep_apply (num_data_at_ Tsh ql v_q).
  forward_call (gv, Tsh, v_q, n).
  { unfold limb, Exp100.ExpConsts.limb_bits; zpow; lia. }
  Intros q2l.
  rename H0 into Hlq2, H1 into Hfq2, H2 into Hq2.
  sep_apply (num_data_at_ Tsh q1l v_q1).
  forward_call (gv, Tsh, v_q1, n + 1).
  { unfold limb, Exp100.ExpConsts.limb_bits; zpow; lia. }
  Intros q3l.
  rename H0 into Hlq3, H1 into Hfq3, H2 into Hq3.
  forward_call (Tsh, Tsh, v_X, v_q, Xl, q2l).
  rewrite HX, Hq2.
  forward_if (temp _t'6 (Vint (Int.repr
    (if orb (X <? M.q n) (negb (X <? M.q (n + 1))) then 1 else 0)))).
  { forward. entailer!.
    destruct (_ <? _); [reflexivity|contradiction]. }
  { forward_call (Tsh, Tsh, v_X, v_q1, Xl, q3l).
    rewrite HX, Hq3.
    forward. entailer!.
    destruct (M.xfix xb <? M.q n); [discriminate|].
    destruct (M.xfix xb <? M.q (n + 1)); reflexivity. }
  forward_if.
  { (* the check fails *)
    forward.
    Exists 2 (@nil Z) 0.
    assert (Hc : M.core_Z xb = inl 2).
    { apply (core_Z_reduce xb Bx), reduce_none.
      destruct (Z.ltb_spec (M.xfix xb) (M.q n)); [left; assumption|].
      destruct (Z.ltb_spec (M.xfix xb) (M.q (n + 1))); [|right; assumption].
      contradiction. }
    rewrite Hc.
    entailer!.
    thaw FT; unfold consts; cbn [Z.eqb]; cancel.
    sep_apply (num_data_at_ Tsh Xl v_X); sep_apply (num_data_at_ Tsh q2l v_q).
    sep_apply (num_data_at_ Tsh q3l v_q1); cancel. }
  assert (Hchk : M.q n <= X < M.q (n + 1)).
  { destruct (Z.ltb_spec X (M.q n)); [discriminate|].
    destruct (Z.ltb_spec X (M.q (n + 1))); [lia|discriminate]. }
  clear H0.
  assert (Hred : M.reduce X = Some n) by (apply reduce_some, Hchk).
  assert (Bn' : n < 2 ^ 17).
  { apply (checked_n_bound X); [lia|]. split; [apply Hchk|apply BX]. }
  (* r and N + 2^17 *)
  assert (Bs : 0 <= M.xsign xb < 2) by (apply xsign_bound; zpow; rep_lia).
  forward_if (EX rl : list Z,
    PROP (Zlength rl = NL; Forall limb rl; valZ rl = M.rarg xb n)
    LOCAL (temp _Nu (Vlong (Int64.repr (M.Nu xb n)));
           lvar _t (tarray tulong 6) v_t; lvar _h (tarray tulong 6) v_h;
           lvar _r (tarray tulong 6) v_r; lvar _q1 (tarray tulong 6) v_q1;
           lvar _q (tarray tulong 6) v_q; lvar _X (tarray tulong 6) v_X;
           gvars gv; temp _y py; temp _s ps)
    SEP (num Tsh rl v_r; num Tsh Xl v_X; num Tsh q2l v_q; num Tsh q3l v_q1;
         FRZL FT; data_at_ Tsh (tarray tulong NL) v_t;
         data_at_ Tsh (tarray tulong NL) v_h;
         data_at_ sh (tarray tulong NL) py; data_at_ sh tlong ps;
         num Ers Exp100.ExpTable.LN2 (gv _LN2);
         num Ers Exp100.ExpTable.RMAX (gv _RMAX);
         data_at Ers tulong (Vlong (Int64.repr Exp100.ExpTable.INV))
           (gv _INV))).
  { (* x < 0: r = q(n+1) - X, N = -(n+1) *)
    destruct (rarg_neg xb n H0') as [Er ENu].
    forward_call (Tsh, Tsh, v_r, v_q1, q3l).
    forward_call (Tsh, Tsh, v_r, v_X, q3l, Xl).
    Intros rl.
    forward.
    Exists rl.
    entailer!.
    rewrite ENu; reflexivity. }
  { (* x >= 0: r = X - q(n), N = n *)
    assert (Hs : M.xsign xb = 0).
    { apply (f_equal Int64.unsigned) in H0.
      rewrite Int64.unsigned_repr in H0 by rep_lia; exact H0. }
    destruct (rarg_pos xb n Hs) as [Er ENu].
    forward_call (Tsh, Tsh, v_r, v_X, Xl).
    forward_call (Tsh, Tsh, v_r, v_q, Xl, q2l).
    Intros rl.
    forward.
    Exists rl.
    entailer!.
    rewrite ENu; reflexivity. }
  Intros rl.
  rename H0 into Hlr, H1 into Hfr, H2 into Hr.
  destruct RMAX_num as [HlR HfR].
  forward_call (Tsh, Ers, v_r, gv _RMAX, rl, Exp100.ExpTable.RMAX).
  rewrite Hr.
  forward_if.
  { (* r >= RMAX *)
    forward.
    Exists 3 (@nil Z) 0.
    assert (Hc : M.core_Z xb = inl 3).
    { apply (core_Z_rmax xb n Bx Hred).
      rewrite M.RMAXvE.
      destruct (Z.ltb_spec (M.rarg xb n) (valZ Exp100.ExpTable.RMAX));
        [discriminate|assumption]. }
    rewrite Hc.
    entailer!.
    thaw FT; unfold consts; cbn [Z.eqb]; cancel.
    sep_apply (num_data_at_ Tsh Xl v_X); sep_apply (num_data_at_ Tsh q2l v_q).
    sep_apply (num_data_at_ Tsh q3l v_q1).
    sep_apply (num_data_at_ Tsh rl v_r); cancel. }
  assert (HrR : M.rarg xb n < M.RMAXv).
  { rewrite M.RMAXvE.
    destruct (Z.ltb_spec (M.rarg xb n) (valZ Exp100.ExpTable.RMAX));
      [assumption|contradiction H0; reflexivity]. }
  clear H0.
  assert (Br : 0 <= M.rarg xb n < 2 ^ r_bits).
  { pose proof RMAXv_lt; rewrite <- Hr.
    pose proof (valZ_bounds rl Hfr); lia. }
  (* Horner's rule *)
  thaw FT.
  rewrite (table_row Ers NC Exp100.ExpTable.C 16 (gv _C))
    by (auto; rewrite ?Zlength_C; lia).
  Intros.
  destruct (C_num 16) as [HlC HfC]; [lia|].
  forward_call (Tsh, Ers, v_h, offset_val (48 * 16) (gv _C),
                Znth 16 Exp100.ExpTable.C).
  gather_SEP (num Ers (Znth 16 Exp100.ExpTable.C) _)
             (rows_but Ers 17 (map vwords Exp100.ExpTable.C) 16 (gv _C)).
  rewrite <- (table_row Ers NC Exp100.ExpTable.C 16 (gv _C))
    by (auto; rewrite ?Zlength_C; lia).
  (* missing: the Horner loop (forward_loop), j = Nu & 63, the call
     num_mulshr(y, T[j], h), *s = hN and return 0; see PICKUP-T5.md *)
  admit.
Admitted.
