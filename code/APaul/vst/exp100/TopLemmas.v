(** * Task T6: exp_encl_bits, and the lemmas maybe_hard_bits needs *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.
Require Exp100.ExpConsts Exp100.ExpModel.

Module M := Exp100.ExpModel.

(** ** What core_Z says on the sizes of y, hN and rc *)

(* lia does not evaluate 2^k: write each 2^k of numeral k as a numeral *)
Ltac zpow :=
  repeat match goal with
  | |- context [2 ^ Zpos ?k] =>
      let v := eval vm_compute in (2 ^ Zpos k) in change (2 ^ Zpos k) with v
  | H : context [2 ^ Zpos ?k] |- _ =>
      let v := eval vm_compute in (2 ^ Zpos k) in
      change (2 ^ Zpos k) with v in H
  end.

(* the code of a failure, without unfolding the tables *)
Ltac proj_inl H :=
  apply (f_equal (fun s : Z + Z * Z =>
    match s with inl r => r | inr _ => 0 end)) in H;
  cbv beta iota in H.

(* a failure of core_Z is 1, 2 or 3 *)
Lemma core_Z_rc xb rc : M.core_Z xb = inl rc -> 1 <= rc <= 3.
Proof.
  unfold M.core_Z.
  destruct (M.be_big <=? M.xbexp xb).
  { intros H; proj_inl H; unfold M.rc_big in H; lia. }
  destruct (M.reduce (M.xfix xb)) as [n|].
  2: { intros H; proj_inl H; unfold M.rc_reduce in H; lia. }
  cbv zeta.
  destruct (negb (M.rarg xb n <? M.RMAXv)).
  { intros H; proj_inl H; unfold M.rc_rmax in H; lia. }
  discriminate.
Qed.

Lemma Cs_bound :
  forallb (fun c => andb (0 <=? c) (c <=? 2 ^ 160)) M.Cs = true.
Proof. vm_compute; reflexivity. Qed.

Lemma Ts_bound :
  forallb (fun t => andb (2 ^ 160 <=? t) (t <? 2 ^ 161)) M.Ts = true.
Proof. vm_compute; reflexivity. Qed.

Lemma Ts_length : length M.Ts = 64%nat.
Proof. vm_compute; reflexivity. Qed.

Lemma Cv0 : M.Cv 0 = 2 ^ 160.
Proof. vm_compute; reflexivity. Qed.

Lemma RMAXv_lt : M.RMAXv < 2 ^ 154.
Proof. apply Z.ltb_lt; vm_compute; reflexivity. Qed.

Lemma LN2v_ge : 2 ^ 185 <= M.LN2v.
Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.

(* every C_i is in [0, 2^160], also past DEG where it is 0 *)
Lemma Cv_all i : 0 <= M.Cv i <= 2 ^ 160.
Proof.
  unfold M.Cv.
  destruct (nth_in_or_default i M.Cs 0) as [Hi| ->]; [|lia].
  pose proof Cs_bound as H; rewrite forallb_forall in H.
  specialize (H _ Hi); rewrite andb_true_iff, !Z.leb_le in H; lia.
Qed.

Lemma Tv_all j : 0 <= j < 64 -> 2 ^ 160 <= M.Tv j < 2 ^ 161.
Proof.
  intros Hj; unfold M.Tv.
  pose proof Ts_bound as H; rewrite forallb_forall in H.
  specialize (H (nth (Z.to_nat j) M.Ts 0)).
  rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in H; apply H, nth_In.
  rewrite Ts_length; lia.
Qed.

Lemma mulshr_bound h r : 0 <= h < 2 ^ 161 -> 0 <= r < 2 ^ 154 ->
  0 <= M.mulshr h r < 2 ^ 155.
Proof.
  intros Hh Hr; rewrite M.mulshrE; unfold Exp100.ExpConsts.P.
  split; [apply Z.div_pos; [nia|lia]|].
  apply Z.div_lt_upper_bound; [lia|].
  rewrite <- Z.pow_add_r by lia; zpow; nia.
Qed.

Lemma horner_from_S r h k :
  M.horner_from r h (S k) = M.horner_from r (M.mulshr h r + M.Cv k) k.
Proof. reflexivity. Qed.

(* the Horner values stay in [2^160, 2^161) once C_0 is added *)
Lemma horner_from_bound r k : 0 <= r < 2 ^ 154 -> forall h,
  0 <= h < 2 ^ 161 ->
  0 <= M.horner_from r h k < 2 ^ 161 /\
  ((0 < k)%nat -> 2 ^ 160 <= M.horner_from r h k).
Proof.
  intros Hr; induction k as [|k IH]; intros h Hh.
  { cbn [M.horner_from]; split; [lia|intros; lia]. }
  rewrite horner_from_S.
  pose proof (mulshr_bound h r Hh Hr); pose proof (Cv_all k).
  assert (Hn : 0 <= M.mulshr h r + M.Cv k < 2 ^ 161) by (zpow; lia).
  destruct k as [|k].
  - cbn [M.horner_from]; rewrite Cv0 in *; zpow; split; [lia|intros; lia].
  - destruct (IH _ Hn) as [IH1 IH2]; split; [lia|intros; apply IH2; lia].
Qed.

Lemma horner_bound r : 0 <= r < 2 ^ 154 ->
  2 ^ 160 <= M.horner r < 2 ^ 161.
Proof.
  intros Hr; unfold M.horner.
  assert (Hc : 0 <= M.Cv Exp100.ExpConsts.DEG < 2 ^ 161).
  { pose proof (Cv_all Exp100.ExpConsts.DEG); zpow; lia. }
  destruct (horner_from_bound r Exp100.ExpConsts.DEG Hr _ Hc) as [H1 H2].
  split; [apply H2; unfold Exp100.ExpConsts.DEG; lia|lia].
Qed.

(* X = floor(|x| 2^P) is below 2^170 *)
Lemma xfix_bound xb : M.xbexp xb < M.be_big -> 0 <= M.xfix xb < 2 ^ 170.
Proof.
  intros Hb.
  assert (He : 0 <= M.xbexp xb) by
    (rewrite M.xbexpE; apply Z.mod_pos_bound; reflexivity).
  assert (Hm : 0 <= M.xmant0 xb < 2 ^ M.mant_bits) by
    (rewrite M.xmant0E; apply Z.mod_pos_bound; reflexivity).
  assert (Hv : 0 <= M.xmant xb < 2 ^ 53).
  { unfold M.xmant; rewrite M.pow2E by discriminate.
    unfold M.mant_bits in *; destruct (M.xbexp xb =? 0); zpow; lia. }
  assert (Hx : 1 <= M.xexpo xb < M.be_big).
  { unfold M.xexpo, M.be_big in *; destruct (Z.eqb_spec (M.xbexp xb) 0); lia. }
  unfold M.xfix; rewrite M.scaleE.
  unfold M.be_big, M.expo_shift, Exp100.ExpConsts.P in *.
  destruct (Z.leb_spec 0 (M.xexpo xb - 1075 + 160)) as [Hp|Hn].
  - split; [apply Z.mul_nonneg_nonneg; lia|].
    apply Z.lt_le_trans with (2 ^ 53 * 2 ^ (M.xexpo xb - 1075 + 160)).
    + apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg|]; lia.
    + rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia.
  - split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
    apply Z.le_lt_trans with (M.xmant xb); [|zpow; lia].
    apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    assert (1 <= 2 ^ (- (M.xexpo xb - 1075 + 160))).
    { apply (Z.pow_le_mono_r 2 0); lia. }
    nia.
Qed.

(* q(n) = floor(n LN2 / 2^32) *)
Lemma qE' n : M.q n = n * M.LN2v / 2 ^ 32.
Proof. unfold M.q; apply M.shrE; discriminate. Qed.

(* a checked n is in [0, 2^17) *)
Lemma n_bound X n : 0 <= X < 2 ^ 170 -> M.q n <= X < M.q (n + 1) ->
  0 <= n < 2 ^ 17.
Proof.
  intros HX [H1 H2]; rewrite !qE' in *; pose proof LN2v_ge as HL.
  split.
  - destruct (Z.leb_spec 0 n) as [|Hn]; [lia|].
    assert ((n + 1) * M.LN2v / 2 ^ 32 <= 0); [|lia].
    apply Z.div_le_upper_bound; [lia|]; zpow; nia.
  - destruct (Z.ltb_spec n (2 ^ 17)) as [|Hn]; [lia|].
    assert (2 ^ 170 <= n * M.LN2v / 2 ^ 32); [|lia].
    apply Z.div_le_lower_bound; [lia|]; zpow; nia.
Qed.

(* y is in [2^160, 2^162) and hN is small *)
Lemma core_bounds xb y hN : M.core_Z xb = inr (y, hN) ->
  2 ^ 160 <= y < 2 ^ 162 /\ - 2 ^ 12 <= hN <= 2 ^ 12.
Proof.
  intros H.
  destruct (M.core_relP xb y hN H)
    as (n & Hbe & [Hq1 Hq2] & Hr & Hy & HhN).
  pose proof (xfix_bound xb Hbe) as HX.
  pose proof (n_bound _ n HX (conj Hq1 Hq2)) as Hn.
  rewrite <- M.RMAXvE in Hr; pose proof RMAXv_lt.
  assert (Hr0 : 0 <= M.rarg xb n < 2 ^ 154).
  { split; [|lia]; unfold M.rarg; destruct (M.xsign xb =? 0); lia. }
  assert (HN : 0 <= M.Nu xb n <= 2 ^ 18).
  { unfold M.Nu, M.N_bias; destruct (M.xsign xb =? 0); zpow; lia. }
  assert (Hj : 0 <= M.Nu xb n mod Exp100.ExpConsts.TAB < 64).
  { apply Z.mod_pos_bound; reflexivity. }
  pose proof (Tv_all _ Hj) as HT.
  pose proof (horner_bound _ Hr0) as HH.
  split.
  - rewrite Hy, M.mulshrE; unfold Exp100.ExpConsts.P; split.
    + apply Z.div_le_lower_bound; [lia|nia].
    + apply Z.div_lt_upper_bound; [lia|].
      rewrite <- Z.pow_add_r by lia; zpow; nia.
  - rewrite HhN; replace M.hN_bias with 2048 by reflexivity.
    unfold Exp100.ExpConsts.TAB; zpow.
    assert (0 <= M.Nu xb n / 64 <= 4096); [|lia].
    split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia].
Qed.

(** ** exp_encl_bits *)

(* the 3 words of M from the 6 limbs of y *)
Definition pack (ys : list Z) : list Z :=
  [Znth 0 ys + 2 ^ 32 * Znth 1 ys; Znth 2 ys + 2 ^ 32 * Znth 3 ys;
   Znth 4 ys + 2 ^ 32 * Znth 5 ys].

Lemma Znth_pack ys i : 0 <= i < 3 ->
  Znth i (pack ys) = Znth (2 * i) ys + 2 ^ 32 * Znth (2 * i + 1) ys.
Proof.
  intros Hi; assert (i = 0 \/ i = 1 \/ i = 2) as [->|[->| ->]] by lia;
  reflexivity.
Qed.

Lemma valW_pack ys : Zlength ys = 6 -> valW (pack ys) = valZ ys.
Proof.
  intros H.
  do 6 (destruct ys as [|? ys];
        [rewrite ?Zlength_cons, Zlength_nil in H; lia|]).
  destruct ys; [|rewrite !Zlength_cons in H;
                 pose proof (Zlength_nonneg ys); lia].
  unfold pack; cbn [valW Exp100.ExpConsts.valZ].
  unfold word_bits, Exp100.ExpConsts.limb_bits.
  change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
  repeat rewrite ?Znth_0_cons, ?Znth_pos_cons by lia; simpl (_ - 1).
  ring.
Qed.

Lemma pack_word ys : Zlength ys = 6 -> Forall limb ys -> Forall word (pack ys).
Proof.
  intros Hl Hf.
  assert (Hk : forall k, 0 <= k < 6 -> 0 <= Znth k ys < 2 ^ 32).
  { intros k Hk; apply (proj1 (Forall_Znth _ _) Hf); lia. }
  pose proof (Hk 0) ; pose proof (Hk 1); pose proof (Hk 2);
  pose proof (Hk 3); pose proof (Hk 4); pose proof (Hk 5).
  unfold pack, word, word_bits; zpow.
  repeat constructor; zpow; lia.
Qed.

(* the C word y[2i] | y[2i+1] << 32 *)
Lemma or_shl a b : 0 <= a < 2 ^ 32 -> 0 <= b < 2 ^ 32 ->
  Int64.or (Int64.repr a) (Int64.shl (Int64.repr b) (Int64.repr 32)) =
  Int64.repr (a + 2 ^ 32 * b).
Proof.
  intros Ha Hb.
  rewrite Int64.shl_mul_two_p; unfold Int64.mul.
  change (Int64.unsigned (Int64.repr 32)) with 32.
  change (two_p 32) with (2 ^ 32).
  rewrite (Int64.unsigned_repr b), (Int64.unsigned_repr (2 ^ 32)) by rep_lia.
  rewrite <- Int64.add_is_or, add64_repr; [f_equal; ring|].
  apply Int64.same_bits_eq; intros i Hi.
  rewrite Int64.bits_and, Int64.bits_zero by lia.
  rewrite !Int64.testbit_repr by lia.
  destruct (Z.ltb_spec i 32).
  - rewrite Z.mul_pow2_bits_low by lia.
    apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ 32)) by lia.
    rewrite Z.mod_pow2_bits_high by lia; reflexivity.
Qed.

(* writing the cell i of a prefix of L *)
Lemma upd_prefix (L : list Z) i : Zlength L = 3 -> 0 <= i < 3 ->
  upd_Znth i (vwords (sublist 0 i L) ++ Zrepeat Vundef (3 - i))
    (Vlong (Int64.repr (Znth i L))) =
  vwords (sublist 0 (i + 1) L) ++ Zrepeat Vundef (3 - (i + 1)).
Proof. intros; unfold vwords; list_solve. Qed.

Lemma body_exp_encl_bits :
  semax_body Vprog Gprog f_exp_encl_bits exp_encl_bits_spec.
Proof.
  start_function.
  forward_call (gv, Tsh, xb, v_y, v_hN).
  Intros vret; destruct vret as [[rc ys] hN]; cbn [fst snd] in *.
  rename H0 into Hok, H1 into Hko.
  destruct (Z.eqb_spec rc 0) as [->|Hrc].
  2: {
    pose proof (core_Z_rc _ _ (Hko Hrc)) as Hr.
    forward_if.
    - forward.
      Exists rc (@nil Z) 0.
      entailer!.
      + unfold M.exp_encl_Z; rewrite (Hko Hrc); reflexivity.
      + rewrite (proj2 (Z.eqb_neq _ _) Hrc); cancel.
    - exfalso; apply Hrc.
      match goal with Hz : Int.repr rc = Int.zero |- _ =>
        apply repr_inj_signed; [rep_lia|rep_lia|exact Hz] end. }
  destruct (Hok eq_refl) as (Hcore & Hl & Hf); clear Hok Hko.
  assert (Hy : forall k, 0 <= k < 6 -> 0 <= Znth k ys < 2 ^ 32).
  { intros k Hk; apply (proj1 (Forall_Znth _ _) Hf); lia. }
  forward_if.
  { elim H0; reflexivity. }
  unfold num; Intros.
  forward_for_simple_bound 3
    (EX i : Z,
     PROP ()
     LOCAL (lvar _hN tlong v_hN; lvar _y (tarray tulong 6) v_y; gvars gv;
            temp _M pM; temp _s ps)
     SEP (data_at Tsh (tarray tulong NL) (vwords ys) v_y;
          data_at Tsh tlong (Vlong (Int64.repr hN)) v_hN; consts gv;
          data_at shM (tarray tulong NM)
            (vwords (sublist 0 i (pack ys)) ++ Zrepeat Vundef (NM - i)) pM;
          data_at_ shs tlong ps)).
  - entailer!.
  - pose proof (Hy (2 * i) ltac:(lia)); pose proof (Hy (2 * i + 1) ltac:(lia)).
    forward.
    { (rewrite Znth_vwords by lia; entailer!). }
    rewrite Znth_vwords by lia.
    forward.
    { (rewrite Znth_vwords by lia; entailer!). }
    rewrite Znth_vwords by lia.
    forward.
    change (Int.unsigned (Int.repr 32)) with 32.
    rewrite or_shl, <- Znth_pack by lia.
    rewrite upd_prefix by (try reflexivity; lia).
    entailer!.
  - forward.
    forward.
    { entailer!.
      destruct (core_bounds _ _ _ Hcore) as [_ HhN]; zpow.
      rewrite Int64.signed_repr by rep_lia; rep_lia. }
    forward.
    Exists 0 (pack ys) (hN - 160).
    rewrite sublist_same, Z.sub_diag, Zrepeat_0, app_nil_r by reflexivity.
    entailer!.
    + unfold M.exp_encl_Z; rewrite Hcore, valW_pack by exact Hl.
    + split; [reflexivity|split; [reflexivity|apply pack_word; auto]].
    + apply derives_refl.
Qed.

(** ** maybe_hard_bits *)

(* D = 16 as a number *)
Definition Dl : list Z := [16; 0; 0; 0; 0; 0].

Lemma Dl_num : Zlength Dl = 6 /\ Forall limb Dl /\ valZ Dl = 16.
Proof.
  split; [reflexivity|split; [|reflexivity]].
  unfold Dl, Exp100.ExpConsts.limb, Exp100.ExpConsts.limb_bits.
  repeat constructor; lia.
Qed.

(* the bit length of a number of 192 bits *)
Lemma bitlen_range v : 0 <= v < 2 ^ 192 -> 0 <= M.bitlen v <= 192.
Proof.
  intros Hv; unfold M.bitlen.
  destruct (Z.leb_spec v 0); [lia|].
  pose proof (Z.log2_nonneg v).
  assert (Z.log2 v < 192) by (apply Z.log2_lt_pow2; lia); lia.
Qed.

(* the value of a number of NL limbs *)
Lemma valZ_range xs : Zlength xs = 6 -> Forall limb xs ->
  0 <= valZ xs < 2 ^ 192.
Proof.
  intros Hl Hf; pose proof (valZ_bounds xs Hf) as H.
  rewrite Hl in H; exact H.
Qed.

(* a number on the stack, freed at return *)
Lemma num_free sh xs p : num sh xs p |-- data_at_ sh (tarray tulong 6) p.
Proof. unfold num; apply data_at_data_at_. Qed.

(* a value of [y - D, y + D] out of the binade of y: hard *)
Lemma decide_bits y hN :
  M.bitlen (y - 16) <> M.bitlen y \/ M.bitlen (y + 16) <> M.bitlen y ->
  M.decide_Z y hN = 1.
Proof.
  intros H; unfold M.decide_Z, M.D; cbv zeta.
  destruct H as [H|H].
  - rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r; reflexivity.
Qed.

(* the decision once the binade is known, with f as the C computes it *)
Lemma decide_f y hN f :
  M.bitlen (y - 16) = M.bitlen y -> M.bitlen (y + 16) = M.bitlen y ->
  f = Z.max (hN - 160 + M.bitlen y - 1) (-1022) - 53 - (hN - 160) ->
  M.decide_Z y hN =
  if orb (f <? 64) (184 <? f) then 1 else
  let lo := M.low y f in
  let hi := M.pow2 f - lo in
  let d := if lo <? hi then lo else hi in
  if M.pow2 (f - 43) + 16 <? d then 0 else 1.
Proof.
  intros H1 H2 Hf; unfold M.decide_Z, M.D; cbv zeta.
  rewrite H1, H2, Z.eqb_refl; cbn [andb negb].
  subst f; reflexivity.
Qed.
