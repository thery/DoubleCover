(** * The bounds exp_core needs, on the integer model

    [core_Z] of ExpModel.v leaves out the sizes: the C needs them so that
    no word wraps and every call meets its precondition.  From |x| < 1024:
    X < 2^170, the guess of n is below 2^17, n + 1 <= 2^17 once n is
    checked, every Horner value is below 2^161 and every T_j below 2^161.
    Also the steps of [reduce] and the four outcomes of [core_Z], stated
    so that no tactic has to unfold the tables. *)

From Stdlib Require Import Bool ZArith Lia List.
From Exp100 Require Import ExpTable ExpConsts ExpModel.
Import ListNotations.

Open Scope Z_scope.

(** lia does not evaluate 2^k: write each 2^k of numeral k as a numeral. *)
Ltac zpow :=
  repeat match goal with
  | |- context [2 ^ Zpos ?k] =>
      let v := eval vm_compute in (2 ^ Zpos k) in change (2 ^ Zpos k) with v
  | H : context [2 ^ Zpos ?k] |- _ =>
      let v := eval vm_compute in (2 ^ Zpos k) in
      change (2 ^ Zpos k) with v in H
  end.

(** ** The sizes *)

Definition X_bits : Z := 170.  (* X = floor(|x| 2^P) < 2^170 *)
Definition n_bits : Z := 17.   (* the guess of n is below 2^17 *)
Definition r_bits : Z := 154.  (* RMAX, hence r, is below 2^154 *)
Definition h_bits : Z := 161.  (* every Horner value is below 2^161 *)
Definition t_bits : Z := 161.  (* every T_j is below 2^161 *)

(** ** X *)

(** The exponent and the mantissa, in the two cases of the C. *)
Lemma xexpo_0 xb : xbexp xb = 0 -> xexpo xb = 1 /\ xmant xb = xmant0 xb.
Proof. intros H; unfold xexpo, xmant; rewrite H; split; reflexivity. Qed.

Lemma xexpo_n xb : xbexp xb <> 0 ->
  xexpo xb = xbexp xb /\ xmant xb = xmant0 xb + 2 ^ 52.
Proof.
intros H; unfold xexpo, xmant; rewrite (proj2 (Z.eqb_neq _ _) H).
rewrite pow2E by discriminate; split; reflexivity.
Qed.

Lemma xmant0_bound xb : 0 <= xmant0 xb < 2 ^ 52.
Proof. rewrite xmant0E; apply Z.mod_pos_bound; reflexivity. Qed.

Lemma xbexp_bound xb : 0 <= xbexp xb < 2 ^ 11.
Proof. rewrite xbexpE; apply Z.mod_pos_bound; reflexivity. Qed.

Lemma xsign_bound xb : 0 <= xb < 2 ^ 64 -> 0 <= xsign xb < 2.
Proof.
intros H; rewrite xsignE; unfold sign_bit; split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|]; zpow; lia.
Qed.

Lemma xmant_bound xb : 0 <= xmant xb < 2 ^ 53.
Proof.
pose proof (xmant0_bound xb) as Hm.
destruct (Z.eqb_spec (xbexp xb) 0) as [H|H];
  [destruct (xexpo_0 xb H) as [_ ->]|destruct (xexpo_n xb H) as [_ ->]];
  zpow; lia.
Qed.

Lemma xexpo_bound xb : xbexp xb < be_big -> 1 <= xexpo xb < be_big.
Proof.
intros Hb; pose proof (xbexp_bound xb).
unfold xexpo, be_big in *; destruct (Z.eqb_spec (xbexp xb) 0); lia.
Qed.

Lemma xfixE xb : xfix xb = scale (xmant xb) (xexpo xb - 1075 + 160).
Proof. reflexivity. Qed.

Lemma xfix_bound xb : xbexp xb < be_big -> 0 <= xfix xb < 2 ^ X_bits.
Proof.
intros Hb.
pose proof (xmant_bound xb) as Hv; pose proof (xexpo_bound xb Hb) as Hx.
rewrite xfixE, scaleE.
unfold be_big, X_bits in *.
destruct (Z.leb_spec 0 (xexpo xb - 1075 + 160)) as [Hp|Hn].
- split; [apply Z.mul_nonneg_nonneg; lia|].
  apply Z.lt_le_trans with (2 ^ 53 * 2 ^ (xexpo xb - 1075 + 160)).
  + apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg|]; lia.
  + rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia.
- split; [apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia]|].
  apply Z.le_lt_trans with (xmant xb); [|lia].
  apply Z.div_le_upper_bound; [apply Z.pow_pos_nonneg; lia|].
  assert (1 <= 2 ^ (- (xexpo xb - 1075 + 160))).
  { apply (Z.pow_le_mono_r 2 0); lia. }
  nia.
Qed.

(** ** n *)

Lemma guess_bound X : 0 <= X < 2 ^ X_bits -> 0 <= guess X < 2 ^ n_bits.
Proof.
intros HX; rewrite guessE.
pose proof limb_INV as Hi; unfold limb, limb_bits in Hi.
unfold P, inv_shift, X_bits, n_bits in *.
split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; [lia|nia].
Qed.

(** The first correction of the guess: lowered when too big. *)
Definition red1 (X g : Z) : Z := if (X <? q g) && (0 <? g) then g - 1 else g.

(** The second: raised when too small. *)
Definition red2 (X n1 : Z) : Z := if X <? q (n1 + 1) then n1 else n1 + 1.

(** The n of [reduce], before its check. *)
Definition red_n (X : Z) : Z := red2 X (red1 X (guess X)).

Lemma reduceE X :
  reduce X = if (X <? q (red_n X)) || negb (X <? q (red_n X + 1))
             then None else Some (red_n X).
Proof. reflexivity. Qed.

Lemma red1_bound X g : 0 <= g < 2 ^ n_bits -> 0 <= red1 X g < 2 ^ n_bits.
Proof.
intros Hg; unfold red1.
destruct ((X <? q g) && (0 <? g)) eqn:E; [|lia].
apply andb_true_iff in E; destruct E as [_ E]; apply Z.ltb_lt in E; lia.
Qed.

Lemma red2_bound X n : 0 <= n < 2 ^ n_bits -> 0 <= red2 X n <= 2 ^ n_bits.
Proof. intros Hn; unfold red2; destruct (X <? q (n + 1)); lia. Qed.

Lemma red_n_bound X :
  0 <= X < 2 ^ X_bits -> 0 <= red_n X <= 2 ^ n_bits.
Proof.
intros HX; apply red2_bound, red1_bound, guess_bound, HX.
Qed.

Lemma LN2v_ge : 2 ^ (X_bits - n_bits + limb_bits) <= LN2v.
Proof. apply Z.leb_le; vm_compute; reflexivity. Qed.

(** A checked n is below 2^17: q(n) <= X < 2^170. *)
Lemma checked_n_bound X n :
  0 <= n -> q n <= X < 2 ^ X_bits -> n < 2 ^ n_bits.
Proof.
intros Hn [Hq HX].
pose proof LN2v_ge as HL.
assert (Hl : n * 2 ^ (X_bits - n_bits) <= q n).
{ unfold q; rewrite shrE by discriminate.
  apply Z.div_le_lower_bound; [reflexivity|].
  unfold X_bits, n_bits, limb_bits in *; nia. }
unfold X_bits, n_bits in *; nia.
Qed.

(** The check of [reduce], passed or failed. *)
Lemma reduce_some X :
  q (red_n X) <= X < q (red_n X + 1) -> reduce X = Some (red_n X).
Proof.
intros [H1 H2]; rewrite reduceE.
rewrite (proj2 (Z.ltb_ge _ _) H1), (proj2 (Z.ltb_lt _ _) H2); reflexivity.
Qed.

Lemma reduce_none X :
  X < q (red_n X) \/ q (red_n X + 1) <= X -> reduce X = None.
Proof.
intros H; rewrite reduceE.
destruct H as [H|H].
- rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity.
- rewrite (proj2 (Z.ltb_ge _ _) H), orb_true_r; reflexivity.
Qed.

(** ** r and the Horner values *)

Lemma RMAXv_lt : RMAXv < 2 ^ r_bits.
Proof. apply Z.ltb_lt; vm_compute; reflexivity. Qed.

Lemma Cv_bound i : (i <= DEG)%nat -> 0 <= Cv i <= 2 ^ P.
Proof.
intros Hi; rewrite CvE, C_ok by exact Hi.
pose proof (factN_gt0 i) as Hf.
split; [apply Z.div_pos; [apply Z.pow_nonneg|]; lia|].
apply Z.div_le_upper_bound; [lia|].
assert (0 < 2 ^ P) by (apply Z.pow_pos_nonneg; unfold P; lia); nia.
Qed.

(** One step of the loop keeps h below 2^161; its two calls fit. *)
Lemma horner_step h r i : 0 <= h < 2 ^ h_bits -> 0 <= r < 2 ^ r_bits ->
  (i <= DEG)%nat ->
  h * r < 2 ^ (P + limb_bits * Z.of_nat NL) /\
  0 <= mulshr h r /\ mulshr h r + Cv i < 2 ^ h_bits.
Proof.
intros Hh Hr Hi; pose proof (Cv_bound i Hi) as Hc.
rewrite mulshrE.
unfold h_bits, r_bits, P, limb_bits, NL in *; cbn [Z.of_nat Pos.of_succ_nat
  Pos.succ] in *.
split; [nia|split; [apply Z.div_pos; lia|]].
assert (h * r / 2 ^ 160 < 2 ^ 160); [|lia].
apply Z.div_lt_upper_bound; [lia|nia].
Qed.

(** H_i is reached from h and k more steps. *)
Lemma horner_from_S r h k :
  horner_from r h (S k) = horner_from r (mulshr h r + Cv k) k.
Proof. reflexivity. Qed.

Lemma horner_from_0 r h : horner_from r h 0 = h.
Proof. reflexivity. Qed.

Lemma horner_start r : horner r = horner_from r (Cv DEG) DEG.
Proof. reflexivity. Qed.

(** r and N + 2^17, for x >= 0 and for x < 0. *)
Lemma rarg_pos xb n : xsign xb = 0 ->
  rarg xb n = xfix xb - q n /\ Nu xb n = 2 ^ n_bits + n.
Proof. intros H; unfold rarg, Nu; rewrite H; split; reflexivity. Qed.

Lemma rarg_neg xb n : xsign xb <> 0 ->
  rarg xb n = q (n + 1) - xfix xb /\ Nu xb n = 2 ^ n_bits - (n + 1).
Proof.
intros H; unfold rarg, Nu; rewrite (proj2 (Z.eqb_neq _ _) H).
split; reflexivity.
Qed.

(** N + 2^17 is unsigned and below 2^18. *)
Lemma Nu_bound xb n : 0 <= n < 2 ^ n_bits -> 0 <= Nu xb n < 2 ^ (n_bits + 1).
Proof.
intros Hn; unfold Nu, N_bias, n_bits in *.
destruct (xsign xb =? 0); zpow; lia.
Qed.

(** ** T *)

Lemma Ts_bound : forallb (fun t => (0 <=? t) && (t <? 2 ^ t_bits)) Ts = true.
Proof. vm_compute; reflexivity. Qed.

Lemma Tv_bound j : 0 <= j < TAB -> 0 <= Tv j < 2 ^ t_bits.
Proof.
intros Hj; unfold Tv.
assert (Hl : length Ts = Z.to_nat TAB) by (vm_compute; reflexivity).
pose proof Ts_bound as H; rewrite forallb_forall in H.
specialize (H (nth (Z.to_nat j) Ts 0)).
rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in H; apply H, nth_In.
rewrite Hl; lia.
Qed.

(** ** The outcomes of core_Z *)

Lemma core_Z_big xb : be_big <= xbexp xb -> core_Z xb = inl rc_big.
Proof. intros H; unfold core_Z; rewrite (proj2 (Z.leb_le _ _) H); reflexivity. Qed.

Lemma core_Z_reduce xb : xbexp xb < be_big ->
  reduce (xfix xb) = None -> core_Z xb = inl rc_reduce.
Proof.
intros H1 H2; unfold core_Z; rewrite (proj2 (Z.leb_gt _ _) H1), H2.
reflexivity.
Qed.

Lemma core_Z_rmax xb n : xbexp xb < be_big ->
  reduce (xfix xb) = Some n -> RMAXv <= rarg xb n -> core_Z xb = inl rc_rmax.
Proof.
intros H1 H2 H3; unfold core_Z; rewrite (proj2 (Z.leb_gt _ _) H1), H2.
cbv beta iota zeta; rewrite (proj2 (Z.ltb_ge _ _) H3); reflexivity.
Qed.

Lemma core_Z_ok xb n : xbexp xb < be_big ->
  reduce (xfix xb) = Some n -> rarg xb n < RMAXv ->
  core_Z xb =
    inr (mulshr (Tv (jidx (Nu xb n))) (horner (rarg xb n)), hidx (Nu xb n)).
Proof.
intros H1 H2 H3; unfold core_Z; rewrite (proj2 (Z.leb_gt _ _) H1), H2.
cbv beta iota zeta; rewrite (proj2 (Z.ltb_lt _ _) H3); reflexivity.
Qed.
