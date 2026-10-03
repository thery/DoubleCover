(** * The sizes of the numbers of the integer model

    [core_Z] of ExpModel.v leaves out the sizes: the programs need them
    so that no word wraps and every call meets its precondition.  From
    |x| < 1024: X < 2^170, a checked n is in [0, 2^17), every C_i is in
    [0, 2^P], every T_j in [2^P, 2^161), every Horner value below 2^161,
    and y in [2^P, 2^162).  Also the steps of [reduce], the outcomes of
    [core_Z] and the bit lengths of [decide_Z], stated so that no tactic
    has to unfold the tables.  Pure Z, Stdlib only: shared by the Rocq,
    VST and Capla proofs. *)

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
Definition y_bits : Z := 162.  (* y is below 2^162 *)
Definition hN_bits : Z := 12.  (* |hN| <= 2^12 *)

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

(* X = floor(|x| 2^P) is below 2^170. *)
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

(* q(n) = floor(n LN2 / 2^32), with LN2 as a number. *)
Lemma qvE n : q n = n * LN2v / 2 ^ limb_bits.
Proof. unfold q; apply shrE; discriminate. Qed.

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

(* q(n) <= X < q(n+1) puts n in [0, 2^17). *)
Lemma n_bound X n : 0 <= X < 2 ^ X_bits -> q n <= X < q (n + 1) ->
  0 <= n < 2 ^ n_bits.
Proof.
intros HX [H1 H2]; rewrite !qvE in *; pose proof LN2v_ge as HL.
unfold X_bits, n_bits, limb_bits in *.
split.
- destruct (Z.leb_spec 0 n) as [|Hn]; [lia|].
  assert ((n + 1) * LN2v / 2 ^ 32 <= 0); [|lia].
  apply Z.div_le_upper_bound; [lia|]; zpow; nia.
- destruct (Z.ltb_spec n (2 ^ 17)) as [|Hn]; [lia|].
  assert (2 ^ 170 <= n * LN2v / 2 ^ 32); [|lia].
  apply Z.div_le_lower_bound; [lia|]; zpow; nia.
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

(** ** r *)

Lemma RMAXv_lt : RMAXv < 2 ^ r_bits.
Proof. apply Z.ltb_lt; vm_compute; reflexivity. Qed.

(* r >= 0 once n is checked. *)
Lemma rarg_ge0 xb n : q n <= xfix xb < q (n + 1) -> 0 <= rarg xb n.
Proof. unfold rarg; destruct (xsign xb =? 0); lia. Qed.

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

(** ** C and T *)

Lemma Cs_bound : forallb (fun c => (0 <=? c) && (c <=? 2 ^ P)) Cs = true.
Proof. vm_compute; reflexivity. Qed.

(* C_0 = 2^P. *)
Lemma Cv0 : Cv 0 = 2 ^ P.
Proof. vm_compute; reflexivity. Qed.

(* Every C_i is in [0, 2^P], also past DEG where it is 0. *)
Lemma Cv_bound i : 0 <= Cv i <= 2 ^ P.
Proof.
unfold Cv.
assert (HP : 0 <= 2 ^ P) by (apply Z.pow_nonneg; lia).
destruct (nth_in_or_default i Cs 0) as [Hi| ->]; [|lia].
pose proof Cs_bound as H; rewrite forallb_forall in H.
specialize (H _ Hi); rewrite andb_true_iff, !Z.leb_le in H; lia.
Qed.

Lemma Ts_bound :
  forallb (fun t => (2 ^ P <=? t) && (t <? 2 ^ t_bits)) Ts = true.
Proof. vm_compute; reflexivity. Qed.

Lemma Ts_length : length Ts = Z.to_nat TAB.
Proof. vm_compute; reflexivity. Qed.

(* Every T_j is in [2^P, 2^161). *)
Lemma Tv_bound j : 0 <= j < TAB -> 2 ^ P <= Tv j < 2 ^ t_bits.
Proof.
intros Hj; unfold Tv.
pose proof Ts_bound as H; rewrite forallb_forall in H.
specialize (H (nth (Z.to_nat j) Ts 0)).
rewrite andb_true_iff, Z.leb_le, Z.ltb_lt in H; apply H, nth_In.
rewrite Ts_length; lia.
Qed.

(** ** The Horner values *)

(* floor(a b / 2^P) >= 0 for a, b >= 0. *)
Lemma mulshr_ge0 a b : 0 <= a -> 0 <= b -> 0 <= mulshr a b.
Proof.
intros Ha Hb; rewrite mulshrE.
apply Z.div_pos; [nia|apply Z.pow_pos_nonneg; unfold P; lia].
Qed.

(* floor(h r / 2^P) < 2^155 for h < 2^161 and r < 2^154. *)
Lemma mulshr_bound h r : 0 <= h < 2 ^ h_bits -> 0 <= r < 2 ^ r_bits ->
  0 <= mulshr h r < 2 ^ (h_bits + r_bits - P).
Proof.
intros Hh Hr; rewrite mulshrE; unfold h_bits, r_bits, P in *.
change (161 + 154 - 160) with 155.
split; [apply Z.div_pos; [nia|lia]|].
apply Z.div_lt_upper_bound; [lia|].
rewrite <- Z.pow_add_r by lia; zpow; nia.
Qed.

(** One step of the loop keeps h below 2^161; its two calls fit. *)
Lemma horner_step h r i : 0 <= h < 2 ^ h_bits -> 0 <= r < 2 ^ r_bits ->
  h * r < 2 ^ (P + limb_bits * Z.of_nat NL) /\
  0 <= mulshr h r /\ mulshr h r + Cv i < 2 ^ h_bits.
Proof.
intros Hh Hr; pose proof (Cv_bound i) as Hc.
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

(* The Horner values stay below 2^161, and in [2^P, 2^161) once C_0 is
   added. *)
Lemma horner_from_bound r k : 0 <= r < 2 ^ r_bits -> forall h,
  0 <= h < 2 ^ h_bits ->
  0 <= horner_from r h k < 2 ^ h_bits /\
  ((0 < k)%nat -> 2 ^ P <= horner_from r h k).
Proof.
intros Hr; induction k as [|k IH]; intros h Hh.
{ rewrite horner_from_0; split; [lia|intros; lia]. }
rewrite horner_from_S.
destruct (horner_step h r k Hh Hr) as (_ & H0 & H1).
pose proof (Cv_bound k) as Hc.
assert (Hn : 0 <= mulshr h r + Cv k < 2 ^ h_bits) by lia.
destruct k as [|k].
- rewrite horner_from_0, Cv0 in *; split; [lia|intros; lia].
- destruct (IH _ Hn) as [IH1 IH2]; split; [lia|intros; apply IH2; lia].
Qed.

Lemma horner_bound r : 0 <= r < 2 ^ r_bits ->
  2 ^ P <= horner r < 2 ^ h_bits.
Proof.
intros Hr; rewrite horner_start.
assert (Hc : 0 <= Cv DEG < 2 ^ h_bits).
{ pose proof (Cv_bound DEG); unfold h_bits, P in *; zpow; lia. }
destruct (horner_from_bound r DEG Hr _ Hc) as [H1 H2].
split; [apply H2; unfold DEG; lia|lia].
Qed.

(* Every Horner value is >= 0, and the last one is >= C_0, for any r >= 0. *)
Lemma horner_from_ge r h k : 0 <= r -> 0 <= h ->
  (k = O -> Cv 0 <= h) -> Cv 0 <= horner_from r h k.
Proof.
intros Hr; revert h; induction k as [|i IH]; intros h Hh H0;
  [now apply H0|].
rewrite horner_from_S; pose proof (mulshr_ge0 h r Hh Hr).
pose proof (Cv_bound i).
apply IH; [lia|intros ->; lia].
Qed.

Lemma horner_ge r : 0 <= r -> 2 ^ P <= horner r.
Proof.
intros Hr; rewrite <- Cv0, horner_start; apply horner_from_ge; auto.
- apply Cv_bound.
- unfold DEG; discriminate.
Qed.

(** ** The outcomes of core_Z *)

(* the code of a failure, without unfolding the tables *)
Ltac proj_inl H :=
  apply (f_equal (fun s : Z + Z * Z =>
    match s with inl r => r | inr _ => 0 end)) in H;
  cbv beta iota in H.

(* A failure of core_Z is 1, 2 or 3. *)
Lemma core_Z_rc xb rc : core_Z xb = inl rc -> 1 <= rc <= 3.
Proof.
unfold core_Z.
destruct (be_big <=? xbexp xb).
{ intros H; proj_inl H; unfold rc_big in H; lia. }
destruct (reduce (xfix xb)) as [n|].
2: { intros H; proj_inl H; unfold rc_reduce in H; lia. }
cbv zeta.
destruct (negb (rarg xb n <? RMAXv)).
{ intros H; proj_inl H; unfold rc_rmax in H; lia. }
discriminate.
Qed.

Lemma core_Z_big xb : be_big <= xbexp xb -> core_Z xb = inl rc_big.
Proof.
intros H; unfold core_Z; rewrite (proj2 (Z.leb_le _ _) H); reflexivity.
Qed.

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

(* y is in [2^P, 2^162) and |hN| <= 2^12. *)
Lemma core_bounds xb y hN : core_Z xb = inr (y, hN) ->
  2 ^ P <= y < 2 ^ y_bits /\ - 2 ^ hN_bits <= hN <= 2 ^ hN_bits.
Proof.
intros H.
destruct (core_relP xb y hN H) as (n & Hbe & [Hq1 Hq2] & Hr & Hy & HhN).
pose proof (xfix_bound xb Hbe) as HX.
pose proof (n_bound _ n HX (conj Hq1 Hq2)) as Hn.
rewrite <- RMAXvE in Hr; pose proof RMAXv_lt.
assert (Hr0 : 0 <= rarg xb n < 2 ^ r_bits).
{ split; [|lia]; apply rarg_ge0; lia. }
pose proof (Nu_bound xb n Hn) as HN.
assert (Hj : 0 <= Nu xb n mod TAB < TAB).
{ apply Z.mod_pos_bound; reflexivity. }
pose proof (Tv_bound _ Hj) as HT.
pose proof (horner_bound _ Hr0) as HH.
rewrite Hy, mulshrE, HhN.
unfold y_bits, hN_bits, t_bits, h_bits, n_bits, P in *.
split.
- split.
  + apply Z.div_le_lower_bound; [lia|nia].
  + apply Z.div_lt_upper_bound; [lia|].
    rewrite <- Z.pow_add_r by lia; zpow; nia.
- replace hN_bias with 2048 by reflexivity.
  unfold TAB; zpow.
  assert (0 <= Nu xb n / 64 <= 4096); [|lia].
  split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia].
Qed.

(** ** Bit lengths and the decision *)

(* The bit length of a number of 192 bits. *)
Lemma bitlen_bound v : 0 <= v < 2 ^ num_bits -> 0 <= bitlen v <= num_bits.
Proof.
intros Hv; unfold bitlen.
destruct (Z.leb_spec v 0); [unfold num_bits; cbn; lia|].
pose proof (Z.log2_nonneg v).
assert (Z.log2 v < num_bits) by (apply Z.log2_lt_pow2; lia); lia.
Qed.

(** If y - D and y + D have b bits, they lie in [2^(b-1), 2^b). *)
Lemma bitlen_range y b : D < y ->
  bitlen (y - D) = b -> bitlen (y + D) = b ->
  1 <= b /\ 2 ^ (b - 1) <= y - D /\ y + D < 2 ^ b.
Proof.
intros Hy Hb1 Hb2; unfold bitlen in Hb1, Hb2.
assert (HD : 0 < D) by (unfold D; lia).
destruct (Z.leb_spec (y - D) 0) as [|_]; [lia|].
destruct (Z.leb_spec (y + D) 0) as [|_]; [lia|].
pose proof (Z.log2_spec (y - D) ltac:(lia)).
pose proof (Z.log2_spec (y + D) ltac:(lia)).
pose proof (Z.log2_nonneg (y - D)).
replace (b - 1) with (Z.log2 (y - D)) by lia.
replace b with (Z.succ (Z.log2 (y + D))) by lia; lia.
Qed.

(* A value of [y - D, y + D] out of the binade of y: hard. *)
Lemma decide_bits y hN :
  bitlen (y - D) <> bitlen y \/ bitlen (y + D) <> bitlen y ->
  decide_Z y hN = 1.
Proof.
intros H; unfold decide_Z; cbv zeta.
destruct H as [H|H].
- rewrite (proj2 (Z.eqb_neq _ _) H); reflexivity.
- rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r; reflexivity.
Qed.

(* The decision once the binade is known, with f as the C computes it. *)
Lemma decide_f y hN f :
  bitlen (y - D) = bitlen y -> bitlen (y + D) = bitlen y ->
  f = Z.max (hN - P + bitlen y - 1) emin - prec - (hN - P) ->
  decide_Z y hN =
  if (f <? f_min) || (f_max <? f) then 1 else
  let lo := low y f in
  let hi := pow2 f - lo in
  let d := if lo <? hi then lo else hi in
  if pow2 (f - m_hard) + D <? d then 0 else 1.
Proof.
intros H1 H2 Hf; unfold decide_Z; cbv zeta.
rewrite H1, H2, Z.eqb_refl; cbn [andb negb].
subst f; reflexivity.
Qed.
