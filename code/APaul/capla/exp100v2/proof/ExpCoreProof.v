(** * exp_core: the reduction, the Horner loop and the table *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpTable ExpConsts ExpModel ExpModelBounds.
Require Import Exp100Capla2.exp100 Exp100Capla2.Bridge Exp100Capla2.Specs.
Require Import Exp100Capla2.LimbLemmas.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** The words of exp_core *)

Section CoreWords.
Transparent Int64.repr Int64.unsigned Int.repr Int.unsigned Int.modu.

Lemma max_unsigned64 : Int64.max_unsigned = 18446744073709551615%Z.
Proof. by []. Qed.

(* c >> k, for a shift amount below 64 *)
Lemma shru_k (c : int64) k : (0 <= k < 64)%Z ->
  Int64.unsigned (Int64.shru' c (Int.modu (Int.repr k) Int64.iwordsize')) =
  (Int64.unsigned c / 2 ^ k)%Z.
Proof.
  move=> Hk.
  have Ek : Int.unsigned (Int.repr k) = k.
  { rewrite Int.unsigned_repr //; change Int.max_unsigned with 4294967295%Z; lia. }
  have -> : Int.modu (Int.repr k) Int64.iwordsize' = Int.repr k.
  { rewrite /Int.modu Ek; f_equal; apply: Z.mod_small.
    change (Int.unsigned Int64.iwordsize') with 64%Z; lia. }
  rewrite /Int64.shru' Ek Z.shiftr_div_pow2; first lia.
  have := Int64.unsigned_range c; have := Z.pow_pos_nonneg 2 k ltac:(lia) (proj1 Hk).
  move=> H2 Hc.
  have := Z.div_le_upper_bound (Int64.unsigned c) (2 ^ k) (Int64.unsigned c) H2
    ltac:(nia).
  have := Z.div_pos (Int64.unsigned c) (2 ^ k) ltac:(lia) H2.
  move=> ? ?; rewrite Int64.unsigned_repr // max_unsigned64.
  change Int64.modulus with 18446744073709551616%Z in Hc; lia.
Qed.

(* c & (2^k - 1) *)
Lemma and_low (c : int64) k : (0 <= k < 64)%Z ->
  Int64.unsigned (Int64.and c (Int64.repr (2 ^ k - 1))) =
  (Int64.unsigned c mod 2 ^ k)%Z.
Proof.
  move=> Hk.
  have := Int64.zero_ext_and k c (proj1 Hk); rewrite two_p_equiv => <-.
  rewrite Int64.zero_ext_mod ?two_p_equiv //.
Qed.

(* m | 2^52, for m < 2^52 *)
Lemma or_top (m : int64) : (Int64.unsigned m < 2 ^ 52)%Z ->
  Int64.unsigned (Int64.or m (Int64.repr 4503599627370496)) =
  (Int64.unsigned m + 2 ^ 52)%Z.
Proof.
  move=> Hm.
  have Ec : Int64.unsigned (Int64.repr 4503599627370496) = (1 * 2 ^ 52)%Z by [].
  have R := Int64.unsigned_range m.
  rewrite /Int64.or Ec lor_add; [lia|lia|].
  rewrite Int64.unsigned_repr; first (rewrite max_unsigned64; lia).
  lia.
Qed.

End CoreWords.

(* The sign, the biased exponent and the stored mantissa of xb. *)
Lemma neg_val (xb : int64) :
  Int64.unsigned (Int64.shru' xb (Int.modu (Int.repr 63) Int64.iwordsize')) =
  ExpModel.xsign (Int64.unsigned xb).
Proof. by rewrite shru_k // ExpModel.xsignE. Qed.

Lemma be_val (xb : int64) :
  Int64.unsigned (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) = ExpModel.xbexp (Int64.unsigned xb).
Proof.
  have -> : Int64.repr 2047 = Int64.repr (2 ^ 11 - 1) by [].
  by rewrite and_low // shru_k // ExpModel.xbexpE.
Qed.

Lemma mx_val (xb : int64) :
  Int64.unsigned (Int64.and xb (Int64.repr 4503599627370495)) =
  ExpModel.xmant0 (Int64.unsigned xb).
Proof.
  have -> : Int64.repr 4503599627370495 = Int64.repr (2 ^ 52 - 1) by [].
  by rewrite and_low // ExpModel.xmant0E.
Qed.

(* A failure: the return code is that of core_Z. *)
Lemma rc_fail (x k : Z) (P : Prop) : (1 <= k <= 3)%Z ->
  ExpModel.core_Z x = inl k ->
  (Int64.unsigned (Int64.repr k) <> 0 ->
     ExpModel.core_Z x = inl (Int64.unsigned (Int64.repr k))) /\
  (Int64.unsigned (Int64.repr k) = 0 -> P).
Proof.
  move=> Hk Hc.
  rewrite Int64.unsigned_repr; first by rewrite max_unsigned64; lia.
  by split=> // H; lia.
Qed.

(* be >= 1033: |x| >= 1024 *)
Lemma core_big (xb : int64) :
  Int64.ltu (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 1033) = false ->
  ExpModel.core_Z (Int64.unsigned xb) = inl ExpModel.rc_big.
Proof.
  move=> H; apply: ExpModelBounds.core_Z_big; rewrite -be_val.
  move: H; rewrite /Int64.ltu; case: Coqlib.zlt => // + _.
  rewrite /ExpModel.be_big Int64.unsigned_repr; first by rewrite max_unsigned64.
  lia.
Qed.

(* be < 1033 *)
Lemma core_small (xb : int64) :
  Int64.ltu (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 1033) = true ->
  (ExpModel.xbexp (Int64.unsigned xb) < ExpModel.be_big)%Z.
Proof. by rewrite /Int64.ltu be_val; case: Coqlib.zlt. Qed.

(* be = 0: a subnormal x, exponent 1, no implicit bit *)
Lemma be_merge0 (xb : int64) :
  Int64.eq (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 0) = true ->
  Int64.repr 1 = Int64.repr (ExpModel.xexpo (Int64.unsigned xb)) /\
  Int64.and xb (Int64.repr 4503599627370495) =
    Int64.repr (ExpModel.xmant (Int64.unsigned xb)).
Proof.
  move=> H.
  have E0 : ExpModel.xbexp (Int64.unsigned xb) = 0%Z.
  { rewrite -be_val; move: H; rewrite /Int64.eq; case: Coqlib.zeq => // -> _. }
  have [-> ->] := ExpModelBounds.xexpo_0 _ E0.
  by rewrite -mx_val Int64.repr_unsigned.
Qed.

(* be <> 0: a normal x, the implicit bit is set *)
Lemma be_merge1 (xb : int64) :
  Int64.eq (Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047)) (Int64.repr 0) = false ->
  Int64.and (Int64.shru' xb (Int.modu (Int.repr 52) Int64.iwordsize'))
    (Int64.repr 2047) = Int64.repr (ExpModel.xexpo (Int64.unsigned xb)) /\
  Int64.or (Int64.and xb (Int64.repr 4503599627370495))
    (Int64.repr 4503599627370496) =
    Int64.repr (ExpModel.xmant (Int64.unsigned xb)).
Proof.
  move=> H.
  have N0 : ExpModel.xbexp (Int64.unsigned xb) <> 0%Z.
  { rewrite -be_val; move: H; rewrite /Int64.eq; case: Coqlib.zeq => // + _. }
  have [E1 E2] := ExpModelBounds.xexpo_n _ N0.
  rewrite E1 E2.
  have Bm := ExpModelBounds.xmant0_bound (Int64.unsigned xb).
  split; first by rewrite -be_val Int64.repr_unsigned.
  rewrite -(Int64.repr_unsigned (Int64.or _ _)) or_top ?mx_val //; lia.
Qed.

(* The arguments of num_scale: X = floor(|x| 2^P). *)
Lemma scale_args (x : Z) : (ExpModel.xbexp x < ExpModel.be_big)%Z ->
  (Int64.unsigned (Int64.repr (ExpModel.xmant x)) < 2 ^ mant_bits)%Z /\
  (Int64.signed (Int64.sub (Int64.repr (ExpModel.xexpo x)) (Int64.repr 915))
     < scale_emax)%Z /\
  ExpModel.scale (Int64.unsigned (Int64.repr (ExpModel.xmant x)))
    (Int64.signed (Int64.sub (Int64.repr (ExpModel.xexpo x)) (Int64.repr 915))) =
  ExpModel.xfix x.
Proof.
  move=> Hb.
  have Bm := ExpModelBounds.xmant_bound x.
  have Be := ExpModelBounds.xexpo_bound x Hb.
  move: Bm Be; rewrite /ExpModel.be_big /mant_bits /scale_emax => Bm Be.
  have Em : Int64.unsigned (Int64.repr (ExpModel.xmant x)) = ExpModel.xmant x.
  { rewrite Int64.unsigned_repr // max_unsigned64; lia. }
  have Ee : Int64.signed (Int64.sub (Int64.repr (ExpModel.xexpo x)) (Int64.repr 915)) =
            (ExpModel.xexpo x - 915)%Z.
  { have Sr : forall z, (-2000 <= z <= 2000)%Z -> Int64.signed (Int64.repr z) = z.
    { move=> z Hz; apply: Int64.signed_repr.
      change Int64.min_signed with (-9223372036854775808)%Z.
      change Int64.max_signed with 9223372036854775807%Z; lia. }
    rewrite Int64.sub_signed (Sr (ExpModel.xexpo x) ltac:(lia)) (Sr 915 ltac:(lia)).
    by rewrite Sr //; lia. }
  rewrite Em Ee ExpModelBounds.xfixE; split; [lia|split; [lia|]].
  by f_equal; lia.
Qed.

(** ** The reduction, on words *)

(* a value below 2^20 is its own unsigned word *)
Lemma unsigned_small20 n : (0 <= n < 1048576)%Z ->
  Int64.unsigned (Int64.repr n) = n.
Proof. by move=> H; rewrite Int64.unsigned_repr // max_unsigned64; lia. Qed.

(* n + 1 *)
Lemma add1_word n : (0 <= n < 524288)%Z ->
  Int64.add (Int64.repr n) (Int64.repr 1) = Int64.repr (n + 1).
Proof.
  move=> H.
  by rewrite /Int64.add (unsigned_small20 n ltac:(lia)) (unsigned_small20 1 ltac:(lia)).
Qed.

(* a small value is a limb *)
Lemma limb_small n : (0 <= n < 1048576)%Z -> limb (Int64.unsigned (Int64.repr n)).
Proof. by move=> H; rewrite unsigned_small20 // /limb /limb_bits; lia. Qed.

Lemma n_lt17 n : (0 <= n < 2 ^ ExpModelBounds.n_bits)%Z -> (0 <= n < 524288)%Z.
Proof. by rewrite /ExpModelBounds.n_bits; lia. Qed.

Lemma n_le17 n : (0 <= n <= 2 ^ ExpModelBounds.n_bits)%Z -> (0 <= n < 524288)%Z.
Proof. by rewrite /ExpModelBounds.n_bits; lia. Qed.

Lemma small_succ n : (0 <= n < 524288)%Z -> (0 <= n + 1 < 1048576)%Z.
Proof. lia. Qed.

Lemma small_le n : (0 <= n < 524288)%Z -> (0 <= n < 1048576)%Z.
Proof. lia. Qed.

(* the first correction of the guess, its three paths *)
Lemma red1_dec X g : (0 <= g < 1048576)%Z ->
  (X <? ExpModel.q g)%Z = true ->
  Int64.ltu (Int64.repr 0) (Int64.repr g) = true ->
  Int64.sub (Int64.repr g) (Int64.repr 1) =
    Int64.repr (ExpModelBounds.red1 X g).
Proof.
  move=> Hg H1; rewrite /Int64.ltu (unsigned_small20 0 ltac:(lia)).
  rewrite (unsigned_small20 g Hg).
  case: Coqlib.zlt => // H2 _.
  rewrite /ExpModelBounds.red1 H1 (proj2 (Z.ltb_lt _ _) H2) /Int64.sub.
  by rewrite (unsigned_small20 1 ltac:(lia)) (unsigned_small20 g Hg).
Qed.

Lemma red1_zero X g : (0 <= g < 1048576)%Z ->
  (X <? ExpModel.q g)%Z = true ->
  Int64.ltu (Int64.repr 0) (Int64.repr g) = false ->
  Int64.repr g = Int64.repr (ExpModelBounds.red1 X g).
Proof.
  move=> Hg H1; rewrite /Int64.ltu (unsigned_small20 0 ltac:(lia)).
  rewrite (unsigned_small20 g Hg).
  case: Coqlib.zlt => // H2 _.
  by rewrite /ExpModelBounds.red1 H1 (proj2 (Z.ltb_ge 0 g) ltac:(lia)).
Qed.

Lemma red1_keep X g :
  (X <? ExpModel.q g)%Z = false ->
  Int64.repr g = Int64.repr (ExpModelBounds.red1 X g).
Proof. by move=> H1; rewrite /ExpModelBounds.red1 H1. Qed.

(* the second correction *)
Lemma red2_keep X n : (X <? ExpModel.q (n + 1))%Z = true ->
  Int64.repr n = Int64.repr (ExpModelBounds.red2 X n).
Proof. by move=> H; rewrite /ExpModelBounds.red2 H. Qed.

Lemma red2_inc X n : (0 <= n < 524288)%Z -> (X <? ExpModel.q (n + 1))%Z = false ->
  Int64.add (Int64.repr n) (Int64.repr 1) = Int64.repr (ExpModelBounds.red2 X n).
Proof. by move=> Hn H; rewrite /ExpModelBounds.red2 H add1_word. Qed.

(** ** The sign and N + 2^17 *)

(* the sign bit of x, as the test neg == 1 reads it *)
Lemma sign_true (xb : int64) :
  Int64.eq (Int64.shru' xb (Int.modu (Int.repr 63) Int64.iwordsize'))
    (Int64.repr 1) = true -> ExpModel.xsign (Int64.unsigned xb) <> 0%Z.
Proof.
  rewrite /Int64.eq neg_val (unsigned_small20 1 ltac:(lia)).
  by case: Coqlib.zeq => // ->.
Qed.

Lemma sign_false (xb : int64) :
  Int64.eq (Int64.shru' xb (Int.modu (Int.repr 63) Int64.iwordsize'))
    (Int64.repr 1) = false -> ExpModel.xsign (Int64.unsigned xb) = 0%Z.
Proof.
  rewrite /Int64.eq neg_val (unsigned_small20 1 ltac:(lia)).
  case: Coqlib.zeq => // H _.
  have := ExpModelBounds.xsign_bound (Int64.unsigned xb).
  have := Int64.unsigned_range xb.
  change Int64.modulus with (2 ^ 64)%Z; lia.
Qed.

(* N + 2^17 for x < 0 and for x >= 0 *)
Lemma nu_neg n : (0 <= n < 131072)%Z ->
  Int64.sub (Int64.repr 131072) (Int64.repr (n + 1)) =
  Int64.repr (2 ^ ExpModelBounds.n_bits - (n + 1)).
Proof.
  move=> H; rewrite /Int64.sub (unsigned_small20 131072 ltac:(lia)).
  by rewrite (unsigned_small20 (n + 1) ltac:(lia)).
Qed.

Lemma nu_pos n : (0 <= n < 131072)%Z ->
  Int64.add (Int64.repr 131072) (Int64.repr n) =
  Int64.repr (2 ^ ExpModelBounds.n_bits + n).
Proof.
  move=> H; rewrite /Int64.add (unsigned_small20 131072 ltac:(lia)).
  by rewrite (unsigned_small20 n ltac:(lia)).
Qed.

(** ** The tables, row by row *)

(* RMAX: its limbs and its value *)
Lemma RM_row (RM : numA) : words RM = ExpTable.RMAX ->
  limbsA RM /\ valA RM = ExpModel.RMAXv.
Proof.
  move=> H; split.
  - by apply/limbsA_Forall; rewrite H; exact: (proj2 ExpConsts.num_RMAX).
  - by rewrite /valA H ExpModel.RMAXvE.
Qed.

(* Row i of C: C_i *)
Lemma Ca_row (Ca : {ffun 'I_CLn -> numA}) :
  (forall i : 'I_CLn, words (Ca i) = nth [::] ExpTable.C i) ->
  forall i : 'I_CLn, limbsA (Ca i) /\ valA (Ca i) = ExpModel.Cv i.
Proof.
  move=> HC i; have Hi := ltn_ord i.
  have Hin : List.In (List.nth i ExpTable.C [::]) ExpTable.C.
  { apply: List.nth_In; rewrite ExpConsts.length_C; apply/ltP; exact: Hi. }
  split.
  - apply/limbsA_Forall; rewrite HC nth_List_nth.
    exact: (proj2 (proj1 (List.Forall_forall _ _) ExpConsts.num_C _ Hin)).
  - by rewrite /valA HC nth_List_nth ExpModel.CvE.
Qed.

(* Row j of T: T_j *)
Lemma Ta_row (Ta : {ffun 'I_TABn -> numA}) :
  (forall j : 'I_TABn, words (Ta j) = nth [::] ExpTable.T j) ->
  forall j : 'I_TABn, limbsA (Ta j) /\ valA (Ta j) = ExpModel.Tv (Z.of_nat j).
Proof.
  move=> HT j; have Hj := ltn_ord j.
  have Hin : List.In (List.nth j ExpTable.T [::]) ExpTable.T.
  { apply: List.nth_In; rewrite ExpConsts.length_T; apply/ltP; exact: Hj. }
  split.
  - apply/limbsA_Forall; rewrite HT nth_List_nth.
    exact: (proj2 (proj1 (List.Forall_forall _ _) ExpConsts.num_T _ Hin)).
  - by rewrite /valA HT nth_List_nth ExpModel.TvE Nat2Z.id.
Qed.

(** ** j, hN and the Horner loop *)

(* j = N mod 64 *)
Lemma jidx_word N : (0 <= N < 2 ^ 18)%Z ->
  Int64.unsigned (Int64.and (Int64.repr N) (Int64.repr 63)) = ExpModel.jidx N.
Proof.
  move=> H.
  have -> : Int64.repr 63 = Int64.repr (2 ^ 6 - 1) by [].
  rewrite and_low // Int64.unsigned_repr ?max_unsigned64; first lia.
  by rewrite ExpModel.jidxE.
Qed.

(* hN = floor(N / 64) - 2048 *)
Lemma hidx_word N : (0 <= N < 2 ^ 18)%Z ->
  Int64.signed (Int64.sub (Int64.shru' (Int64.repr N)
    (Int.modu (Int.repr 6) Int64.iwordsize')) (Int64.repr 2048)) =
  ExpModel.hidx N.
Proof.
  move=> H.
  have E : Int64.unsigned (Int64.shru' (Int64.repr N)
             (Int.modu (Int.repr 6) Int64.iwordsize')) = (N / 2 ^ 6)%Z.
  { rewrite shru_k // Int64.unsigned_repr // max_unsigned64; lia. }
  have B : (0 <= N / 2 ^ 6 <= 4096)%Z.
  { split; [apply: Z.div_pos; lia|apply: Z.div_le_upper_bound; lia]. }
  rewrite /Int64.sub E (unsigned_small20 2048 ltac:(lia)) ExpModel.hidxE.
  rewrite Int64.signed_repr; last by [].
  change Int64.min_signed with (-9223372036854775808)%Z.
  change Int64.max_signed with 9223372036854775807%Z; lia.
Qed.

(* One round of the loop: H_(16-k) from H_(16-k-1) *)
Lemma horner_from_step r h k : (k < 16)%nat ->
  ExpModel.horner_from r h (16 - k) =
  ExpModel.horner_from r (ExpModel.mulshr h r + ExpModel.Cv (15 - k)) (16 - k.+1).
Proof.
  move=> Hk; have -> : (16 - k = (15 - k).+1)%nat by rewrite subSn.
  by rewrite subSS.
Qed.

(* j as an index of T *)
Lemma jidx_ord N (H : ((Int64.and (Int64.repr N) (Int64.repr 63)):N < TABn)%nat) :
  (0 <= N < 2 ^ 18)%Z -> Z.of_nat (Ordinal H) = ExpModel.jidx N.
Proof.
  move=> HN; rewrite -(jidx_word N HN) /=.
  rewrite Z2Nat.id //; exact: (proj1 (Int64.unsigned_range _)).
Qed.

(* T_j H_0 fits in the product of num_mulshr *)
Lemma table_fit a b :
  (2 ^ ExpConsts.P <= a < 2 ^ ExpModelBounds.t_bits)%Z ->
  (2 ^ ExpConsts.P <= b < 2 ^ ExpModelBounds.h_bits)%Z ->
  (a * b < 2 ^ (ExpConsts.P + ExpModel.num_bits))%Z.
Proof.
  move=> Ha Hb.
  have Hc : (2 ^ ExpModelBounds.t_bits * 2 ^ ExpModelBounds.h_bits <=
             2 ^ (ExpConsts.P + ExpModel.num_bits))%Z.
  { by apply/Z.leb_le; vm_compute. }
  apply: (Z.lt_le_trans _ _ _ _ Hc).
  have P0 : (0 <= 2 ^ ExpConsts.P)%Z by apply: Z.pow_nonneg.
  apply: Z.mul_lt_mono_nonneg; lia.
Qed.

(* h_bits < num_bits *)
Lemma h_num : (2 ^ ExpModelBounds.h_bits < 2 ^ ExpModel.num_bits)%Z.
Proof. by apply/Z.ltb_lt; vm_compute. Qed.

(* Writing hs[0] *)
Lemma hs_write (hs : {ffun 'I_1 -> int64}) (v : int64) :
  (hs ↑[ (Int64.repr 0):N ← v ]) ord0 = v.
Proof. by rewrite (setfP _ _ _ (isT : ((Int64.repr 0):N < 1)%nat)). Qed.

(* The start of the loop: H_16 = C_16 *)
Lemma horner_init R : ExpModel.horner_from R (ExpModel.Cv 16)
  (16 - (Int64.repr 0):N) = ExpModel.horner R.
Proof.
  have -> : (((Int64.repr 0):N) = 0)%nat by [].
  by rewrite subn0 ExpModelBounds.horner_start /ExpConsts.DEG.
Qed.

Theorem exp_core_ok :
  guess_n_spec -> mul_ln2_spec -> num_add_spec -> num_copy_spec ->
  num_lt_spec -> num_mulshr_spec -> num_scale_spec -> num_sub_spec ->
  exp_core_spec.
Proof.
move=> GN ML NA NC NLT NM NS NSB μ xb y hs X q q1 rr h t Ta Ca L2 RM r rl Hok.
enter_func; csteps.
(* |x| >= 1024 *)
case B1: Int64.ltu => /=; last first.
{ csteps; cret.
  do 9 eexists; split; first by []. split; first by [].
  by apply: rc_fail; [rewrite /=; lia | exact: core_big]. }
have Hsm := core_small xb B1.
csteps.
(* be = 0 or not: the two paths meet with be = xexpo, mx = xmant *)
evar (G : Prop).
enough (HG : G).
{ case B2: Int64.eq => /=; csteps; rewrite/call/= /envC/=; evalf.
  - have [E1 E2] := be_merge0 xb B2.
    rewrite E2 [X in Int64.sub X _]E1.
    generalize (Vint64 (Int64.repr 1)) (Vbool true).
    exact HG.
  - have [E1 E2] := be_merge1 xb B2.
    rewrite E1 E2.
    generalize (Vbool false) at 2.
    generalize (Vint64 (Int64.repr (ExpModel.xexpo (Int64.unsigned xb)))).
    exact HG. }
subst G; move=> vbe vb.
(* X = floor(|x| 2^P) *)
have [Hv [He Hsc]] := scale_args _ Hsm.
case E: eval_func => [[]|] //=; move/(NS _ _ _ _ _ _ Hv He): E => [X1 [-> [LX1 VX1]]].
rewrite Hsc in VX1.
csteps.
(* the guess g of n *)
call GN => /(_ LX1) [-> ->].
csteps.
have [HTa [HCa [HL2 HRM]]] := Hok.
have RX := ExpModelBounds.xfix_bound _ Hsm.
have Rg : (0 <= ExpModel.guess (valA X1) < 2 ^ ExpModelBounds.n_bits)%Z.
{ by apply: ExpModelBounds.guess_bound; rewrite VX1. }
have Ug : Int64.unsigned (Int64.repr (ExpModel.guess (valA X1))) =
          ExpModel.guess (valA X1).
{ rewrite Int64.unsigned_repr // max_unsigned64.
  by move: Rg; rewrite /ExpModelBounds.n_bits; lia. }
have Lg : limb (Int64.unsigned (Int64.repr (ExpModel.guess (valA X1)))).
{ by rewrite Ug /limb /limb_bits; move: Rg; rewrite /ExpModelBounds.n_bits; lia. }
(* q = q(g), lt = X < q *)
call ML => /(_ HL2 Lg) [q3 [-> [Lq3 Vq3]]].
csteps.
call NLT => /(_ LX1 Lq3) [-> ->].
csteps.
rewrite Vq3 Ug.
have Rg20 : (0 <= ExpModel.guess (valA X1) < 1048576)%Z.
{ by move: Rg; rewrite /ExpModelBounds.n_bits; lia. }
set n1 := ExpModelBounds.red1 (valA X1) (ExpModel.guess (valA X1)).
have Rn1 : (0 <= n1 < 2 ^ ExpModelBounds.n_bits)%Z.
{ exact: ExpModelBounds.red1_bound. }
have Rn1' := n_lt17 _ Rn1.
(* n1: the guess lowered once if X < q(g) and g > 0; three paths *)
case LT1: (valA X1 <? _) => /=; csteps.
1: case LT2: Int64.ltu => /=; csteps.
1: rewrite (red1_dec _ _ Rg20 LT1 LT2) -/n1.
2: rewrite (red1_zero _ _ Rg20 LT1 LT2) -/n1.
3: rewrite (red1_keep _ _ LT1) -/n1.
(* q1 = q(n1 + 1), lt = X < q1 *)
all: rewrite (add1_word n1 Rn1').
all: have Ln1 := limb_small _ (small_succ _ Rn1').
all: call ML => /(_ HL2 Ln1) [q4 [-> [Lq4 Vq4]]].
all: csteps.
all: call NLT => /(_ LX1 Lq4) [-> ->].
all: csteps.
all: rewrite Vq4 (unsigned_small20 _ (small_succ _ Rn1')).
(* n2: n1 raised once if X >= q(n1 + 1); two paths *)
all: set n2 := ExpModelBounds.red2 (valA X1) n1.
all: case LT3: (valA X1 <? ExpModel.q (n1 + 1)) => /=; csteps.
all: match goal with
  | LT3 : (_ <? ExpModel.q (_ + 1))%Z = true |- _ => rewrite (red2_keep _ _ LT3) -/n2
  | LT3 : (_ <? ExpModel.q (_ + 1))%Z = false |- _ => rewrite (red2_inc _ _ Rn1' LT3) -/n2
  end.
all: have Rn2 : (0 <= n2 <= 2 ^ ExpModelBounds.n_bits)%Z :=
       ExpModelBounds.red2_bound (valA X1) n1 Rn1.
all: have Rn2' := n_le17 _ Rn2.
(* q = q(n2), q1 = q(n2 + 1) *)
all: have Ln2 := limb_small _ (small_le _ Rn2').
all: call ML => /(_ HL2 Ln2) [q5 [-> [Lq5 Vq5]]].
all: csteps.
all: rewrite (add1_word n2 Rn2').
all: have Ln21 := limb_small _ (small_succ _ Rn2').
all: call ML => /(_ HL2 Ln21) [q6 [-> [Lq6 Vq6]]].
all: csteps.
(* the check q(n2) <= X < q(n2 + 1) *)
all: call NLT => /(_ LX1 Lq5) [-> ->].
all: csteps.
all: rewrite Vq5 (unsigned_small20 _ (small_le _ Rn2')).
all: have Hred : n2 = ExpModelBounds.red_n (valA X1) by [].
all: case LT4: (valA X1 <? ExpModel.q n2) => /=.
all: lazymatch type of LT4 with _ = true => csteps; cret | _ => idtac end.
all: lazymatch type of LT4 with _ = true =>
  do 9 eexists; split; [by []|]; split; [by []|];
  apply: rc_fail; first by rewrite /=; lia
  | _ => idtac end.
all: lazymatch type of LT4 with _ = true =>
  apply: (ExpModelBounds.core_Z_reduce _ Hsm);
  apply: ExpModelBounds.reduce_none; left; rewrite -VX1 -Hred; apply/Z.ltb_lt; exact: LT4
  | _ => idtac end.
all: csteps.
all: call NLT => /(_ LX1 Lq6) [-> ->].
all: rewrite Vq6 (unsigned_small20 _ (small_succ _ Rn2')).
all: case LT5: (valA X1 <? ExpModel.q (n2 + 1)) => /=.
all: lazymatch type of LT5 with _ = false => csteps; cret | _ => idtac end.
all: lazymatch type of LT5 with _ = false =>
  do 9 eexists; split; [by []|]; split; [by []|];
  apply: rc_fail; first by rewrite /=; lia
  | _ => idtac end.
all: lazymatch type of LT5 with _ = false =>
  apply: (ExpModelBounds.core_Z_reduce _ Hsm);
  apply: ExpModelBounds.reduce_none; right; rewrite -VX1 -Hred; apply/Z.ltb_ge; exact: LT5
  | _ => idtac end.
(* n2 is checked: reduce X = Some n2 *)
all: have Hq : (ExpModel.q n2 <= ExpModel.xfix (Int64.unsigned xb) <
                ExpModel.q (n2 + 1))%Z
  by rewrite -VX1; split; [apply/Z.ltb_ge|apply/Z.ltb_lt].
all: have Hrs : ExpModel.reduce (ExpModel.xfix (Int64.unsigned xb)) = Some n2
  by rewrite Hred -VX1; apply: ExpModelBounds.reduce_some; rewrite -Hred VX1.
all: have Rn2b := ExpModelBounds.n_bound _ _ RX Hq.
(* r and N + 2^17, for x < 0 and for x >= 0 *)
all: clear LT1 LT3 Ln1 Lq3 Vq3 Lq4 Vq4 Ln2 Ln21 Lg Ug Rg Rg20.
all: try clear LT2.
all: csteps.
all: case B3: Int64.eq => /=; csteps.
all: call NC => ->.
all: csteps.
all: have Hle5 : (valA X1 <= valA q6)%Z.
all: first [by rewrite Vq6 (unsigned_small20 _ (small_succ _ Rn2')); move/Z.ltb_lt: LT5; lia | idtac].
all: have Hle4 : (valA q5 <= valA X1)%Z.
all: first [by rewrite Vq5 (unsigned_small20 _ (small_le _ Rn2')); move/Z.ltb_ge: LT4; lia | idtac].
all: lazymatch type of B3 with
  | _ = true => call NSB => /(_ Lq6 LX1 Hle5) [r1 [-> [Lr1 Vr1]]]
  | _ = false => call NSB => /(_ LX1 Lq5 Hle4) [r1 [-> [Lr1 Vr1]]]
  end.
all: csteps.
all: have Hr : valA r1 = ExpModel.rarg (Int64.unsigned xb) n2.
all: first [lazymatch type of B3 with
  | _ = true =>
    have [Er _] := ExpModelBounds.rarg_neg (Int64.unsigned xb) n2 (sign_true _ B3);
    by rewrite Er Vr1 Vq6 (unsigned_small20 _ (small_succ _ Rn2')) VX1
  | _ = false =>
    have [Er _] := ExpModelBounds.rarg_pos (Int64.unsigned xb) n2 (sign_false _ B3);
    by rewrite Er Vr1 Vq5 (unsigned_small20 _ (small_le _ Rn2')) VX1
  end | idtac].
(* r < RMAX *)
all: have [LRM VRM] := RM_row RM HRM.
all: call NLT => /(_ Lr1 LRM) [-> ->].
all: rewrite Hr VRM.
all: case LT6: (ExpModel.rarg (Int64.unsigned xb) n2 <? ExpModel.RMAXv)%Z => /=.
all: lazymatch type of LT6 with _ = false => csteps; cret | _ => idtac end.
all: lazymatch type of LT6 with _ = false =>
  do 9 eexists; split; [by []|]; split; [by []|];
  apply: rc_fail; first by rewrite /=; lia
  | _ => idtac end.
all: lazymatch type of LT6 with _ = false =>
  apply: (ExpModelBounds.core_Z_rmax _ _ Hsm Hrs); apply/Z.ltb_ge; exact: LT6
  | _ => idtac end.
all: csteps.
(* h = C_16 *)
all: call NC => ->.
all: csteps.
all: set R := ExpModel.rarg (Int64.unsigned xb) n2.
all: have HR : (0 <= R < 2 ^ ExpModelBounds.r_bits)%Z.
all: first [by have := ExpModelBounds.RMAXv_lt; move/Z.ltb_lt: LT6 => L6;
            have := ExpModelBounds.rarg_ge0 _ _ Hq; rewrite -/R; lia | idtac].
all: have [LC16 VC16] := Ca_row Ca HCa (Ordinal H).
(* the Horner loop: after k rounds, h = H_(16-k) *)
all: inv I := { [:: h0; k] } (fun (hv : numA) kv =>
  (kv:N <= 16)%nat /\ limbsA hv /\
  (0 <= valA hv < 2 ^ ExpModelBounds.h_bits)%Z /\
  ExpModel.horner_from R (valA hv) (16 - kv:N) = ExpModel.horner R).
all: enter_loop I.
all: lazymatch goal with |- INV _ _ _ =>
  prove_inv; exsp; rewrite ?VC16;
  first [ exact: LC16 | exact: horner_init
        | have := ExpModelBounds.Cv_bound (Ordinal H);
          rewrite /ExpModelBounds.h_bits /ExpConsts.P; lia ]
  | _ => idtac end.
all: unfold_inv => - [Hk0 [Lh0 [Rh0 Eh0]]].
all: csteps.
all: case END: Int64.ltu => /=.
(* one round *)
all: lazymatch type of END with _ = true => have Hk : (k0:N < 16)%nat; [by move: END; clia|]; csteps;
  have HR' : (0 <= valA r1 < 2 ^ ExpModelBounds.r_bits)%Z; [by rewrite Hr|];
  have [Hhr [Hm0 Hm1]] :=
    ExpModelBounds.horner_step (valA h1) (valA r1) (15 - k0:N) Rh0 HR';
  call NM => /(_ Lh0 Lr1 Hhr) [t2 [-> [Lt2 Vt2]]]; csteps | _ => idtac end.
all: lazymatch type of END with _ = true => 
  have Ei : ((Int64.sub (Int64.repr 15) k0):N = 15 - k0:N)%nat; [by clia k0|];
  have [LCi VCi] := Ca_row Ca HCa (Ordinal H0);
  have ECi : ExpModel.Cv (Ordinal H0) = ExpModel.Cv (15 - k0:N);
    [by congr ExpModel.Cv; exact: Ei|];
  have Hsum : (valA t2 + valA (Ca (Ordinal H0)) < 2 ^ ExpModel.num_bits)%Z;
    [by rewrite Vt2 VCi ECi; exact: (Z.lt_trans _ _ _ Hm1 h_num)|];
  call NA => /(_ Lt2 LCi Hsum) [t3 [-> [Lt3 Vt3]]]; csteps;
  call NC => ->; csteps | _ => idtac end.
all: lazymatch type of END with _ = true => 
  have Vt3' : valA t3 = (ExpModel.mulshr (valA h1) R + ExpModel.Cv (15 - k0:N))%Z;
    [by rewrite Vt3 Vt2 VCi Hr -/R ECi|];
  have Ek1 : ((Int64.add k0 (Int64.repr 1)):N = (k0:N).+1)%nat; [by clia k0|];
  have Rt3 : (0 <= valA t3 < 2 ^ ExpModelBounds.h_bits)%Z;
    [by rewrite Vt3' -/R -[R]Hr; have := ExpModelBounds.Cv_bound (15 - k0:N); lia|];
  cret; split=> // _; split;
  [ solve_loop_conditions
  | prove_inv; exsp; rewrite ?Ek1;
    first [ exact: Hk | exact: Rt3 | exact: Lt3
          | by rewrite Vt3' -(horner_from_step _ _ _ Hk) ] ] | _ => idtac end.
(* the exit: H_0, then y = floor(T_j H_0 / 2^P) and hN *)
all: lazymatch type of END with _ = false => have E16 : k0:N = 16%nat; [by move: END Hk0; clia|];
  rewrite E16 subnn in Eh0;
  have Eh : valA h1 = ExpModel.horner R := Eh0;
  csteps; cret; split=> //= _; csteps;
  have Rn17 : (0 <= n2 < 131072)%Z; [by move: Rn2b; rewrite /ExpModelBounds.n_bits; lia|] | _ => idtac end.
all: lazymatch type of END with _ = false => 
  lazymatch goal with
  | B3 : Int64.eq _ (Int64.repr 1) = true |- _ =>
    have [_ ENu] := ExpModelBounds.rarg_neg (Int64.unsigned xb) n2 (sign_true _ B3);
    rewrite (add1_word n2 Rn2') (nu_neg n2 Rn17) -ENu in H0 *
  | B3 : Int64.eq _ (Int64.repr 1) = false |- _ =>
    have [_ ENu] := ExpModelBounds.rarg_pos (Int64.unsigned xb) n2 (sign_false _ B3);
    rewrite (nu_pos n2 Rn17) -ENu in H0 *
  end | _ => idtac end.
all: lazymatch type of END with _ = false => 
  have RN := ExpModelBounds.Nu_bound (Int64.unsigned xb) n2 Rn2b;
  have RN' : (0 <= ExpModel.Nu (Int64.unsigned xb) n2 < 2 ^ 18)%Z;
    [by move: RN; rewrite /ExpModelBounds.n_bits|];
  have [LTj VTj] := Ta_row Ta HTa (Ordinal H0);
  rewrite (jidx_ord _ H0 RN') in VTj;
  have HT := ExpModelBounds.Tv_bound _
    (Z.mod_pos_bound (ExpModel.Nu (Int64.unsigned xb) n2) ExpConsts.TAB
       ltac:(by []));
  rewrite -ExpModel.jidxE in HT;
  have HH := ExpModelBounds.horner_bound R HR;
  have Hfit : (valA (Ta (Ordinal H0)) * valA h1 <
               2 ^ (ExpConsts.P + ExpModel.num_bits))%Z;
    [by rewrite VTj Eh; exact: table_fit|];
  call NM => /(_ LTj Lh0 Hfit) [y1 [-> [Ly1 Vy1]]];
  csteps; cret | _ => idtac end.
all: lazymatch type of END with _ = false => 
  do 9 eexists; split; [by []|]; split; [by []|];
  split; [by []|];
  move=> _; split; [exact: Ly1|];
  have LT6' : (ExpModel.rarg (Int64.unsigned xb) n2 < ExpModel.RMAXv)%Z;
    [by apply/Z.ltb_lt|];
  rewrite (ExpModelBounds.core_Z_ok _ _ Hsm Hrs LT6') hs_write
    (hidx_word _ RN') Vy1 VTj Eh;
  by [] | _ => idtac end.
Qed.
