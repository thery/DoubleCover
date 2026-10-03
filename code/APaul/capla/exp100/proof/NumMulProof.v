(** * num_mul_small, num_mulshr: the specs (task T5) *)

Require Import BinNums ZArith List Lia Utf8.
Import ListNotations.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat ssrZ zify.
Require Import Integers Floats Maps Coqlib Errors.
Require Import Tactics BUtils ListUtils PTreeaux.
Require Import Syntax BValues BEnv Types.
Require Import Validity Alias SemPath Ops.
Require Import SemanticsCommon L1Sem L1ExprSem.
Require Import L1facts L1BigStepSem.
Require Import Exp100Capla.ExpBase Exp100Capla.Bridge Exp100Capla.Specs.
From Exp100 Require Import ExpNum ExpLimbs.
From Exp100 Require ExpConsts ExpModel ExpModelBounds.
Require Import ProofHeader WP ZifyIntegers.
Require Import ProofTactics.
Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Section Mul.
Transparent Int64.mul.

(* A step of a product: a w + c fits in a word when the three are limbs. *)
Lemma mul_add_word (a w c : int64) :
  (Int64.unsigned a < 2 ^ 32)%Z -> (Int64.unsigned w < 2 ^ 32)%Z ->
  (Int64.unsigned c < 2 ^ 32)%Z ->
  Int64.unsigned (Int64.add (Int64.mul a w) c) =
  (Int64.unsigned a * Int64.unsigned w + Int64.unsigned c)%Z.
Proof.
  move=> Ha Hw Hc.
  have := Int64.unsigned_range a; have := Int64.unsigned_range w;
    have := Int64.unsigned_range c => Rc Rw Ra.
  rewrite Int64.add_unsigned /Int64.mul.
  have Ep : (0 <= Int64.unsigned a * Int64.unsigned w <= (2 ^ 32 - 1) * (2 ^ 32 - 1))%Z
    by nia.
  have M : Int64.max_unsigned = 18446744073709551615%Z by [].
  rewrite (Int64.unsigned_repr (Int64.unsigned a * Int64.unsigned w)) ?M; lia.
Qed.

End Mul.

(* The carry of a word below 2^64 is a limb. *)
Lemma carry_limb (s : int64) :
  (Int64.unsigned (Int64.shru' s (Int.modu (Int.repr 32) Int64.iwordsize')) < 2 ^ 32)%Z.
Proof.
  rewrite shru32; have := Int64.unsigned_range s.
  change Int64.modulus with (2 ^ 32 * 2 ^ 32)%Z => Hs.
  apply: Z.div_lt_upper_bound; lia.
Qed.

(* The low limb of a word is a limb. *)
Lemma mask_limb (s : int64) :
  (Int64.unsigned (Int64.and s (Int64.repr 4294967295)) < 2 ^ 32)%Z.
Proof.
  rewrite and_mask; have := Z.mod_pos_bound (Int64.unsigned s) (2 ^ 32); lia.
Qed.

(* One step of the loop of num_mul_small, on the numbers. *)
Lemma num_mul_small_step xs ps' nk (c s w : int64) :
  (nk < 6)%coq_nat -> length xs = 6%nat -> length ps' = 7%nat ->
  Int64.unsigned s = (Int64.unsigned (List.nth nk xs Int64.zero) * Int64.unsigned w
                      + Int64.unsigned c)%Z ->
  (val32 (firstn nk ps') + Int64.unsigned c * base32 nk =
   val32 (firstn nk xs) * Int64.unsigned w)%Z ->
  (val32 (firstn (S nk) (replace nk ps' (Int64.and s (Int64.repr 4294967295)))) +
   Int64.unsigned (Int64.shru' s (Int.modu (Int.repr 32) Int64.iwordsize')) *
     base32 (S nk) =
   val32 (firstn (S nk) xs) * Int64.unsigned w)%Z.
Proof.
  move=> Hk Hx Hl Es HV.
  rewrite !val32_firstn_S ?replace_length ?Hl ?Hx; try lia.
  rewrite firstn_replace nth_replace_same ?Hl; try lia.
  rewrite and_mask shru32 base32S.
  have Ed := Z.div_mod (Int64.unsigned s) (2 ^ 32) ltac:(lia).
  have E : (base32 nk * (Int64.unsigned s mod 2 ^ 32) +
            Int64.unsigned s / 2 ^ 32 * (base32 nk * 2 ^ 32) =
            base32 nk * Int64.unsigned s)%Z.
  { rewrite {3}Ed; ring. }
  rewrite -Z.add_assoc E Es Z.mul_add_distr_r -HV; ring.
Qed.

(* The last write p[6] = c, on the numbers. *)
Lemma num_mul_small_end ps' (c : int64) :
  length ps' = 7%nat ->
  val32 (replace 6 ps' c) =
  (val32 (firstn 6 ps') + base32 6 * Int64.unsigned c)%Z.
Proof.
  move=> Hl; rewrite replace_split ?Hl // val32_app length_firstn Hl.
  have -> : skipn 7 ps' = [] by apply: skipn_all2; rewrite Hl.
  cbn [val32 Init.Nat.min]; lia.
Qed.

(* p = a w on 7 limbs, for w < 2^32 *)
Theorem num_mul_small_spec ps xs w e1 result :
  length ps = 7%nat -> length xs = 6%nat -> limbs xs ->
  (Int64.unsigned w < 2 ^ limb_bits)%Z ->
  eval_funcall ge (Internal num_mul_small43)
    [Varr (map Vint64 ps); Varr (map Vint64 xs); Vint64 w] e1 (Some result) ->
  exists ps', e1!(param 0 num_mul_small43) = Some (Varr (map Vint64 ps')) /\
    length ps' = 7%nat /\ limbs ps' /\
    val32 ps' = (val32 xs * Int64.unsigned w)%Z.
Proof.
  move=> Hp Hx Lx Hw.
  intro_eval_funcall num_mul_small43 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  name_var "i" i.
  name_var "p" PP.
  name_var "a" A.
  name_var "c" CY.
  name_var "__copy_w" W.
  repeat prog.
  pose Inv := fun (e: env) (se: senv) =>
    exists k ps' c,
      e!i = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      let nk := nat_of k in
      e!PP = Some (Varr (map Vint64 ps')) /\
      e!CY = Some (Vint64 c) /\
      (Int64.unsigned c < 2 ^ 32)%Z /\
      length ps' = 7%nat /\
      (forall p, (p < nk)%coq_nat ->
         (Int64.unsigned (List.nth p ps' Int64.zero) < 2 ^ 32)%Z) /\
      (val32 (firstn nk ps') + Int64.unsigned c * base32 nk =
       val32 (firstn nk xs) * Int64.unsigned w)%Z.
  exists Inv; split.
  - rewrite /Inv.
    exists (Int64.repr 0), ps, (Int64.repr 0).
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //; try lia.
  - move=>>.
    repeat prog.
    rewrite/Inv /=.
    intros (k & ps' & c & [= ->] & Hk6 & [= ->] & [= ->] & Hc & Hl & Hlo & HV)
      => /=.
    set nk := nat_of k.
    simplWP.
    case END: Int64.ltu; simplWP.
    + repeat prog.
      have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
      change (Z.to_nat (Int64.unsigned k)) with nk.
      rewrite !nth_map_V64 ?length_map; try lia.
      rewrite /sem_binarith /sem_cast /shrink /=.
      set a := List.nth nk xs Int64.zero.
      have La : (Int64.unsigned a < 2 ^ 32)%Z by apply: Lx.
      set s := Int64.add (Int64.mul a w) c.
      have Es : Int64.unsigned s =
                (Int64.unsigned a * Int64.unsigned w + Int64.unsigned c)%Z.
      { exact: mul_add_word. }
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      exists (Int64.add k (Int64.repr 1)),
        (replace nk ps' (Int64.and s (Int64.repr 4294967295))),
        (Int64.shru' s (Int.modu (Int.repr 32) Int64.iwordsize')).
      rewrite Hk1 replace_map; repeat split => //.
      * clia k.
      * exact: carry_limb.
      * by rewrite replace_length.
      * move=> p Hp0.
        have [Hp1|->] : (p < nk)%coq_nat \/ p = nk by lia.
        -- rewrite nth_replace_other; try lia; apply: Hlo; lia.
        -- rewrite nth_replace_same ?Hl; try lia; exact: mask_limb.
      * exact: (num_mul_small_step xs ps' nk c s w Hk Hx Hl Es HV).
    + (* the loop ends with k = 6, then p[6] = c *)
      have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
      have F6 : firstn 6 xs = xs by apply: List.firstn_all2; rewrite Hx.
      move: HV; rewrite -/nk Ek F6 => HV.
      repeat prog.
      change (Z.to_nat (Int64.unsigned (Int64.repr 6))) with 6%nat.
      exists (replace 6 ps' c); rewrite replace_map; repeat split => //.
      * by rewrite replace_length.
      * move=> p.
        have [Hp1|[->|Hp1]] :
          (p < 6)%coq_nat \/ p = 6%nat \/ (7 <= p)%coq_nat by lia.
        -- rewrite nth_replace_other; try lia; apply: Hlo; rewrite -/nk Ek; lia.
        -- by rewrite nth_replace_same ?Hl.
        -- rewrite nth_overflow ?replace_length ?Hl //.
      * rewrite num_mul_small_end // -HV; ring.
Qed.

(* Writing x at limb k changes the number by (x - old) 2^(32 k). *)
Lemma val32_replace l k x : (k < length l)%coq_nat ->
  val32 (replace k l x) =
  (val32 l + (Int64.unsigned x - Int64.unsigned (List.nth k l Int64.zero)) *
     base32 k)%Z.
Proof.
  move=> Hk; rewrite !val32_valZ replace_unsigned // valZ_upd ?length_map //.
  by rewrite nth_unsigned base32_limb.
Qed.

Lemma base32_add m n : base32 (m + n) = (base32 m * base32 n)%Z.
Proof. rewrite /base32 -Z.pow_add_r; try lia; f_equal; lia. Qed.

Section Mul2.
Transparent Int64.mul.

(* a b + p + c fits in a word when the four are limbs. *)
Lemma mul_add2_word (a b p c : int64) :
  (Int64.unsigned a < 2 ^ 32)%Z -> (Int64.unsigned b < 2 ^ 32)%Z ->
  (Int64.unsigned p < 2 ^ 32)%Z -> (Int64.unsigned c < 2 ^ 32)%Z ->
  Int64.unsigned (Int64.add (Int64.add (Int64.mul a b) p) c) =
  (Int64.unsigned a * Int64.unsigned b + Int64.unsigned p + Int64.unsigned c)%Z.
Proof.
  move=> Ha Hb Hp Hc.
  have := Int64.unsigned_range a; have := Int64.unsigned_range b;
    have := Int64.unsigned_range p; have := Int64.unsigned_range c.
  move=> Rc Rp Rb Ra.
  have Ep : (0 <= Int64.unsigned a * Int64.unsigned b <=
             (2 ^ 32 - 1) * (2 ^ 32 - 1))%Z by nia.
  have M : Int64.max_unsigned = 18446744073709551615%Z by [].
  rewrite !Int64.add_unsigned /Int64.mul.
  rewrite (Int64.unsigned_repr (Int64.unsigned a * Int64.unsigned b)) ?M; lia.
Qed.

End Mul2.

(* One step of the inner loop of num_mulshr, on the numbers. *)
Lemma num_mulshr_step ps ys (V0 : Z) nk nj (a c s : int64) :
  (nk < 6)%coq_nat -> (nj < 6)%coq_nat -> length ps = 12%nat -> length ys = 6%nat ->
  Int64.unsigned s = (Int64.unsigned a * Int64.unsigned (List.nth nj ys Int64.zero)
     + Int64.unsigned (List.nth (nk + nj) ps Int64.zero) + Int64.unsigned c)%Z ->
  (val32 ps + Int64.unsigned c * base32 (nk + nj) =
   V0 + Int64.unsigned a * val32 (firstn nj ys) * base32 nk)%Z ->
  (val32 (replace (nk + nj) ps (Int64.and s (Int64.repr 4294967295))) +
   Int64.unsigned (Int64.shru' s (Int.modu (Int.repr 32) Int64.iwordsize')) *
     base32 (nk + S nj) =
   V0 + Int64.unsigned a * val32 (firstn (S nj) ys) * base32 nk)%Z.
Proof.
  move=> Hk Hj Hl Hy Es HV.
  rewrite val32_replace; [lia|].
  rewrite val32_firstn_S; [lia|].
  rewrite and_mask shru32 -addSnnS base32S base32_add.
  have Ed := Z.div_mod (Int64.unsigned s) (2 ^ 32) ltac:(lia).
  move: HV; rewrite base32_add => HV.
  set B := base32 nk in HV *; set C := base32 nj in HV *.
  set p := Int64.unsigned (List.nth (nk + nj) ps Int64.zero) in Es *.
  set b := Int64.unsigned (List.nth nj ys Int64.zero) in Es *.
  have E : ((Int64.unsigned s mod 2 ^ 32 - p) * (B * C) +
            Int64.unsigned s / 2 ^ 32 * (B * C * 2 ^ 32) =
            (Int64.unsigned s - p) * (B * C))%Z.
  { rewrite {3}Ed; ring. }
  rewrite -Z.add_assoc E Es.
  have -> : val32 ps = (V0 + Int64.unsigned a * val32 (firstn nj ys) * B -
                        Int64.unsigned c * (B * C))%Z by lia.
  ring.
Qed.

(* The end of the inner loop: p[i + 6] = c, on a limb that was 0. *)
Lemma num_mulshr_top ps nk (c : int64) :
  (nk + 6 < length ps)%coq_nat ->
  List.nth (nk + 6) ps Int64.zero = Int64.zero ->
  val32 (replace (nk + 6) ps c) =
  (val32 ps + Int64.unsigned c * base32 (nk + 6))%Z.
Proof.
  move=> Hk H0; rewrite val32_replace // H0.
  have -> : Int64.unsigned Int64.zero = 0%Z by [].
  ring.
Qed.

(* Limbs 5 .. 10 of a product of 12 limbs below 2^352 are its top part. *)
Lemma num_mulshr_shift ps : length ps = 12%nat -> limbs ps ->
  (val32 ps < base32 11)%Z ->
  val32 (firstn 6 (skipn 5 ps)) = (val32 ps / base32 5)%Z.
Proof.
  move=> Hl Hp Hv.
  rewrite !val32_valZ -firstn_map -skipn_map base32_limb.
  apply: valZ_shift; first by apply/limbs_Forall.
  by rewrite -val32_valZ -base32_limb.
Qed.

(* The last loop of num_mulshr copies limbs 5 .. 10 of the product. *)
Lemma copy_top (ps rs : list int64) : length ps = 12%nat -> length rs = 6%nat ->
  (forall q, (q < 6)%coq_nat ->
     List.nth q rs Int64.zero = List.nth (q + 5) ps Int64.zero) ->
  rs = firstn 6 (skipn 5 ps).
Proof.
  move=> Hl Hr Hq.
  apply: (nth_ext _ _ Int64.zero Int64.zero).
  - by rewrite Hr length_firstn length_skipn Hl.
  - move=> q; rewrite Hr => Hq6.
    rewrite nth_firstn (proj2 (Nat.ltb_lt q 6) Hq6) nth_skipn Hq //.
    f_equal; lia.
Qed.

(* The result of num_mulshr, from the product of 12 limbs. *)
Lemma mulshr_final (ps rs : list int64) (X Y : Z) :
  length ps = 12%nat -> limbs ps -> val32 ps = (X * Y)%Z ->
  (X * Y < 2 ^ (ExpConsts.P + ExpModel.num_bits))%Z ->
  rs = firstn 6 (skipn 5 ps) ->
  length rs = 6%nat /\ limbs rs /\ val32 rs = ExpModel.mulshr X Y.
Proof.
  move=> Hl Hp HV Hfit ->.
  split; first by rewrite length_firstn length_skipn Hl.
  split.
  - move=> q; rewrite nth_firstn; case: Nat.ltb_spec => _; last by [].
    by rewrite nth_skipn; apply: Hp.
  - rewrite num_mulshr_shift //; first by rewrite HV.
    by rewrite HV ExpModel.mulshrE.
Qed.

(* r = floor(a b / 2^160), when it fits in 192 bits *)
Theorem num_mulshr_spec rs xs ys e1 result :
  length rs = 6%nat -> length xs = 6%nat -> length ys = 6%nat ->
  limbs xs -> limbs ys ->
  (val32 xs * val32 ys < 2 ^ (ExpConsts.P + ExpModel.num_bits))%Z ->
  eval_funcall ge (Internal num_mulshr59)
    [Varr (map Vint64 rs); Varr (map Vint64 xs); Varr (map Vint64 ys)]
    e1 (Some result) ->
  exists rs', e1!(param 0 num_mulshr59) = Some (Varr (map Vint64 rs')) /\
    length rs' = 6%nat /\ limbs rs' /\
    val32 rs' = ExpModel.mulshr (val32 xs) (val32 ys).
Proof.
  move=> Hr Hx Hy Lx Ly Hfit.
  intro_eval_funcall num_mulshr59 out se1 exec.
  apply_WP_stmt exec out e1 se1.
  set (I1 := VAR 48%positive "i") in *; change (PTree.prev 48%positive) with I1.
  set (I2 := VAR 57%positive "i") in *; change (PTree.prev 57%positive) with I2.
  name_var "j" J.
  name_var "p" PP.
  name_var "r" R.
  name_var "c" CY.
  repeat prog.
  (* p = (the first i limbs of a) b, its limbs i + 6 .. 11 still 0 *)
  pose Inv := fun (e: env) (se: senv) =>
    exists k ps,
      e!I1 = Some (Vint64 k) /\ (Int64.unsigned k <= 6)%Z /\
      let nk := nat_of k in
      e!PP = Some (Varr (map Vint64 ps)) /\
      length ps = 12%nat /\ limbs ps /\
      (forall p, (nk + 6 <= p)%coq_nat -> List.nth p ps Int64.zero = Int64.zero) /\
      val32 ps = (val32 (firstn nk xs) * val32 ys)%Z.
  exists Inv; split.
  { rewrite /Inv.
    exists (Int64.repr 0), (repeat Int64.zero 12).
    change (nat_of (Int64.repr 0)) with 0%nat.
    repeat split => //.
    all: by move=> p; rewrite nth_repeat. }
  move=>>.
  repeat prog.
  rewrite/Inv /=.
  intros (k & ps0 & [= ->] & Hk6 & [= ->] & Hl0 & Hp0 & Hz0 & HV0) => /=.
  set nk := nat_of k.
  simplWP.
  case END: Int64.ltu; simplWP.
  - repeat prog.
    have Hk : (nk < 6)%coq_nat by rewrite /nk /nat_of; clia k.
    set a := List.nth nk xs Int64.zero.
    have La : (Int64.unsigned a < 2 ^ 32)%Z by apply: Lx.
    (* p + c 2^(32 (i + j)) = p0 + a_i (the first j limbs of b) 2^(32 i) *)
    pose Inv2 := fun (e: env) (se: senv) =>
      exists j ps c,
        e!J = Some (Vint64 j) /\ (Int64.unsigned j <= 6)%Z /\
        let nj := nat_of j in
        e!PP = Some (Varr (map Vint64 ps)) /\
        e!CY = Some (Vint64 c) /\ (Int64.unsigned c < 2 ^ 32)%Z /\
        length ps = 12%nat /\ limbs ps /\
        (forall p, (nk + 6 <= p)%coq_nat -> List.nth p ps Int64.zero = Int64.zero) /\
        (val32 ps + Int64.unsigned c * base32 (nk + nj) =
         val32 ps0 + Int64.unsigned a * val32 (firstn nj ys) * base32 nk)%Z.
    exists Inv2; split.
    { rewrite /Inv2.
      exists (Int64.repr 0), ps0, (Int64.repr 0).
      change (nat_of (Int64.repr 0)) with 0%nat.
      repeat split => //; try lia.
      all: try (change (Int64.unsigned (Int64.repr 0)) with 0%Z; rewrite firstn_O;
                cbn [val32]; ring). }
    move=>>.
    repeat prog.
    rewrite/Inv2 /=.
    intros (j & ps & c & [= ->] & Hj6 & [= ->] & [= ->] & Hc & Hl & Hp & Hz & HV) => /=.
    set nj := nat_of j.
    simplWP.
    case END2: Int64.ltu; simplWP.
    + repeat prog.
      have Hj : (nj < 6)%coq_nat by rewrite /nj /nat_of; clia j.
      have Hkj : Z.to_nat (Int64.unsigned (Int64.add k j)) = (nk + nj)%nat.
      { rewrite /nk /nj /nat_of; clia k, j. }
      change (Z.to_nat (Int64.unsigned k)) with nk.
      change (Z.to_nat (Int64.unsigned j)) with nj.
      rewrite Hkj.
      rewrite !nth_map_V64 ?length_map; try lia.
      rewrite /sem_binarith /sem_cast /shrink /=.
      set b := List.nth nj ys Int64.zero.
      set pk := List.nth (nk + nj) ps Int64.zero.
      have Lb : (Int64.unsigned b < 2 ^ 32)%Z by apply: Ly.
      have Lp : (Int64.unsigned pk < 2 ^ 32)%Z by apply: Hp.
      set s := Int64.add (Int64.add (Int64.mul a b) pk) c.
      have Es : Int64.unsigned s =
        (Int64.unsigned a * Int64.unsigned b + Int64.unsigned pk +
         Int64.unsigned c)%Z.
      { exact: mul_add2_word. }
      have Hj1 : nat_of (Int64.add j (Int64.repr 1)) = S nj.
      { rewrite /nj /nat_of; clia j. }
      exists (Int64.add j (Int64.repr 1)),
        (replace (nk + nj) ps (Int64.and s (Int64.repr 4294967295))),
        (Int64.shru' s (Int.modu (Int.repr 32) Int64.iwordsize')).
      rewrite Hj1 replace_map; repeat split => //.
      * clia j.
      * exact: carry_limb.
      * by rewrite replace_length.
      * move=> q.
        have [Hq|->] : q <> (nk + nj)%nat \/ q = (nk + nj)%nat by lia.
        -- by rewrite nth_replace_other //; apply: Hp.
        -- rewrite nth_replace_same ?Hl; [lia|exact: mask_limb].
      * by move=> q Hq; rewrite nth_replace_other; [lia|apply: Hz].
      * exact: (num_mulshr_step ps ys (val32 ps0) nk nj a c s Hk Hj Hl Hy Es HV).
    + (* j = 6: p[i + 6] = c *)
      have Ej : nj = 6%nat by move: END2 Hj6; rewrite /nj /nat_of; clia j.
      have F6 : firstn 6 ys = ys by apply: List.firstn_all2; rewrite Hy.
      move: HV; rewrite -/nj Ej F6 => HV.
      repeat prog.
      rewrite /index /=.
      have Hk6' : Z.to_nat (Int64.unsigned (Int64.add k (Int64.repr 6))) = (nk + 6)%nat.
      { rewrite /nk /nat_of; clia k. }
      have Hk1 : nat_of (Int64.add k (Int64.repr 1)) = S nk.
      { rewrite /nk /nat_of; clia k. }
      rewrite Hk6' replace_map.
      exists (Int64.add k (Int64.repr 1)), (replace (nk + 6) ps c).
      rewrite Hk1; repeat split => //.
      all: first [clia k | by rewrite replace_length | idtac].
      * move=> q.
        have [Hq|->] : q <> (nk + 6)%nat \/ q = (nk + 6)%nat by lia.
        -- by rewrite nth_replace_other //; apply: Hp.
        -- by rewrite nth_replace_same ?Hl; [lia|].
      * by move=> q Hq; rewrite nth_replace_other; [lia|apply: Hz; lia].
      * rewrite num_mulshr_top; [lia| apply: Hz; lia|].
        rewrite val32_firstn_S; [lia|].
        rewrite HV HV0 /a /nk; ring.
  - (* i = 6: r = limbs 5 .. 10 of p *)
    have Ek : nk = 6%nat by move: END Hk6; rewrite /nk /nat_of; clia k.
    have F6 : firstn 6 xs = xs by apply: List.firstn_all2; rewrite Hx.
    move: HV0; rewrite -/nk Ek F6 => HV0.
    repeat prog.
    pose Inv3 := fun (e: env) (se: senv) =>
      exists k2 rs',
        e!I2 = Some (Vint64 k2) /\ (Int64.unsigned k2 <= 6)%Z /\
        e!R = Some (Varr (map Vint64 rs')) /\ length rs' = 6%nat /\
        (forall q, (q < nat_of k2)%coq_nat ->
           List.nth q rs' Int64.zero = List.nth (q + 5) ps0 Int64.zero).
    exists Inv3; split.
    { rewrite /Inv3.
      exists (Int64.repr 0), rs.
      change (nat_of (Int64.repr 0)) with 0%nat.
      repeat split => //; try lia. }
    move=>>.
    repeat prog.
    rewrite/Inv3 /=.
    intros (k2 & rs' & [= ->] & Hk2 & [= ->] & Hlr & Hq) => /=.
    set n2 := nat_of k2.
    simplWP.
    case END3: Int64.ltu; simplWP.
    + repeat prog.
      have Hn2 : (n2 < 6)%coq_nat by rewrite /n2 /nat_of; clia k2.
      have E5 : Z.to_nat (Int64.unsigned (Int64.add k2 (Int64.repr 5))) =
                (n2 + 5)%nat.
      { rewrite /n2 /nat_of; clia k2. }
      have Hk21 : nat_of (Int64.add k2 (Int64.repr 1)) = S n2.
      { rewrite /n2 /nat_of; clia k2. }
      change (Z.to_nat (Int64.unsigned k2)) with n2.
      rewrite E5.
      rewrite nth_map_V64 ?length_map; [lia|].
      rewrite /shrink /= replace_map.
      exists (Int64.add k2 (Int64.repr 1)),
        (replace n2 rs' (List.nth (n2 + 5) ps0 Int64.zero)).
      rewrite Hk21; repeat split => //.
      all: first [clia k2 | by rewrite replace_length | idtac].
      move=> q Hq0.
      (have [Hq1|->] : (q < n2)%coq_nat \/ q = n2 by lia);
        [rewrite nth_replace_other; try lia; exact: Hq
        | rewrite nth_replace_same; try lia; done].
    + have En2 : n2 = 6%nat by move: END3 Hk2; rewrite /n2 /nat_of; clia k2.
      repeat prog.
      exists rs'.
      have Ers : rs' = firstn 6 (skipn 5 ps0).
      { apply: copy_top => // q Hq6; apply: Hq; rewrite -/n2 En2; lia. }
      have [H1 [H2 H3]] := mulshr_final ps0 rs' _ _ Hl0 Hp0 HV0 Hfit Ers.
      by repeat split.
Qed.
