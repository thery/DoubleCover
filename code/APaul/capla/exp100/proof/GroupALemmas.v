(** * Tactics and pure lemmas shared by the group A proofs *)

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

(* Drop the function record and the execution once the WP is applied. *)
Ltac tidy :=
  repeat match goal with
  | H : context [fn_body] |- _ => clear H
  | H : valid_function_outcome _ |- _ => clear H
  | H : well_typed_option_value _ _ |- _ => clear H
  end;
  repeat match goal with H := _ |- _ => clear H end.

(* Two lists of length 6 that agree below 6 are equal. *)
Lemma list6_ext (l1 l2 : list int64) : length l1 = 6%nat -> length l2 = 6%nat ->
  (forall p, (p < 6)%coq_nat -> List.nth p l1 Int64.zero = List.nth p l2 Int64.zero) ->
  l1 = l2.
Proof.
  move=> H1 H2 H; apply: (List.nth_ext _ _ Int64.zero Int64.zero); first lia.
  move=> p Hp; apply: H; lia.
Qed.

(* Six zero words: the number 0. *)
Lemma zeros6_aux : length (repeat Int64.zero 6) = 6%nat /\
  limbs (repeat Int64.zero 6) /\ val32 (repeat Int64.zero 6) = 0%Z.
Proof.
  split => //; split; last by rewrite /= Int64.unsigned_zero.
  move=> p; case: (Nat.lt_ge_cases p 6) => Hp.
  - by rewrite nth_repeat_lt // Int64.unsigned_zero.
  - by rewrite nth_overflow ?repeat_length // Int64.unsigned_zero.
Qed.

(* The index of a one-dimensional array access. *)
Lemma index1 x n : index [Vint64 x] [n] = Z.to_nat (Int64.unsigned x).
Proof. by rewrite /index /build_index /=. Qed.

(* The divisor 32 is not 0. *)
Lemma eq32 : Int64.eq (Int64.repr 32) Int64.zero = false.
Proof. by []. Qed.

(* A write in a list of limbs changes its number by the difference. *)
Lemma val32_replace l j w : (j < length l)%coq_nat ->
  val32 (replace j l w) =
  (val32 l + base32 j * (Int64.unsigned w - Int64.unsigned (List.nth j l Int64.zero)))%Z.
Proof.
  elim: l j => [|x l IH] [|j]; cbn [val32 replace length List.nth] => H;
    try lia.
  - rewrite base32_0; lia.
  - rewrite IH; first lia.
    rewrite base32S; ring.
Qed.

(* A write of a limb keeps every limb below 2^32. *)
Lemma limbs_replace l j w : limbs l -> (Int64.unsigned w < 2 ^ 32)%Z ->
  limbs (replace j l w).
Proof.
  move=> Hl Hw p.
  have [->|Hp] := Nat.eq_dec p j.
  - case: (Nat.lt_ge_cases j (length l)) => Hj.
    + by rewrite nth_replace_same.
    + rewrite nth_overflow ?replace_length // Int64.unsigned_zero; lia.
  - rewrite nth_replace_other //; exact: Hl.
Qed.

Section Words.
Transparent Int64.modu Int64.divu Int64.sub Int64.neg Int64.repr Int64.unsigned Int64.signed Int.repr
  Int.unsigned Int.modu.

(* The amount of a shift by a word k, cast to 32 bits. *)
Lemma amt_unsigned k : (Int64.unsigned k < 64)%Z ->
  Int.unsigned (Int.modu (Int64.loword k) Int64.iwordsize') = Int64.unsigned k.
Proof.
  move=> Hk; have := Int64.unsigned_range k => Hr.
  rewrite /Int.modu /Int64.loword.
  have E : Int.unsigned Int64.iwordsize' = 64%Z by [].
  rewrite E Int.unsigned_repr; first by change Int.max_unsigned with 4294967295%Z; lia.
  rewrite Z.mod_small; first lia.
  rewrite Int.unsigned_repr //; change Int.max_unsigned with 4294967295%Z; lia.
Qed.

(* x << k, for k < 64. *)
Lemma shl_amt x k : (Int64.unsigned k < 64)%Z ->
  Int64.unsigned (Int64.shl' x (Int.modu (Int64.loword k) Int64.iwordsize')) =
  ((Int64.unsigned x * 2 ^ Int64.unsigned k) mod 2 ^ 64)%Z.
Proof.
  move=> Hk; rewrite /Int64.shl' amt_unsigned // Z.shiftl_mul_pow2.
  - have := Int64.unsigned_range k; lia.
  - by rewrite Int64.unsigned_repr_eq.
Qed.

(* x >> k, for k < 64. *)
Lemma shr_amt x k : (Int64.unsigned k < 64)%Z ->
  Int64.unsigned (Int64.shru' x (Int.modu (Int64.loword k) Int64.iwordsize')) =
  (Int64.unsigned x / 2 ^ Int64.unsigned k)%Z.
Proof.
  move=> Hk; rewrite /Int64.shru' amt_unsigned // Z.shiftr_div_pow2.
  - have := Int64.unsigned_range k; lia.
  - rewrite Int64.unsigned_repr //.
    have Hx := Int64.unsigned_range x.
    have Hp := Z.pow_pos_nonneg 2 (Int64.unsigned k) ltac:(lia)
                 (proj1 (Int64.unsigned_range k)).
    have H0 := Z.div_pos (Int64.unsigned x) _ (proj1 Hx) Hp.
    have H1 : (Int64.unsigned x / 2 ^ Int64.unsigned k <= Int64.unsigned x)%Z.
    { apply: Z.div_le_upper_bound => //; nia. }
    change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* f / 32 and f mod 32. *)
Lemma divu32 x :
  Int64.unsigned (Int64.divu x (Int64.repr 32)) = (Int64.unsigned x / 32)%Z.
Proof.
  have Hr := Int64.unsigned_range x.
  have H0 := Z.div_pos (Int64.unsigned x) 32 (proj1 Hr) ltac:(lia).
  have H1 : (Int64.unsigned x / 32 <= Int64.unsigned x)%Z.
  { apply: Z.div_le_upper_bound; lia. }
  rewrite /Int64.divu.
  change (Int64.unsigned (Int64.repr 32)) with 32%Z.
  rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

Lemma modu32 x :
  Int64.unsigned (Int64.modu x (Int64.repr 32)) = (Int64.unsigned x mod 32)%Z.
Proof.
  have := Z.mod_pos_bound (Int64.unsigned x) 32 ltac:(lia) => H.
  rewrite /Int64.modu.
  change (Int64.unsigned (Int64.repr 32)) with 32%Z.
  rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* The m low bits of a word. *)
Lemma and_low y m : (0 <= m < 64)%Z ->
  Int64.and y (Int64.repr (2 ^ m - 1)) = Int64.repr (Int64.unsigned y mod 2 ^ m).
Proof.
  move=> Hm.
  have -> : (2 ^ m - 1 = Z.ones m)%Z by rewrite Z.ones_equiv; lia.
  apply: Int64.same_bits_eq => k Hk.
  rewrite Int64.bits_and //.
  rewrite !Int64.testbit_repr //.
  rewrite -Z.land_ones; first lia.
  by rewrite Z.land_spec.
Qed.

(* The mask (1 << (f mod 32)) - 1. *)
Lemma mask_eq f :
  Int64.sub (Int64.shl' (Int64.repr 1)
     (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
     (Int64.repr 1) = Int64.repr (2 ^ (Int64.unsigned f mod 32) - 1).
Proof.
  have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
  have Hp : (2 ^ (Int64.unsigned f mod 32) < 2 ^ 32)%Z.
  { apply: Z.pow_lt_mono_r; lia. }
  have Hp0 : (0 < 2 ^ (Int64.unsigned f mod 32))%Z.
  { apply: Z.pow_pos_nonneg; lia. }
  rewrite /Int64.sub; congr Int64.repr.
  rewrite shl_amt modu32; first lia.
  change (Int64.unsigned (Int64.repr 1)) with 1%Z.
  rewrite Z.mul_1_l Z.mod_small //; lia.
Qed.

(* b & ((1 << (f mod 32)) - 1) = b mod 2^(f mod 32). *)
Lemma mask_and y f :
  Int64.unsigned (Int64.and y (Int64.sub (Int64.shl' (Int64.repr 1)
     (Int.modu (Int64.loword (Int64.modu f (Int64.repr 32))) Int64.iwordsize'))
     (Int64.repr 1))) = (Int64.unsigned y mod 2 ^ (Int64.unsigned f mod 32))%Z.
Proof.
  have Hm := Z.mod_pos_bound (Int64.unsigned f) 32 ltac:(lia).
  rewrite mask_eq and_low; first lia.
  have := Z.mod_pos_bound (Int64.unsigned y) (2 ^ (Int64.unsigned f mod 32))
            ltac:(apply: Z.pow_pos_nonneg; lia).
  have : (2 ^ (Int64.unsigned f mod 32) < 2 ^ 32)%Z.
  { apply: Z.pow_lt_mono_r; lia. }
  move=> ? ?; rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* Bit k of a word: (a >> k) & 1. *)
Lemma bit_amt a k : (Int64.unsigned k < 64)%Z ->
  Int64.and (Int64.shru' a (Int.modu (Int64.loword k) Int64.iwordsize'))
    (Int64.repr 1) =
  Int64.repr ((Int64.unsigned a / 2 ^ Int64.unsigned k) mod 2).
Proof.
  move=> Hk.
  change (Int64.repr 1) with (Int64.repr (2 ^ 1 - 1)).
  by rewrite and_low // shr_amt.
Qed.

(* A word with a non-negative signed value. *)
Lemma unsigned_signed_nonneg e : (0 <= Int64.signed e)%Z ->
  Int64.unsigned e = Int64.signed e.
Proof.
  rewrite /Int64.signed; case: zlt => // H1 H2.
  have := Int64.unsigned_range e; move: H1 H2.
  change Int64.half_modulus with 9223372036854775808%Z.
  change Int64.modulus with 18446744073709551616%Z; lia.
Qed.

(* -e for a negative word e. *)
Lemma unsigned_neg e : (Int64.signed e < 0)%Z ->
  Int64.unsigned (Int64.neg e) = (- Int64.signed e)%Z.
Proof.
  move=> He; have := Int64.signed_range e => Hr.
  have Hlt : Int64.lt e Int64.zero = true.
  { rewrite /Int64.lt Int64.signed_zero; case: zlt => //; lia. }
  rewrite /Int64.neg Int64.unsigned_repr_eq Int64.unsigned_signed Hlt.
  move: Hr.
  change Int64.modulus with 18446744073709551616%Z.
  change Int64.min_signed with (-9223372036854775808)%Z.
  change Int64.max_signed with 9223372036854775807%Z.
  move=> Hr.
  rewrite (_ : (- (Int64.signed e + 18446744073709551616) =
                - Int64.signed e + (-1) * 18446744073709551616)%Z); first lia.
  rewrite Z.mod_add; first lia.
  rewrite Z.mod_small //; lia.
Qed.

(* Two limbs of a word below 2^64 hold its value. *)
Lemma split_word W :
  (Int64.unsigned (Int64.and W (Int64.repr 4294967295)) +
   2 ^ 32 * Int64.unsigned (Int64.shru' W (Int.modu (Int.repr 32) Int64.iwordsize')) =
   Int64.unsigned W)%Z.
Proof.
  rewrite and_mask shru32.
  have := Z.div_mod (Int64.unsigned W) (2 ^ 32) ltac:(lia); lia.
Qed.

End Words.

(* 2^f as six limbs: the limb f / 32 holds 2^(f mod 32). *)
Lemma pow2_limbs f w : (0 <= f < 192)%Z ->
  Int64.unsigned w = (2 ^ (f mod 32))%Z ->
  let l := replace (Z.to_nat (f / 32)) (repeat Int64.zero 6) w in
  length l = 6%nat /\ limbs l /\ val32 l = (2 ^ f)%Z.
Proof.
  move=> Hf Hw l.
  have Hm := Z.mod_pos_bound f 32 ltac:(lia).
  have Hd : (0 <= f / 32 < 6)%Z.
  { split; [apply: Z.div_pos | apply: Z.div_lt_upper_bound]; lia. }
  have [Hl [Hz Hv]] := zeros6_aux.
  split; first by rewrite /l replace_length.
  split.
  - apply: limbs_replace => //; rewrite Hw.
    apply: Z.pow_lt_mono_r; lia.
  - rewrite /l val32_replace ?repeat_length; first lia.
    rewrite Hv nth_repeat_lt; first lia.
    rewrite Int64.unsigned_zero Hw /base32 Z2Nat.id; first lia.
    rewrite Z.sub_0_r Z.add_0_l -Z.pow_add_r; try lia.
    congr (2 ^ _)%Z; have := Z.div_mod f 32 ltac:(lia); lia.
Qed.

(** ** Splitting a list of limbs *)

(* A list cut around its element k. *)
Lemma list_split (l : list int64) k : (k < length l)%coq_nat ->
  l = (firstn k l ++ List.nth k l Int64.zero :: skipn (S k) l)%list.
Proof.
  elim: l k => [|x l IH] [|k] /= H; try lia; first by [].
  rewrite -IH //; lia.
Qed.

(* The first k limbs of limbs are limbs. *)
Lemma limbs_firstn l k : limbs l -> limbs (firstn k l).
Proof.
  elim: l k => [|x l IH] [|k] Hl p; cbn [firstn];
    try by case: p => [|p]; rewrite /= Int64.unsigned_zero; lia.
  case: p => [|p]; first exact: (Hl 0%nat).
  apply: IH => q; exact: (Hl (S q)).
Qed.

(* (A + 2^n B) mod 2^(n+m), for A < 2^n. *)
Lemma mod_shift A B n m : (0 <= n)%Z -> (0 <= m)%Z -> (0 <= A < 2 ^ n)%Z ->
  ((A + 2 ^ n * B) mod 2 ^ (n + m) = A + 2 ^ n * (B mod 2 ^ m))%Z.
Proof.
  move=> Hn Hm HA.
  have Hp : (0 < 2 ^ m)%Z by apply: Z.pow_pos_nonneg; lia.
  have HB := Z.mod_pos_bound B (2 ^ m) Hp.
  have E : (2 ^ (n + m) = 2 ^ n * 2 ^ m)%Z by apply: Z.pow_add_r.
  rewrite E.
  symmetry; apply: (Z.mod_unique _ _ (B / 2 ^ m)); [left|].
  - nia.
  - have EB := Z.div_mod B (2 ^ m) ltac:(lia).
    rewrite {1}EB; ring.
Qed.

(* b mod 2^(32 j + r): the low j limbs, limb j mod 2^r, then zeros. *)
Lemma low_limbs ys xs j r w :
  length ys = 6%nat -> limbs ys -> (j < 6)%coq_nat -> (0 <= r < 32)%Z ->
  length xs = 6%nat ->
  (forall p, (p < 6)%coq_nat -> List.nth p xs Int64.zero =
     if (p <? j)%nat then List.nth p ys Int64.zero
     else if (p =? j)%nat then w else Int64.zero) ->
  Int64.unsigned w = (Int64.unsigned (List.nth j ys Int64.zero) mod 2 ^ r)%Z ->
  limbs xs /\ val32 xs = (val32 ys mod 2 ^ (32 * Z.of_nat j + r))%Z.
Proof.
  move=> Hly Hy Hj Hr Hlx Hx Hw.
  have Hyj := Hy j.
  have Hm := Z.mod_pos_bound (Int64.unsigned (List.nth j ys Int64.zero)) (2 ^ r)
               ltac:(apply: Z.pow_pos_nonneg; lia).
  have Hw32 : (Int64.unsigned w < 2 ^ 32)%Z.
  { have : (2 ^ r <= 2 ^ 32)%Z by apply: Z.pow_le_mono_r; lia. lia. }
  split.
  - move=> p; case: (Nat.lt_ge_cases p 6) => Hp.
    + rewrite Hx //; case: Nat.ltb; first exact: Hy.
      case: Nat.eqb => //; rewrite Int64.unsigned_zero; lia.
    + rewrite nth_overflow ?Int64.unsigned_zero; lia.
  - have Ex : xs = (firstn j ys ++ w :: repeat Int64.zero (5 - j))%list.
    { apply: list6_ext => //.
      - rewrite length_app length_firstn /= repeat_length; lia.
      - move=> p Hp; rewrite Hx //.
        have Lf : length (firstn j ys) = j by rewrite length_firstn; lia.
        case: (Nat.ltb_spec p j) => Hpj.
        + rewrite app_nth1 ?Lf // List.nth_firstn.
          by case: (Nat.ltb_spec p j) => //; lia.
        + rewrite app_nth2 ?Lf //.
          case: (Nat.eqb_spec p j) => Hpj'.
          * by rewrite Hpj' Nat.sub_diag.
          * have -> : (p - j = S (p - j - 1))%coq_nat by lia.
            rewrite /= nth_repeat_lt //; lia. }
    rewrite Ex {2}(list_split ys j) ?Hly //.
    rewrite !val32_app length_firstn.
    have -> : Init.Nat.min j (length ys) = j by lia.
    cbn [val32].
    have -> : val32 (repeat Int64.zero (5 - j)) = 0%Z.
    { by elim: (5 - j)%nat => [|n IH] //=; rewrite IH Int64.unsigned_zero. }
    have HA := val32_bound (firstn j ys) (limbs_firstn _ _ Hy).
    rewrite length_firstn in HA.
    have Ej : Init.Nat.min j (length ys) = j by lia.
    rewrite Ej /base32 in HA *.
    rewrite mod_shift; try lia.
    + have := val32_nonneg (firstn j ys); lia.
    + rewrite Z.mul_0_r Z.add_0_r Hw; congr (_ + _ * _)%Z.
      rewrite -Z.add_mod_idemp_r; first by apply: Z.pow_nonzero; lia.
      have -> : (2 ^ 32 = 2 ^ (32 - r) * 2 ^ r)%Z.
      { rewrite -Z.pow_add_r; try lia; congr (2 ^ _)%Z; lia. }
      rewrite (Z.mul_comm (2 ^ (32 - r))) -Z.mul_assoc Z.mul_comm Z.mod_mul;
        first by apply: Z.pow_nonzero; lia.
      by rewrite Z.add_0_r.
Qed.

(* Evaluate the operations on words that the WP leaves. *)
Ltac wsimpl :=
  rewrite /sem_cmpu /sem_cmp /sem_binarith /sem_cast /shrink /=;
  try unfold divu64; try unfold modu64; try unfold shl64; try unfold shru64;
  try unfold Ops.sem_cast; rewrite /= ?eq32 /=.

(* Show the goal without the function record (for probes only). *)
Ltac peek :=
  match goal with F := context [no_repet_check_correct] |- _ => clearbody F end;
  repeat match goal with H := _ |- _ =>
    lazymatch type of H with positive => fail | _ => clear H end end.

(** ** Comparing numbers from the top limb *)

(* The limbs above i agree: the tails after i are equal. *)
Lemma skipn_eq_top (xs ys : list int64) i :
  length xs = 6%nat -> length ys = 6%nat ->
  (forall p, (i < p)%coq_nat -> (p < 6)%coq_nat ->
     List.nth p xs Int64.zero = List.nth p ys Int64.zero) ->
  skipn (S i) xs = skipn (S i) ys.
Proof.
  move=> Hx Hy H.
  apply: (List.nth_ext _ _ Int64.zero Int64.zero).
  - rewrite !length_skipn; lia.
  - move=> p Hp; rewrite !List.nth_skipn; apply: H; rewrite length_skipn in Hp; lia.
Qed.

(* Equal limbs above i and a smaller limb i: a smaller number. *)
Lemma val32_lt_top xs ys i :
  length xs = 6%nat -> length ys = 6%nat -> limbs xs -> limbs ys ->
  (i < 6)%coq_nat ->
  (forall p, (i < p)%coq_nat -> (p < 6)%coq_nat ->
     List.nth p xs Int64.zero = List.nth p ys Int64.zero) ->
  (Int64.unsigned (List.nth i xs Int64.zero) <
   Int64.unsigned (List.nth i ys Int64.zero))%Z ->
  (val32 xs < val32 ys)%Z.
Proof.
  move=> Hx Hy Lx Ly Hi Ht Hlt.
  have Es := skipn_eq_top xs ys i Hx Hy Ht.
  have Ex := list_split xs i ltac:(lia).
  have Ey := list_split ys i ltac:(lia).
  rewrite {1}Ex {1}Ey Es.
  rewrite !val32_app.
  rewrite !length_firstn.
  have -> : Init.Nat.min i (length xs) = i by lia.
  have -> : Init.Nat.min i (length ys) = i by lia.
  cbn [val32].
  have HA := val32_bound (firstn i xs) (limbs_firstn _ _ Lx).
  rewrite length_firstn in HA.
  have E : Init.Nat.min i (length xs) = i by lia.
  rewrite E in HA.
  have HB := val32_nonneg (firstn i ys).
  have HP := base32_pos i.
  move: HA HB HP Hlt.
  set B := base32 i; set T := val32 (skipn (S i) ys).
  set x := Int64.unsigned (nth i xs _); set y := Int64.unsigned (nth i ys _).
  nia.
Qed.

(** ** Bit lengths *)

(* A number of n bits plus 2^n has n + 1 bits. *)
Lemma bitlen_top Y n : (0 <= n)%Z -> (0 <= Y < 2 ^ n)%Z ->
  ExpModel.bitlen (Y + 2 ^ n) = (n + 1)%Z.
Proof.
  move=> Hn HY; rewrite /ExpModel.bitlen.
  have Hp : (0 < 2 ^ n)%Z by apply: Z.pow_pos_nonneg; lia.
  case: (Z.leb_spec (Y + 2 ^ n) 0) => H; first lia.
  rewrite (Z.log2_unique (Y + 2 ^ n) n) //.
  rewrite Z.pow_succ_r; lia.
Qed.

(* Scanning bit k of limb i. *)
Lemma bitlen_step X i w k : (0 <= k)%Z -> (0 <= X < base32 i)%Z ->
  ExpModel.bitlen (X + base32 i * (w mod 2 ^ (k + 1))) =
  if ((w / 2 ^ k) mod 2 =? 0)%Z
  then ExpModel.bitlen (X + base32 i * (w mod 2 ^ k))
  else (32 * Z.of_nat i + k + 1)%Z.
Proof.
  move=> Hk HX.
  have Hk2 : (0 < 2 ^ k)%Z by apply: Z.pow_pos_nonneg; lia.
  have E2 : (2 ^ (k + 1) = 2 ^ k * 2)%Z by rewrite Z.pow_add_r ?Z.pow_1_r; lia.
  rewrite E2 Z.rem_mul_r; try lia.
  have Hb := Z.mod_pos_bound (w / 2 ^ k) 2 ltac:(lia).
  have Hr := Z.mod_pos_bound w (2 ^ k) Hk2.
  have HB := base32_pos i.
  case: (Z.eqb_spec ((w / 2 ^ k) mod 2) 0) => E.
  - by rewrite E Z.mul_0_r Z.add_0_r.
  - have -> : ((w / 2 ^ k) mod 2 = 1)%Z by lia.
    have Eb : (base32 i * 2 ^ k = 2 ^ (32 * Z.of_nat i + k))%Z.
    { rewrite /base32 -Z.pow_add_r //; lia. }
    have -> : (X + base32 i * (w mod 2 ^ k + 2 ^ k * 1) =
               X + base32 i * (w mod 2 ^ k) + 2 ^ (32 * Z.of_nat i + k))%Z.
    { rewrite -Eb; ring. }
    apply: bitlen_top; first lia.
    rewrite -Eb; nia.
Qed.

(** ** Writes into six zero limbs *)

(* Two words written at q and q + 1. *)
Lemma val32_write2 q x0 x1 : (q + 1 < 6)%coq_nat ->
  let l := replace (q + 1) (replace q (repeat Int64.zero 6) x0) x1 in
  length l = 6%nat /\
  val32 l = (base32 q * (Int64.unsigned x0 + 2 ^ 32 * Int64.unsigned x1))%Z /\
  ((Int64.unsigned x0 < 2 ^ 32)%Z -> (Int64.unsigned x1 < 2 ^ 32)%Z -> limbs l).
Proof.
  move=> Hq l.
  have [Hl [Hz Hv]] := zeros6_aux.
  split; first by rewrite /l; rewrite !replace_length.
  split.
  - rewrite /l.
    rewrite val32_replace; first by rewrite replace_length repeat_length; lia.
    rewrite val32_replace; first by rewrite repeat_length; lia.
    rewrite nth_replace_other; first lia.
    rewrite Hv.
    rewrite nth_repeat_lt; first lia.
    rewrite nth_repeat_lt; first lia.
    rewrite Int64.unsigned_zero addn1 base32S; ring.
  - move=> H0 H1; apply: limbs_replace => //; exact: limbs_replace.
Qed.

(* Three words written at q, q + 1 and q + 2. *)
Lemma val32_write3 q x0 x1 x2 : (q + 2 < 6)%coq_nat ->
  let l := replace (q + 2) (replace (q + 1) (replace q (repeat Int64.zero 6) x0) x1) x2 in
  length l = 6%nat /\
  val32 l = (base32 q * (Int64.unsigned x0 + 2 ^ 32 * Int64.unsigned x1 +
                         2 ^ 64 * Int64.unsigned x2))%Z /\
  ((Int64.unsigned x0 < 2 ^ 32)%Z -> (Int64.unsigned x1 < 2 ^ 32)%Z ->
   (Int64.unsigned x2 < 2 ^ 32)%Z -> limbs l).
Proof.
  move=> Hq l.
  have [Hl [Hv Hlim]] := val32_write2 q x0 x1 ltac:(lia).
  split; first by rewrite /l replace_length.
  split.
  - rewrite /l.
    rewrite val32_replace; first by rewrite Hl; lia.
    rewrite Hv.
    rewrite nth_replace_other; first lia.
    rewrite nth_replace_other; first lia.
    rewrite nth_repeat_lt; first lia.
    rewrite Int64.unsigned_zero addn2; rewrite !base32S; ring.
  - move=> H0 H1 H2; apply: limbs_replace => //; exact: Hlim.
Qed.

(* v 2^e in three limbs from limb e / 32, as num_scale computes it. *)
Lemma scale_pos V E lo hi : (0 <= V < 2 ^ 53)%Z -> (0 <= E < 128)%Z ->
  lo = (V mod 2 ^ 32 * 2 ^ (E mod 32))%Z ->
  hi = (V / 2 ^ 32 * 2 ^ (E mod 32) + lo / 2 ^ 32)%Z ->
  (base32 (Z.to_nat (E / 32)) *
     (lo mod 2 ^ 32 + 2 ^ 32 * (hi mod 2 ^ 32) + 2 ^ 64 * (hi / 2 ^ 32)) =
   V * 2 ^ E)%Z.
Proof.
  move=> HV HE Elo Ehi.
  have Hr := Z.mod_pos_bound E 32 ltac:(lia).
  have Hq : (0 <= E / 32)%Z by apply: Z.div_pos; lia.
  have E64 : (2 ^ 64 = 2 ^ 32 * 2 ^ 32)%Z by [].
  have Hhi := Z.div_mod hi (2 ^ 32) ltac:(lia).
  have Hlo := Z.div_mod lo (2 ^ 32) ltac:(lia).
  have HVd := Z.div_mod V (2 ^ 32) ltac:(lia).
  have -> : (lo mod 2 ^ 32 + 2 ^ 32 * (hi mod 2 ^ 32) + 2 ^ 64 * (hi / 2 ^ 32) =
             V * 2 ^ (E mod 32))%Z.
  { rewrite E64; nia. }
  rewrite /base32 Z2Nat.id // Z.mul_comm -Z.mul_assoc -Z.pow_add_r; try lia.
  have := Z.div_mod E 32 ltac:(lia) => HEd.
  rewrite (_ : (E mod 32 + 32 * (E / 32) = E)%Z) //; lia.
Qed.
