(** * Numbers as lists of limbs

    The value [valZ] of a list of limbs of 32 bits, least significant
    first, on Stdlib lists: appending, writing one limb, dropping or
    keeping the low limbs, and the bounds.  Then the or of two pieces
    without common bits, the words of 64 bits made of two limbs, and the
    end of a carry loop.  Pure Z, Stdlib only: shared by the Rocq, VST and
    Capla proofs. *)

From Stdlib Require Import Bool ZArith Lia List.
From Exp100 Require Import ExpConsts.
Import ListNotations.

Open Scope Z_scope.

(** ** The value of a list of limbs *)

Lemma valZ_app a b :
  valZ (a ++ b) = valZ a + 2 ^ (limb_bits * Z.of_nat (length a)) * valZ b.
Proof.
induction a as [|w a IH]; cbn [app valZ length].
- rewrite Z.mul_0_r, Z.pow_0_r; lia.
- rewrite IH, Nat2Z.inj_succ, Z.mul_succ_r.
  rewrite Z.pow_add_r by (unfold limb_bits; lia); ring.
Qed.

(** Limbs stand for a number of [limb_bits] bits per limb. *)
Lemma valZ_bounds xs : Forall limb xs ->
  0 <= valZ xs < 2 ^ (limb_bits * Z.of_nat (length xs)).
Proof.
induction 1 as [|w xs Hw _ IH]; cbn [valZ length].
- rewrite Z.mul_0_r, Z.pow_0_r; lia.
- rewrite Nat2Z.inj_succ, Z.mul_succ_r.
  rewrite Z.add_comm, Z.pow_add_r by (unfold limb_bits; lia).
  unfold limb in Hw; nia.
Qed.

(** A number of exp100.c is below 2^192. *)
Lemma valZ_num xs : num xs -> 0 <= valZ xs < 2 ^ (limb_bits * Z.of_nat NL).
Proof. intros [Hl Hf]; rewrite <- Hl; apply valZ_bounds, Hf. Qed.

(* The low limbs and the high limbs of a list of limbs are limbs. *)
Lemma limbs_split k xs : Forall limb xs ->
  Forall limb (firstn k xs) /\ Forall limb (skipn k xs).
Proof. rewrite <- (firstn_skipn k xs) at 1; apply Forall_app. Qed.

(* The k low limbs, then the others. *)
Lemma valZ_split k xs : valZ xs =
  valZ (firstn k xs) + 2 ^ (limb_bits * Z.of_nat k) * valZ (skipn k xs).
Proof.
rewrite <- (firstn_skipn k xs) at 1; rewrite valZ_app.
destruct (Nat.le_gt_cases k (length xs)) as [Hk|Hk].
- rewrite firstn_length_le by exact Hk; reflexivity.
- rewrite skipn_all2 by lia; cbn [valZ]; lia.
Qed.

(* The k low limbs stand for the number modulo 2^(32 k). *)
Lemma valZ_firstn k xs : Forall limb xs ->
  valZ (firstn k xs) = valZ xs mod 2 ^ (limb_bits * Z.of_nat k).
Proof.
intros H; destruct (limbs_split k xs H) as [H1 H2].
pose proof (valZ_bounds _ H1) as B1; pose proof (valZ_bounds _ H2) as B2.
assert (Hl : 2 ^ (limb_bits * Z.of_nat (length (firstn k xs))) <=
             2 ^ (limb_bits * Z.of_nat k)).
{ apply Z.pow_le_mono_r; [lia|]; pose proof (firstn_le_length k xs).
  unfold limb_bits; lia. }
apply Z.mod_unique with (valZ (skipn k xs)); [lia|].
rewrite (valZ_split k xs) at 1; ring.
Qed.

(* Dropping k limbs divides the number by 2^(32 k). *)
Lemma valZ_skipn k xs : Forall limb xs ->
  valZ (skipn k xs) = valZ xs / 2 ^ (limb_bits * Z.of_nat k).
Proof.
intros H; destruct (limbs_split k xs H) as [H1 _].
pose proof (valZ_bounds _ H1) as B1.
assert (Hl : 2 ^ (limb_bits * Z.of_nat (length (firstn k xs))) <=
             2 ^ (limb_bits * Z.of_nat k)).
{ apply Z.pow_le_mono_r; [lia|]; pose proof (firstn_le_length k xs).
  unfold limb_bits; lia. }
apply Z.div_unique with (valZ (firstn k xs)); [lia|].
rewrite (valZ_split k xs) at 1; ring.
Qed.

(* Dropping the low limb divides the number by 2^32. *)
Lemma valZ_drop1 xs : Forall limb xs ->
  valZ (skipn 1 xs) = valZ xs / 2 ^ limb_bits.
Proof.
intros H; rewrite valZ_skipn by exact H; f_equal; unfold limb_bits; lia.
Qed.

(* m limbs from limb k of a number below 2^(32 (k + m)) are its top part. *)
Lemma valZ_shift k m xs : Forall limb xs ->
  valZ xs < 2 ^ (limb_bits * Z.of_nat (k + m)) ->
  valZ (firstn m (skipn k xs)) = valZ xs / 2 ^ (limb_bits * Z.of_nat k).
Proof.
intros H Hv; destruct (limbs_split k xs H) as [_ H2].
rewrite valZ_firstn, valZ_skipn by assumption.
pose proof (valZ_bounds _ H) as [B0 _].
rewrite Nat2Z.inj_add, Z.mul_add_distr_l, Z.pow_add_r in Hv
  by (unfold limb_bits; lia).
assert (Hk : 0 < 2 ^ (limb_bits * Z.of_nat k))
  by (apply Z.pow_pos_nonneg; unfold limb_bits; lia).
apply Z.mod_small; split; [apply Z.div_pos; lia|].
apply Z.div_lt_upper_bound; lia.
Qed.

(* A list cut around its element k. *)
Lemma list_middle k (xs : list Z) : (k < length xs)%nat ->
  xs = firstn k xs ++ nth k xs 0 :: skipn (S k) xs.
Proof.
revert k; induction xs as [|w xs IH]; intros k Hk; cbn [length] in Hk;
  [lia|].
destruct k as [|k]; [reflexivity|].
cbn [firstn skipn nth app]; f_equal; apply IH; lia.
Qed.

(* The k + 1 low limbs: the k low ones and limb k. *)
Lemma valZ_firstn_S k xs : (k < length xs)%nat ->
  valZ (firstn (S k) xs) =
  valZ (firstn k xs) + 2 ^ (limb_bits * Z.of_nat k) * nth k xs 0.
Proof.
intros Hk; rewrite (list_middle k xs Hk) at 1.
rewrite firstn_app, firstn_firstn, firstn_length_le by lia.
replace (Nat.min (S k) k) with k by lia; replace (S k - k)%nat with 1%nat
  by lia.
rewrite valZ_app, firstn_length_le by lia; cbn [firstn valZ]; ring.
Qed.

(* Writing v at limb k changes the number by (v - old) 2^(32 k). *)
Lemma valZ_upd xs k v : (k < length xs)%nat ->
  valZ (firstn k xs ++ v :: skipn (S k) xs) =
  valZ xs + (v - nth k xs 0) * 2 ^ (limb_bits * Z.of_nat k).
Proof.
intros Hk; rewrite (list_middle k xs Hk) at 3.
rewrite !valZ_app, firstn_length_le by lia; cbn [valZ]; ring.
Qed.

(** ** Or is plus on disjoint bits *)

(* a below 2^k and a multiple of 2^k have no common bit. *)
Lemma lor_add a b k : 0 <= k -> 0 <= a < 2 ^ k ->
  Z.lor a (b * 2 ^ k) = a + b * 2 ^ k.
Proof.
intros Hk Ha.
assert (Hl : Z.land a (b * 2 ^ k) = 0).
{ apply Z.bits_inj'; intros i Hi.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i k).
  - rewrite Z.mul_pow2_bits_low by lia; apply andb_false_r.
  - rewrite <- (Z.mod_small a (2 ^ k)) by lia.
    rewrite Z.mod_pow2_bits_high by lia; reflexivity. }
rewrite <- Z.lxor_lor, <- Z.add_nocarry_lxor by exact Hl; reflexivity.
Qed.

Lemma lor_shift7 a b : 0 <= a < 2 ^ 7 -> Z.lor a (b * 2 ^ 7) = a + b * 2 ^ 7.
Proof. apply lor_add; lia. Qed.

(* The word a | b << 32 of two limbs. *)
Lemma or_shl a b : 0 <= a < 2 ^ limb_bits ->
  Z.lor a (Z.shiftl b limb_bits) = a + 2 ^ limb_bits * b.
Proof.
intros Ha; rewrite Z.shiftl_mul_pow2 by (unfold limb_bits; lia).
rewrite lor_add by (unfold limb_bits in *; lia); ring.
Qed.

(* Bits 32 k + s .. 32 (k + 2) of a number of k + 2 limbs, from its two top
   limbs a and b: a >> s | b << (32 - s). *)
Lemma valZ_top2 l a b s : Forall limb l -> limb a -> 0 <= s <= limb_bits ->
  Z.lor (Z.shiftr a s) (Z.shiftl b (limb_bits - s)) =
  valZ (l ++ [a; b]) / 2 ^ (limb_bits * Z.of_nat (length l) + s).
Proof.
intros Hl Ha Hs; unfold limb in Ha.
pose proof (valZ_bounds l Hl) as HL.
rewrite valZ_app; cbn [valZ].
set (L := valZ l) in *; set (m := limb_bits * Z.of_nat (length l)) in *.
assert (Hm : 0 <= m) by (unfold m, limb_bits; lia).
assert (H2s : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
assert (H2m : 0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
assert (Hd := Z.div_mod a (2 ^ s) ltac:(lia)).
assert (Hmo := Z.mod_pos_bound a (2 ^ s) H2s).
assert (Hlt : a / 2 ^ s < 2 ^ (limb_bits - s)).
{ apply Z.div_lt_upper_bound; [lia|].
  rewrite <- Z.pow_add_r by lia; replace (s + (limb_bits - s)) with limb_bits
    by ring; lia. }
rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
assert (Ha1 : 0 <= a / 2 ^ s) by (apply Z.div_pos; lia).
rewrite lor_add by lia.
set (a1 := a / 2 ^ s) in *; set (a0 := a mod 2 ^ s) in *.
assert (E32 : 2 ^ limb_bits = 2 ^ s * 2 ^ (limb_bits - s)).
{ rewrite <- Z.pow_add_r by lia; f_equal; ring. }
apply Z.div_unique with (L + 2 ^ m * a0).
- left; split; [nia|]; rewrite Z.pow_add_r by lia; nia.
- rewrite Hd at 1; rewrite Z.pow_add_r, E32 by lia; ring.
Qed.

(* Bits 185 .. 223 of a number of 7 limbs, from its limbs 5 and 6. *)
Lemma bits185 p : length p = S NL -> Forall limb p ->
  Z.lor (Z.shiftr (nth 5 p 0) 25) (Z.shiftl (nth 6 p 0) 7) = valZ p / 2 ^ 185.
Proof.
intros Hl Hf.
do 7 (destruct p as [|? p]; [discriminate|]); destruct p; [|discriminate].
change [z; z0; z1; z2; z3; z4; z5] with ([z; z0; z1; z2; z3] ++ [z4; z5])
  in Hf |- *.
rewrite Forall_app in Hf; destruct Hf as [H1 H2].
inversion H2 as [|? ? Ha _]; subst.
apply (valZ_top2 _ _ _ 25 H1 Ha); unfold limb_bits; lia.
Qed.

(** ** Words of two limbs *)

Definition word_bits : Z := 64.  (* bits of a word *)
Definition word (w : Z) : Prop := 0 <= w < 2 ^ word_bits.

(** The number a list of words stands for, least significant first. *)
Fixpoint valW (ws : list Z) : Z :=
  match ws with
  | [] => 0
  | w :: r => w + 2 ^ word_bits * valW r
  end.

(** The 3 words of a number of 6 limbs: y[2i] | y[2i+1] << 32. *)
Definition pack (ys : list Z) : list Z :=
  [nth 0 ys 0 + 2 ^ limb_bits * nth 1 ys 0;
   nth 2 ys 0 + 2 ^ limb_bits * nth 3 ys 0;
   nth 4 ys 0 + 2 ^ limb_bits * nth 5 ys 0].

Lemma nth_pack ys i : (i < 3)%nat ->
  nth i (pack ys) 0 =
  nth (2 * i) ys 0 + 2 ^ limb_bits * nth (2 * i + 1) ys 0.
Proof.
intros Hi; destruct i as [|[|[|i]]]; [reflexivity..|lia].
Qed.

Lemma valW_pack ys : length ys = NL -> valW (pack ys) = valZ ys.
Proof.
intros H.
do 6 (destruct ys as [|? ys]; [discriminate|]); destruct ys; [|discriminate].
unfold pack; cbn [valW valZ nth].
unfold word_bits, limb_bits.
change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); ring.
Qed.

Lemma pack_word ys : num ys -> Forall word (pack ys).
Proof.
intros [Hl Hf].
do 6 (destruct ys as [|? ys]; [discriminate|]); destruct ys; [|discriminate].
unfold pack, word, word_bits; cbn [nth].
repeat match goal with H : Forall _ (_ :: _) |- _ =>
  inversion H; subst; clear H end.
unfold limb, limb_bits in *.
repeat constructor; change (2 ^ 64) with (2 ^ 32 * 2 ^ 32); nia.
Qed.

(** ** Carries *)

(* The end of a carry loop: the carry is 0 when the sum fits. *)
Lemma carry_end (a c s B : Z) : 0 <= a -> 0 <= c -> 0 < B ->
  a + c * B = s -> s < B -> a = s.
Proof. intros Ha Hc HB E Hs; assert (c = 0) by nia; subst; lia. Qed.
