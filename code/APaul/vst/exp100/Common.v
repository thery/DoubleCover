(** * What the proofs of the functions of exp100.c share

    The C types of exp100.c; a number as an array of [NL] cells of 64
    bits, each holding a limb of 32 bits; the constant tables as
    read-only globals, tied to the lists of ExpTable.v; the word lemmas.
    The integers are those of ExpConsts.v ([valZ], [limb]), always named
    through the abbreviations below: ExpConsts is never imported, so its
    names never meet those of VST nor [valZ] of code/APaul/vst/Words.v
    (words of 64 bits). *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight.
Require Exp100.ExpTable Exp100.ExpConsts.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** ** Sizes, as in exp100.h (numerals, so that list_solve sees them) *)

Notation NL := 6%Z.     (* limbs of a number *)
Notation NP := 7%Z.     (* limbs of a number times a limb *)
Notation NT := 64%Z.    (* rows of T *)
Notation NC := 17%Z.    (* rows of C: DEG + 1 *)
Notation NM := 3%Z.     (* words of 64 bits of the output M *)

(** ** Numbers *)

Notation limb_bits := Exp100.ExpNum.limb_bits.
Notation limb := Exp100.ExpNum.limb.
Notation valZ := Exp100.ExpNum.valZ.

(** A word of 64 bits, and the number a list of words stands for. *)
Definition word_bits : Z := 64.
Definition word (w : Z) : Prop := 0 <= w < 2 ^ word_bits.

Fixpoint valW (ws : list Z) : Z :=
  match ws with
  | [] => 0
  | w :: r => w + 2 ^ word_bits * valW r
  end.

(** The values of the cells holding [xs]. *)
Definition vwords (xs : list Z) : list val := map Vlong (map Int64.repr xs).

(** A number [xs] at [p]. *)
Definition num (sh : share) (xs : list Z) (p : val) : mpred :=
  data_at sh (tarray tulong NL) (vwords xs) p.

Lemma Zlength_vwords xs : Zlength (vwords xs) = Zlength xs.
Proof. unfold vwords; rewrite !Zlength_map; reflexivity. Qed.

Lemma Znth_vwords xs k : 0 <= k < Zlength xs ->
  Znth k (vwords xs) = Vlong (Int64.repr (Znth k xs)).
Proof.
  intros Hk; unfold vwords.
  rewrite Znth_map by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia; reflexivity.
Qed.

(** Writing a word [w] at [k]. *)
Lemma upd_vwords xs k w : 0 <= k < Zlength xs ->
  upd_Znth k (vwords xs) (Vlong w) =
  vwords (upd_Znth k xs (Int64.unsigned w)).
Proof.
  intros Hk; unfold vwords.
  rewrite <- (Int64.repr_unsigned w) at 1.
  rewrite (upd_Znth_map Vlong), (upd_Znth_map Int64.repr); reflexivity.
Qed.

(** ** The value of a list of limbs *)

Lemma valZ_app a b :
  valZ (a ++ b) = valZ a + 2 ^ (limb_bits * Zlength a) * valZ b.
Proof.
  induction a as [|w a IH]; cbn [app Exp100.ExpNum.valZ].
  - change (Zlength (@nil Z)) with 0; rewrite Z.mul_0_r, Z.pow_0_r; lia.
  - rewrite IH, Zlength_cons, <- Z.add_1_r.
    replace (limb_bits * (Zlength a + 1))
      with (limb_bits * Zlength a + limb_bits) by lia.
    rewrite Z.pow_add_r
      by (unfold Exp100.ExpNum.limb_bits;
          pose proof (Zlength_nonneg a); lia).
    ring.
Qed.

Lemma valZ_sublist_succ xs b : 0 <= b < Zlength xs ->
  valZ (sublist 0 (b + 1) xs) =
  valZ (sublist 0 b xs) + 2 ^ (limb_bits * b) * Znth b xs.
Proof.
  intros Hb; rewrite (sublist_split 0 b (b + 1)) by lia.
  rewrite valZ_app, sublist_len_1 by lia; simpl Exp100.ExpNum.valZ.
  rewrite Zlength_sublist by lia; replace (b - 0) with b by lia; ring.
Qed.

(** Limbs stand for a number of [limb_bits] bits per limb. *)
Lemma valZ_bounds xs : Forall limb xs ->
  0 <= valZ xs < 2 ^ (limb_bits * Zlength xs).
Proof.
  induction 1 as [|w xs Hw _ IH]; cbn [Exp100.ExpNum.valZ].
  - change (Zlength (@nil Z)) with 0; simpl; lia.
  - rewrite Zlength_cons, <- Z.add_1_r, Z.mul_add_distr_l, Z.mul_1_r.
    rewrite Z.add_comm, Z.pow_add_r
      by (unfold Exp100.ExpNum.limb_bits;
          pose proof (Zlength_nonneg xs); lia).
    unfold Exp100.ExpNum.limb in Hw; nia.
Qed.

(** ** Word lemmas *)

Lemma and_mask32 z : 0 <= z < 2 ^ 64 ->
  Int64.and (Int64.repr z) (Int64.repr 4294967295) =
  Int64.repr (z mod 2 ^ 32).
Proof.
  intros Hz.
  change 4294967295 with (Z.ones 32).
  apply Int64.same_bits_eq; intros k Hk.
  rewrite Int64.bits_and by lia.
  rewrite !Int64.testbit_repr by lia.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_spec; reflexivity.
Qed.

Lemma shru32 z : 0 <= z < 2 ^ 64 ->
  Int64.shru (Int64.repr z) (Int64.repr 32) = Int64.repr (z / 2 ^ 32).
Proof.
  intros Hz.
  rewrite Int64.shru_div_two_p.
  rewrite !Int64.unsigned_repr by (unfold Int64.max_unsigned; simpl; lia).
  reflexivity.
Qed.

(** ** The constants *)

(** The read-only globals, as the lists of ExpTable.v. *)
Definition consts (gv : globals) : mpred :=
  (data_at Ers (tarray (tarray tulong NL) NT)
     (map vwords Exp100.ExpTable.T) (gv _T) *
   data_at Ers (tarray (tarray tulong NL) NC)
     (map vwords Exp100.ExpTable.C) (gv _C) *
   num Ers Exp100.ExpTable.LN2 (gv _LN2) *
   num Ers Exp100.ExpTable.RMAX (gv _RMAX) *
   data_at Ers tulong (Vlong (Int64.repr Exp100.ExpTable.INV)) (gv _INV))%logic.

(** The initial data of a list of words. *)
Definition init_words (xs : list Z) : list init_data :=
  map (fun z => Init_int64 (Int64.repr z)) xs.

(** The data exp100.c is compiled with are the lists of ExpTable.v. *)
Lemma v_T_init : gvar_init v_T = init_words (concat Exp100.ExpTable.T).
Proof. reflexivity. Qed.

Lemma v_C_init : gvar_init v_C = init_words (concat Exp100.ExpTable.C).
Proof. reflexivity. Qed.

Lemma v_LN2_init : gvar_init v_LN2 = init_words Exp100.ExpTable.LN2.
Proof. reflexivity. Qed.

Lemma v_RMAX_init : gvar_init v_RMAX = init_words Exp100.ExpTable.RMAX.
Proof. reflexivity. Qed.

Lemma v_INV_init : gvar_init v_INV = init_words [Exp100.ExpTable.INV].
Proof. reflexivity. Qed.

(** The constants are numbers, in the form the statements ask. *)
Lemma LN2_num :
  Zlength Exp100.ExpTable.LN2 = NL /\ Forall limb Exp100.ExpTable.LN2.
Proof. split; [reflexivity|exact (proj2 Exp100.ExpConsts.num_LN2)]. Qed.

Lemma RMAX_num :
  Zlength Exp100.ExpTable.RMAX = NL /\ Forall limb Exp100.ExpTable.RMAX.
Proof. split; [reflexivity|exact (proj2 Exp100.ExpConsts.num_RMAX)]. Qed.

Lemma INV_limb : limb Exp100.ExpTable.INV.
Proof. exact Exp100.ExpConsts.limb_INV. Qed.

Lemma T_num j : 0 <= j < NT ->
  Zlength (Znth j Exp100.ExpTable.T) = NL /\
  Forall limb (Znth j Exp100.ExpTable.T).
Proof.
  intros Hj.
  assert (Hn : Exp100.ExpNum.num (Znth j Exp100.ExpTable.T)).
  { apply (proj1 (Forall_Znth _ _) Exp100.ExpConsts.num_T).
    replace (Zlength Exp100.ExpTable.T) with NT by reflexivity; lia. }
  destruct Hn as [Hl Hf]; split; [rewrite Zlength_correct, Hl|]; auto.
Qed.

Lemma C_num i : 0 <= i < NC ->
  Zlength (Znth i Exp100.ExpTable.C) = NL /\
  Forall limb (Znth i Exp100.ExpTable.C).
Proof.
  intros Hi.
  assert (Hn : Exp100.ExpNum.num (Znth i Exp100.ExpTable.C)).
  { apply (proj1 (Forall_Znth _ _) Exp100.ExpConsts.num_C).
    replace (Zlength Exp100.ExpTable.C) with NC by reflexivity; lia. }
  destruct Hn as [Hl Hf]; split; [rewrite Zlength_correct, Hl|]; auto.
Qed.
