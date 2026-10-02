(** * What the proofs of the functions of htr3.c share

    The C types of [htr3.c], and the array of words: a list [xs] of
    integers in [0, 2^64) held as [tarray tulong]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** The values of the array holding the words [xs]. *)
Definition vwords (xs : list Z) : list val := map Vlong (map Int64.repr xs).

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

(** The words after a write at [k]: [Int64.unsigned] gives a word. *)
Lemma Forall_word_upd xs k w : Forall word xs ->
  Forall word (upd_Znth k xs (Int64.unsigned w)).
Proof.
  intros Hw; apply Forall_upd_Znth; auto.
  unfold word, wbits; pose proof (Int64.unsigned_range w); auto.
Qed.
