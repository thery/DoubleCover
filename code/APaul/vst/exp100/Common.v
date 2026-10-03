Require Import VST.floyd.proofauto.
Require Import E.Limbs E.exp100_clight.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition NL := 6.
Definition vwords (xs : list Z) : list val := map Vlong (map Int64.repr xs).
Definition num (sh : share) (xs : list Z) (p : val) :=
  data_at sh (tarray tulong NL) (vwords xs) p.
Lemma Znth_vwords xs k : 0 <= k < Zlength xs ->
  Znth k (vwords xs) = Vlong (Int64.repr (Znth k xs)).
Proof.
  intros Hk; unfold vwords.
  rewrite Znth_map by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia; reflexivity.
Qed.
Lemma upd_vwords xs k w : 0 <= k < Zlength xs ->
  upd_Znth k (vwords xs) (Vlong w) = vwords (upd_Znth k xs (Int64.unsigned w)).
Proof.
  intros Hk; unfold vwords.
  rewrite <- (Int64.repr_unsigned w) at 1.
  rewrite (upd_Znth_map Vlong), (upd_Znth_map Int64.repr); reflexivity.
Qed.
