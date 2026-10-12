(** * add: B_ia <- B_ia + B_ib mod 2^(64 l)

    The proof of the function [add] of [htr3.c] against [add_spec]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Spec_add.

Definition Gprog : funspecs := [add_spec].

(** One [ADD_LIMB]: the sum modulo 2^64 plus its carry times 2^64 is the
    sum. *)
Lemma add_ltu a b : word a -> word b ->
  Int64.unsigned (Int64.add (Int64.repr a) (Int64.repr b)) +
    2 ^ wbits *
      Z.b2z (Int64.ltu (Int64.add (Int64.repr a) (Int64.repr b))
               (Int64.repr b)) =
  a + b.
Proof.
  intros Ha Hb; unfold word, wbits in *.
  unfold Int64.add, Int64.ltu.
  rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64) in *.
  rewrite (Z.mod_small a), (Z.mod_small b) by lia.
  destruct (zlt (a + b) (2 ^ 64)).
  - rewrite (Z.mod_small (a + b)) by lia.
    destruct (zlt (a + b) b); simpl; lia.
  - rewrite <- (Z.mod_unique_pos (a + b) (2 ^ 64) 1 (a + b - 2 ^ 64))
      by lia.
    destruct (zlt (a + b - 2 ^ 64) b); simpl; lia.
Qed.

(** One step of the loop, the two [ADD_LIMB]: the old word plus the old
    carry, then plus the word added.  The new word plus the sum of the two
    carries times 2^64 is the old word plus the word added plus the old
    carry, and the sum of the two carries is a carry again. *)
Lemma limb_step x y c : word x -> word y -> 0 <= c <= 1 ->
  let a1 := Int64.add (Int64.repr x) (Int64.repr c) in
  let a2 := Int64.add a1 (Int64.repr y) in
  let cd := Z.b2z (Int64.ltu a1 (Int64.repr c)) +
            Z.b2z (Int64.ltu a2 (Int64.repr y)) in
  Int64.unsigned a2 + 2 ^ wbits * cd = x + y + c /\ 0 <= cd <= 1.
Proof.
  intros Hx Hy Hc a1 a2 cd.
  assert (Wc : word c) by (unfold word, wbits; lia).
  pose proof (add_ltu x c Hx Wc) as H1; fold a1 in H1.
  assert (W1 : word (Int64.unsigned a1))
    by (unfold word, wbits; pose proof (Int64.unsigned_range a1); auto).
  pose proof (add_ltu (Int64.unsigned a1) y W1 Hy) as H2.
  rewrite Int64.repr_unsigned in H2; fold a2 in H2.
  pose proof (Int64.unsigned_range a2) as R2.
  change Int64.modulus with (2 ^ 64) in R2.
  unfold word, wbits in *.
  unfold cd.
  destruct (Int64.ltu a1 (Int64.repr c)), (Int64.ltu a2 (Int64.repr y));
    simpl in *; lia.
Qed.

Lemma body_add : semax_body Vprog Gprog f_add add_spec.
Proof.
  start_function.
  assert_PROP (Zlength xs <= Int64.max_unsigned).
  { entailer!.
    destruct H6 as (Hp & _ & Hsz & _).
    destruct p; try contradiction.
    simpl in Hsz; rewrite Z.max_r in Hsz by lia.
    pose proof (Ptrofs.unsigned_range i).
    change Ptrofs.modulus with Int64.modulus in Hsz.
    unfold Int64.max_unsigned; lia. }
  forward.
  forward_for_simple_bound l
    (EX i : Z, EX xs' : list Z, EX c : Z,
     PROP (0 <= c <= 1; Zlength xs' = Zlength xs; Forall word xs';
           forall q, q < ia \/ ia + i <= q -> Znth q xs' = Znth q xs;
           (valZ (sublist ia (ia + i) xs') + c * baseZ i =
             valZ (sublist ia (ia + i) xs) + valZ (sublist ib (ib + i) xs))%Z)
     LOCAL (temp _cy (Vlong (Int64.repr c)); temp _B p;
            temp _ia (Vlong (Int64.repr ia)); temp _ib (Vlong (Int64.repr ib));
            temp _l (Vlong (Int64.repr l)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p)).
  - Exists xs 0.
    entailer!.
    rewrite !sublist_nil; reflexivity.
  - Intros.
    rename H8 into Hc, H9 into Hlen, H10 into Hw, H11 into Hout,
      H12 into Hval.
    set (x := Znth (ia + i) xs).
    set (y := Znth (ib + i) xs).
    assert (Ex : Znth (ia + i) xs' = x) by (apply Hout; lia).
    assert (Ey : Znth (ib + i) xs' = y) by (apply Hout; lia).
    assert (Wx : word x) by (apply Forall_Znth; auto; lia).
    assert (Wy : word y) by (apply Forall_Znth; auto; lia).
    forward.
    { entailer!; rewrite Znth_vwords by lia; exact I. }
    rewrite Znth_vwords, Ex by lia.
    forward.
    { entailer!; rewrite Znth_vwords by lia; exact I. }
    rewrite Znth_vwords, Ey by lia.
    forward. forward. forward. forward. forward. forward.
    pose proof (limb_step x y c Wx Wy Hc) as [Hs Hcd]; cbv zeta in Hs, Hcd.
    set (a1 := Int64.add (Int64.repr x) (Int64.repr c)) in *.
    set (a2 := Int64.add a1 (Int64.repr y)) in *.
    change (Int64.cmpu Clt) with Int64.ltu.
    set (c1 := Z.b2z (Int64.ltu a1 (Int64.repr c))) in *.
    set (d := Z.b2z (Int64.ltu a2 (Int64.repr y))) in *.
    assert (Hc1 : 0 <= c1 <= 1)
      by (unfold c1; destruct (Int64.ltu a1 (Int64.repr c)); simpl; lia).
    assert (Hd : 0 <= d <= 1)
      by (unfold d; destruct (Int64.ltu a2 (Int64.repr y)); simpl; lia).
    rewrite !Int.signed_repr by rep_lia.
    rewrite add64_repr, upd_vwords by lia.
    set (xs1 := upd_Znth (ia + i) xs' (Int64.unsigned a2)).
    Exists xs1 (c1 + d).
    entailer!.
    repeat split.
    all: try lia.
    * unfold xs1; rewrite upd_Znth_Zlength; lia.
    * apply Forall_word_upd; auto.
    * intros q Hq.
      unfold xs1; rewrite upd_Znth_diff' by lia.
      apply Hout; lia.
    * pose proof (valZ_step 1 xs xs' ia ib i c (c1 + d) (Int64.unsigned a2))
        as Hst.
      unfold xs1; unfold wbits in *; lia.
  - Intros xs' c.
    Exists xs'; entailer!.
    apply (valZ_mod _ _ (- c)); auto.
    + apply Forall_sublist; auto.
    + rewrite Zlength_sublist; lia.
    + lia.
Qed.
Print Assumptions body_add.
