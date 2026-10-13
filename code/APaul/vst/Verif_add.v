(** * add: B_ia <- B_ia + B_ib mod 2^(64 l)

    The proof of the function [add] of [htr3.c] against [add_spec]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Spec_add.

Definition Gprog : funspecs := [addcarry_spec; add_spec].

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
     LOCAL (temp _cy (Vint (Int.repr c)); temp _B p;
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
    (* the cell ia + i, alone, for the call *)
    set (n := Zlength xs) in *.
    set (vs := vwords xs').
    assert (Lvs : Zlength vs = n) by (unfold vs; rewrite Zlength_vwords; lia).
    assert_PROP (field_compatible (tarray tulong n) [] p) as FC
      by (unfold vs; entailer!).
    assert (NA : naturally_aligned tulong) by (simpl; auto).
    assert (B1 : 0 <= ia + i <= ia + i + 1) by lia.
    assert (B2 : ia + i + 1 <= n <= Zlength vs) by lia.
    assert (E0 : vs = sublist 0 n vs) by (rewrite sublist_same by lia; reflexivity).
    rewrite (split3_data_at_Tarray sh tulong n (ia + i) (ia + i + 1) vs vs
               (sublist 0 (ia + i) vs) (sublist (ia + i) (ia + i + 1) vs)
               (sublist (ia + i + 1) n vs) p NA B1 B2 E0 eq_refl eq_refl eq_refl).
    replace (ia + i + 1 - (ia + i)) with 1 by lia.
    rewrite sublist_len_1 by lia.
    erewrite (data_at_singleton_array_eq sh tulong (Znth (ia + i) vs)) by reflexivity.
    set (a0 := field_address0 (Tarray tulong n noattr) (SUB (ia + i)) p).
    set (a1 := field_address0 (Tarray tulong n noattr) (SUB (ia + i + 1)) p).
    forward_call (c, x, y, sh, a0).
    { entailer!.
      unfold a0.
      match goal with |- context [field_address0 (Tarray tulong ?N noattr) _ _] =>
        change (Tarray tulong N noattr) with (tarray tulong N) end.
      rewrite arr_field_address0 by (auto; lia).
      simpl.
      rewrite zero_ext_inrange
        by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
      reflexivity. }
    { sep_apply (data_at_data_at_ sh tulong (Znth (ia + i) vs) a0); cancel. }
    forward.
    (* the array again, with the new word at ia + i *)
    set (w := Int64.repr (x + y + c)).
    set (xs1 := upd_Znth (ia + i) xs' (Int64.unsigned w)).
    assert (Vs1 : vwords xs1 = upd_Znth (ia + i) vs (Vlong w))
      by (unfold xs1, vs; rewrite upd_vwords by lia; reflexivity).
    assert (L1 : Zlength (upd_Znth (ia + i) vs (Vlong w)) = n)
      by (rewrite upd_Znth_Zlength; lia).
    assert (B3 : ia + i + 1 <= n <= Zlength (upd_Znth (ia + i) vs (Vlong w)))
      by lia.
    assert (E1 : upd_Znth (ia + i) vs (Vlong w) =
                 sublist 0 n (upd_Znth (ia + i) vs (Vlong w)))
      by (rewrite sublist_same by lia; reflexivity).
    assert (JOIN :
      (data_at sh (Tarray tulong (ia + i) noattr) (sublist 0 (ia + i) vs) p *
       data_at sh tulong (Vlong w) a0 *
       data_at sh (Tarray tulong (n - (ia + i + 1)) noattr)
         (sublist (ia + i + 1) n vs) a1)%logic =
      data_at sh (tarray tulong n) (vwords xs1) p).
    { rewrite Vs1; unfold tarray.
      rewrite (split3_data_at_Tarray sh tulong n (ia + i) (ia + i + 1)
                 _ _ _ _ _ p NA B1 B3 E1 eq_refl eq_refl eq_refl).
      replace (ia + i + 1 - (ia + i)) with 1 by lia.
      (* reptype tulong is val: lia needs the same Zlength as Lvs *)
      change (reptype tulong) with val.
      rewrite sublist_len_1 by (rewrite upd_Znth_Zlength; lia).
      rewrite upd_Znth_same by lia.
      erewrite (data_at_singleton_array_eq sh tulong (Vlong w)) by reflexivity.
      rewrite sublist_upd_Znth_l, sublist_upd_Znth_r by lia.
      reflexivity. }
    (* the new carry, the new word *)
    assert (Bxy : 0 <= x + y + c < 2 * 2 ^ wbits) by (unfold word in *; lia).
    set (c' := (x + y + c) / 2 ^ wbits).
    assert (Hc' : 0 <= c' <= 1).
    { unfold c'; split.
      - apply Z.div_pos; [lia | unfold wbits; lia].
      - assert ((x + y + c) / 2 ^ wbits < 2)
          by (apply Z.div_lt_upper_bound; unfold wbits in *; lia).
        lia. }
    assert (Ew : Int64.unsigned w + 2 ^ wbits * c' = x + y + c).
    { unfold w, c'; rewrite Int64.unsigned_repr_eq.
      change Int64.modulus with (2 ^ wbits).
      pose proof (Z.div_mod (x + y + c) (2 ^ wbits)) as Dm.
      unfold wbits in *; lia. }
    rewrite zero_ext_inrange
      by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
    Exists xs1 c'.
    entailer!.
    + repeat split.
      * unfold xs1; rewrite upd_Znth_Zlength; lia.
      * unfold xs1; apply Forall_word_upd; auto.
      * intros q Hq.
        unfold xs1; rewrite upd_Znth_diff' by lia.
        apply Hout; lia.
      * pose proof (valZ_step 1 xs xs' ia ib i c c' (Int64.unsigned w)) as Hst.
        unfold xs1; unfold wbits in *; lia.
    + rewrite <- JOIN; cancel.
  - Intros xs' c.
    Exists xs'; entailer!.
    apply (valZ_mod _ _ (- c)); auto.
    + apply Forall_sublist; auto.
    + rewrite Zlength_sublist; lia.
    + lia.
Qed.
Print Assumptions body_add.
