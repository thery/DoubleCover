(** * sub: B_ia <- B_ia - B_ib mod 2^(64 l)

    The function [sub] of [htr3.c] on a flat array of words, at two
    disjoint offsets [ia] and [ib]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.

Definition sub_spec : ident * funspec :=
 DECLARE _sub
 WITH sh : share, p : val, xs : list Z, ia : Z, ib : Z, l : Z
 PRE [ tptr tulong, tulong, tulong, tulong ]
   PROP (writable_share sh; Forall word xs;
         0 <= ia; 0 <= ib; 0 <= l;
         ia + l <= Zlength xs; ib + l <= Zlength xs;
         ia + l <= ib \/ ib + l <= ia)
   PARAMS (p; Vlong (Int64.repr ia); Vlong (Int64.repr ib);
           Vlong (Int64.repr l))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs) p)
 POST [ tvoid ]
   EX xs' : list Z,
   PROP (Zlength xs' = Zlength xs; Forall word xs';
         valZ (sublist ia (ia + l) xs') =
           (valZ (sublist ia (ia + l) xs) - valZ (sublist ib (ib + l) xs))
             mod baseZ l;
         forall q, q < ia \/ ia + l <= q -> Znth q xs' = Znth q xs)
   RETURN ()
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p).

Definition Gprog : funspecs := [sub_spec].

(** One step of the loop: the new word minus the new borrow times 2^64 is
    the old word minus the word subtracted minus the old borrow. *)
Lemma borrow_step x y c : word x -> word y -> 0 <= c <= 1 ->
  let t := Int64.add (Int64.repr y) (Int64.repr c) in
  Int64.unsigned (Int64.sub (Int64.repr x) t) -
    2 ^ wbits *
      (if orb (Int64.ltu t (Int64.repr c)) (Int64.ltu (Int64.repr x) t)
       then 1 else 0) =
  x - y - c.
Proof.
  intros Hx Hy Hc t; unfold word, wbits in *.
  unfold t, Int64.sub, Int64.add, Int64.ltu.
  rewrite !Int64.unsigned_repr_eq.
  change Int64.modulus with (2 ^ 64) in *.
  rewrite (Z.mod_small x), (Z.mod_small c) by lia.
  rewrite (Z.mod_small y) by lia.
  destruct (Z.eq_dec (y + c) (2 ^ 64)) as [E|E].
  - rewrite E, Z_mod_same_full.
    destruct (zlt 0 c); try lia; simpl.
    change (Z.pow_pos 2 64) with (2 ^ 64).
    rewrite Z.sub_0_r, (Z.mod_small x) by lia; lia.
  - rewrite (Z.mod_small (y + c)) by lia.
    destruct (zlt (y + c) c); try lia; simpl.
    change (Z.pow_pos 2 64) with (2 ^ 64).
    destruct (zlt x (y + c)).
    + rewrite <- (Z.mod_unique_pos (x - (y + c)) (2 ^ 64) (-1)
        (x - (y + c) + 2 ^ 64)) by lia.
      lia.
    + rewrite Z.mod_small; lia.
Qed.

Lemma body_sub : semax_body Vprog Gprog f_sub sub_spec.
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
           valZ (sublist ia (ia + i) xs') - c * baseZ i =
             valZ (sublist ia (ia + i) xs) - valZ (sublist ib (ib + i) xs))
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
    rewrite Znth_vwords, Ey by lia.
    forward.
    set (t := Int64.add (Int64.repr y) (Int64.repr c)).
    forward_if (temp _t'1 (Vint (if orb (Int64.ltu t (Int64.repr c))
                                        (Int64.ltu (Int64.repr x) t)
                                 then Int.one else Int.zero))).
    + forward.
      entailer!.
      match goal with E : Int64.ltu t _ = true |- _ => rewrite E end.
      reflexivity.
    + forward.
      { entailer!; rewrite Znth_vwords by lia; exact I. }
      rewrite Znth_vwords, Ex by lia.
      forward.
      entailer!.
      match goal with E : Int64.ltu t _ = false |- _ => rewrite E end.
      simpl; unfold bool2val, Int64.cmpu.
      destruct (Int64.ltu _ t); reflexivity.
    + forward.
      forward.
      { entailer!; rewrite Znth_vwords by lia; exact I. }
      rewrite Znth_vwords, Ex by lia.
      forward.
      pose proof (borrow_step x y c Wx Wy Hc) as Hs; cbv zeta in Hs.
      fold t in Hs.
      set (d := Int64.sub (Int64.repr x) t) in *.
      set (b := orb (Int64.ltu t (Int64.repr c)) (Int64.ltu (Int64.repr x) t))
        in *.
      Exists (upd_Znth (ia + i) xs' (Int64.unsigned d)) (if b then 1 else 0).
      rewrite upd_vwords by lia.
      entailer!.
      repeat split.
      * destruct b; lia.
      * destruct b; lia.
      * rewrite upd_Znth_Zlength; lia.
      * apply Forall_word_upd; auto.
      * intros q Hq.
        rewrite upd_Znth_diff' by lia.
        apply Hout; lia.
      * pose proof (valZ_step (-1) xs xs' ia ib i c (if b then 1 else 0)
          (Int64.unsigned d)) as Hst.
        unfold wbits in *; lia.
      * destruct b; reflexivity.
  - Intros xs' c.
    Exists xs'; entailer!.
    apply (valZ_mod _ _ c); auto.
    + apply Forall_sublist; auto.
    + rewrite Zlength_sublist; lia.
Qed.
