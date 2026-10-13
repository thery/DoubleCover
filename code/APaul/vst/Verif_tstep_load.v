(** * tstep_load and tstep: one step of the table, each word read once

    The function [tstep_load] of [htr3.c] does what [tstep_add] does
    (Verif_tstep.v): coefficient [t] becomes coefficient [t] plus
    coefficient [t+1] modulo [baseZ l], for [t = 0 .. k-2].  It keeps the
    old coefficient [t] in the local array [a] and loads coefficient [t+1]
    once into [b]; the words of the new coefficient [t] are written by
    [_addcarry_u64], used through its statement [addcarry_spec].  [tstep]
    calls [tstep_load] with [k] and [l] written as constants, or
    [tstep_add] for [l > 10]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Spec_add HtrVst.Verif_tstep.

(** The statement of [tstep_load]: that of [tstep], with [l <= 10], the
    size of [a] and [b]. *)
Definition tstep_load_spec : ident * funspec :=
 DECLARE _tstep_load
 WITH sh : share, p : val, xs : list Z, k : Z, l : Z
 PRE [ tptr tulong, tulong, tulong ]
   PROP (writable_share sh; Forall word xs;
         1 <= k; 1 <= l <= 10; k * l <= Zlength xs)
   PARAMS (p; Vlong (Int64.repr k); Vlong (Int64.repr l))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs) p)
 POST [ tvoid ]
   EX xs' : list Z,
   PROP (Zlength xs' = Zlength xs; Forall word xs';
         coefsZ xs' l k =
           map (fun z => z mod baseZ l) (tstepZ (coefsZ xs l k));
         forall q, k * l <= q -> Znth q xs' = Znth q xs)
   RETURN ()
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p).

Definition Gprog : funspecs :=
  [addcarry_spec; tstep_add_spec; tstep_load_spec; tstep_spec].

(** ** The local arrays: the first [i] words copied, the others as before *)

(** The array [a] or [b] after [i] words of [src] from [off] are copied
    into it, the rest [old]. *)
Definition copied (src : list Z) (off i : Z) (old : list val) : list val :=
  vwords (sublist off (off + i) src) ++ sublist i 10 old.

Lemma Zlength_copied src off i old :
  0 <= off -> 0 <= i <= 10 -> off + i <= Zlength src -> Zlength old = 10 ->
  Zlength (copied src off i old) = 10.
Proof.
  intros; unfold copied.
  rewrite Zlength_app, Zlength_vwords, !Zlength_sublist by lia; lia.
Qed.

(** Nothing copied: the array as before. *)
Lemma copied_0 src off old : Zlength old = 10 -> copied src off 0 old = old.
Proof.
  intros Hl; unfold copied.
  rewrite Z.add_0_r, sublist_nil, sublist_same by lia; reflexivity.
Qed.

(** One more word copied. *)
Lemma copied_step src off i old :
  0 <= off -> 0 <= i < 10 -> off + i < Zlength src -> Zlength old = 10 ->
  upd_Znth i (copied src off i old) (Vlong (Int64.repr (Znth (off + i) src))) =
  copied src off (i + 1) old.
Proof.
  intros Ho Hi Hs Hl; unfold copied, vwords.
  replace (off + (i + 1)) with (off + i + 1) by lia.
  rewrite (sublist_split off (off + i) (off + i + 1) src) by lia.
  rewrite (sublist_len_1 (off + i) src) by lia.
  rewrite !map_app; simpl map.
  rewrite upd_Znth_app2 by (rewrite !Zlength_map, Zlength_sublist by lia;
                            rewrite Zlength_sublist by lia; lia).
  rewrite !Zlength_map, Zlength_sublist by lia.
  replace (i - (off + i - off)) with 0 by lia.
  rewrite (sublist_split i (i + 1) 10 old) by lia.
  rewrite (sublist_len_1 i) by lia.
  simpl app; rewrite upd_Znth0.
  rewrite <- app_assoc; reflexivity.
Qed.

(** Reading word [i < n] of an array whose first [n] words are copied. *)
Lemma Znth_copied src off n old i :
  0 <= off -> 0 <= i < n -> n <= 10 -> off + n <= Zlength src ->
  Zlength old = 10 ->
  Znth i (copied src off n old) = Vlong (Int64.repr (Znth (off + i) src)).
Proof.
  intros; unfold copied.
  rewrite Znth_app1 by (rewrite Zlength_vwords, Zlength_sublist; lia).
  rewrite Znth_vwords by (rewrite Zlength_sublist; lia).
  rewrite Znth_sublist by lia; f_equal; f_equal; f_equal; lia.
Qed.

(** ** tstep_load *)

Lemma body_tstep_load : semax_body Vprog Gprog f_tstep_load tstep_load_spec.
Proof.
  start_function.
  assert_PROP (Zlength xs <= Int64.max_unsigned).
  { entailer!.
    match goal with H : field_compatible _ _ p |- _ =>
      destruct H as (Hp & _ & Hsz & _) end.
    destruct p; try contradiction.
    simpl in Hsz; rewrite Z.max_r in Hsz by lia.
    pose proof (Ptrofs.unsigned_range i).
    change Ptrofs.modulus with Int64.modulus in Hsz.
    unfold Int64.max_unsigned; lia. }
  assert (Hk : k <= Int64.max_unsigned) by nia.
  assert (Hlm : l <= Int64.max_unsigned) by nia.
  set (u := Zrepeat Vundef 10).
  assert (Lu : Zlength u = 10) by reflexivity.
  (* a = the words 0 .. l-1 of B, coefficient 0 *)
  forward_for_simple_bound l
    (EX i : Z,
     PROP ()
     LOCAL (lvar _b (tarray tulong 10) v_b; lvar _a (tarray tulong 10) v_a;
            temp _B p; temp _k (Vlong (Int64.repr k));
            temp _l (Vlong (Int64.repr l)))
     SEP (data_at_ Tsh (tarray tulong 10) v_b;
          data_at Tsh (tarray tulong 10) (copied xs 0 i u) v_a;
          data_at sh (tarray tulong (Zlength xs)) (vwords xs) p)).
  - entailer!.
  - assert (i < Zlength xs) by nia.
    forward.
    { entailer!. rewrite Znth_vwords by lia. exact I. }
    rewrite Znth_vwords by lia.
    forward.
    entailer!.
    replace i with (0 + i) at 2 by lia.
    rewrite copied_step by lia.
    apply derives_refl.
  - (* the main loop: before the test, t steps done; a holds the old
       coefficient t; after the body, t + 1 steps done *)
    forward_loop
      (EX t : Z, EX xs' : list Z, EX ra : list val, EX vb : list val,
       PROP (0 <= t <= k - 1; Zlength xs' = Zlength xs; Forall word xs';
             tstep_inv xs xs' l t; Zlength ra = 10; Zlength vb = 10)
       LOCAL (temp _t (Vlong (Int64.repr t));
              lvar _b (tarray tulong 10) v_b; lvar _a (tarray tulong 10) v_a;
              temp _B p; temp _k (Vlong (Int64.repr k));
              temp _l (Vlong (Int64.repr l)))
       SEP (data_at Tsh (tarray tulong 10) vb v_b;
            data_at Tsh (tarray tulong 10) (copied xs (t * l) l ra) v_a;
            data_at sh (tarray tulong (Zlength xs)) (vwords xs') p))
    continue:
      (EX t : Z, EX xs' : list Z, EX ra : list val, EX vb : list val,
       PROP (0 <= t < k - 1; Zlength xs' = Zlength xs; Forall word xs';
             tstep_inv xs xs' l (t + 1); Zlength ra = 10; Zlength vb = 10)
       LOCAL (temp _t (Vlong (Int64.repr t));
              lvar _b (tarray tulong 10) v_b; lvar _a (tarray tulong 10) v_a;
              temp _B p; temp _k (Vlong (Int64.repr k));
              temp _l (Vlong (Int64.repr l)))
       SEP (data_at Tsh (tarray tulong 10) vb v_b;
            data_at Tsh (tarray tulong 10) (copied xs ((t + 1) * l) l ra) v_a;
            data_at sh (tarray tulong (Zlength xs)) (vwords xs') p))
    break:
      (EX xs' : list Z, EX ra : list val, EX vb : list val,
       PROP (Zlength xs' = Zlength xs; Forall word xs';
             tstep_inv xs xs' l (k - 1); Zlength ra = 10; Zlength vb = 10)
       LOCAL (lvar _b (tarray tulong 10) v_b; lvar _a (tarray tulong 10) v_a)
       SEP (data_at Tsh (tarray tulong 10) vb v_b;
            data_at Tsh (tarray tulong 10) ra v_a;
            data_at sh (tarray tulong (Zlength xs)) (vwords xs') p)).
    + forward.
      Exists 0 xs u u.
      entailer!.
      split; intros; [lia | reflexivity].
    + Intros t xs' ra vb.
      forward_if.
      * match goal with H : context [Int64.add] |- _ =>
          rewrite add64_repr, !Int64.unsigned_repr in H by rep_lia end.
        (* b = the words of coefficient t + 1 *)
        forward_for_simple_bound l
          (EX i : Z,
           PROP ()
           LOCAL (temp _t (Vlong (Int64.repr t));
                  lvar _b (tarray tulong 10) v_b; lvar _a (tarray tulong 10) v_a;
                  temp _B p; temp _k (Vlong (Int64.repr k));
                  temp _l (Vlong (Int64.repr l)))
           SEP (data_at Tsh (tarray tulong 10) (copied xs' ((t + 1) * l) i vb) v_b;
                data_at Tsh (tarray tulong 10) (copied xs (t * l) l ra) v_a;
                data_at sh (tarray tulong (Zlength xs)) (vwords xs') p)).
        -- entailer!.
           rewrite copied_0 by auto; apply derives_refl.
        -- assert ((t + 1) * l + i < Zlength xs) by nia.
           forward.
           { entailer!. rewrite Znth_vwords by lia. exact I. }
           rewrite Znth_vwords by lia.
           forward.
           entailer!.
           rewrite copied_step by lia.
           apply derives_refl.
        -- (* the words of the new coefficient t, with _addcarry_u64 *)
           forward.
           set (ia := t * l). set (ib := (t + 1) * l).
           assert (Eia : ia = t * l) by reflexivity.
           assert (Eib : ib = ia + l) by (unfold ib, ia; lia).
           assert (Hbl : ib + l <= Zlength xs) by nia.
           match goal with H : tstep_inv _ _ _ _ |- _ =>
             pose proof H as [Hdone Hold] end.
           forward_for_simple_bound l
             (EX i : Z, EX ys : list Z, EX c : Z,
              PROP (0 <= c <= 1; Zlength ys = Zlength xs; Forall word ys;
                    forall q, q < ia \/ ia + i <= q -> Znth q ys = Znth q xs';
                    (valZ (sublist ia (ia + i) ys) + c * baseZ i =
                      valZ (sublist ia (ia + i) xs') +
                      valZ (sublist ib (ib + i) xs'))%Z)
              LOCAL (temp _cy (Vint (Int.repr c));
                     temp _t (Vlong (Int64.repr t));
                     lvar _b (tarray tulong 10) v_b;
                     lvar _a (tarray tulong 10) v_a;
                     temp _B p; temp _k (Vlong (Int64.repr k));
                     temp _l (Vlong (Int64.repr l)))
              SEP (data_at Tsh (tarray tulong 10) (copied xs' ib l vb) v_b;
                   data_at Tsh (tarray tulong 10) (copied xs ia l ra) v_a;
                   data_at sh (tarray tulong (Zlength xs)) (vwords ys) p)).
           ++ Exists xs' 0.
              entailer!.
              rewrite !sublist_nil; reflexivity.
           ++ Intros.
              match goal with H : 0 <= c <= 1 |- _ => rename H into Hc end.
              match goal with H : Zlength ys = Zlength xs |- _ => rename H into Hlen end.
              match goal with H : Forall word ys |- _ => rename H into Hw end.
              match goal with H : forall q, q < ia \/ _ -> Znth q ys = _ |- _ =>
                rename H into Hout end.
              match goal with H : valZ (sublist ia _ ys) + _ = _ |- _ =>
                rename H into Hval end.
              assert (Hlen' : Zlength xs' = Zlength xs) by assumption.
              set (x := Znth (ia + i) xs').
              set (y := Znth (ib + i) xs').
              assert (Ex : Znth (ia + i) ys = x) by (apply Hout; lia).
              assert (Exa : Znth (ia + i) xs = x)
                by (unfold x; symmetry; apply Hold; lia).
              assert (Wx : word x) by (apply Forall_Znth; auto; lia).
              assert (Wy : word y) by (apply Forall_Znth; auto; lia).
              forward.
              { entailer!. rewrite Znth_copied by lia. exact I. }
              rewrite Znth_copied, Exa by lia.
              forward.
              { entailer!. rewrite Znth_copied by lia. exact I. }
              rewrite Znth_copied by lia.
              fold y.
              (* the word ia + i, alone, for the call *)
              set (n := Zlength xs) in *.
              set (vs := vwords ys).
              assert (Lvs : Zlength vs = n) by (unfold vs; rewrite Zlength_vwords; lia).
              assert_PROP (field_compatible (tarray tulong n) [] p) as FC
                by (unfold vs; entailer!).
              assert (NA : naturally_aligned tulong) by (simpl; auto).
              assert (B1 : 0 <= ia + i <= ia + i + 1) by lia.
              assert (B2 : ia + i + 1 <= n <= Zlength vs) by lia.
              assert (E0 : vs = sublist 0 n vs)
                by (rewrite sublist_same by lia; reflexivity).
              rewrite (split3_data_at_Tarray sh tulong n (ia + i) (ia + i + 1) vs vs
                         (sublist 0 (ia + i) vs) (sublist (ia + i) (ia + i + 1) vs)
                         (sublist (ia + i + 1) n vs) p NA B1 B2 E0
                         eq_refl eq_refl eq_refl).
              replace (ia + i + 1 - (ia + i)) with 1 by lia.
              rewrite sublist_len_1 by lia.
              erewrite (data_at_singleton_array_eq sh tulong (Znth (ia + i) vs))
                by reflexivity.
              set (a0 := field_address0 (Tarray tulong n noattr) (SUB (ia + i)) p).
              set (a1 := field_address0 (Tarray tulong n noattr) (SUB (ia + i + 1)) p).
              forward_call (c, x, y, sh, a0).
              { entailer!.
                unfold a0.
                match goal with |- context [field_address0 (Tarray tulong ?N noattr) _ _] =>
                  change (Tarray tulong N noattr) with (tarray tulong N) end.
                rewrite arr_field_address0 by (auto; nia).
                simpl.
                rewrite zero_ext_inrange
                  by (rewrite Int.unsigned_repr by rep_lia; simpl; lia).
                reflexivity. }
              { sep_apply (data_at_data_at_ sh tulong (Znth (ia + i) vs) a0); cancel. }
              forward.
              (* the array again, with the new word at ia + i *)
              set (w := Int64.repr (x + y + c)).
              set (ys1 := upd_Znth (ia + i) ys (Int64.unsigned w)).
              assert (Vs1 : vwords ys1 = upd_Znth (ia + i) vs (Vlong w))
                by (unfold ys1, vs; rewrite upd_vwords by lia; reflexivity).
              assert (L1 : Zlength (upd_Znth (ia + i) vs (Vlong w)) = n)
                by (rewrite upd_Znth_Zlength; lia).
              assert (B3 : ia + i + 1 <= n <=
                           Zlength (upd_Znth (ia + i) vs (Vlong w))) by lia.
              assert (E1 : upd_Znth (ia + i) vs (Vlong w) =
                           sublist 0 n (upd_Znth (ia + i) vs (Vlong w)))
                by (rewrite sublist_same by lia; reflexivity).
              assert (JOIN :
                (data_at sh (Tarray tulong (ia + i) noattr) (sublist 0 (ia + i) vs) p *
                 data_at sh tulong (Vlong w) a0 *
                 data_at sh (Tarray tulong (n - (ia + i + 1)) noattr)
                   (sublist (ia + i + 1) n vs) a1)%logic =
                data_at sh (tarray tulong n) (vwords ys1) p).
              { rewrite Vs1; unfold tarray.
                rewrite (split3_data_at_Tarray sh tulong n (ia + i) (ia + i + 1)
                           _ _ _ _ _ p NA B1 B3 E1 eq_refl eq_refl eq_refl).
                replace (ia + i + 1 - (ia + i)) with 1 by lia.
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
              Exists ys1 c'.
              entailer!.
              ** repeat split.
                 --- unfold ys1; rewrite upd_Znth_Zlength; lia.
                 --- unfold ys1; apply Forall_word_upd; auto.
                 --- intros q Hq.
                     unfold ys1; rewrite upd_Znth_diff' by lia.
                     apply Hout; lia.
                 --- pose proof (valZ_step 1 xs' ys (t * l) ((t + 1) * l) i c c'
                                   (Int64.unsigned w)) as Hst.
                     unfold ys1; unfold wbits in *; lia.
              ** rewrite <- JOIN; cancel.
           ++ Intros ys c.
              match goal with H : Zlength ys = Zlength xs |- _ => rename H into Hlen end.
              match goal with H : Forall word ys |- _ => rename H into Hw end.
              match goal with H : forall q, q < ia \/ _ -> Znth q ys = _ |- _ =>
                rename H into Hout end.
              match goal with H : valZ (sublist ia _ ys) + _ = _ |- _ =>
                rename H into Hval end.
              (* the new coefficient t *)
              assert (Hblock : valZ (sublist ia (ia + l) ys) =
                (valZ (sublist ia (ia + l) xs') + valZ (sublist ib (ib + l) xs'))
                  mod baseZ l).
              { apply (valZ_mod _ _ (- c)); auto.
                - apply Forall_sublist; auto.
                - rewrite Zlength_sublist; lia.
                - lia. }
              (* a = b, the old coefficient t + 1 *)
              forward_for_simple_bound l
                (EX i : Z,
                 PROP ()
                 LOCAL (temp _t (Vlong (Int64.repr t));
                        lvar _b (tarray tulong 10) v_b;
                        lvar _a (tarray tulong 10) v_a;
                        temp _B p; temp _k (Vlong (Int64.repr k));
                        temp _l (Vlong (Int64.repr l)))
                 SEP (data_at Tsh (tarray tulong 10) (copied xs' ib l vb) v_b;
                      data_at Tsh (tarray tulong 10)
                        (copied xs' ib i (copied xs ia l ra)) v_a;
                      data_at sh (tarray tulong (Zlength xs)) (vwords ys) p)).
              ** entailer!.
                 rewrite copied_0 by (apply Zlength_copied; nia).
                 apply derives_refl.
              ** forward.
                 { entailer!. rewrite Znth_copied by nia. exact I. }
                 rewrite Znth_copied by nia.
                 forward.
                 entailer!.
                 rewrite copied_step by (try apply Zlength_copied; nia).
                 apply derives_refl.
              ** Exists t ys (copied xs ia l ra) (copied xs' ib l vb).
                 entailer!.
                 --- split.
                     +++ apply (tstep_inv_step xs xs' ys l t); auto; try nia.
                     +++ apply Zlength_copied; nia.
                 --- (* coefficient t + 1 is the same in xs' and xs *)
                     unfold copied.
                     rewrite (sublist_ext ((t + 1) * l) ((t + 1) * l + l) xs' xs)
                       by (try nia; intros q Hq; apply Hold; nia).
                     apply derives_refl.
      * match goal with H : context [Int64.add] |- _ =>
          rewrite add64_repr, !Int64.unsigned_repr in H by rep_lia end.
        forward.
        Exists xs' (copied xs (t * l) l ra) vb.
        entailer!.
        replace (k - 1) with t by lia; auto.
    + Intros t xs' ra vb.
      forward.
      Exists (t + 1) xs' ra vb.
      entailer!.
    + (* the loop is the end of the function: its exit is the postcondition *)
      Intros xs' ra vb.
      unfold abbreviate in POSTCONDITION; subst POSTCONDITION; simpl RA_normal.
      unfold stackframe_of; simpl fn_vars; simpl map.
      simpl fold_right.
      go_lowerx.
      Exists xs'; entailer!.
      * match goal with H : tstep_inv _ _ _ _ |- _ => destruct H as [Hdone Hout] end.
        split.
        -- apply (tstep_inv_final xs xs' l k); auto; try lia; split; auto.
        -- intros q Hq; apply Hout; nia.
      * rewrite !var_block_data_at_ by (first [reflexivity | auto]).
        unfold_lift.
        repeat match goal with H : lvar_denote ?i ?t ?v ?r |- _ =>
          rewrite (lvar_eval_lvar i t v r H); clear H end.
        sep_apply (data_at_data_at_ Tsh (tarray tulong 10) vb v_b).
        sep_apply (data_at_data_at_ Tsh (tarray tulong 10) ra v_a).
        cancel.
Qed.

Print Assumptions body_tstep_load.

(** ** tstep: [kl] is [16 k + l] when [k <= 13] and [l <= 10], else 0; the
    cases are the pairs of the table files, each calls [tstep_load] with its
    [k] and [l]; the default switches on [s], [l] when [l <= 10], else 0:
    [tstep_load] with its [l], or [tstep_add]. *)

Definition klkey (k l : Z) : Z :=
  if andb (k <=? 13) (l <=? 10) then 16 * k + l else 0.

(** A case [16 K + L] of the switch on [kl]: then [k = K] and [l = L], and
    the call of [tstep_load] with the constants [K] and [L] is the call with
    [k] and [l]. *)
Ltac kl_case sh p xs k l K L :=
  match goal with |- semax _ _ ?S _ =>
    let S' := eval simpl in S in change S with S' end;
  match goal with E : _ = klkey _ _ |- _ =>
    assert (k = K /\ l = L) as [Ek El]
      by (unfold klkey in E; destruct (Z.leb_spec k 13), (Z.leb_spec l 10);
          simpl in E; lia) end;
  forward_call (sh, p, xs, k, l); [subst k l; entailer! |];
  let ys := fresh "ys" in Intros ys; forward; Exists ys; entailer!.

Lemma body_tstep : semax_body Vprog Gprog f_tstep tstep_spec.
Proof.
  start_function.
  assert_PROP (Zlength xs <= Int64.max_unsigned).
  { entailer!.
    match goal with H : field_compatible _ _ p |- _ =>
      destruct H as (Hp & _ & Hsz & _) end.
    destruct p; try contradiction.
    simpl in Hsz; rewrite Z.max_r in Hsz by lia.
    pose proof (Ptrofs.unsigned_range i).
    change Ptrofs.modulus with Int64.modulus in Hsz.
    unfold Int64.max_unsigned; lia. }
  assert (Hk : k <= Int64.max_unsigned) by nia.
  assert (Hlm : l <= Int64.max_unsigned) by nia.
  forward_if (temp _t'1 (Vint (Int.repr (Z.b2z (andb (k <=? 13) (l <=? 10)))))).
  - forward.
    entailer!.
    match goal with H : context [Int64.unsigned (Int64.repr 13)] |- _ =>
      rewrite !Int64.unsigned_repr in H by rep_lia end.
    unfold Int64.cmpu, Int64.ltu.
    rewrite !Int64.unsigned_repr by rep_lia.
    destruct (zlt 10 l), (Z.leb_spec k 13), (Z.leb_spec l 10);
      simpl; try reflexivity; lia.
  - forward.
    entailer!.
    match goal with H : context [Int64.unsigned (Int64.repr 13)] |- _ =>
      rewrite !Int64.unsigned_repr in H by rep_lia end.
    destruct (Z.leb_spec k 13); simpl; [lia | reflexivity].
  - forward_if (temp _t'2 (Vint (Int.repr (klkey k l)))).
    + forward.
      entailer!.
      match goal with H : (_ && _)%bool = true |- _ =>
        unfold klkey; rewrite H; reflexivity end.
    + forward.
      entailer!.
      match goal with H : (_ && _)%bool = false |- _ =>
        unfold klkey; rewrite H; reflexivity end.
    + forward.
      assert (Hkey : 0 <= klkey k l <= 218)
        by (unfold klkey; destruct (Z.leb_spec k 13), (Z.leb_spec l 10);
            simpl; lia).
      eapply (semax_switch_PQR (klkey k l)); [reflexivity | entailer! | entailer! |].
      rewrite Int.unsigned_repr by rep_lia.
      match goal with |- semax _ _ ?S _ =>
        let S' := eval cbv [select_switch select_switch_case] in S in
        change S with S' end.
      destruct (zeq 34 (klkey k l)) as [E|?]; [kl_case sh p xs k l 2 2 |].
      destruct (zeq 50 (klkey k l)) as [E|?]; [kl_case sh p xs k l 3 2 |].
      destruct (zeq 67 (klkey k l)) as [E|?]; [kl_case sh p xs k l 4 3 |].
      destruct (zeq 84 (klkey k l)) as [E|?]; [kl_case sh p xs k l 5 4 |].
      destruct (zeq 100 (klkey k l)) as [E|?]; [kl_case sh p xs k l 6 4 |].
      destruct (zeq 117 (klkey k l)) as [E|?]; [kl_case sh p xs k l 7 5 |].
      destruct (zeq 133 (klkey k l)) as [E|?]; [kl_case sh p xs k l 8 5 |].
      destruct (zeq 150 (klkey k l)) as [E|?]; [kl_case sh p xs k l 9 6 |].
      destruct (zeq 167 (klkey k l)) as [E|?]; [kl_case sh p xs k l 10 7 |].
      destruct (zeq 183 (klkey k l)) as [E|?]; [kl_case sh p xs k l 11 7 |].
      destruct (zeq 200 (klkey k l)) as [E|?]; [kl_case sh p xs k l 12 8 |].
      destruct (zeq 216 (klkey k l)) as [E|?]; [kl_case sh p xs k l 13 8 |].
      (* none of the pairs: the switch on s *)
      match goal with |- semax _ _ ?S _ =>
        let S' := eval simpl in S in change S with S' end.
      forward_if (temp _t'3 (Vint (Int.repr (if l <=? 10 then l else 0)))).
      { forward.
        entailer!.
        match goal with H : context [Int64.unsigned (Int64.repr 10)] |- _ =>
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        destruct (Z.leb_spec l 10); [reflexivity | lia]. }
      { forward.
        entailer!.
        match goal with H : context [Int64.unsigned (Int64.repr 10)] |- _ =>
          rewrite !Int64.unsigned_repr in H by rep_lia end.
        destruct (Z.leb_spec l 10); [lia | reflexivity]. }
      forward.
      assert (Hsv : 0 <= (if l <=? 10 then l else 0) <= 10)
        by (destruct (Z.leb_spec l 10); lia).
      remember (if l <=? 10 then l else 0) as sv eqn:Esv.
      repeat apply -> semax_seq_skip.
      apply semax_seq with
        (EX ys : list Z,
         PROP (Zlength ys = Zlength xs; Forall word ys;
               coefsZ ys l k =
                 map (fun z => z mod baseZ l) (tstepZ (coefsZ xs l k));
               forall q, k * l <= q -> Znth q ys = Znth q xs)
         LOCAL ()
         SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p)).
      2: { abbreviate_semax. Intros ys. forward. Exists ys; entailer!. }
      eapply (semax_switch_PQR sv); [reflexivity | entailer! | entailer! |].
      rewrite Int.unsigned_repr by rep_lia.
      assert (sv = 0 \/ sv = 1 \/ sv = 2 \/ sv = 3 \/ sv = 4 \/ sv = 5 \/
              sv = 6 \/ sv = 7 \/ sv = 8 \/ sv = 9 \/ sv = 10) as Hcase by lia.
      destruct Hcase as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]; rewrite E;
        match goal with |- semax _ _ ?S _ =>
          let S' := eval simpl in S in change S with S' end.
      (* sv = 0: l > 10, tstep_add *)
      1: { forward_call (sh, p, xs, k, l).
           Intros ys. forward. Exists ys; entailer!. }
      (* sv = n, 1 <= n <= 10: then l = n *)
      all: assert (l = sv) as El by (destruct (Z.leb_spec l 10); lia);
        rewrite E in El; clear E Esv Hsv.
      all: forward_call (sh, p, xs, k, l); [subst l; entailer! |].
      all: Intros ys; forward; Exists ys; entailer!.
Qed.

Print Assumptions body_tstep.
