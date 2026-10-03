(** * The globals of exp100.c at program start hold the constants

    VST gives [main] the initial globals as [globvars2pred]: one [mapsto]
    per initial word.  This file turns the five globals T, C, LN2, RMAX,
    INV of exp100.c into [consts gv], the form every statement asks. *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common.
Require Exp100.ExpTable.

(** An array of [n] words of 64 bits at an aligned offset fits. *)
Lemma fc_words b k n : 0 <= k -> 0 <= n -> 8 * (k + n) < Ptrofs.modulus ->
  field_compatible (tarray tulong n) nil (Vptr b (Ptrofs.repr (8 * k))).
Proof.
  intros Hk Hn Hm.
  assert (Hr : Ptrofs.unsigned (Ptrofs.repr (8 * k)) = 8 * k)
    by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
  repeat split; auto.
  - unfold size_compatible; simpl sizeof; rewrite Hr, Z.max_r by lia; lia.
  - unfold align_compatible; rewrite Hr.
    apply align_compatible_rec_Tarray; intros i Hi.
    eapply align_compatible_rec_by_value; [reflexivity|].
    simpl; apply Z.divide_add_r; [exists k; lia|exists i; lia].
Qed.

(** The initial words [ws] at word offset [k] hold the array [ws]. *)
Lemma init_words_data_at gv sh b ws k :
  0 <= k -> 8 * (k + Zlength ws) < Ptrofs.modulus ->
  init_data_list2pred gv (init_words ws) sh (Vptr b (Ptrofs.repr (8 * k)))
  |-- data_at sh (tarray tulong (Zlength ws)) (vwords ws)
        (Vptr b (Ptrofs.repr (8 * k))).
Proof.
  revert k; induction ws as [|w ws IH]; intros k Hk Hm.
  - simpl; rewrite data_at_zero_array_eq; auto; exact I.
  - rewrite Zlength_cons in Hm |- *; pose proof (Zlength_nonneg ws).
    change (vwords (w :: ws)) with ([Vlong (Int64.repr w)] ++ vwords ws).
    rewrite (split2_data_at_Tarray_app 1)
      by (rewrite ?Zlength_vwords; reflexivity || lia).
    simpl init_data_list2pred.
    rewrite field_address0_offset
      by (apply arr_field_compatible0; [apply fc_words; lia | lia]).
    simpl offset_val.
    replace (Ptrofs.add (Ptrofs.repr (8 * k)) (Ptrofs.repr (0 + 8 * 1)))
      with (Ptrofs.repr (8 * (k + 1))).
    2:{ rewrite Ptrofs.add_unsigned, !Ptrofs.unsigned_repr
          by (unfold Ptrofs.max_unsigned; lia).
        f_equal; lia. }
    replace (Ptrofs.add (Ptrofs.repr (8 * k)) (Ptrofs.repr 8))
      with (Ptrofs.repr (8 * (k + 1))).
    2:{ rewrite Ptrofs.add_unsigned, !Ptrofs.unsigned_repr
          by (unfold Ptrofs.max_unsigned; lia).
        f_equal; lia. }
    replace (Z.succ (Zlength ws) - 1) with (Zlength ws) by lia.
    apply sepcon_derives.
    + rewrite (data_at_singleton_array_eq sh tulong (Vlong (Int64.repr w)))
        by reflexivity.
      erewrite mapsto_data_at';
        [apply derives_refl|reflexivity|reflexivity| |apply JMeq_refl].
      assert (Hr : Ptrofs.unsigned (Ptrofs.repr (8 * k)) = 8 * k)
        by (apply Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia).
      repeat split; auto.
      * unfold size_compatible; simpl sizeof; rewrite Hr; lia.
      * unfold align_compatible; rewrite Hr.
        eapply align_compatible_rec_by_value; [reflexivity|].
        simpl; exists k; lia.
    + apply IH; lia.
Qed.

(** Initial words at no address hold nothing. *)
Lemma init_words_undef gv sh ws : ws <> [] ->
  init_data_list2pred gv (init_words ws) sh Vundef |-- FF.
Proof.
  destruct ws as [|w ws]; [congruence|]; intros _; simpl.
  rewrite mapsto_isptr; normalize.
Qed.

(** A global holds its initial words, when it is at the start of a block. *)
Definition at_start (p : val) : Prop :=
  p = Vundef \/ exists b, p = Vptr b Ptrofs.zero.

Lemma init_words_num gv sh ws p : at_start p -> ws <> [] ->
  8 * Zlength ws < Ptrofs.modulus ->
  init_data_list2pred gv (init_words ws) sh p
  |-- data_at sh (tarray tulong (Zlength ws)) (vwords ws) p.
Proof.
  intros [->|[b ->]] Hn Hm.
  - eapply derives_trans; [apply init_words_undef; auto|apply FF_left].
  - change Ptrofs.zero with (Ptrofs.repr (8 * 0)).
    apply init_words_data_at; lia.
Qed.

(** The rows of a table, laid out one after the other. *)
Lemma init_rows gv sh rows m p : at_start p -> rows <> [] -> 0 < m ->
  Forall (fun r => Zlength r = m) rows ->
  8 * (Zlength rows * m) < Ptrofs.modulus ->
  init_data_list2pred gv (init_words (concat rows)) sh p
  |-- data_at sh (tarray (tarray tulong m) (Zlength rows)) (map vwords rows) p.
Proof.
  intros Hp Hr Hm Hl Hs.
  assert (Hc : Zlength (concat rows) = Zlength rows * m)
    by (apply Zlength_concat'; auto).
  rewrite data_at_2darray_concat;
    [|rewrite Zlength_map; reflexivity
     |apply Forall_map; eapply Forall_impl; [|exact Hl];
      intros r Hr'; simpl; rewrite Zlength_vwords; exact Hr'
     |reflexivity].
  eapply derives_trans;
    [apply (init_words_num gv sh (concat rows) p); auto; [|lia]|].
  { destruct rows as [|r rows]; [congruence|]; inversion Hl; subst.
    simpl; destruct r; [rewrite Zlength_nil in Hm; lia|simpl; congruence]. }
  rewrite Hc; apply derives_refl'; f_equal.
  unfold vwords; rewrite !concat_map, map_map; reflexivity.
Qed.

(** A global of one word. *)
Lemma init_word gv sh x p : at_start p ->
  init_data_list2pred gv (init_words [x]) sh p
  |-- data_at sh tulong (Vlong (Int64.repr x)) p.
Proof.
  intros Hp; eapply derives_trans;
    [apply (init_words_num gv sh [x] p); auto; [congruence|reflexivity]|].
  rewrite (data_at_singleton_array_eq sh tulong (Vlong (Int64.repr x)))
    by reflexivity.
  apply derives_refl.
Qed.

(** The five globals of exp100.c, as VST gives them to [main], are
    [consts gv], when each global is at the start of its block. *)
Lemma globvars_consts gv : (forall i, at_start (gv i)) ->
  globvars2pred gv [(_T, v_T); (_C, v_C); (_LN2, v_LN2);
                    (_RMAX, v_RMAX); (_INV, v_INV)]
  |-- consts gv.
Proof.
  intros Hg; unfold globvars2pred; cbn [map fold_right].
  unfold globvar2pred; cbn [fst snd].
  change (gvar_volatile v_T) with false; change (gvar_volatile v_C) with false;
  change (gvar_volatile v_LN2) with false;
  change (gvar_volatile v_RMAX) with false;
  change (gvar_volatile v_INV) with false.
  change (gvar_readonly v_T) with true; change (gvar_readonly v_C) with true;
  change (gvar_readonly v_LN2) with true;
  change (gvar_readonly v_RMAX) with true;
  change (gvar_readonly v_INV) with true.
  cbv iota; change (readonly2share true) with Ers.
  rewrite v_T_init, v_C_init, v_LN2_init, v_RMAX_init, v_INV_init.
  unfold consts, num; rewrite sepcon_emp, !sepcon_assoc.
  apply sepcon_derives; [|apply sepcon_derives; [|apply sepcon_derives;
    [|apply sepcon_derives]]].
  - eapply derives_trans; [apply init_rows; auto|apply derives_refl].
    + discriminate.
    + lia.
    + apply Forall_Znth; intros j Hj; apply T_num; exact Hj.
    + reflexivity.
  - eapply derives_trans; [apply init_rows; auto|apply derives_refl].
    + discriminate.
    + lia.
    + apply Forall_Znth; intros j Hj; apply C_num; exact Hj.
    + reflexivity.
  - eapply derives_trans; [apply init_words_num; auto|apply derives_refl].
    + discriminate.
    + reflexivity.
  - eapply derives_trans; [apply init_words_num; auto|apply derives_refl].
    + discriminate.
    + reflexivity.
  - apply init_word; auto.
Qed.
