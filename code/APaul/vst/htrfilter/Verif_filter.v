(** * search_filter: the search of one line, then the filter

    The proof of [search_filter_spec] ([Spec_filter.v]).  [search] and
    [maybe_hard_bits] are used through their statements. *)

Require Import VST.floyd.proofauto.
Require Import HF.htr_filter_clight HF.FCommon HF.Spec_filter.
Require HtrVst.Words HtrVst.Fdiff HtrVst.Common HtrVst.Spec_search.
Require HtrVst.Verif_search E.Common E.Spec.
Require Exp100.ExpModel.

Local Notation vwords := HtrVst.Common.vwords.
Local Notation word := HtrVst.Words.word.
Local Notation coefs := HtrVst.Fdiff.coefs.
Local Notation cands := HtrVst.Spec_search.cands.
Local Notation consts := E.Common.consts.

(** ** The list kept after [i] candidates *)

Lemma firstn_S_snoc {A} (xs : list A) i d : (i < length xs)%nat ->
  firstn (S i) xs = firstn i xs ++ [nth i xs d].
Proof.
  revert xs; induction i as [|i IH]; intros [|a xs] H; cbn in *;
    try lia; try reflexivity.
  f_equal; apply IH; lia.
Qed.

(** Among the first [i] of the candidates [cs1] written in [out], those
    kept. *)
Definition kept_upto (neg xb0 : Z) (cs1 : list nat) (i : Z) : list nat :=
  filter (keep neg xb0) (firstn (Z.to_nat i) cs1).

Lemma kept_upto_le neg xb0 cs1 i : 0 <= i ->
  Zlength (kept_upto neg xb0 cs1 i) <= i.
Proof.
  intros Hi; unfold kept_upto; rewrite Zlength_correct.
  pose proof (filter_length_le (keep neg xb0) (firstn (Z.to_nat i) cs1)).
  rewrite length_firstn in H; lia.
Qed.

Lemma kept_upto_succ neg xb0 cs1 i : 0 <= i < Zlength cs1 ->
  kept_upto neg xb0 cs1 (i + 1) =
  kept_upto neg xb0 cs1 i ++
    (if keep neg xb0 (nth (Z.to_nat i) cs1 O)
     then [nth (Z.to_nat i) cs1 O] else []).
Proof.
  intros Hi; unfold kept_upto.
  rewrite Zlength_correct in Hi.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  rewrite (firstn_S_snoc cs1 (Z.to_nat i) O) by lia.
  rewrite filter_app; cbn [filter].
  destruct (keep neg xb0 _); reflexivity.
Qed.

(** The first [cap] candidates. *)
Lemma Zlength_firstn_cap (cs : list nat) cap : 0 <= cap ->
  Zlength (firstn (Z.to_nat cap) cs) = Z.min (Zlength cs) cap.
Proof.
  intros Hc; rewrite !Zlength_correct, length_firstn; lia.
Qed.

(** The entry [i >= kept] of [out] is still the candidate [i]. *)
Lemma out_read (os1 : list val) (cs1 fl : list nat) (cap i : Z) :
  Zlength os1 = cap -> Zlength cs1 <= cap ->
  sublist 0 (Zlength cs1) os1 = vwords (map Z.of_nat cs1) ->
  Zlength fl <= i < Zlength cs1 ->
  @Znth val Vundef i
    (vwords (map Z.of_nat fl) ++ sublist (Zlength fl) cap os1) =
  Vlong (Int64.repr (Z.of_nat (nth (Z.to_nat i) cs1 O))).
Proof.
  intros Ho Hc Hs Hi.
  pose proof (Zlength_nonneg fl).
  rewrite Znth_app2 by (rewrite HtrVst.Common.Zlength_vwords, Zlength_map; lia).
  rewrite HtrVst.Common.Zlength_vwords, Zlength_map.
  rewrite Znth_sublist by lia.
  replace (i - Zlength fl + Zlength fl) with i by lia.
  rewrite <- (Z.add_0_r i) at 1.
  rewrite <- (Znth_sublist 0 i (Zlength cs1) os1) by lia.
  rewrite Hs, HtrVst.Common.Znth_vwords by (rewrite Zlength_map; lia).
  rewrite Znth_map by lia.
  rewrite <- nth_Znth by lia; reflexivity.
Qed.

(** Writing the kept [x] at index [kept]. *)
Lemma out_keep (os1 : list val) (fl : list nat) (cap : Z) (x : nat) :
  Zlength os1 = cap -> Zlength fl < cap ->
  upd_Znth (Zlength fl) (vwords (map Z.of_nat fl) ++
                           sublist (Zlength fl) cap os1)
    (Vlong (Int64.repr (Z.of_nat x))) =
  vwords (map Z.of_nat (fl ++ [x])) ++ sublist (Zlength (fl ++ [x])) cap os1.
Proof.
  intros Ho Hc.
  pose proof (Zlength_nonneg fl).
  rewrite upd_Znth_app2
    by (rewrite HtrVst.Common.Zlength_vwords, Zlength_map, Zlength_sublist; lia).
  rewrite HtrVst.Common.Zlength_vwords, Zlength_map, Z.sub_diag.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite (sublist_split (Zlength fl) (Zlength fl + 1) cap) by lia.
  rewrite (sublist_len_1 (Zlength fl)) by lia.
  rewrite upd_Znth_app1 by (rewrite Zlength_cons, Zlength_nil; lia).
  unfold vwords; rewrite !map_app, <- app_assoc; reflexivity.
Qed.

(** The prefix [a] of [a ++ b]. *)
Lemma sublist_prefix (a b : list val) : sublist 0 (Zlength a) (a ++ b) = a.
Proof.
  pose proof (Zlength_nonneg a).
  rewrite sublist_app1 by lia; apply sublist_same; lia.
Qed.

Lemma sublist_prefix_nat (fl : list nat) (b : list val) :
  sublist 0 (Zlength fl) (vwords (map Z.of_nat fl) ++ b) =
  vwords (map Z.of_nat fl).
Proof.
  rewrite <- (Zlength_map _ _ Z.of_nat fl),
    <- (HtrVst.Common.Zlength_vwords (map Z.of_nat fl)).
  apply sublist_prefix.
Qed.

(** The bits computed by the C: [xb0 + j] or [xb0 - j] on 64 bits. *)
Lemma xbj_add xb0 j : Int64.repr (xbj 0 xb0 j) = Int64.repr (xb0 + j).
Proof.
  unfold xbj; cbn [Z.eqb]; change (2 ^ 64) with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned; reflexivity.
Qed.

Lemma xbj_sub neg xb0 j : neg <> 0 ->
  Int64.repr (xbj neg xb0 j) = Int64.repr (xb0 - j).
Proof.
  intros Hn; unfold xbj; rewrite (proj2 (Z.eqb_neq neg 0) Hn).
  change (2 ^ 64) with Int64.modulus.
  rewrite <- Int64.unsigned_repr_eq, Int64.repr_unsigned; reflexivity.
Qed.

Lemma xbj_range neg xb0 j : 0 <= xbj neg xb0 j <= Int64.max_unsigned.
Proof.
  unfold xbj; pose proof (Z.mod_pos_bound
    (if Z.eqb neg 0 then xb0 + j else xb0 - j) (2 ^ 64) ltac:(lia)).
  rep_lia.
Qed.

(* entailer! must not look inside the tables *)
Local Opaque consts.

Lemma body_search_filter :
  semax_body Vprog Gprog f_search_filter search_filter_spec.
Proof.
  start_function.
  (* search, whose statement is made with htr3's compspecs *)
  rewrite <- !data_at_htr_exp.
  forward_call (sh, p, xs, k, l, n, err, sho, q, os, cap).
  Intros vret; destruct vret as [xs1 os1]; simpl fst in *; simpl snd in *.
  set (cs := cands l err (coefs xs l k) (Z.to_nat n)) in *.
  assert (Hcn : Zlength cs <= n).
  { unfold cs; rewrite Zlength_correct.
    pose proof (HtrVst.Verif_search.cands_length l err (coefs xs l k)
                  (Z.to_nat n)); lia. }
  forward.
  (* c = min(count, cap) *)
  forward_if (PROP ()
    LOCAL (temp _c (Vlong (Int64.repr (Z.min (Zlength cs) cap)));
           temp _count (Vlong (Int64.repr (Zlength cs)));
           gvars gv; temp _B p; temp _out q; temp _cap (Vlong (Int64.repr cap));
           temp _xb0 (Vlong (Int64.repr xb0)); temp _neg (Vint (Int.repr neg)))
    SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs1) p;
         data_at sho (tarray tulong cap) os1 q; consts gv)).
  - forward. entailer!. rewrite Z.min_r by lia. reflexivity.
  - forward. entailer!. rewrite Z.min_l by lia. reflexivity.
  - set (cs1 := firstn (Z.to_nat cap) cs) in *.
    assert (Hc1 : Zlength cs1 = Z.min (Zlength cs) cap)
      by (apply Zlength_firstn_cap; lia).
    rewrite <- Hc1 in *.
    forward.
    (* the filter: after i candidates, kept_upto i at the start of out *)
    forward_for_simple_bound (Zlength cs1)
     (EX i : Z,
      PROP ()
      LOCAL (temp _kept
               (Vlong (Int64.repr (Zlength (kept_upto neg xb0 cs1 i))));
             temp _c (Vlong (Int64.repr (Zlength cs1)));
             gvars gv; temp _out q;
             temp _xb0 (Vlong (Int64.repr xb0)); temp _neg (Vint (Int.repr neg)))
      SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs1) p;
           data_at sho (tarray tulong cap)
             (vwords (map Z.of_nat (kept_upto neg xb0 cs1 i)) ++
              sublist (Zlength (kept_upto neg xb0 cs1 i)) cap os1) q;
           consts gv)).
    + unfold kept_upto; cbn [firstn filter map Zlength].
      rewrite Zlength_nil, sublist_same by lia. entailer!.
    + set (kl := kept_upto neg xb0 cs1 i) in *.
      assert (Hkl : Zlength kl <= i) by (apply kept_upto_le; lia).
      assert (Hcap : Zlength cs1 <= cap) by lia.
      set (x := nth (Z.to_nat i) cs1 O).
      assert (Hxn : Z.of_nat x < n).
      { assert (Hin : In x cs).
        { assert (Hin1 : In x cs1)
            by (apply nth_In; rewrite Zlength_correct in H14; lia).
          unfold cs1 in Hin1; rewrite <- (firstn_skipn (Z.to_nat cap) cs).
          apply in_or_app; left; exact Hin1. }
        unfold cs, HtrVst.Spec_search.cands in Hin.
        apply filter_In in Hin; destruct Hin as [Hin _].
        apply in_seq in Hin; lia. }
      forward.
      { entailer!.
        rewrite (out_read os1 cs1 kl (Zlength os) i) by (auto; lia).
        exact I. }
      rewrite (out_read os1 cs1 kl cap i) by (auto; lia).
      fold x.
      (* the bits of the input j *)
      forward_if (PROP ()
        LOCAL (temp _xb (Vlong (Int64.repr (xbj neg xb0 (Z.of_nat x))));
               temp _j (Vlong (Int64.repr (Z.of_nat x)));
               temp _i (Vlong (Int64.repr i));
               temp _kept (Vlong (Int64.repr (Zlength kl)));
               temp _c (Vlong (Int64.repr (Zlength cs1))); gvars gv;
               temp _out q; temp _xb0 (Vlong (Int64.repr xb0));
               temp _neg (Vint (Int.repr neg)))
        SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs1) p;
             data_at sho (tarray tulong cap)
               (vwords (map Z.of_nat kl) ++ sublist (Zlength kl) cap os1) q;
             consts gv)).
      * forward. entailer!. rewrite xbj_sub by auto. reflexivity.
      * assert (Hn0 : neg = 0).
        { apply (f_equal Int.signed) in H15.
          rewrite Int.signed_repr in H15 by rep_lia. exact H15. }
        subst neg.
        forward. entailer!. rewrite xbj_add. reflexivity.
      * forward_call (gv, xbj neg xb0 (Z.of_nat x)).
        { apply xbj_range. }
        assert (Hsucc := kept_upto_succ neg xb0 cs1 i H14).
        fold x kl in Hsucc.
        assert (Hr : 0 <= Exp100.ExpModel.maybe_hard_Z
                            (xbj neg xb0 (Z.of_nat x)) <= 1).
        { unfold Exp100.ExpModel.maybe_hard_Z.
          destruct (Exp100.ExpModel.core_Z _) as [r|[y hN]]; [lia|].
          unfold Exp100.ExpModel.decide_Z; cbv zeta.
          repeat match goal with |- context [if ?b then _ else _] =>
            destruct b end; lia. }
        (* keep j when maybe_hard_bits answers 1 *)
        forward_if (PROP ()
          LOCAL (temp _i (Vlong (Int64.repr i));
                 temp _kept (Vlong (Int64.repr
                   (Zlength (kept_upto neg xb0 cs1 (i + 1)))));
                 temp _c (Vlong (Int64.repr (Zlength cs1))); gvars gv;
                 temp _out q; temp _xb0 (Vlong (Int64.repr xb0));
                 temp _neg (Vint (Int.repr neg)))
          SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs1) p;
               data_at sho (tarray tulong cap)
                 (vwords (map Z.of_nat (kept_upto neg xb0 cs1 (i + 1))) ++
                  sublist (Zlength (kept_upto neg xb0 cs1 (i + 1))) cap os1)
                 q;
               consts gv)).
        -- assert (Hk : keep neg xb0 x = true)
             by (unfold keep; apply Z.eqb_eq; assumption).
           rewrite Hk in Hsucc.
           forward.
           { entailer!. }
           forward.
           entailer!.
           { rewrite Hsucc, Zlength_app, Zlength_cons, Zlength_nil.
             reflexivity. }
           rewrite Hsucc, (out_keep os1 kl (Zlength os) x) by lia.
           apply derives_refl.
        -- assert (Hk : keep neg xb0 x = false)
             by (unfold keep; apply Z.eqb_neq; assumption).
           rewrite Hk, app_nil_r in Hsucc.
           forward.
           entailer!.
           rewrite Hsucc. apply derives_refl.
    + (* the end: kept and out *)
      assert (Hfl : kept_upto neg xb0 cs1 (Zlength cs1) =
                    kept_list l err xs k n cap neg xb0).
      { unfold kept_upto, kept_list.
        rewrite Zlength_correct, Nat2Z.id, firstn_all. reflexivity. }
      rewrite Hfl.
      forward.
      (* return substitutes cap by Zlength os *)
      set (fl := kept_list l err xs k n (Zlength os) neg xb0) in *.
      Exists xs1
        (vwords (map Z.of_nat fl) ++ sublist (Zlength fl) (Zlength os) os1).
      entailer!.
      apply sublist_prefix_nat.
Qed.

Print Assumptions body_search_filter.
