(** * search: the search of one line

    The proof of [search_spec] ([Spec_search.v]).  [search] calls
    [difftab] and [tstep], used through their statements. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.Fdiff HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Verif_sub HtrVst.Spec_add HtrVst.Verif_difftab.
Require Import HtrVst.Verif_tstep HtrVst.Spec_search.

Definition Gprog : funspecs :=
  [sub_spec; add_spec; difftab_spec; tstep_spec; search_spec].

(** ** The coefficients *)

(** [upto] is [seq] read as integers. *)
Lemma upto_seq m : upto m = map Z.of_nat (seq 0 m).
Proof.
  induction m as [|m IH]; [reflexivity|].
  cbn [upto seq map]; rewrite IH, <- seq_shift, !map_map.
  f_equal; apply map_ext; intros; lia.
Qed.

(** The coefficients of [Verif_tstep.v] are those of [Fdiff.v]. *)
Lemma coefsZ_coefs xs l k : coefsZ xs l k = coefs xs l k.
Proof.
  unfold coefsZ, coefs; rewrite upto_seq, map_map; reflexivity.
Qed.

Lemma Zlength_coefs xs l k : 0 <= k -> Zlength (coefs xs l k) = k.
Proof.
  intros Hk; rewrite <- coefsZ_coefs; unfold coefsZ.
  rewrite Zlength_map, Zlength_upto; lia.
Qed.

Lemma length_coefs xs l k : length (coefs xs l k) = Z.to_nat k.
Proof. unfold coefs; rewrite length_map, length_seq; reflexivity. Qed.

(** The first coefficient, when there is one. *)
Lemma nth0_coefs xs l k : 1 <= k -> nth 0 (coefs xs l k) 0 = coef xs l 0.
Proof.
  intros Hk; unfold coefs.
  replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia; reflexivity.
Qed.

(** The top word of [B_0] is the word [l - 1] of the array. *)
Lemma top_word xs l : Forall word xs -> 1 <= l -> l <= Zlength xs ->
  coef xs l 0 / 2 ^ (wbits * (l - 1)) = Znth (l - 1) xs.
Proof.
  intros Hw Hl Hlx; unfold coef.
  replace (0 * l) with 0 by lia; replace (0 + l) with (l - 1 + 1) by lia.
  rewrite valZ_sublist_succ by lia.
  pose proof (valZ_bound (sublist 0 (l - 1) xs)
    (Forall_sublist _ _ _ _ Hw)) as Hb.
  rewrite Zlength_sublist, Z.sub_0_r in Hb by lia.
  replace (l - 1 - 0) with (l - 1) by lia.
  unfold baseZ in *.
  rewrite Z.mul_comm, Z.div_add by (apply Z.pow_nonzero; unfold wbits; lia).
  rewrite Z.div_small by lia; lia.
Qed.

(** ** The window *)

(** Adding [e] to the top digit of a number written in base [M]. *)
Lemma add_top_digit X B M u e : 0 <= X < B -> 0 < M ->
  X + B * ((u + e) mod M) = (X + B * u + e * B) mod (B * M).
Proof.
  intros HX HM.
  pose proof (Z.div_mod (u + e) M ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (u + e) M HM) as Hr.
  apply (Z.mod_unique_pos _ _ ((u + e) / M)); [nia|].
  replace (X + B * u + e * B) with (X + B * (u + e)) by ring.
  rewrite Hd at 1; ring.
Qed.

(** After [difftab] and the window, the array holds table 0 modulo
    [beta^l]. *)
Lemma window_coefs xs1 ds l k err : Forall word xs1 ->
  1 <= l -> 1 <= k -> k * l <= Zlength xs1 ->
  coefs xs1 l k = map (fun j => fdiff ds j mod baseZ l) (seq 0 (Z.to_nat k)) ->
  coefs (upd_Znth (l - 1) xs1 ((Znth (l - 1) xs1 + err) mod 2 ^ wbits)) l k
  = map (fun z => z mod baseZ l)
      (window l err (map (fdiff ds) (seq 0 (Z.to_nat k)))).
Proof.
  intros Hw Hl Hk Hkl.
  set (xs2 := upd_Znth _ _ _).
  unfold coefs.
  replace (Z.to_nat k) with (S (Z.to_nat (k - 1))) by lia.
  cbn [seq map window].
  intros E; injection E as H0 Ht.
  f_equal.
  - (* B_0: the top word gets err *)
    assert (Hlx : l <= Zlength xs1) by nia.
    assert (Hs : forall ys, l <= Zlength ys -> coef ys l 0 =
      valZ (sublist 0 (l - 1) ys) + baseZ (l - 1) * Znth (l - 1) ys).
    { intros ys Hy; unfold coef.
      replace (0 * l) with 0 by lia; replace (0 + l) with (l - 1 + 1) by lia.
      rewrite valZ_sublist_succ by lia.
      replace (l - 1 - 0) with (l - 1) by lia; reflexivity. }
    change (Z.of_nat 0) with 0.
    rewrite <- Zplus_mod_idemp_l, <- H0.
    assert (Hl2 : l <= Zlength xs2)
      by (unfold xs2; rewrite upd_Znth_Zlength; lia).
    rewrite (Hs xs2 Hl2), (Hs xs1 Hlx).
    unfold xs2; rewrite sublist_upd_Znth_l, upd_Znth_same by lia.
    pose proof (valZ_bound (sublist 0 (l - 1) xs1)
      (Forall_sublist _ _ _ _ Hw)) as Hb.
    rewrite Zlength_sublist, Z.sub_0_r in Hb by lia.
    assert (Eb : baseZ l = baseZ (l - 1) * 2 ^ wbits)
      by (rewrite <- baseZ_succ by lia; f_equal; lia).
    rewrite Eb.
    replace (2 ^ (wbits * (l - 1))) with (baseZ (l - 1)) by reflexivity.
    apply add_top_digit; [exact Hb | unfold wbits; lia].
  - (* the other coefficients are left as they are *)
    rewrite map_map, <- Ht.
    apply map_ext_in; intros i Hi; apply in_seq in Hi.
    apply coef_eq; try nia.
    + unfold xs2; rewrite upd_Znth_Zlength; nia.
    + intros q Hq; unfold xs2; rewrite upd_Znth_diff by nia; reflexivity.
Qed.

(** ** One step of the table *)

(** Reducing modulo [b] before a step of the table changes nothing modulo
    [b]. *)
Lemma tstepZ_mod b ds :
  map (fun z => z mod b) (tstepZ (map (fun z => z mod b) ds)) =
  map (fun z => z mod b) (tstepZ ds).
Proof.
  induction ds as [|a ds IH]; [reflexivity|].
  destruct ds as [|c r]; [cbn; rewrite Zmod_mod; reflexivity|].
  change (tstepZ (a :: c :: r)) with ((a + c) :: tstepZ (c :: r)).
  change (map (fun z => z mod b) (a :: c :: r)) with
    (a mod b :: map (fun z => z mod b) (c :: r)).
  change (tstepZ (a mod b :: map (fun z => z mod b) (c :: r))) with
    ((a mod b + c mod b) :: tstepZ (map (fun z => z mod b) (c :: r))).
  transitivity ((a mod b + c mod b) mod b ::
    map (fun z => z mod b) (tstepZ (map (fun z => z mod b) (c :: r))));
    [reflexivity|].
  rewrite IH, <- Zplus_mod; reflexivity.
Qed.

(** One call of [tstep]: the array goes from table [j] to table [j + 1]. *)
Lemma table_step xs' xs'' l k err ds j :
  coefs xs' l k = map (fun z => z mod baseZ l) (table l err ds j) ->
  coefs xs'' l k =
    map (fun z => z mod baseZ l) (tstepZ (coefs xs' l k)) ->
  coefs xs'' l k = map (fun z => z mod baseZ l) (table l err ds (S j)).
Proof.
  intros H1 H2; rewrite H2, H1, tstepZ_mod; reflexivity.
Qed.

(** The test of the loop is [cand]: the word [l - 1] against [2 err]. *)
Lemma cand_word xs l k err ds j : Forall word xs ->
  1 <= l -> 1 <= k -> k * l <= Zlength xs ->
  coefs xs l k = map (fun z => z mod baseZ l) (table l err ds j) ->
  cand l err ds j = (Znth (l - 1) xs <=? 2 * err).
Proof.
  intros Hw Hl Hk Hkl HV; unfold cand, top.
  assert (E : nth 0 (table l err ds j) 0 mod baseZ l = coef xs l 0).
  { rewrite <- nth0_coefs with (k := k) by lia; rewrite HV.
    destruct (table l err ds j); [reflexivity|reflexivity]. }
  rewrite E, (top_word xs l Hw Hl) by nia; reflexivity.
Qed.

(** ** The candidates *)

(** One more [j]: [j] is added when it is a candidate. *)
Lemma cands_S l err ds j :
  cands l err ds (S j) =
  cands l err ds j ++ (if cand l err ds j then [j] else []).
Proof.
  unfold cands; rewrite seq_S, filter_app; cbn [filter Nat.add].
  destruct (cand l err ds j); reflexivity.
Qed.

(** There are at most [j] candidates below [j]. *)
Lemma cands_length l err ds j : (length (cands l err ds j) <= j)%nat.
Proof.
  unfold cands; pose proof (filter_length_le (cand l err ds) (seq 0 j)).
  rewrite length_seq in H; exact H.
Qed.

(** The first [cap] candidates, as integers. *)
Lemma firstn_cands (cs : list nat) cap : 0 <= cap ->
  map Z.of_nat (firstn (Z.to_nat cap) cs) =
  sublist 0 (Z.min (Zlength cs) cap) (map Z.of_nat cs).
Proof.
  intros Hc; rewrite sublist_firstn, firstn_map; f_equal.
  rewrite Zlength_correct.
  destruct (Z.le_ge_cases (Z.of_nat (length cs)) cap).
  - rewrite Z.min_l, Nat2Z.id by lia.
    rewrite !firstn_all2 by lia; reflexivity.
  - rewrite Z.min_r by lia; reflexivity.
Qed.

(** The candidates below [j], as integers: [count] and [out] hold them. *)
Definition candsZ l err ds (j : Z) : list Z :=
  map Z.of_nat (cands l err ds (Z.to_nat j)).

Lemma candsZ_succ l err ds j : 0 <= j ->
  candsZ l err ds (j + 1) =
  candsZ l err ds j ++ (if cand l err ds (Z.to_nat j) then [j] else []).
Proof.
  intros Hj; unfold candsZ.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  rewrite cands_S, map_app; f_equal.
  destruct (cand l err ds (Z.to_nat j)); [|reflexivity].
  cbn; rewrite Z2Nat.id by lia; reflexivity.
Qed.

Lemma candsZ_length l err ds j : 0 <= j -> Zlength (candsZ l err ds j) <= j.
Proof.
  intros Hj; unfold candsZ; rewrite Zlength_map, Zlength_correct.
  pose proof (cands_length l err ds (Z.to_nat j)); lia.
Qed.

(** A candidate [x] is written at index [count], while [count < cap]. *)
Lemma out_write os (cs : list Z) cap x :
  Zlength cs < cap -> Zlength os = cap ->
  sublist 0 (Z.min (Zlength cs) cap) os =
    vwords (sublist 0 (Z.min (Zlength cs) cap) cs) ->
  sublist 0 (Z.min (Zlength (cs ++ [x])) cap)
    (upd_Znth (Zlength cs) os (Vlong (Int64.repr x))) =
  vwords (sublist 0 (Z.min (Zlength (cs ++ [x])) cap) (cs ++ [x])).
Proof.
  intros Hc Ho H.
  pose proof (Zlength_nonneg cs).
  assert (Ha : Zlength (cs ++ [x]) = Zlength cs + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  rewrite Z.min_l in H by lia.
  rewrite (sublist_same 0 (Zlength cs) cs) in H by lia.
  rewrite Ha, Z.min_l by lia.
  rewrite (sublist_same 0 (Zlength cs + 1) (cs ++ [x])) by lia.
  rewrite (sublist_split 0 (Zlength cs) (Zlength cs + 1))
    by (rewrite ?upd_Znth_Zlength; lia).
  rewrite sublist_upd_Znth_l, H by lia.
  rewrite sublist_len_1 by (rewrite upd_Znth_Zlength; lia).
  rewrite upd_Znth_same by lia.
  unfold vwords; rewrite !map_app; reflexivity.
Qed.

(** Once [count >= cap], [out] is left as it is. *)
Lemma out_full os (cs : list Z) cap x : 0 <= cap <= Zlength cs ->
  sublist 0 (Z.min (Zlength cs) cap) os =
    vwords (sublist 0 (Z.min (Zlength cs) cap) cs) ->
  sublist 0 (Z.min (Zlength (cs ++ [x])) cap) os =
  vwords (sublist 0 (Z.min (Zlength (cs ++ [x])) cap) (cs ++ [x])).
Proof.
  intros Hc H.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  rewrite Z.min_r in * by lia.
  rewrite sublist_app1 by lia; exact H.
Qed.

(** ** The proof *)

Lemma body_search : semax_body Vprog Gprog f_search search_spec.
Proof.
  start_function.
  assert_PROP (Zlength xs <= Int64.max_unsigned).
  { entailer!.
    match goal with Hf : field_compatible _ _ p
      |- _ => destruct Hf as (Hp & _ & Hsz & _) end.
    destruct p; try contradiction.
    simpl in Hsz; rewrite Z.max_r in Hsz by lia.
    pose proof (Ptrofs.unsigned_range i).
    change Ptrofs.modulus with Int64.modulus in Hsz.
    unfold Int64.max_unsigned; lia. }
  assert (Hk : k <= Int64.max_unsigned) by nia.
  assert (Hl : l <= Int64.max_unsigned) by nia.
  forward.
  forward_call (sh, p, xs, k, l).
  Intros xs1.
  match goal with E : Zlength xs1 = Zlength xs |- _ => rename E into Hl1 end.
  match goal with E : Forall word xs1 |- _ => rename E into Hw1 end.
  match goal with E : coefs xs1 l k = _ |- _ => rename E into Hd1 end.
  assert (Hlx : l <= Zlength xs1) by nia.
  forward.
  { entailer!; rewrite Znth_vwords by lia; exact I. }
  rewrite Znth_vwords by lia.
  forward.
  rewrite upd_vwords by lia.
  set (xs2 := upd_Znth (l - 1) xs1 _).
  set (ds := coefs xs l k).
  assert (Hw2 : Forall word xs2) by (apply Forall_word_upd; auto).
  assert (Hl2 : Zlength xs2 = Zlength xs)
    by (unfold xs2; rewrite upd_Znth_Zlength; lia).
  assert (Hc2 : coefs xs2 l k =
               map (fun z => z mod baseZ l) (table l err ds 0)).
  { unfold table; simpl Nat.iter; unfold ds; rewrite length_coefs.
    unfold xs2; rewrite Int64.add_unsigned, Int64.unsigned_repr_eq.
    assert (Hx : word (Znth (l - 1) xs1)) by (apply Forall_Znth; auto; lia).
    unfold word, wbits in Hx.
    rewrite !Int64.unsigned_repr by rep_lia.
    change Int64.modulus with (2 ^ wbits).
    apply window_coefs; auto; nia. }
  clearbody xs2.
  (* Before the test: j steps done.  After the call of tstep: j + 1. *)
  forward_loop
    (EX j : Z, EX ys : list Z, EX os1 : list val,
     PROP (0 <= j <= n; Zlength ys = Zlength xs; Forall word ys;
           coefs ys l k =
             map (fun z => z mod baseZ l) (table l err ds (Z.to_nat j));
           Zlength os1 = cap;
           sublist 0 (Z.min (Zlength (candsZ l err ds j)) cap) os1 =
             vwords (sublist 0 (Z.min (Zlength (candsZ l err ds j)) cap)
                       (candsZ l err ds j)))
     LOCAL (temp _j (Vlong (Int64.repr j));
            temp _count (Vlong (Int64.repr (Zlength (candsZ l err ds j))));
            temp _B p; temp _k (Vlong (Int64.repr k));
            temp _l (Vlong (Int64.repr l)); temp _n (Vlong (Int64.repr n));
            temp _err (Vlong (Int64.repr err)); temp _out q;
            temp _cap (Vlong (Int64.repr cap)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p;
          data_at sho (tarray tulong cap) os1 q))
  continue:
    (EX j : Z, EX ys : list Z, EX os1 : list val,
     PROP (0 <= j < n; Zlength ys = Zlength xs; Forall word ys;
           coefs ys l k =
             map (fun z => z mod baseZ l) (table l err ds (Z.to_nat (j + 1)));
           Zlength os1 = cap;
           sublist 0 (Z.min (Zlength (candsZ l err ds (j + 1))) cap) os1 =
             vwords (sublist 0 (Z.min (Zlength (candsZ l err ds (j + 1))) cap)
                       (candsZ l err ds (j + 1))))
     LOCAL (temp _j (Vlong (Int64.repr j));
            temp _count
              (Vlong (Int64.repr (Zlength (candsZ l err ds (j + 1)))));
            temp _B p; temp _k (Vlong (Int64.repr k));
            temp _l (Vlong (Int64.repr l)); temp _n (Vlong (Int64.repr n));
            temp _err (Vlong (Int64.repr err)); temp _out q;
            temp _cap (Vlong (Int64.repr cap)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p;
          data_at sho (tarray tulong cap) os1 q))
  break:
    (EX ys : list Z, EX os1 : list val,
     PROP (Zlength ys = Zlength xs; Forall word ys; Zlength os1 = cap;
           sublist 0 (Z.min (Zlength (candsZ l err ds n)) cap) os1 =
             vwords (sublist 0 (Z.min (Zlength (candsZ l err ds n)) cap)
                       (candsZ l err ds n)))
     LOCAL (temp _count (Vlong (Int64.repr (Zlength (candsZ l err ds n)))))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p;
          data_at sho (tarray tulong cap) os1 q)).
  - forward.
    Exists 0 xs2 os.
    entailer!.
    change (candsZ l err ds 0) with (@nil Z).
    rewrite Zlength_nil, Z.min_l by (pose proof (Zlength_nonneg os); lia).
    rewrite !sublist_nil; reflexivity.
  - Intros j ys os1.
    match goal with E : 0 <= j <= n |- _ => rename E into Hj end.
    match goal with E : Zlength ys = Zlength xs |- _ => rename E into Hly end.
    match goal with E : Forall word ys |- _ => rename E into Hwy end.
    match goal with E : coefs ys l k = _ |- _ => rename E into Hcy end.
    match goal with E : Zlength os1 = cap |- _ => rename E into Hlo end.
    match goal with E : sublist 0 _ os1 = _ |- _ => rename E into Hout end.
    forward_if.
    + (* j < n: one step *)
      assert (Hn : j < n) by (try lia; rep_lia).
      forward.
      { entailer!; rewrite Znth_vwords by lia; exact I. }
      rewrite Znth_vwords by lia.
      assert (Hcand := cand_word ys l k err ds (Z.to_nat j) Hwy
                         ltac:(lia) ltac:(lia) ltac:(nia) Hcy).
      assert (Hcl := candsZ_length l err ds j ltac:(lia)).
      assert (Hx : word (Znth (l - 1) ys)) by (apply Forall_Znth; auto; lia).
      unfold word, wbits in Hx.
      assert (Hsucc := candsZ_succ l err ds j ltac:(lia)).
      assert (H2e : Int64.unsigned (Int64.mul (Int64.repr 2) (Int64.repr err))
                    = 2 * err)
        by (rewrite mul64_repr, Int64.unsigned_repr; rep_lia).
      set (c := Zlength (candsZ l err ds j)) in *.
      set (cs := candsZ l err ds j) in *.
      assert (Hc0 : 0 <= c) by (unfold c; apply Zlength_nonneg).
      forward_if
        (EX os2 : list val,
         PROP (Zlength os2 = cap;
               sublist 0 (Z.min (Zlength (candsZ l err ds (j + 1))) cap) os2 =
               vwords (sublist 0
                 (Z.min (Zlength (candsZ l err ds (j + 1))) cap)
                 (candsZ l err ds (j + 1))))
         LOCAL (temp _j (Vlong (Int64.repr j));
                temp _count
                  (Vlong (Int64.repr (Zlength (candsZ l err ds (j + 1)))));
                temp _B p; temp _k (Vlong (Int64.repr k));
                temp _l (Vlong (Int64.repr l));
                temp _n (Vlong (Int64.repr n));
                temp _err (Vlong (Int64.repr err)); temp _out q;
                temp _cap (Vlong (Int64.repr cap)))
         SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p;
              data_at sho (tarray tulong cap) os2 q)).
      * (* j is a candidate *)
        match goal with E : Int64.unsigned (Int64.mul _ _) >= _ |- _ =>
          rewrite H2e, Int64.unsigned_repr in E by rep_lia;
          rename E into Hle end.
        assert (Ht : cand l err ds (Z.to_nat j) = true)
          by (rewrite Hcand; apply Z.leb_le; lia).
        rewrite Ht in Hsucc.
        assert (Hlc : Zlength (candsZ l err ds (j + 1)) = c + 1)
          by (rewrite Hsucc, Zlength_app, Zlength_cons, Zlength_nil; lia).
        forward_if
          (EX os2 : list val,
           PROP (Zlength os2 = cap;
                 sublist 0 (Z.min (Zlength (candsZ l err ds (j + 1))) cap)
                   os2 =
                 vwords (sublist 0
                   (Z.min (Zlength (candsZ l err ds (j + 1))) cap)
                   (candsZ l err ds (j + 1))))
           LOCAL (temp _j (Vlong (Int64.repr j));
                  temp _count (Vlong (Int64.repr c));
                  temp _B p; temp _k (Vlong (Int64.repr k));
                  temp _l (Vlong (Int64.repr l));
                  temp _n (Vlong (Int64.repr n));
                  temp _err (Vlong (Int64.repr err)); temp _out q;
                  temp _cap (Vlong (Int64.repr cap)))
           SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p;
                data_at sho (tarray tulong cap) os2 q)).
        -- (* count < cap: j is written in out *)
           assert (Hcc : c < cap) by lia.
           forward.
           Exists (upd_Znth c os1 (Vlong (Int64.repr j))).
           entailer!.
           rewrite Hsucc; apply out_write; auto.
        -- (* count >= cap: out is full *)
           assert (Hcc : cap <= c) by lia.
           forward.
           Exists os1.
           entailer!.
           rewrite Hsucc; apply out_full; auto; lia.
        -- Intros os2.
           forward.
           Exists os2.
           entailer!.
           rewrite Hlc; reflexivity.
      * (* j is not a candidate *)
        match goal with E : Int64.unsigned (Int64.mul _ _) < _ |- _ =>
          rewrite H2e, Int64.unsigned_repr in E by rep_lia;
          rename E into Hle end.
        assert (Ht : cand l err ds (Z.to_nat j) = false)
          by (rewrite Hcand; apply Z.leb_gt; lia).
        rewrite Ht, app_nil_r in Hsucc.
        forward.
        Exists os1.
        entailer!.
        rewrite Hsucc; auto.
      * (* the step of the table *)
        Intros os2.
        replace_SEP 0 (data_at sh (tarray tulong (Zlength ys)) (vwords ys) p)
          by (rewrite Hly; entailer!).
        forward_call (sh, p, ys, k, l).
        Intros ys'.
        match goal with E : coefsZ ys' l k = _ |- _ =>
          rewrite !coefsZ_coefs in E; rename E into Hcy' end.
        Exists j ys' os2.
        rewrite Hly.
        entailer!.
        replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
        apply (table_step ys ys'); auto.
    + (* j = n: the loop ends *)
      forward.
      Exists ys os1.
      assert (Ejn : j = n) by (try lia; rep_lia).
      subst j.
      entailer!.
  - (* j <- j + 1 *)
    Intros j ys os1.
    forward.
    Exists (j + 1) ys os1.
    entailer!.
  - (* the end: count and out *)
    Intros ys os1.
    forward.
    Exists ys os1.
    entailer!.
    match goal with E : sublist 0 _ os1 = _ |- _ => rename E into Hend end.
    unfold candsZ, ds in *; rewrite Zlength_map in *.
    split; [|reflexivity].
    rewrite <- ZtoNat_Zlength, firstn_cands by apply Zlength_nonneg.
    exact Hend.
Qed.

Print Assumptions body_search.
