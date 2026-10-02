(** * difftab: the table of differences

    The function [difftab] of [htr3.c]: on a flat array holding the [k]
    coefficients [B_0 .. B_(k-1)] of [l] words each, for [i = 1 .. k-1] and
    [j = k-1] down to [i], [B_j -= B_(j-1)].  The coefficients become their
    forward differences at 0, modulo [2^(64 l)]. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.Fdiff HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Verif_sub.

Definition difftab_spec : ident * funspec :=
 DECLARE _difftab
 WITH sh : share, p : val, xs : list Z, k : Z, l : Z
 PRE [ tptr tulong, tulong, tulong ]
   PROP (writable_share sh; Forall word xs;
         0 <= k <= Int64.max_unsigned; 0 <= l; k * l <= Zlength xs)
   PARAMS (p; Vlong (Int64.repr k); Vlong (Int64.repr l))
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs) p)
 POST [ tvoid ]
   EX xs' : list Z,
   PROP (Zlength xs' = Zlength xs; Forall word xs';
         coefs xs' l k =
           map (fun j => fdiff (coefs xs l k) j mod baseZ l)
             (seq 0 (Z.to_nat k));
         forall q, k * l <= q -> Znth q xs' = Znth q xs)
   RETURN ()
   SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p).

Definition Gprog : funspecs := [sub_spec; difftab_spec].

Lemma body_difftab : semax_body Vprog Gprog f_difftab difftab_spec.
Proof.
  start_function.
  assert_PROP (Zlength xs <= Int64.max_unsigned).
  { entailer!.
    match goal with Hf : field_compatible _ _ _ |- _ =>
      destruct Hf as (Hp & _ & Hsz & _) end.
    destruct p; try contradiction.
    simpl in Hsz; rewrite Z.max_r in Hsz by lia.
    pose proof (Ptrofs.unsigned_range i).
    change Ptrofs.modulus with Int64.modulus in Hsz.
    unfold Int64.max_unsigned; lia. }
  set (X := fun n : nat => coef xs l (Z.of_nat n)).
  forward_loop
    (EX i : Z, EX ys : list Z,
     PROP (1 <= i <= Z.max 1 k; Zlength ys = Zlength xs; Forall word ys;
           forall q, k * l <= q -> Znth q ys = Znth q xs;
           forall r, 0 <= r < k ->
             coef ys l r = stage X (Z.to_nat (i - 1)) (Z.to_nat r) mod baseZ l)
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _B p;
            temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p))
  continue:
    (EX i : Z, EX ys : list Z,
     PROP (1 <= i < k; Zlength ys = Zlength xs; Forall word ys;
           forall q, k * l <= q -> Znth q ys = Znth q xs;
           forall r, 0 <= r < k ->
             coef ys l r = stage X (Z.to_nat i) (Z.to_nat r) mod baseZ l)
     LOCAL (temp _i (Vlong (Int64.repr i)); temp _B p;
            temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p))
  break:
    (EX ys : list Z,
     PROP (Zlength ys = Zlength xs; Forall word ys;
           forall q, k * l <= q -> Znth q ys = Znth q xs;
           forall r, 0 <= r < k ->
             coef ys l r = stage X (Z.to_nat (k - 1)) (Z.to_nat r) mod baseZ l)
     LOCAL (temp _B p)
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords ys) p)).
  - forward.
    Exists 1 xs.
    entailer!.
    intros r Hr; rewrite stage0; unfold X; rewrite Z2Nat.id by lia.
    rewrite Z.mod_small; auto.
    apply coef_bound; auto; nia.
  - Intros i ys.
    rename H4 into Hi, H5 into Hlen, H6 into Hw, H7 into Htl, H8 into Hc.
    forward_if.
    + assert (Hik : i < k) by assumption.
      forward_loop
        (EX j : Z, EX zs : list Z,
         PROP (i - 1 <= j <= k - 1; Zlength zs = Zlength xs; Forall word zs;
               forall q, k * l <= q -> Znth q zs = Znth q xs;
               forall r, 0 <= r < k ->
                 coef zs l r =
                   (if j <? r then stage X (Z.to_nat i) (Z.to_nat r)
                    else stage X (Z.to_nat (i - 1)) (Z.to_nat r))
                   mod baseZ l)
         LOCAL (temp _j (Vlong (Int64.repr j));
                temp _i (Vlong (Int64.repr i)); temp _B p;
                temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
         SEP (data_at sh (tarray tulong (Zlength xs)) (vwords zs) p))
      continue:
        (EX j : Z, EX zs : list Z,
         PROP (i <= j <= k - 1; Zlength zs = Zlength xs; Forall word zs;
               forall q, k * l <= q -> Znth q zs = Znth q xs;
               forall r, 0 <= r < k ->
                 coef zs l r =
                   (if j - 1 <? r then stage X (Z.to_nat i) (Z.to_nat r)
                    else stage X (Z.to_nat (i - 1)) (Z.to_nat r))
                   mod baseZ l)
         LOCAL (temp _j (Vlong (Int64.repr j));
                temp _i (Vlong (Int64.repr i)); temp _B p;
                temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
         SEP (data_at sh (tarray tulong (Zlength xs)) (vwords zs) p))
      break:
        (EX zs : list Z,
         PROP (Zlength zs = Zlength xs; Forall word zs;
               forall q, k * l <= q -> Znth q zs = Znth q xs;
               forall r, 0 <= r < k ->
                 coef zs l r = stage X (Z.to_nat i) (Z.to_nat r) mod baseZ l)
         LOCAL (temp _i (Vlong (Int64.repr i)); temp _B p;
                temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
         SEP (data_at sh (tarray tulong (Zlength xs)) (vwords zs) p)).
      * forward.
        Exists (k - 1) ys.
        entailer!.
        intros r Hr; rewrite (proj2 (Z.ltb_ge (k - 1) r)) by lia; auto.
      * Intros j zs.
        forward_if.
        -- match goal with E : i - 1 <= j <= k - 1 |- _ => rename E into Hj end.
           match goal with E : i <= j |- _ => rename E into Hij
                         | E : j >= i |- _ => rename E into Hij end.
           match goal with E : Zlength zs = Zlength xs |- _ =>
             rename E into Hzl end.
           match goal with E : Forall word zs |- _ => rename E into Hzw end.
           match goal with E : forall q, k * l <= q -> Znth q zs = _ |- _ =>
             rename E into Hztl end.
           match goal with E : forall r, 0 <= r < k -> coef zs l r = _ |- _ =>
             rename E into Hzc end.
           rewrite <- Hzl.
           forward_call (sh, p, zs, j * l, (j - 1) * l, l).
           { repeat split; nia. }
           Intros zs'.
           match goal with E : Zlength zs' = Zlength zs |- _ =>
             rename E into Hzl' end.
           match goal with E : forall q, _ \/ _ -> Znth q zs' = _ |- _ =>
             rename E into Hout end.
           match goal with E : valZ _ = _ mod baseZ l |- _ =>
             rename E into Hval end.
           Exists j zs'.
           rewrite Hzl.
           entailer!.
           split.
           { intros q Hq; rewrite Hout by nia; apply Hztl; auto. }
           intros r Hr; destruct (Z.eq_dec r j) as [->|Hrj].
           ++ (* B_j -= B_(j-1): one step of pass i *)
              rewrite (proj2 (Z.ltb_lt (j - 1) j)) by lia.
              unfold coef at 1; rewrite Hval.
              change (valZ (sublist (j * l) (j * l + l) zs)) with
                (coef zs l j).
              change (valZ (sublist ((j - 1) * l) ((j - 1) * l + l) zs))
                with (coef zs l (j - 1)).
              rewrite (Hzc j), (Hzc (j - 1)) by lia.
              rewrite (proj2 (Z.ltb_ge j j)), (proj2 (Z.ltb_ge j (j - 1)))
                by lia.
              rewrite <- Zminus_mod.
              replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
              replace (Z.to_nat (j - 1)) with (Z.to_nat j - 1)%nat by lia.
              rewrite stage_step by lia; reflexivity.
           ++ (* the other coefficients are unchanged *)
              rewrite (coef_eq zs zs') by
                (try intros q Hq; try apply Hout; nia).
              rewrite Hzc by lia.
              destruct (Z.ltb_spec (j - 1) r), (Z.ltb_spec j r);
                auto; lia.
        -- (* j = i - 1: pass i is done *)
           forward.
           Exists zs.
           entailer!.
           intros r Hr.
           match goal with E : forall r, 0 <= r < k -> coef zs l r = _ |- _ =>
             rewrite E by lia end.
           destruct (Z.ltb_spec j r); auto.
           replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
           rewrite stage_low by lia; reflexivity.
      * Intros j zs.
        forward.
        Exists (j - 1) zs.
        entailer!.
      * Intros zs.
        Exists i zs.
        entailer!.
    + (* i = k (or k = 0): the last pass is done *)
      forward.
      Exists ys.
      entailer!.
      intros r Hr; replace (k - 1) with (i - 1) by lia; auto.
  - Intros i ys.
    forward.
    Exists (i + 1) ys.
    entailer!.
    replace (i + 1 - 1) with i by lia; auto.
  - Intros ys.
    unfold POSTCONDITION, abbreviate; simpl_ret_assert.
    Exists ys.
    entailer!.
    match goal with E : forall r, 0 <= r < k -> coef ys l r = _ |- _ =>
      rename E into Hend end.
    change (coefs xs l k) with (map X (seq 0 (Z.to_nat k))).
    unfold coefs; apply map_ext_in; intros j Hj; apply in_seq in Hj.
    rewrite Hend by lia.
    rewrite Nat2Z.id, stage_end, fdiff_dif by lia; reflexivity.
Qed.
