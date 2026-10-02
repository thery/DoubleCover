(** * tstep: one step of the table

    The function [tstep] of [htr3.c]: the array holds [k] coefficients of
    [l] words each, and [tstep] replaces coefficient [t] by coefficient [t]
    plus coefficient [t+1] modulo [baseZ l], for [t = 0 .. k-2], the last
    one unchanged.  It calls [add], used through its statement. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Spec_add.

(** One step of the table on the values: [d_t + d_(t+1)], the last one
    unchanged (as in [code/APaul/rocq/HtrDefs.v]). *)
Fixpoint tstepZ (ds : list Z) : list Z :=
  match ds with
  | a :: (b :: _) as r => (a + b) :: tstepZ r
  | _ => ds
  end.

(** The value of coefficient [i]: the words [i l .. i l + l - 1]. *)
Definition coefZ (xs : list Z) (l i : Z) : Z :=
  valZ (sublist (i * l) (i * l + l) xs).

(** The values of the coefficients [0 .. k-1]. *)
Definition coefsZ (xs : list Z) (l k : Z) : list Z :=
  map (coefZ xs l) (upto (Z.to_nat k)).

Definition tstep_spec : ident * funspec :=
 DECLARE _tstep
 WITH sh : share, p : val, xs : list Z, k : Z, l : Z
 PRE [ tptr tulong, tulong, tulong ]
   PROP (writable_share sh; Forall word xs;
         1 <= k; 1 <= l; k * l <= Zlength xs)
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

Definition Gprog : funspecs := [add_spec; tstep_spec].

(** ** tstepZ, element by element *)

Lemma Zlength_tstepZ ds : Zlength (tstepZ ds) = Zlength ds.
Proof.
  induction ds as [|a r IH]; [reflexivity|].
  destruct r as [|b r]; [reflexivity|].
  change (tstepZ (a :: b :: r)) with ((a + b) :: tstepZ (b :: r)).
  rewrite !Zlength_cons, IH, Zlength_cons; reflexivity.
Qed.

(** Element [i] below the last one is [d_i + d_(i+1)]. *)
Lemma Znth_tstepZ ds i : 0 <= i -> i + 1 < Zlength ds ->
  Znth i (tstepZ ds) = Znth i ds + Znth (i + 1) ds.
Proof.
  revert i; induction ds as [|a r IH]; intros i Hi Hl.
  - rewrite Zlength_nil in Hl; lia.
  - destruct r as [|b r].
    + rewrite Zlength_cons, Zlength_nil in Hl; lia.
    + change (tstepZ (a :: b :: r)) with ((a + b) :: tstepZ (b :: r)).
      rewrite Zlength_cons in Hl.
      destruct (Z.eq_dec i 0) as [->|Hi0].
      * rewrite !Znth_0_cons; simpl.
        rewrite Znth_pos_cons by lia.
        rewrite Znth_0_cons; reflexivity.
      * rewrite !Znth_pos_cons by lia.
        rewrite IH by lia.
        rewrite (Znth_pos_cons (i + 1)) by lia.
        replace (i + 1 - 1) with (i - 1 + 1) by lia; reflexivity.
Qed.

(** The last element is unchanged. *)
Lemma Znth_tstepZ_last ds : 0 < Zlength ds ->
  Znth (Zlength ds - 1) (tstepZ ds) = Znth (Zlength ds - 1) ds.
Proof.
  induction ds as [|a r IH]; intros Hl.
  - rewrite Zlength_nil in Hl; lia.
  - destruct r as [|b r]; [reflexivity|].
    change (tstepZ (a :: b :: r)) with ((a + b) :: tstepZ (b :: r)).
    pose proof (Zlength_nonneg r).
    rewrite !Zlength_cons in *.
    rewrite !Znth_pos_cons by lia.
    replace (Z.succ (Z.succ (Zlength r)) - 1 - 1)
      with (Z.succ (Zlength r) - 1) by lia.
    apply IH; lia.
Qed.

(** ** Coefficients *)

(** Two arrays that agree on [a .. b-1] have the same words there. *)
Lemma sublist_ext a b (xs ys : list Z) : 0 <= a <= b ->
  b <= Zlength xs -> b <= Zlength ys ->
  (forall q, a <= q < b -> Znth q xs = Znth q ys) ->
  sublist a b xs = sublist a b ys.
Proof.
  intros Hab Hx Hy Hq.
  apply Znth_eq_ext; [rewrite !Zlength_sublist; lia|].
  intros i Hi; rewrite Zlength_sublist in Hi by lia.
  rewrite !Znth_sublist by lia; apply Hq; lia.
Qed.

(** After [t] calls: coefficients [0 .. t-1] are the new ones and the words
    from [t l] on are the old ones. *)
Definition tstep_inv (xs xs' : list Z) (l t : Z) : Prop :=
  (forall i, 0 <= i < t ->
     coefZ xs' l i = (coefZ xs l i + coefZ xs l (i + 1)) mod baseZ l) /\
  (forall q, t * l <= q -> Znth q xs' = Znth q xs).

(** One call of [add] at [t l] and [(t+1) l] keeps the invariant. *)
Lemma tstep_inv_step xs xs' xs'' l t : 1 <= l -> 0 <= t ->
  (t + 2) * l <= Zlength xs ->
  Zlength xs' = Zlength xs -> Zlength xs'' = Zlength xs ->
  tstep_inv xs xs' l t ->
  valZ (sublist (t * l) (t * l + l) xs'') =
    (valZ (sublist (t * l) (t * l + l) xs') +
     valZ (sublist ((t + 1) * l) ((t + 1) * l + l) xs')) mod baseZ l ->
  (forall q, q < t * l \/ t * l + l <= q -> Znth q xs'' = Znth q xs') ->
  tstep_inv xs xs'' l (t + 1).
Proof.
  intros Hl Ht Hk H1 H2 [Hdone Hout] Hv Hrest; split.
  - intros i Hi.
    destruct (Z.eq_dec i t) as [->|Hit].
    + unfold coefZ; rewrite Hv.
      rewrite (sublist_ext (t * l) _ xs' xs) by (try lia; intros q Hq;
        apply Hout; lia).
      rewrite (sublist_ext ((t + 1) * l) _ xs' xs) by (try nia; intros q Hq;
        apply Hout; nia).
      reflexivity.
    + rewrite <- Hdone by lia; unfold coefZ.
      f_equal; apply sublist_ext; try nia.
      intros q Hq; apply Hrest; nia.
  - intros q Hq; rewrite Hrest by nia; apply Hout; nia.
Qed.

(** At [t = k - 1], the coefficients are [tstepZ] of the old ones modulo
    [baseZ l]. *)
Lemma tstep_inv_final xs xs' l k : 1 <= l -> 1 <= k ->
  k * l <= Zlength xs -> Zlength xs' = Zlength xs -> Forall word xs ->
  tstep_inv xs xs' l (k - 1) ->
  coefsZ xs' l k = map (fun z => z mod baseZ l) (tstepZ (coefsZ xs l k)).
Proof.
  intros Hl Hk Hkl Hlen Hw [Hdone Hout].
  assert (Lc : forall ys, Zlength (coefsZ ys l k) = k).
  { intros; unfold coefsZ; rewrite Zlength_map, Zlength_upto; lia. }
  assert (Nc : forall ys i, 0 <= i < k ->
    Znth i (coefsZ ys l k) = coefZ ys l i).
  { intros ys i Hi; unfold coefsZ.
    rewrite Znth_map by (rewrite Zlength_upto; lia).
    rewrite Znth_upto by lia; reflexivity. }
  apply Znth_eq_ext.
  { rewrite Zlength_map, Zlength_tstepZ, !Lc; reflexivity. }
  intros i Hi; rewrite Lc in Hi.
  rewrite Znth_map by (rewrite Zlength_tstepZ, Lc; lia).
  rewrite Nc by lia.
  destruct (Z.eq_dec i (k - 1)) as [->|Hik].
  - pose proof (Znth_tstepZ_last (coefsZ xs l k)) as E.
    rewrite Lc in E; rewrite E, Nc by lia.
    unfold coefZ.
    rewrite (sublist_ext ((k - 1) * l) _ xs' xs) by (try nia; intros q Hq;
      apply Hout; lia).
    symmetry; apply Z.mod_small.
    pose proof (valZ_bound (sublist ((k - 1) * l) ((k - 1) * l + l) xs)
      (Forall_sublist _ _ _ _ Hw)) as B.
    rewrite Zlength_sublist in B by nia.
    replace ((k - 1) * l + l - (k - 1) * l) with l in B by lia; exact B.
  - rewrite Znth_tstepZ by (try rewrite Lc; lia).
    rewrite !Nc by lia.
    apply Hdone; lia.
Qed.

Lemma body_tstep : semax_body Vprog Gprog f_tstep tstep_spec.
Proof.
  start_function.
  assert_PROP (Zlength xs <= Int64.max_unsigned).
  { entailer!.
    match goal with H : field_compatible _ _ _ |- _ =>
      destruct H as (Hp & _ & Hsz & _) end.
    destruct p; try contradiction.
    simpl in Hsz; rewrite Z.max_r in Hsz by lia.
    pose proof (Ptrofs.unsigned_range i).
    change Ptrofs.modulus with Int64.modulus in Hsz.
    unfold Int64.max_unsigned; lia. }
  (* k and l are words: k l is at most the length of the array. *)
  assert (Hk : k <= Int64.max_unsigned) by nia.
  assert (Hl : l <= Int64.max_unsigned) by nia.
  (* Before the test: t calls done.  After the call: t + 1 calls done. *)
  forward_loop
    (EX t : Z, EX xs' : list Z,
     PROP (0 <= t <= k - 1; Zlength xs' = Zlength xs; Forall word xs';
           tstep_inv xs xs' l t)
     LOCAL (temp _t (Vlong (Int64.repr t)); temp _B p;
            temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p))
  continue:
    (EX t : Z, EX xs' : list Z,
     PROP (0 <= t < k - 1; Zlength xs' = Zlength xs; Forall word xs';
           tstep_inv xs xs' l (t + 1))
     LOCAL (temp _t (Vlong (Int64.repr t)); temp _B p;
            temp _k (Vlong (Int64.repr k)); temp _l (Vlong (Int64.repr l)))
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p))
  break:
    (EX xs' : list Z,
     PROP (Zlength xs' = Zlength xs; Forall word xs';
           tstep_inv xs xs' l (k - 1))
     LOCAL ()
     SEP (data_at sh (tarray tulong (Zlength xs)) (vwords xs') p)).
  - forward; Exists 0 xs; entailer!.
    split; intros; [lia | reflexivity].
  - Intros t xs'.
    forward_if.
    + match goal with H : context [Int64.add] |- _ =>
        rewrite add64_repr, !Int64.unsigned_repr in H by rep_lia end.
      replace_SEP 0 (data_at sh (tarray tulong (Zlength xs')) (vwords xs') p)
        by (rewrite H5; entailer!).
      forward_call (sh, p, xs', t * l, (t + 1) * l, l).
      { repeat split; nia. }
      Intros xs''.
      rewrite H5.
      Exists t xs''; entailer!.
      apply (tstep_inv_step xs xs' xs''); auto; nia.
    + match goal with H : context [Int64.add] |- _ =>
        rewrite add64_repr, !Int64.unsigned_repr in H by rep_lia end.
      forward.
      Exists xs'; entailer!.
      replace (k - 1) with t by lia; auto.
  - Intros t xs'.
    forward.
    Exists (t + 1) xs'; entailer!.
  - (* The loop is the end of the function: its exit is the postcondition. *)
    Intros xs'.
    unfold abbreviate in POSTCONDITION; subst POSTCONDITION; simpl RA_normal.
    unfold stackframe_of; simpl fn_vars; simpl map.
    simpl fold_right.
    go_lowerx.
    Exists xs'; entailer!.
    destruct H6 as [Hdone Hout]; split.
    + apply (tstep_inv_final xs xs' l k); auto; split; auto.
    + intros q Hq; apply Hout; nia.
Qed.

Print Assumptions body_tstep.
