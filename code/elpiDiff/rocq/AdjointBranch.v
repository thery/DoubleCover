(* AdjointBranch.v — the adjoint simulation of branches (milestone M2).

   The forward sweep computes a branch with prim: the statements of the branch
   taken, then its value into the storage of the let (psim_body). The reverse
   sweep replays the branch taken (adj Replay) and transposes it, from the
   adjoint of the let: the simulation of the body of the branch (asim_body),
   run in the store of the reverse sweep. Branch bodies bind operations, reads
   of arrays and branches (well_formed: no update, map or fold in a branch). *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect AdjointCorrect.

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   The atoms of a body (the analyses, binders opened with fresh) are the
   variables that occur in it (well_formed, binders opened with anon). *)

Lemma atom_member_id x l : atom_member (AVar x) l = atom_member (AVar (AV (aid x) false)) l.
Proof. reflexivity. Qed.

Lemma atom_member_remove_full x y l :
  atom_member y (atom_remove x l) = negb (same_term x y) && atom_member y l.
Proof.
  unfold atom_member, atom_remove; induction l as [| z l IH]; simpl; [destruct (same_term x y); reflexivity |].
  destruct (same_term x z) eqn:Exz; simpl; rewrite IH.
  - destruct (same_term x y) eqn:Exy; simpl; [reflexivity |].
    destruct (same_term y z) eqn:Eyz; simpl; [| reflexivity].
    exfalso; destruct x, y, z; simpl in *; try discriminate.
    apply Nat.eqb_eq in Exz, Eyz; apply Nat.eqb_neq in Exy; lia.
  - destruct (same_term x y) eqn:Exy, (same_term y z) eqn:Eyz; simpl; try reflexivity.
    exfalso; destruct x, y, z; simpl in *; try discriminate.
    apply Nat.eqb_eq in Exy, Eyz; apply Nat.eqb_neq in Exz; lia.
Qed.

Lemma atom_member_atoms_cons a l y :
  atom_member y (atoms_of_atoms (a :: l)) = atom_member y (atoms_of_atom a) || atom_member y (atoms_of_atoms l).
Proof. simpl; apply atom_member_union. Qed.

Lemma same_fresh j i : j <> i -> same_term (AVar (fresh j)) (AVar (AV i false)) = false.
Proof. intros H; unfold same_term, fresh; cbn [aid]; apply Nat.eqb_neq; exact H. Qed.

Definition dummy_tvar : tvar W := TVar ResultVar Real None false false false false None.

(* A variable opened by both analyses at k. *)
Definition opened (k : nat) : pv := PV (fresh k) (anon k) dummy_tvar (VInt 0%Z) 0.

Lemma atoms_atom G (aP : atom pv) aA aW i :
  atom_eq (gA G) aP aA -> atom_eq (gW G) aP aW -> (forall q, In q G -> aid (pa q) = vid (pw q)) ->
  atom_member (AVar (AV i false)) (atoms_of_atom aA) = occurs_atom i aW.
Proof.
  intros HA HW Hid; apply atom_graph in HA as [-> HA]; apply atom_graph in HW as [-> HW].
  destruct aP as [q | |]; simpl; [| reflexivity | reflexivity].
  rewrite (Hid q (HA q eq_refl)), Nat.eqb_sym, orb_false_r; reflexivity.
Qed.

Lemma atoms_occurs :
  (forall bP : anf pv bare, forall G bA bW k i,
     anf_eq (gA G) bP bA -> anf_eq (gW G) bP bW -> (forall q, In q G -> aid (pa q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (atoms_of_anf k bA) = occurs_anf i k bW) /\
  (forall eP : value pv bare, forall G eA eW k i,
     value_eq (gA G) eP eA -> value_eq (gW G) eP eW -> (forall q, In q G -> aid (pa q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (atoms_of_value k eA) = occurs_value i k eW).
Proof.
  apply anf_value_ind.
  - intros a e IHe b IHb G bA bW k i HA HW Hid Hi.
    destruct bA as [aA eA cA | ], bW as [aW eW cW | ]; simpl in HA, HW; try contradiction.
    destruct HA as [HeA HcA], HW as [HeW HcW]; cbn [atoms_of_anf occurs_anf].
    rewrite atom_member_union, atom_member_remove_full, (IHe G eA eW k i HeA HeW Hid Hi).
    rewrite same_fresh by lia; simpl.
    f_equal; apply (IHb (opened k) (opened k :: G)); [exact (HcA _ _) | exact (HcW _ _) | | lia].
    intros q [<- | Hq]; [reflexivity | exact (Hid q Hq)].
  - intros x G bA bW k i HA HW Hid Hi.
    destruct bA as [ | aA], bW as [ | aW]; simpl in HA, HW; try contradiction.
    exact (atoms_atom G x aA aW i HA HW Hid).
  - intros f x G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [_ HA], HW as [_ HW].
    exact (atoms_atom G x _ _ i HA HW Hid).
  - intros f x y G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [_ [HA1 HA2]], HW as [_ [HW1 HW2]].
    cbn [atoms_of_value occurs_value]; rewrite !atom_member_atoms_cons; simpl atoms_of_atoms.
    rewrite (atoms_atom G x _ _ i HA1 HW1 Hid), (atoms_atom G y _ _ i HA2 HW2 Hid), orb_false_r; reflexivity.
  - intros x j G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [HA1 HA2], HW as [HW1 HW2].
    cbn [atoms_of_value occurs_value]; rewrite !atom_member_atoms_cons; simpl atoms_of_atoms.
    rewrite (atoms_atom G x _ _ i HA1 HW1 Hid), (atoms_atom G j _ _ i HA2 HW2 Hid), orb_false_r; reflexivity.
  - intros x j y G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [HA1 [HA2 HA3]], HW as [HW1 [HW2 HW3]].
    cbn [atoms_of_value occurs_value]; rewrite !atom_member_atoms_cons; simpl atoms_of_atoms.
    rewrite (atoms_atom G x _ _ i HA1 HW1 Hid), (atoms_atom G j _ _ i HA2 HW2 Hid), (atoms_atom G y _ _ i HA3 HW3 Hid).
    rewrite orb_false_r, orb_assoc; reflexivity.
  - intros c t IHt e IHe G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [HA1 [HA2 HA3]], HW as [HW1 [HW2 HW3]].
    cbn [atoms_of_value occurs_value]; rewrite !atom_member_union.
    rewrite (atoms_atom G c _ _ i HA1 HW1 Hid), (IHt G _ _ k i HA2 HW2 Hid Hi), (IHe G _ _ k i HA3 HW3 Hid Hi).
    reflexivity.
  - intros lo hi b IHb G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [HA1 [HA2 HA3]], HW as [HW1 [HW2 HW3]].
    cbn [atoms_of_value occurs_value]; rewrite atom_member_union, !atom_member_atoms_cons; simpl atoms_of_atoms.
    rewrite (atoms_atom G lo _ _ i HA1 HW1 Hid), (atoms_atom G hi _ _ i HA2 HW2 Hid), orb_false_r.
    rewrite atom_member_remove_full, same_fresh by lia; simpl.
    f_equal; apply (IHb (opened k) (opened k :: G)); [exact (HA3 _ _) | exact (HW3 _ _) | | lia].
    intros q [<- | Hq]; [reflexivity | exact (Hid q Hq)].
  - intros a lo hi init b IHb G eA eW k i HA HW Hid Hi.
    destruct eA, eW; simpl in HA, HW; try contradiction.
    destruct HA as [HA1 [HA2 [HA3 HA4]]], HW as [HW1 [HW2 [HW3 HW4]]].
    cbn [atoms_of_value occurs_value]; rewrite atom_member_union, !atom_member_atoms_cons; simpl atoms_of_atoms.
    rewrite (atoms_atom G lo _ _ i HA1 HW1 Hid), (atoms_atom G hi _ _ i HA2 HW2 Hid), (atoms_atom G init _ _ i HA3 HW3 Hid).
    rewrite orb_false_r, !atom_member_remove_full, !same_fresh by lia; simpl.
    rewrite (orb_assoc (occurs_atom i _) (occurs_atom i _)); f_equal; apply (IHb (opened k) (opened (S k)) (opened (S k) :: opened k :: G));
      [exact (HA4 _ _ _ _) | exact (HW4 _ _ _ _) | | lia].
    intros q [<- | [<- | Hq]]; [reflexivity | reflexivity | exact (Hid q Hq)].
Qed.

(* The atoms the partial derivatives read are operands. *)
Lemma read_by1 f (a : atom avar) y :
  atom_member y (read_by a (partial1 f a)) = true -> atom_member y (atoms_of_atom a) = true.
Proof.
  unfold read_by; destruct (partial1 f a) as [p |] eqn:Ep; [| discriminate].
  destruct (varied a); [| discriminate].
  destruct f as [| | | | | | z |]; simpl in Ep; try discriminate; try (destruct z; simpl in Ep);
    injection Ep as <-; simpl; rewrite ?atom_member_union; simpl; rewrite ?orb_false_r; auto; discriminate.
Qed.

Lemma read_by_atom (a b : atom avar) y :
  atom_member y (read_by a (Some (PAtom b))) = true -> atom_member y (atoms_of_atom b) = true.
Proof. unfold read_by; destruct (varied a); simpl; [auto | discriminate]. Qed.

Lemma read_by_div (a b c : atom avar) y :
  atom_member y (read_by c (Some (POp2 Divide (PNum "1") (PAtom b)))) = true \/
  atom_member y (read_by c (Some (POp1 Neg (POp2 Divide (PAtom a) (POp2 Mul (PAtom b) (PAtom b)))))) = true ->
  atom_member y (atoms_of_atom a) = true \/ atom_member y (atoms_of_atom b) = true.
Proof.
  unfold read_by; destruct (varied c); simpl; [| intros [H | H]; discriminate].
  rewrite !atom_member_union; simpl; intros [H | H]; [right; exact H |].
  apply orb_true_iff in H as [H | H]; [left; exact H |].
  rewrite orb_diag in H; right; exact H.
Qed.

Lemma needs_op2 f (a b : atom avar) y :
  atom_member y (fst (match partial2 f a b with
                      | Some (pa, pb) => (atom_union (read_by a (Some pa)) (read_by b (Some pb)), atoms_of_atoms [a; b])
                      | None => ([], atoms_of_atoms [a; b]) end))
  || atom_member y (snd (match partial2 f a b with
                      | Some (pa, pb) => (atom_union (read_by a (Some pa)) (read_by b (Some pb)), atoms_of_atoms [a; b])
                      | None => ([], atoms_of_atoms [a; b]) end)) = true ->
  atom_member y (atoms_of_atom a) || atom_member y (atoms_of_atom b) = true.
Proof.
  assert (Hs : atom_member y (atoms_of_atoms [a; b]) = atom_member y (atoms_of_atom a) || atom_member y (atoms_of_atom b))
    by (simpl; rewrite !atom_member_union; simpl; rewrite ?orb_false_r; reflexivity).
  destruct f; cbn [partial2 fst snd]; rewrite Hs; intros H; apply orb_true_iff in H as [H | H]; auto;
    unfold read_by in H; destruct (varied a), (varied b); simpl atoms_of_pexpr in H;
    rewrite ?atom_member_union in H; simpl in H; rewrite ?atom_member_union in H; simpl in H;
    apply orb_true_iff; repeat (apply orb_true_iff in H as [H | H]); auto; discriminate.
Qed.

Lemma pairing_ext_own O s s' : (forall t m, In (t, m) O -> barv s m = barv s' m) -> pairing O s = pairing O s'.
Proof.
  induction O as [| [t m] O IH]; intros H; simpl; [reflexivity |].
  rewrite (H t m (or_introl eq_refl)), IH; [reflexivity |]; intros t' m' Hi; apply (H t'); right; exact Hi.
Qed.

Section Branch.
Variable cv : bool.

(* What the adjoint code of a body needs occurs in it. *)
Lemma needs_occurs :
  (forall bP : anf pv bare, forall G bA bW m k i,
     anf_eq (gA G) bP bA -> anf_eq (gW G) bP bW -> (forall q, In q G -> aid (pa q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (fst (needs cv m k bA)) || atom_member (AVar (AV i false)) (snd (needs cv m k bA)) = true ->
     occurs_anf i k bW = true) /\
  (forall eP : value pv bare, forall G eA eW k i,
     value_eq (gA G) eP eA -> value_eq (gW G) eP eW -> (forall q, In q G -> aid (pa q) = vid (pw q)) -> (i < k)%nat ->
     atom_member (AVar (AV i false)) (fst (value_needs cv k eA)) || atom_member (AVar (AV i false)) (snd (value_needs cv k eA)) = true ->
     occurs_value i k eW = true).
Proof.
  apply anf_value_ind.
  - intros a e IHe b IHb G bA bW m k i HA HW Hid Hi Hn.
    destruct bA as [aA eA cA | ], bW as [aW eW cW | ]; simpl in HA, HW; try contradiction.
    destruct HA as [HeA HcA], HW as [HeW HcW]; cbn [occurs_anf].
    set (x1 := PV (let_binder k eA) (anon k) dummy_tvar (VInt 0%Z) 0).
    assert (Hid' : forall q, In q (x1 :: G) -> aid (pa q) = vid (pw q)) by (intros q [<- | Hq]; [reflexivity | exact (Hid q Hq)]).
    assert (IHc : atom_member (AVar (AV i false)) (fst (needs cv m (S k) (cA (let_binder k eA)))) ||
                  atom_member (AVar (AV i false)) (snd (needs cv m (S k) (cA (let_binder k eA)))) = true ->
                  occurs_anf i (S k) (cW (anon k)) = true)
      by exact (IHb x1 (x1 :: G) (cA (let_binder k eA)) (cW (anon k)) m (S k) i (HcA x1 _) (HcW x1 _) Hid' ltac:(lia)).
    assert (Hval : atom_member (AVar (AV i false)) (fst (value_needs cv k eA)) ||
                   atom_member (AVar (AV i false)) (snd (value_needs cv k eA)) = true -> occurs_value i k eW = true)
      by exact (IHe G eA eW k i HeA HeW Hid Hi).
    assert (Hat : atom_member (AVar (AV i false)) (atoms_of_value k eA) = occurs_value i k eW)
      by exact ((proj2 atoms_occurs) e G eA eW k i HeA HeW Hid Hi).
    cbn [needs] in Hn; destruct (needs cv m (S k) (cA (let_binder k eA))) as [ub lb] eqn:Eb.
    destruct (varied_value k eA && atom_member (AVar (let_binder k eA)) ub);
      [destruct (value_needs cv k eA) as [rd fl] eqn:Ev |];
      destruct (atom_member (AVar (let_binder k eA)) lb || _);
      cbn [fst snd] in Hn, Hval, IHc |- *;
      rewrite ?atom_member_union, ?atom_member_remove_full in Hn; simpl in Hn;
      apply orb_true_iff; repeat (apply orb_true_iff in Hn as [Hn | Hn]);
      repeat (apply andb_true_iff in Hn as [_ Hn]);
      first [ right; apply IHc; rewrite Hn; try reflexivity; apply orb_true_r
            | left; apply Hval; rewrite Hn; try reflexivity; apply orb_true_r
            | left; rewrite <- Hat; exact Hn
            | discriminate ].
  - intros x G bA bW m k i HA HW Hid Hi Hn.
    destruct bA as [ | aA], bW as [ | aW]; simpl in HA, HW; try contradiction.
    cbn [occurs_anf]; rewrite <- (atoms_atom G x aA aW i HA HW Hid).
    cbn [needs] in Hn; destruct (sweep_eqb m Forward && cv); cbn [fst snd] in Hn;
      [rewrite orb_diag in Hn; exact Hn | rewrite orb_false_r in Hn; exact Hn].
  - intros f x G eA eW k i HA HW Hid Hi Hn.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [<- HA], HW as [_ HW].
    cbn [occurs_value]; rewrite <- (atoms_atom G x _ _ i HA HW Hid).
    cbn [value_needs fst snd] in Hn; apply orb_true_iff in Hn as [Hn | Hn]; [exact (read_by1 _ _ _ Hn) | exact Hn].
  - intros f x y G eA eW k i HA HW Hid Hi Hn.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [<- [HA1 HA2]], HW as [_ [HW1 HW2]].
    cbn [occurs_value]; rewrite <- (atoms_atom G x _ _ i HA1 HW1 Hid), <- (atoms_atom G y _ _ i HA2 HW2 Hid).
    cbn [value_needs] in Hn; destruct (comparison f); [simpl in Hn; discriminate |].
    exact (needs_op2 f _ _ _ Hn).
  - intros x j G eA eW k i HA HW Hid Hi Hn.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [HA1 HA2], HW as [HW1 HW2].
    cbn [occurs_value]; rewrite <- (atoms_atom G x _ _ i HA1 HW1 Hid), <- (atoms_atom G j _ _ i HA2 HW2 Hid).
    cbn [value_needs fst snd] in Hn; apply orb_true_iff in Hn as [Hn | Hn]; apply orb_true_iff; [right | left]; exact Hn.
  - intros x j y G eA eW k i HA HW Hid Hi Hn.
    destruct eA, eW; simpl in HA, HW; try contradiction; destruct HA as [HA1 [HA2 HA3]], HW as [HW1 [HW2 HW3]].
    cbn [occurs_value]; rewrite <- (atoms_atom G x _ _ i HA1 HW1 Hid), <- (atoms_atom G j _ _ i HA2 HW2 Hid),
      <- (atoms_atom G y _ _ i HA3 HW3 Hid).
    cbn [value_needs fst snd] in Hn; simpl atoms_of_atoms in Hn; rewrite ?atom_member_union, ?orb_false_r in Hn.
    repeat (apply orb_true_iff in Hn as [Hn | Hn]); rewrite Hn; rewrite ?orb_true_r; reflexivity.
  - intros c t IHt e IHe G eA eW k i HA HW Hid Hi Hn.
    destruct eA as [| | | | cA0 tA0 eA0 | |], eW as [| | | | cW0 tW0 eW0 | |]; simpl in HA, HW; try contradiction; destruct HA as [HA1 [HA2 HA3]], HW as [HW1 [HW2 HW3]].
    cbn [occurs_value]; rewrite <- (atoms_atom G c _ _ i HA1 HW1 Hid).
    pose proof (IHt G _ _ Replay k i HA2 HW2 Hid Hi) as Ht; pose proof (IHe G _ _ Replay k i HA3 HW3 Hid Hi) as He.
    cbn [value_needs] in Hn; destruct (needs cv Replay k tA0) as [ut lt], (needs cv Replay k eA0) as [ue le].
    cbn [fst snd] in Hn, Ht, He; rewrite !atom_member_union in Hn.
    repeat (apply orb_true_iff in Hn as [Hn | Hn]);
      first [rewrite Hn; reflexivity
            | rewrite Ht by (rewrite Hn; rewrite ?orb_true_r; reflexivity); rewrite ?orb_true_r; reflexivity
            | rewrite He by (rewrite Hn; rewrite ?orb_true_r; reflexivity); rewrite ?orb_true_r; reflexivity].
  - intros lo hi b IHb G eA eW k i HA HW Hid Hi Hn.
    destruct eA as [| | | | | lA hA bA0 |], eW as [| | | | | lW hW bW0 |]; simpl in HA, HW; try contradiction; destruct HA as [HA1 [HA2 HA3]], HW as [HW1 [HW2 HW3]].
    cbn [occurs_value]; rewrite <- (atoms_atom G lo _ _ i HA1 HW1 Hid), <- (atoms_atom G hi _ _ i HA2 HW2 Hid).
    assert (Hid' : forall q, In q (opened k :: G) -> aid (pa q) = vid (pw q)) by (intros q [<- | Hq]; [reflexivity | exact (Hid q Hq)]).
    pose proof (IHb (opened k) (opened k :: G) _ _ Replay (S k) i (HA3 _ _) (HW3 _ _) Hid' ltac:(lia)) as Hb.
    cbn [pa pw opened] in Hb; cbn [value_needs] in Hn; destruct (needs cv Replay (S k) (bA0 (fresh k))) as [u l].
    cbn [fst snd] in Hn, Hb; simpl atoms_of_atoms in Hn.
    rewrite ?atom_member_union, ?atom_member_remove_full, ?orb_false_r in Hn; rewrite same_fresh in Hn by lia; simpl in Hn.
    repeat (apply orb_true_iff in Hn as [Hn | Hn]);
      first [rewrite Hn; rewrite ?orb_true_r; reflexivity
            | rewrite Hb by (rewrite Hn; rewrite ?orb_true_r; reflexivity); rewrite ?orb_true_r; reflexivity].
  - intros a lo hi init b IHb G eA eW k i HA HW Hid Hi Hn.
    destruct eA as [| | | | | | aA0 lA hA init0 b0], eW as [| | | | | | aW0 lW hW initW bW0]; simpl in HA, HW; try contradiction.
    destruct HA as [HA1 [HA2 [HA3 HA4]]], HW as [HW1 [HW2 [HW3 HW4]]].
    cbn [occurs_value]; rewrite <- (atoms_atom G lo _ _ i HA1 HW1 Hid), <- (atoms_atom G hi _ _ i HA2 HW2 Hid),
      <- (atoms_atom G init _ _ i HA3 HW3 Hid).
    set (sv := PV (snd (fold_binders k init0 b0)) (anon (S k)) dummy_tvar (VInt 0%Z) 0).
    assert (Hid' : forall q, In q (sv :: opened k :: G) -> aid (pa q) = vid (pw q))
      by (intros q [<- | [<- | Hq]]; [reflexivity | reflexivity | exact (Hid q Hq)]).
    pose proof (IHb (opened k) sv (sv :: opened k :: G) _ _ Replay (S (S k)) i (HA4 _ _ _ _) (HW4 _ _ _ _) Hid' ltac:(lia)) as Hb.
    cbn [value_needs] in Hn; unfold sv, fold_binders in Hb; unfold fold_binders in Hn; cbn [fst snd pa pw opened] in Hb; unfold fresh in Hb.
    destruct (needs cv Replay (S (S k)) (b0 (AV k false) (AV (S k) (fold_varied k init0 b0)))) as [u l].
    cbn [fst snd] in Hn, Hb; simpl atoms_of_atoms in Hn.
    rewrite ?atom_member_union, ?atom_member_remove_full, ?orb_false_r in Hn.
    assert (E1 : same_term (AVar (AV k false)) (AVar (AV i false)) = false) by exact (same_fresh k i ltac:(lia)).
    assert (E2 : same_term (AVar (AV (S k) (fold_varied k init0 b0))) (AVar (AV i false)) = false)
      by (unfold same_term; cbn [aid]; apply Nat.eqb_neq; lia).
    rewrite ?E1, ?E2 in Hn; simpl in Hn.
    repeat (apply orb_true_iff in Hn as [Hn | Hn]);
      first [rewrite Hn; rewrite ?orb_true_r; reflexivity
            | rewrite Hb by (rewrite Hn; rewrite ?orb_true_r; reflexivity); rewrite ?orb_true_r; reflexivity].
Qed.

Ltac fwd_intro :=
  let L := fresh "L" in let k := fresh "k" in let c := fresh "c" in let s := fresh "s" in
  intros L k c s wP pp tail eA eW eT eD te n ve ty m rec HA HW HT HD Hc Htc Htail [j [Ej Hj]] Hst Hrec Hev;
  destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.

(* The atoms of a value are variables that occur in it. *)
Lemma vatoms_live L k (eP : value pv bare) eA eW p :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L -> In p L ->
  vatoms k eA p -> live_value k eW p.
Proof.
  intros HA HW HL Hp; unfold vatoms, live_value; rewrite atom_member_id.
  destruct (static_in _ _ _ HL Hp) as [Eid [Hk _]].
  rewrite ((proj2 atoms_occurs) eP L eA eW k (aid (pa p)) HA HW); [rewrite Eid; auto | | lia].
  intros q Hq; exact (proj1 (static_in _ _ _ HL Hq)).
Qed.

Lemma live_atoms L k (bP : anf pv bare) bA bW p :
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> Forall (static_ok k) L -> In p L ->
  live_anf k bW p -> atom_member (AVar (pa p)) (atoms_of_anf k bA) = true.
Proof.
  intros HA HW HL Hp; unfold live_anf; rewrite atom_member_id.
  destruct (static_in _ _ _ HL Hp) as [Eid [Hk _]].
  rewrite ((proj1 atoms_occurs) bP L bA bW k (aid (pa p)) HA HW); [rewrite Eid; auto | | lia].
  intros q Hq; exact (proj1 (static_in _ _ _ HL Hq)).
Qed.

(* The forward sweep of a branch body: prim computes every let, then the
   value of the body, from the variables that occur in it. *)
Definition psim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m m' bA bW bT bD ty v,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  actx L k c s wP pp (live_anf k bW) (live_anf k bW) ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  let '((sb, x), c') :=
    open_pairs (prim W (option_map (amap pt) wP) m (rebuild _ bT (annotate_body_t cv m' k bA))) c in
  (c <= c')%nat /\
  exists s1, run sb s = Some s1 /\ fwd_frame c None None s s1 /\ tapes_kept s s1 /\ xev s1 x = Some (primal v).

Lemma prim_let w m a e b :
  prim W w m (ALet a e b) =
  let '(vr, _, _) := let_ann a in
  with_storage w e b (fun n rec =>
    sbind (fwd_value W w m e (Transform.type_of e) n rec) (fun se =>
    sbind (prim W w m (b (open_let (Transform.type_of e) n vr rec))) (fun '(sb, x) => Done (app se sb, x)))).
Proof. reflexivity. Qed.

Lemma psim_ret (aP : atom pv) : psim_body (ARet aP).
Proof.
  intros L k c s wP pp m m' bA bW bT bD ty v HA HW HT HD Hc Htc Hev.
  destruct bA as [| aA], bW as [| aW], bT as [| aT], bD as [| aD]; simpl in HA, HW, HT, HD;
    try contradiction.
  graph HA; graph HW; graph HT; graph HD.
  cbn [annotate_body_t rebuild prim open_pairs].
  split; [lia |]; exists s; split; [reflexivity |].
  split; [intros ? ? ? ? ? ?; reflexivity | split; [apply tapes_kept_refl |]].
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  apply (aspell_ok k s aP); [| exact Hev].
  intros p ->; split; [exact (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (H p eq_refl)) |].
  apply (a_store _ _ _ _ _ _ _ _ _ Hc p (H p eq_refl)); unfold live_anf; simpl; apply Nat.eqb_refl.
Qed.

Lemma psim_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  asim_fwd cv eP -> act_value eP -> (forall wP tail, storage wP tail eP = None) -> (forall x, psim_body (cP x)) ->
  psim_body (ALet a eP cP).
Proof.
  intros IHf IHa Hsn IHb L k c s wP pp m m' bA bW bT bD ty v HA HW HT HD Hc Htc Hev.
  destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |], bD as [aD eD cD |];
    simpl in HA, HW, HT, HD; try contradiction.
  destruct HA as [HeA HcA], HW as [HeW HcW], HT as [HeT HcT], HD as [HeD HcD].
  simpl in Htc, Hev.
  destruct (typecheck_value (option_map (amap pw) wP) (wplace pp) (WellFormed.is_tail cW k) k eW)
    as [te d0] eqn:Hte.
  destruct d0; simpl in Htc; [| discriminate].
  destruct (aeval_value (duals reals) eD) as [ve |] eqn:Hve; [| discriminate].
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  cbn [annotate_body_t].
  destruct (needs cv m' (S k) (cA (let_binder k eA))) as [u l] eqn:Hneeds.
  set (vr := varied_value k eA). set (vt := annotate_value_t cv k eA).
  set (rest := annotate_body_t cv m' (S k) (cA (let_binder k eA))).
  cbn [rebuild]. rewrite prim_let. cbv [let_ann].
  rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
  match goal with |- context [with_storage _ _ _ ?K] => set (Kf := K) end.
  destruct (open_with_storage' L k wP eP eT vt (fun v0 => rebuild _ (cT v0) rest) Kf c HeT HL) as [n [rec [c0 [Hopen Hn]]]].
  { intros a0 E; destruct (s_written _ _ _ _ _ _ _ Hs _ E) as [y [-> [Hy _]]]; eauto. }
  lazymatch goal with |- context [@open_pairs ?A ?t c] =>
    assert (E : @open_pairs A t c = @open_pairs A (Kf n rec) c0) by exact Hopen; rewrite E; clear E end.
  rewrite <- (is_tail_transfer L k cP cW cT rest HcW HcT) in Hn by
    (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]]; auto).
  set (tail := WellFormed.is_tail cW k) in *.
  assert (Htail_ty : tail = true -> te = ty).
  { intros Ht; destruct (tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL eq_refl Ht) as [_ E].
    rewrite E in Htc; simpl in Htc; injection Htc; auto. }
  assert (Es := Hsn wP tail); rewrite Es in Hn; destruct Hn as [-> [-> ->]].
  unfold Kf; rewrite open_pairs_sbind.
  destruct (open_pairs (fwd_value W (option_map (amap pt) wP) m (rebuild_value (tvar W) eT vt) te (DBound (c, c)) false) (S c))
    as [se c1] eqn:Hfe.
  rewrite open_pairs_sbind.
  destruct (open_pairs (prim W (option_map (amap pt) wP) m (rebuild (tvar W) (cT (open_let te (DBound (c, c)) vr false)) rest)) c1)
    as [[sb xb] c2] eqn:Hob.
  cbn [open_pairs].
  assert (Hc01 : (S c <= c1)%nat).
  { pose proof (open_pairs_mono (fwd_value W (option_map (amap pt) wP) m (rebuild_value (tvar W) eT vt) te (DBound (c, c)) false) (S c)) as H0.
    rewrite Hfe in H0; exact H0. }
  pose proof (aids_below L k HL) as Haid.
  assert (Hlv_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p)
    by (intros p H0; unfold live_value, live_anf in *; simpl; rewrite H0; reflexivity).
  destruct (IHa L k wP pp tail eA eW eD te ve HeA HeW HeD HL Hte Hve) as [Hht [Hz Hra]].
  assert (Hnotin : forall p, In p L -> stored p <> DBound (c, c)).
  { intros p Hp E; pose proof (s_num _ _ _ _ _ _ _ Hs p Hp) as H0; unfold stored in E; injection E as E; lia. }
  set (x := PV (let_binder k eA) (VInfo k te None) (open_let te (DBound (c, c)) vr false) ve c).
  assert (Hx : aid (pa x) = k) by reflexivity.
  assert (HxL : ~ In x L) by exact (fresh_notin L k x Haid Hx).
  (* the forward sweep of the value *)
  assert (Hc1 : actx L k (S c) s wP pp (live_value k eW) (vatoms k eA) ty).
  { apply (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); [| lia].
    intros p Hp Hv; exact (Hlv_e p (vatoms_live L k eP eA eW p HeA HeW HL Hp Hv)). }
  assert (Hj1 : exists j, DBound (c, c) = DBound (j, j) /\ (j < S c)%nat) by (exists c; split; [reflexivity | lia]).
  assert (Hst1 : match storage wP tail eP with
                 | Some m0 => DBound (c, c) = m0
                 | None => forall p, In p L -> stored p <> DBound (c, c) end) by (rewrite Es; exact Hnotin).
  assert (Hr1 : false = true -> exists l0, store_get s (keyv (TapeOf (DBound (c, c)))) = Some (VTape l0))
    by discriminate.
  pose proof (IHf L k (S c) s wP pp tail eA eW eT eD te (DBound (c, c)) ve ty m false HeA HeW HeT HeD Hc1 Hte
                Htail_ty Hj1 Hst1 Hr1 Hve) as IH.
  cbv zeta in IH; fold vt in IH; rewrite Hfe in IH.
  destruct IH as [_ [se1 [R1 [F1 [T1 S1]]]]].
  (* the rest of the body, with x in scope *)
  assert (Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p -> live_anf k (ALet aW eW cW) p).
  { unfold live_anf; intros p Hp H; simpl.
    rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx eq_refl) in H.
    rewrite H; apply orb_true_r. }
  assert (Hold : forall p, In p L -> store_get se1 (keyv (stored p)) = store_get s (keyv (stored p))).
  { intros p Hp; apply F1; [unfold stored; simpl; pose proof (s_num _ _ _ _ _ _ _ Hs p Hp); lia | reflexivity | simpl; tauto |
      intros E; apply (Hnotin p Hp); congruence | discriminate]. }
  assert (Hxs : static_ok (S k) x).
  { repeat split; simpl; auto; try lia; discriminate. }
  assert (Hs' : sctx (x :: L) (S k) (S c) wP pp (live_anf (S k) (cW (VInfo k te None))) ty).
  { constructor.
    - constructor; [exact Hxs |]; apply Forall_impl with (P := static_ok k); auto.
      intros p Hp; apply (static_mono k); auto.
    - intros p q [<- | Hp] [<- | Hq] E; auto.
      + specialize (Haid _ Hq); destruct (static_in _ _ _ HL Hq) as [E' _]; simpl in E; lia.
      + specialize (Haid _ Hp); destruct (static_in _ _ _ HL Hp) as [E' _]; simpl in E; lia.
      + exact (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
    - intros p [<- | Hp]; simpl; [lia |].
      pose proof (s_num _ _ _ _ _ _ _ Hs _ Hp); lia.
    - intros a0 E; destruct (s_written _ _ _ _ _ _ _ Hs _ E) as [y [-> [Hy Hv]]].
      exists y; split; [reflexivity | split; [right; exact Hy | exact Hv]].
    - pose proof (s_place _ _ _ _ _ _ _ Hs) as Hp; destruct pp; simpl in *; auto.
      destruct Hp as [A [B C]]; split; [right; exact A | split; [right; exact B | exact C]].
    - intros o p Ho [<- | Hp] Ep.
      + pose proof (s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho)); simpl in Ep; lia.
      + destruct (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Ep) as [H | H]; [left; exact H |].
        right; intros Hl; apply H, Hlive_c; auto.
    - intros p o [<- | Hp] Lp Ha Hg Ho.
      + destruct (inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_intror Ha))
          as [_ [o' [Ho' Es']]].
        rewrite Es in Es'; discriminate.
      + exact (s_arrays _ _ _ _ _ _ _ Hs p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho).
    - exact (s_ty _ _ _ _ _ _ _ Hs).
    - intros y Hpp Hw Ha.
      destruct (s_top _ _ _ _ _ _ _ Hs y Hpp Hw Ha) as [T1' T2'].
      destruct (s_written _ _ _ _ _ _ _ Hs _ Hw) as [y' [E [Hy _]]]; injection E as <-.
      split; [exact T1' | intros Ly; apply T2', Hlive_c; auto]. }
  assert (Hc' : actx (x :: L) (S k) c1 se1 wP pp (live_anf (S k) (cW (VInfo k te None)))
                  (live_anf (S k) (cW (VInfo k te None))) ty).
  { constructor; [exact (sctx_weaken _ _ _ _ _ _ _ _ _ Hs' (fun p H => H) Hc01) | | |].
    - intros p [<- | Hp]; [reflexivity | exact (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp)].
    - intros p [<- | Hp] Hl; [exact S1 |].
      rewrite Hold; [| exact Hp]; apply (a_store _ _ _ _ _ _ _ _ _ Hc p Hp), Hlive_c; auto.
    - intros p [<- | Hp] Hr; [discriminate |].
      destruct (a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr) as [lt Hlt]; exact (T1 _ _ Hlt). }
  pose proof (IHb x (x :: L) (S k) c1 se1 wP pp m m' (cA (pa x)) (cW (pw x)) (cT (pt x)) (cD (pd x)) ty v
                (HcA x _) (HcW x _) (HcT x _) (HcD x _) Hc' Htc Hev) as IH.
  unfold x in IH; cbn [pt pa pd pw] in IH; fold rest in IH.
  lazymatch type of IH with context [@open_pairs ?A ?t c1] =>
    assert (E : @open_pairs A t c1 = (sb, xb, c2)) by exact Hob; rewrite E in IH; clear E end.
  destruct IH as [Hc12 [s1 [Rb [Fb [Tb Vb]]]]].
  lazymatch goal with |- context [@open_pairs ?A ?t c1] =>
    assert (E : @open_pairs A t c1 = (sb, xb, c2)) by exact Hob; rewrite E; clear E end.
  cbn [open_pairs].
  split; [lia |].
  exists s1; split; [rewrite run_app, R1; exact Rb |].
  split.
  { intros v0 Hb0 Hc0 Ht0 _ _.
    rewrite (Fb v0 (below_mono c c1 v0 Hb0 ltac:(lia)) Hc0 Ht0 ltac:(discriminate) ltac:(discriminate)).
    apply F1; [exact (below_mono c (S c) v0 Hb0 ltac:(lia)) | exact Hc0 | exact Ht0 | | discriminate].
    intros E; injection E as <-; simpl in Hb0; lia. }
  split; [exact (tapes_kept_trans _ _ _ T1 Tb) | exact Vb].
Qed.

(* A branch body sits in place PBranch, where nothing is updated in place. *)
Lemma sctx_branch L k c wP pp (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> (forall p, live' p -> live p) -> sctx L k c wP PBranch live' Real.
Proof.
  intros Hs Hl; destruct Hs; constructor; auto; simpl; try (intros; discriminate); try exact I.
Qed.

(* The forward sweep of a branch: the result is a real variable, assigned by
   the branch taken after its statements. *)
Lemma afwd_ite (cP : atom pv) (tP eP : anf pv bare) :
  psim_body tP -> psim_body eP -> asim_fwd cv (AIte cP tP eP).
Proof.
  intros IHt IHe; fwd_intro; simpl in Htc, Hev, Hst |- *.
  rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT, t2 into tD, e2 into eD.
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  (* typing *)
  assert (Hpp : pp = PTop \/ pp = PBranch \/ pp = PScalar)
    by (destruct pp as [| | | ix sx]; auto; simpl in Htc; discriminate).
  assert (Htc' : (if ty_eqb (of_atom (amap pw cP)) Boolean
                  then let '(t3, d1) := typecheck (option_map (amap pw) wP) InBranch k tW in
                       let '(t4, d2) := typecheck (option_map (amap pw) wP) InBranch k eW in
                       if is_ok d1 then if is_ok d2 then if ty_eqb t3 Real && ty_eqb t4 Real
                         then (Real, Ok) else (Real, Error "both branches must compute a real")
                       else (Real, d2) else (Real, d1)
                  else (Real, Error "a branch condition must be a comparison")) = (te, Ok))
    by (destruct Hpp as [-> | [-> | ->]]; exact Htc).
  clear Htc.
  destruct (ty_eqb (of_atom (amap pw cP)) Boolean) eqn:Ecb; [| discriminate].
  destruct (typecheck (option_map (amap pw) wP) InBranch k tW) as [t3 d1] eqn:HtW.
  destruct (typecheck (option_map (amap pw) wP) InBranch k eW) as [t4 d2] eqn:HeW.
  destruct d1, d2; simpl in Htc'; try discriminate.
  destruct (ty_eqb t3 Real) eqn:E3, (ty_eqb t4 Real) eqn:E4; simpl in Htc'; try discriminate.
  injection Htc' as <-; apply ty_eqb_true in E3, E4; subst t3 t4.
  (* the condition *)
  destruct (aeval_atom (duals reals) (amap pd cP)) as [[| | b | |] |] eqn:Hcd; try discriminate.
  assert (Hcs : forall p, cP = AVar p -> static_ok k p /\ store_get s (keyv (stored p)) = Some (primal (pd p))).
  { intros p ->; split; [exact (static_in _ _ _ HL (H p eq_refl)) |].
    apply (a_store _ _ _ _ _ _ _ _ _ Hc p (H p eq_refl)); unfold vatoms; simpl.
    rewrite !atom_member_union; simpl; rewrite Nat.eqb_refl; reflexivity. }
  pose proof (aspell_ok k s cP _ Hcs Hcd) as Hsc; simpl in Hsc.
  (* the two bodies, opened *)
  rewrite open_pairs_sbind.
  destruct (open_pairs (prim W (option_map (amap pt) wP) m (rebuild (tvar W) tT (annotate_body_t cv Replay k tA))) c)
    as [[st vt] c1] eqn:Hot.
  rewrite open_pairs_sbind.
  destruct (open_pairs (prim W (option_map (amap pt) wP) m (rebuild (tvar W) eT (annotate_body_t cv Replay k eA))) c1)
    as [[se' ve'] c2] eqn:Hoe.
  pose proof (open_pairs_mono (prim W (option_map (amap pt) wP) m (rebuild (tvar W) tT (annotate_body_t cv Replay k tA))) c) as M1.
  pose proof (open_pairs_mono (prim W (option_map (amap pt) wP) m (rebuild (tvar W) eT (annotate_body_t cv Replay k eA))) c1) as M2.
  rewrite Hot in M1; rewrite Hoe in M2; simpl in M1, M2.
  cbn [open_pairs].
  set (n := DBound (j, j)) in *.
  set (s0 := store_set s (keyv n) (VReal 0%R)).
  assert (Hnp : forall p, In p L -> keyv n <> keyv (stored p)).
  { intros p Hp K; apply keyv_inj in K; [| reflexivity | reflexivity]; exact (Hst p Hp (eq_sym K)). }
  assert (Hcn : forall p, cP = AVar p -> static_ok k p /\ pn p <> j).
  { intros p E; split; [exact (proj1 (Hcs p E)) |]; intros Ej'; apply (Hst p (H p E)).
    unfold stored, n; rewrite Ej'; reflexivity. }
  destruct (avoid_spell k cP j Hcn) as [C1 _].
  assert (Hsc0 : xev s0 (spell (amap pt cP)) = Some (VBool b)) by (unfold s0; rewrite xev_set_other; auto).
  (* the branch taken *)
  assert (Hctx : forall bW, (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
                  (forall p, In p L -> live_anf k bW p -> vatoms k (AIte (amap pa cP) tA eA) p) ->
                  forall c', (c <= c')%nat -> actx L k c' s0 wP PBranch (live_anf k bW) (live_anf k bW) Real).
  { intros bW Hl Ha c' Hcc; constructor.
    - exact (sctx_weaken _ _ _ _ _ _ _ _ _ (sctx_branch _ _ _ _ _ _ _ _ Hs Hl) (fun p H0 => H0) Hcc).
    - exact (a_bar _ _ _ _ _ _ _ _ _ Hc).
    - intros p Hp Hl'; unfold s0; rewrite store_get_set_other by exact (Hnp p Hp).
      exact (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (Ha p Hp Hl')).
    - intros p Hp Hr; destruct (a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr) as [lt Hlt]; exists lt.
      unfold s0; rewrite store_get_set_other; [exact Hlt |]; intros K; apply keyv_inj in K; [discriminate | reflexivity | reflexivity]. }
  assert (Hbody : exists (sb : list (dstmt W)) (vb : dexpr W) (s1 : store R) (vv : val (dual R)),
            run sb s0 = Some s1 /\ fwd_frame c None None s0 s1 /\ tapes_kept s0 s1 /\ xev s1 vb = Some (primal vv) /\
            ve = vv /\ (if b then st else se') = sb /\ (if b then vt else ve') = vb).
  { destruct b.
    - assert (Hl : forall p, live_anf k tW p -> live_value k (AIte (amap pw cP) tW eW) p)
        by (unfold live_anf, live_value; intros p H'; simpl; rewrite H', orb_true_r; reflexivity).
      assert (Ha : forall p, In p L -> live_anf k tW p -> vatoms k (AIte (amap pa cP) tA eA) p).
      { intros p Hp Hl'; unfold vatoms; simpl; rewrite !atom_member_union.
        rewrite (live_atoms L k tP tA tW p H9 H6 HL Hp Hl'), orb_true_r; reflexivity. }
      specialize (IHt L k c s0 wP PBranch m Replay tA tW tT tD Real ve H9 H6 H3 H0
                    (Hctx tW Hl Ha c (le_n c)) HtW Hev).
      rewrite Hot in IHt; destruct IHt as [_ [s1 [Hrun [Hfr [Htk Hv]]]]].
      exists st, vt, s1, ve; repeat split; auto.
    - assert (Hl : forall p, live_anf k eW p -> live_value k (AIte (amap pw cP) tW eW) p)
        by (unfold live_anf, live_value; intros p H'; simpl; rewrite H', !orb_true_r; reflexivity).
      assert (Ha : forall p, In p L -> live_anf k eW p -> vatoms k (AIte (amap pa cP) tA eA) p).
      { intros p Hp Hl'; unfold vatoms; simpl; rewrite !atom_member_union.
        rewrite (live_atoms L k eP eA eW p H10 H7 HL Hp Hl'), !orb_true_r; reflexivity. }
      specialize (IHe L k c1 s0 wP PBranch m Replay eA eW eT eD Real ve H10 H7 H4 H1
                    (Hctx eW Hl Ha c1 M1) HeW Hev).
      rewrite Hoe in IHe; destruct IHe as [_ [s1 [Hrun [Hfr [Htk Hv]]]]].
      exists se', ve', s1, ve; repeat split; auto.
      intros v0 Hb0; apply Hfr; exact (below_mono c c1 v0 Hb0 M1). }
  destruct Hbody as [sb [vb [s1 [vv [Hrun [Hfr [Htk [Hv [<- [Esb Evb]]]]]]]]]].
  split; [lia |].
  exists (store_set s1 (keyv n) (primal ve)).
  split.
  { rewrite run_realvar; fold s0; rewrite run_branch with (b := b) by exact Hsc0.
    destruct b; subst sb vb; rewrite run_app, Hrun, run_assign_var with (v := primal ve) by exact Hv; reflexivity. }
  split.
  { intros v0 Hb0 Hc0 Ht0 Hne _.
    rewrite store_get_set_other by (intros K; apply keyv_inj in K; [subst v0; apply Hne; reflexivity | reflexivity | exact Hc0]).
    rewrite (Hfr v0 Hb0 Hc0 Ht0 ltac:(discriminate) ltac:(discriminate)).
    unfold s0; apply store_get_set_other; intros K; apply keyv_inj in K; [subst v0; apply Hne; reflexivity | reflexivity | exact Hc0]. }
  split; [| apply store_get_set_same].
  apply (tapes_kept_trans _ s1); [apply (tapes_kept_trans _ s0); [apply tapes_kept_set; [simpl; tauto | reflexivity] | exact Htk] |].
  apply tapes_kept_set; [simpl; tauto | reflexivity].
Qed.

Ltac rev_intro :=
  let L := fresh "L" in let k := fresh "k" in let c := fresh "c" in
  intros L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs Hbar Htc Htail [j [Ej Hj]] Hst Hev Hvr;
  destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.

Lemma rev_value_ite w vo (c : atom (tvar W)) t e te n :
  rev_value W w vo (AIte c t e) te n =
  sbind (adj W w vo Replay t (DVar (BarOf n))) (fun '(ft, rt) =>
  sbind (adj W w vo Replay e (DVar (BarOf n))) (fun '(fe, re) =>
    Done [DBranch (spell c) (app ft rt) (app fe re)])).
Proof. reflexivity. Qed.

Lemma tbr_occurs L k (bP : anf pv bare) bA bW m p :
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> Forall (static_ok k) L -> In p L ->
  (tbr cv m k bA p \/ useful cv m k bA p) -> live_anf k bW p.
Proof.
  intros HA HW HL Hp Ht; unfold live_anf.
  destruct (static_in _ _ _ HL Hp) as [Eid [Hk _]]; rewrite <- Eid.
  apply ((proj1 needs_occurs) bP L bA bW m k (aid (pa p)) HA HW); [| lia |].
  - intros q Hq; exact (proj1 (static_in _ _ _ HL Hq)).
  - unfold tbr, useful in Ht; destruct Ht as [Ht | Ht]; rewrite atom_member_id in Ht; rewrite Ht; [apply orb_true_r | reflexivity].
Qed.

(* The reverse sweep of a branch: the branch taken is replayed, then
   transposed from the adjoint of the variable of the let. *)
Lemma arev_ite (cP : atom pv) (tP eP : anf pv bare) :
  asim_body cv tP -> asim_body cv eP -> asim_rev cv (AIte cP tP eP).
Proof.
  intros IHt IHe; rev_intro; simpl in Htc, Hev, Hst; cbn [rebuild_value annotate_value_t]; rewrite rev_value_ite.
  rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT, t2 into tD, e2 into eD.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  (* typing *)
  assert (Hpp : pp = PTop \/ pp = PBranch \/ pp = PScalar)
    by (destruct pp as [| | | ix sx]; auto; simpl in Htc; discriminate).
  assert (Hnl : not_in_loop pp) by (destruct Hpp as [-> | [-> | ->]]; exact I).
  assert (Htc' : (if ty_eqb (of_atom (amap pw cP)) Boolean
                  then let '(t3, d1) := typecheck (option_map (amap pw) wP) InBranch k tW in
                       let '(t4, d2) := typecheck (option_map (amap pw) wP) InBranch k eW in
                       if is_ok d1 then if is_ok d2 then if ty_eqb t3 Real && ty_eqb t4 Real
                         then (Real, Ok) else (Real, Error "both branches must compute a real")
                       else (Real, d2) else (Real, d1)
                  else (Real, Error "a branch condition must be a comparison")) = (te, Ok))
    by (destruct Hpp as [-> | [-> | ->]]; exact Htc).
  clear Htc.
  destruct (ty_eqb (of_atom (amap pw cP)) Boolean) eqn:Ecb; [| discriminate].
  destruct (typecheck (option_map (amap pw) wP) InBranch k tW) as [t3 d1] eqn:HtW.
  destruct (typecheck (option_map (amap pw) wP) InBranch k eW) as [t4 d2] eqn:HeW.
  destruct d1, d2; simpl in Htc'; try discriminate.
  destruct (ty_eqb t3 Real) eqn:E3, (ty_eqb t4 Real) eqn:E4; simpl in Htc'; try discriminate.
  injection Htc' as <-; apply ty_eqb_true in E3, E4; subst t3 t4.
  destruct (aeval_atom (duals reals) (amap pd cP)) as [[| | b | |] |] eqn:Hcd; try discriminate.
  (* the two bodies, opened *)
  rewrite open_pairs_sbind.
  lazymatch goal with |- context [@open_pairs ?A ?t c] => destruct (@open_pairs A t c) as [[ft rt] c1] eqn:Hot end.
  assert (M1 : (c <= c1)%nat)
    by (lazymatch type of Hot with @open_pairs _ ?t c = _ => pose proof (open_pairs_mono t c) as Mo; rewrite Hot in Mo; exact Mo end).
  cbv iota beta; rewrite open_pairs_sbind.
  lazymatch goal with |- context [@open_pairs ?A ?t c1] => destruct (@open_pairs A t c1) as [[fe re] c2] eqn:Hoe end.
  assert (M2 : (c1 <= c2)%nat)
    by (lazymatch type of Hoe with @open_pairs _ ?t c1 = _ => pose proof (open_pairs_mono t c1) as Mo; rewrite Hoe in Mo; exact Mo end).
  cbn [open_pairs]; split; [lia |].
  intros s2 O Hrd Hr Hns Htp.
  set (n := DBound (j, j)) in *.
  destruct (Hns eq_refl) as [Hn_notin Hsh].
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  (* the reads of the reverse sweep of the branch *)
  assert (Hreads : forall p, In p L ->
            atom_member (AVar (pa p)) (atom_union (atom_union (atoms_of_atom (amap pa cP)) (snd (needs cv Replay k tA)))
                                                   (snd (needs cv Replay k eA))) = true ->
            vreads cv k (AIte (amap pa cP) tA eA) p).
  { intros p _ Hm; unfold vreads; cbn [value_needs].
    destruct (needs cv Replay k tA), (needs cv Replay k eA); exact Hm. }
  assert (Hflows : forall p, In p L ->
            atom_member (AVar (pa p)) (atom_union (fst (needs cv Replay k tA)) (fst (needs cv Replay k eA))) = true ->
            vflows cv k (AIte (amap pa cP) tA eA) p).
  { intros p _ Hm; unfold vflows; cbn [value_needs].
    destruct (needs cv Replay k tA), (needs cv Replay k eA); exact Hm. }
  (* the condition *)
  assert (Hcs : forall p, cP = AVar p -> static_ok k p /\ store_get s2 (keyv (stored p)) = Some (primal (pd p))).
  { intros p ->; split; [exact (static_in _ _ _ HL (H8 p eq_refl)) |].
    apply (Hrd p (H8 p eq_refl)); [| unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity | left; exact Hnl].
    apply (Hreads p (H8 p eq_refl)); rewrite !atom_member_union; simpl; rewrite Nat.eqb_refl; reflexivity. }
  pose proof (aspell_ok k s2 cP _ Hcs Hcd) as Hsc; simpl in Hsc.
  (* the branch taken *)
  assert (Gen : forall (bP : anf pv bare) bA bW bT bD cb fb rb cb',
            asim_body cv bP -> anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
            typecheck (option_map (amap pw) wP) InBranch k bW = (Real, Ok) -> aeval (duals reals) bD = Some ve ->
            (c <= cb)%nat ->
            open_pairs (adj W (option_map (amap pt) wP) vo Replay (rebuild (tvar W) bT (annotate_body_t cv Replay k bA))
                          (DVar (BarOf n))) cb = ((fb, rb), cb') ->
            (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
            (forall p, In p L -> tbr cv Replay k bA p -> vreads cv k (AIte (amap pa cP) tA eA) p) ->
            (forall p, In p L -> useful cv Replay k bA p -> vflows cv k (AIte (amap pa cP) tA eA) p) ->
            exists s3, run (fb ++ rb) s2 = Some s3 /\
              (forall v, below c v -> consistent v -> is_primal v -> v <> n -> store_get s3 (keyv v) = store_get s2 (keyv v)) /\
              tapes_kept s2 s3 /\
              rev_frame c (inplace wP pp) (oput O n (TangentCorrect.tangent ve)) s2 s3 /\
              (forall t m, In (t, m) O -> shaped t (barv s3 m)) /\
              pairing O s3 = pairing (oput O n (TangentCorrect.tangent ve)) s2).
  { intros bP bA bW bT bD cb fb rb cb' IH HbA HbW HbT HbD Htcb Hevb Hcb Hob Hlive Htbr Huse.
    assert (Hctx : actx L k cb s2 wP PBranch (live_anf k bW) (tbr cv Replay k bA) Real).
    { constructor.
      - exact (sctx_weaken _ _ _ _ _ _ _ _ _ (sctx_branch _ _ _ _ _ _ _ _ Hs Hlive) (fun p Hm => Hm) Hcb).
      - exact Hbar.
      - intros p Hp Ht; apply (Hrd p Hp (Htbr p Hp Ht)); [| left; exact Hnl].
        apply Hlive, (tbr_occurs L k bP bA bW Replay p HbA HbW HL Hp (or_introl Ht)).
      - exact Htp. }
    specialize (IH L k cb s2 wP PBranch Replay bA bW bT bD Real ve (DVar (BarOf n)) vo HbA HbW HbT HbD Hctx I Htcb Hevb
                  ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
    lazymatch type of IH with context [@open_pairs ?A ?t cb] =>
      assert (E : @open_pairs A t cb = ((fb, rb), cb')) by exact Hob; rewrite E in IH; clear E end.
    destruct IH as [_ [Hht [s1 [R1 [F1 [T1 [_ Hrev]]]]]]].
    destruct ve as [d | | | |]; try (simpl in Hht; contradiction).
    simpl in Hsh; destruct (barv s2 n) as [[bn | | | |] |] eqn:Ebn; try contradiction.
    assert (Hown : forall t m, In (t, m) O -> barv s1 m = barv s2 m).
    { intros t m Hi; destruct (r_below _ _ _ _ _ _ _ Hr t m Hi) as [jm [-> Hjm]]; unfold barv.
      apply F1; [simpl; lia | reflexivity | simpl; tauto | discriminate | discriminate]. }
    assert (Hbn1 : barv s1 n = Some (VReal bn)).
    { rewrite <- Ebn; unfold barv; apply F1; [simpl; lia | reflexivity | simpl; tauto | discriminate | discriminate]. }
    assert (Hr1 : rctx L cb wP PBranch O (useful cv Replay k bA) s1).
    { constructor.
      - exact (r_nodup _ _ _ _ _ _ _ Hr).
      - intros t m Hi; rewrite (Hown t m Hi); exact (r_shape _ _ _ _ _ _ _ Hr t m Hi).
      - intros t m Hi; destruct (r_below _ _ _ _ _ _ _ Hr t m Hi) as [jm [E Hjm]]; exists jm; split; [exact E | lia].
      - intros p Hp Hu Hv; exact (r_useful _ _ _ _ _ _ _ Hr p Hp (Huse p Hp Hu) Hv).
      - intros p t Hp Hu Hi; exact (r_value _ _ _ _ _ _ _ Hr p t Hp (Huse p Hp Hu) Hi).
      - intros o E; discriminate. }
    assert (Hseed : seed_ok cb Real (DVar (BarOf n)) s1).
    { split; [intros y [<- | []]; split; [simpl; lia | reflexivity] |].
      intros _; exists bn; exact Hbn1. }
    assert (Htp1 : tapes_ok L s1) by (intros p Hp Hrp; destruct (Htp p Hp Hrp) as [lt Hlt]; exact (T1 _ _ Hlt)).
    destruct (Hrev s1 O (fun _ _ _ _ => eq_refl) Hr1 Hseed Htp1) as [s3 [R3 [_ [_ [T3 [F3 [S3 P3]]]]]]].
    exists s3; split; [rewrite run_app, R1; exact R3 |].
    assert (Hprim : forall v, below c v -> consistent v -> is_primal v -> store_get s3 (keyv v) = store_get s2 (keyv v)).
    { intros v Hb0 Hc0 Hp0.
      rewrite (F3 v (below_mono c cb v Hb0 Hcb) Hc0 ltac:(destruct v; simpl in Hp0 |- *; tauto) ltac:(discriminate)
                 ltac:(intros m0 E; subst v; destruct Hp0)).
      apply F1; [exact (below_mono c cb v Hb0 Hcb) | exact Hc0 | destruct v; simpl in Hp0 |- *; tauto | discriminate | discriminate]. }
    split; [intros v Hb0 Hc0 Hp0 _; exact (Hprim v Hb0 Hc0 Hp0) |].
    split; [exact (tapes_kept_trans _ _ _ T1 T3) |].
    split.
    { intros v Hb0 Hc0 Ht0 _ Hb'.
      rewrite (F3 v (below_mono c cb v Hb0 Hcb) Hc0 Ht0 ltac:(discriminate)).
      - apply F1; [exact (below_mono c cb v Hb0 Hcb) | exact Hc0 | exact Ht0 | discriminate | discriminate].
      - intros m0 E Hm; apply (Hb' m0 E); rewrite (oput_notin O n _ Hn_notin); right; exact Hm. }
    split; [exact S3 |].
    rewrite P3, (oput_notin O n _ Hn_notin); unfold result_pairing, seed_value.
    change (xev s1 (DVar (BarOf n))) with (barv s1 n); rewrite Hbn1.
    simpl; rewrite (pairing_ext_own O s1 s2 Hown); unfold pairing at 2; fold pairing.
    cbn [fold_right]; rewrite Ebn; fold (pairing O s2); simpl; ring. }
  destruct b.
  - destruct (Gen tP tA tW tT tD c ft rt c1 IHt H9 H6 H3 H0 HtW Hev (le_n c) Hot) as [s3 Hs3].
    + unfold live_anf, live_value; intros p H'; simpl; rewrite H', orb_true_r; reflexivity.
    + intros p Hp Ht; apply Hreads; [exact Hp |]; unfold tbr in Ht; rewrite !atom_member_union, Ht, orb_true_r; reflexivity.
    + intros p Hp Ht; apply Hflows; [exact Hp |]; unfold useful in Ht; rewrite atom_member_union, Ht; reflexivity.
    + exists s3; destruct Hs3 as [R3 Hs3]; split; [| exact Hs3].
      rewrite run_branch with (b := true) by exact Hsc; rewrite R3; reflexivity.
  - destruct (Gen eP eA eW eT eD c1 fe re c2 IHe H10 H7 H4 H1 HeW Hev M1 Hoe) as [s3 Hs3].
    + unfold live_anf, live_value; intros p H'; simpl; rewrite H', !orb_true_r; reflexivity.
    + intros p Hp Ht; apply Hreads; [exact Hp |]; unfold tbr in Ht; rewrite !atom_member_union, Ht, !orb_true_r; reflexivity.
    + intros p Hp Ht; apply Hflows; [exact Hp |]; unfold useful in Ht; rewrite atom_member_union, Ht, orb_true_r; reflexivity.
    + exists s3; destruct Hs3 as [R3 Hs3]; split; [| exact Hs3].
      rewrite run_branch with (b := false) by exact Hsc; rewrite R3; reflexivity.
Qed.

End Branch.
