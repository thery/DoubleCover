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
