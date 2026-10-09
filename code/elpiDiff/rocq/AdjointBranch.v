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
  AnfEquiv Correctness TangentCorrect TangentLoops TangentGood AdjointCorrect.

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


(* The value of a body has the type it is checked at, and a zero tangent when
   the body is not varied. *)
Definition act_body (bP : anf pv bare) : Prop :=
  forall L k wP pp bA bW bD ty v,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gD L) bP bD -> Forall (static_ok k) L ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  has_type ty v /\ (varied_anf k bA = false -> zero v).

Lemma act_ret (aP : atom pv) : act_body (ARet aP).
Proof.
  intros L k wP pp bA bW bD ty v HA HW HD HL Htc Hev.
  destruct bA as [| aA], bW as [| aW], bD as [| aD]; simpl in HA, HW, HD; try contradiction.
  apply atom_graph in HA as [-> Hin]; apply atom_graph in HW as [-> _]; apply atom_graph in HD as [-> _].
  assert (H1 : forall p, aP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  simpl in Htc, Hev |- *.
  assert (Ety : ty = of_atom (amap pw aP)).
  { destruct aP as [p | |]; simpl in Htc; [| injection Htc as <-; reflexivity | injection Htc as <-; reflexivity].
    destruct (varg (pw p)) as [[? ?] |];
      [destruct (_ && _) | ]; injection Htc as <-; [discriminate | reflexivity | reflexivity]. }
  subst ty; split; [exact (atom_type k aP v H1 Hev) |].
  intros Hv; exact (atom_zero k aP v H1 Hv Hev).
Qed.

Lemma act_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  act_value eP -> (forall x, act_body (cP x)) -> act_body (ALet a eP cP).
Proof.
  intros IHa IHb L k wP pp bA bW bD ty v HA HW HD HL Htc Hev.
  destruct bA as [aA eA cA |], bW as [aW eW cW |], bD as [aD eD cD |]; simpl in HA, HW, HD; try contradiction.
  destruct HA as [HeA HcA], HW as [HeW HcW], HD as [HeD HcD].
  simpl in Htc, Hev.
  destruct (typecheck_value (option_map (amap pw) wP) (wplace pp) (WellFormed.is_tail cW k) k eW)
    as [te d0] eqn:Hte.
  destruct d0; simpl in Htc; [| discriminate].
  destruct (aeval_value (duals reals) eD) as [ve |] eqn:Hve; [| discriminate].
  destruct (IHa L k wP pp _ eA eW eD te ve HeA HeW HeD HL Hte Hve) as [Ht [Hz Hra]].
  set (vr := varied_value k eA).
  set (x := PV (let_binder k eA) (VInfo k te None) (open_let te (DBound (0%nat, 0%nat) : dvar W) vr false) ve 0).
  assert (Hxs : static_ok (S k) x).
  { repeat split; simpl; auto; try lia; discriminate. }
  assert (HL' : Forall (static_ok (S k)) (x :: L)).
  { constructor; [exact Hxs |]; apply Forall_impl with (P := static_ok k); auto.
    intros p Hp; apply (static_mono k); auto. }
  exact (IHb x (x :: L) (S k) wP pp (cA (pa x)) (cW (pw x)) (cD (pd x)) ty v
           (HcA x (pa x)) (HcW x (pw x)) (HcD x (pd x)) HL' Htc Hev).
Qed.

Lemma act_ite (cP : atom pv) (tP eP : anf pv bare) :
  act_body tP -> act_body eP -> act_value (AIte cP tP eP).
Proof.
  intros IHt IHe L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev.
  destruct eA as [| | | | ? tA eA0 | |], eW as [| | | | ? tW eW0 | |], eD as [| | | | ? tD eD0 | |];
    simpl in HA, HW, HD; try contradiction.
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.
  simpl in Htc, Hev |- *.
  assert (Htc' : (if ty_eqb (of_atom (amap pw cP)) Boolean
                  then let '(t3, d1) := typecheck (option_map (amap pw) wP) InBranch k tW in
                       let '(t4, d2) := typecheck (option_map (amap pw) wP) InBranch k eW0 in
                       if is_ok d1 then if is_ok d2 then if ty_eqb t3 Real && ty_eqb t4 Real
                         then (Real, Ok) else (Real, Error "both branches must compute a real")
                       else (Real, d2) else (Real, d1)
                  else (Real, Error "a branch condition must be a comparison")) = (te, Ok))
    by (destruct pp; [exact Htc | exact Htc | exact Htc | discriminate]).
  clear Htc.
  destruct (ty_eqb (of_atom (amap pw cP)) Boolean); [| discriminate].
  destruct (typecheck (option_map (amap pw) wP) InBranch k tW) as [t3 d1] eqn:HtW.
  destruct (typecheck (option_map (amap pw) wP) InBranch k eW0) as [t4 d2] eqn:HeW.
  destruct d1, d2; simpl in Htc'; try discriminate.
  destruct (ty_eqb t3 Real) eqn:E3, (ty_eqb t4 Real) eqn:E4; simpl in Htc'; try discriminate.
  injection Htc' as <-; apply ty_eqb_true in E3, E4; subst t3 t4.
  destruct (aeval_atom (duals reals) (amap pd cP)) as [[| | b | |] |]; try discriminate.
  split; [| split; [| intros _; exact I]].
  - destruct b; [exact (proj1 (IHt L k wP PBranch _ _ _ Real ve ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) HL HtW Hev))
                | exact (proj1 (IHe L k wP PBranch _ _ _ Real ve ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) HL HeW Hev))].
  - intros Hv; apply orb_false_iff in Hv as [Hvt Hve].
    destruct b; [exact (proj2 (IHt L k wP PBranch _ _ _ Real ve ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) HL HtW Hev) Hvt)
                | exact (proj2 (IHe L k wP PBranch _ _ _ Real ve ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) HL HeW Hev) Hve)].
Qed.

Lemma owner_ite (cP : atom pv) (tP eP : anf pv bare) : act_owner (AIte cP tP eP).
Proof. intros L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es; discriminate. Qed.

Lemma inplace_ite (cP : atom pv) (tP eP : anf pv bare) : inplace_only (AIte cP tP eP).
Proof. intros L k wP pp tail eW te _ _ Hst; destruct Hst; reflexivity. Qed.


(* Loops. *)
Lemma run_forback i lo hi b ss s l h :
  xev s lo = Some (VInt l) -> xev s hi = Some (VInt h) ->
  run (DForBack i lo hi b :: ss) s =
  match exec_down R (run b) (out_dvar nat i) (h - 1) (count l h) s with Some s1 => run ss s1 | None => None end.
Proof.
  intros Hl Hh; unfold run; cbn [map out_dstmt exec_stmts exec]; unfold xev in Hl, Hh; rewrite Hl, Hh.
  reflexivity.
Qed.

(* A loop down from n - 1 to 0, by an invariant indexed by the next index. *)
Lemma exec_down_loop (body : store R -> option (store R)) (i : dvar nat) (N : nat) (P : nat -> store R -> Prop) :
  (forall j s, (j < N)%nat -> P (S j) s -> exists s', body (store_set s (KVar i) (VInt (Z.of_nat j))) = Some s' /\ P j s') ->
  forall n s, (n <= N)%nat -> P n s -> exists s', exec_down R body i (Z.of_nat n - 1) n s = Some s' /\ P 0%nat s'.
Proof.
  intros Hstep n; induction n as [| n IH]; intros s Hn Hp; cbn [exec_down]; [exists s; auto |].
  replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n) by lia.
  destruct (Hstep n s ltac:(lia) Hp) as [s1 [Hb Hp1]]; rewrite Hb.
  exact (IH s1 ltac:(lia) Hp1).
Qed.

Lemma eval_map_nth (ev : val (dual R) -> option (val (dual R))) i n xs j d0 :
  eval_map ev i n = Some xs -> (j < n)%nat -> ev (VInt (i + Z.of_nat j)) = Some (VReal (nth j xs d0)).
Proof.
  revert i xs j; induction n as [| n IH]; intros i xs j H Hj; [lia |]; simpl in H.
  destruct (ev (VInt i)) as [[x | | | |] |] eqn:E; try discriminate.
  destruct (eval_map ev (i + 1)%Z n) as [xs1 |] eqn:E1; [| discriminate]; injection H as <-.
  destruct j as [| j]; [simpl; rewrite Z.add_0_r; exact E |].
  simpl nth; replace (i + Z.of_nat (S j))%Z with (i + 1 + Z.of_nat j)%Z by lia.
  apply IH; [exact E1 | lia].
Qed.

Lemma skipn_nth_cons {A : Type} (l : list A) j d :
  (j < length l)%nat -> skipn j l = nth j l d :: skipn (S j) l.
Proof. revert l; induction j as [| j IH]; intros [| a l] H; simpl in *; try lia; auto; apply IH; lia. Qed.

Lemma dotr_zero_l l m : Forall (fun x => x = 0) l -> dotr l m = 0.
Proof.
  intros H; revert m; induction H as [| x l Hx Hl IH]; intros [| b m]; try reflexivity.
  rewrite dotr_cons, IH, Hx; ring.
Qed.

Lemma inner_tangent_zero v b : zero v -> inner (TangentCorrect.tangent v) b = 0.
Proof.
  intros Hz; destruct v as [d | | | l |]; simpl in Hz |- *; try (destruct b as [[] |]; reflexivity).
  - destruct b as [[y | | | |] |]; try reflexivity; rewrite Hz; ring.
  - destruct b as [[| | | m |] |]; try reflexivity.
    apply dotr_zero_l; rewrite Forall_map; exact Hz.
Qed.

Lemma xev_at s a ix l z :
  store_get s (keyv a) = Some (VArray l) -> store_get s (keyv ix) = Some (VInt z) ->
  xev s (DAt (DVar a) (DVar ix)) = option_map VReal (nth_z z l).
Proof.
  intros Ha Hi; unfold xev, keyv in *; simpl; rewrite Ha, Hi; destruct (nth_z z l); reflexivity.
Qed.

Lemma nth_z_of_nat {A : Type} (l : list A) j d : (j < length l)%nat -> nth_z (Z.of_nat j) l = Some (nth j l d).
Proof.
  intros H; unfold nth_z.
  replace (Z.of_nat j <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Nat2Z.id; apply nth_error_nth'; exact H.
Qed.

(* Owners, without one of them. *)
Definition odel (O : owners) (n : dvar W) : owners :=
  filter (fun tm => if dvar_eq_dec_c (snd tm) n then false else true) O.

Lemma odel_in O n t m : In (t, m) (odel O n) <-> In (t, m) O /\ m <> n.
Proof. unfold odel; rewrite filter_In; simpl; destruct (dvar_eq_dec_c m n); intuition congruence. Qed.

Lemma odel_snd O n m : In m (map snd (odel O n)) -> In m (map snd O) /\ m <> n.
Proof.
  intros H; apply in_map_iff in H as [[t m'] [E Hi]]; simpl in E; subst m'.
  apply odel_in in Hi as [Hi Hn]; split; [apply in_map_iff; exists (t, m); auto | exact Hn].
Qed.

Lemma odel_nodup O n : NoDup (map snd O) -> NoDup (map snd (odel O n)).
Proof.
  induction O as [| [t m] O IH]; intros H; simpl; [constructor |].
  inversion H as [| ? ? Hm Hd]; subst; unfold odel; simpl.
  destruct (dvar_eq_dec_c m n); [exact (IH Hd) |]; simpl; constructor; [| exact (IH Hd)].
  intros Hi; apply Hm, (odel_snd O n m Hi).
Qed.

Lemma odel_ok O n : owners_ok O -> owners_ok (odel O n).
Proof. intros H t m Hi; apply odel_in in Hi as [Hi _]; exact (H t m Hi). Qed.

Lemma odel_notin O n : ~ In n (map snd O) -> odel O n = O.
Proof.
  induction O as [| [t m] O IH]; intros H; simpl; [reflexivity |]; unfold odel; simpl.
  destruct (dvar_eq_dec_c m n) as [-> | Hne]; [destruct H; left; reflexivity |].
  f_equal; apply IH; intros I; apply H; right; exact I.
Qed.

Lemma pairing_odel O n t s :
  NoDup (map snd O) -> In (t, n) O -> pairing O s = pairing (odel O n) s + inner t (barv s n).
Proof.
  induction O as [| [t0 n0] O IH]; intros Hd Hi; simpl in Hi; [contradiction |].
  inversion Hd as [| ? ? Hn Hd']; subst; unfold odel; simpl.
  destruct (dvar_eq_dec_c n0 n) as [-> | Hne].
  - destruct Hi as [E | Hi]; [injection E as -> | destruct Hn; apply in_map_iff; exists (t, n); auto].
    fold (odel O n); rewrite odel_notin by exact Hn; simpl; ring.
  - destruct Hi as [E | Hi]; [injection E as _ E; congruence |].
    simpl; fold (odel O n); rewrite (IH Hd' Hi); ring.
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

Lemma live_vatoms L k (eP : value pv bare) eA eW p :
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L -> In p L ->
  live_value k eW p -> vatoms k eA p.
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
  { constructor; [exact (sctx_weaken _ _ _ _ _ _ _ _ _ Hs' (fun p H => H) Hc01) | | | |].
    - intros p [<- | Hp]; [reflexivity | exact (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp)].
    - intros p [<- | Hp] Hl; [exact S1 |].
      rewrite Hold; [| exact Hp]; apply (a_store _ _ _ _ _ _ _ _ _ Hc p Hp), Hlive_c; auto.
    - intros p [<- | Hp] Hr; [discriminate |].
      destruct (a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr) as [lt Hlt]; exact (T1 _ _ Hlt).
    - intros o Ho; rewrite Hold; [exact (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho) | exact (owner_in_s _ _ _ _ _ _ _ _ Hs Ho)]. }
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
      unfold s0; rewrite store_get_set_other; [exact Hlt |]; intros K; apply keyv_inj in K; [discriminate | reflexivity | reflexivity].
    - intros o Ho; unfold owner in Ho; destruct wP as [[] |]; discriminate. }
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
              (not_in_loop pp -> storage wP tail (AIte cP tP eP) <> None -> forall o, owner wP pp = Some o ->
                 avaried (pa o) = false -> store_get s3 (keyv n) = store_get s2 (keyv n)) /\
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
      - exact Htp.
      - intros o Ho; unfold owner in Ho; destruct wP as [[] |]; discriminate. }
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
      - intros o E; discriminate.
      - exact (r_args _ _ _ _ _ _ _ Hr).
      - exact (r_written _ _ _ _ _ _ _ Hr). }
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
    split; [intros _ Hsn; destruct Hsn; reflexivity |].
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



(* The forward sweep of a map: a loop over the indices, computing each element
   by the primal computation of the body, into the written array. *)
Lemma afwd_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, psim_body (bP x)) -> asim_fwd cv (AMap loP hiP bP).
Proof.
  intros IHb L k c s wP pp tail eA eW eT eD te n ve ty m rec HA HW HT HD Hc Htc Htail [j [Ej Hj]] Hst Hrec Hev.
  pose proof HA as HA0; pose proof HW as HW0.
  destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.
  simpl in Htc, Hev, Hst |- *.
  rename b into bA, b0 into bW, b1 into bT, b2 into bD.
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  destruct pp as [| | | ix0 sx0]; simpl in Htc; try discriminate.
  destruct tail; [| discriminate].
  destruct loP as [? | ? | l0]; simpl in Htc; try discriminate.
  destruct hiP as [? | ? | h]; simpl in Htc; try discriminate.
  destruct (negb (l0 =? 0)%Z) eqn:El; [discriminate |].
  apply negb_false_iff, Z.eqb_eq in El; subst l0.
  assert (Hte : te = Array (h - 0)) by (clear - Htc; crush_match Htc).
  destruct (owner wP PTop) as [o |] eqn:Eo;
    [| destruct (s_ty _ _ _ _ _ _ _ Hs ltac:(rewrite <- (Htail eq_refl), Hte; exact I) Eo)].
  destruct wP as [[o' | |] |]; simpl in Eo; try discriminate.
  destruct (vty (pw o')) as [| | | ny] eqn:Ey; try discriminate; injection Eo as ->.
  simpl in Hst; injection Hst as Ej; subst j.
  assert (Hfacts : occurs_anf (vid (pw o)) (S k) (bW (anon k)) = false /\
                   typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None)) = (Real, Ok)).
  { simpl in Htc; destruct (varg (pw o)) as [[nm [] ] |]; simpl in Htc; try discriminate;
      destruct (occurs_anf (vid (pw o)) (S k) (bW (anon k))); try discriminate;
      destruct (typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None))) as [tb [| mm]];
      simpl in Htc; try discriminate; destruct (ty_eqb tb Real) eqn:Etb; try discriminate;
      apply ty_eqb_true in Etb; subst; auto. }
  destruct Hfacts as [Hnocc HtB].
  destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [o'' [Eo'' [HoL _]]]; injection Eo'' as <-.
  assert (Ehn : ny = (h - 0)%Z).
  { destruct (s_top _ _ _ _ _ _ _ Hs o eq_refl eq_refl ltac:(rewrite Ey; exact I)) as [Hty _].
    rewrite Ey, <- (Htail eq_refl), Hte in Hty; injection Hty as E; symmetry; exact E. }
  (* the written array, at the start *)
  assert (Hown : owner (Some (AVar o)) PTop = Some o) by (simpl; rewrite Ey; reflexivity).
  pose proof (a_owner _ _ _ _ _ _ _ _ _ Hc o Hown) as A1.
  destruct (static_in _ _ _ HL HoL) as [_ [_ [_ [_ [_ [_ [_ [_ [Hht _]]]]]]]]].
  rewrite Ey in Hht; destruct (pd o) as [| | | lo |] eqn:Epd; try contradiction; simpl in Hht.
  simpl in A1; set (l1 := map dfst lo) in A1.
  (* the dual evaluation *)
  simpl in Hev; destruct (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h)) as [xs |] eqn:Hxs;
    [| discriminate]; injection Hev as <-.
  (* the body, opened *)
  rewrite open_pairs_sbind.
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] => destruct (@open_pairs A t (S c)) as [[sb vb] c2] eqn:Hob end.
  assert (Hc2 : (S c <= c2)%nat)
    by (lazymatch type of Hob with @open_pairs _ ?t _ = _ => pose proof (open_pairs_mono t (S c)) as Mo; rewrite Hob in Mo; exact Mo end).
  cbn [open_pairs spell amap]; split; [lia |].
  set (n := DBound (pn o, pn o)) in *.
  set (i := DBound (c, c)) in *.
  set (bodyst := (sb ++ [DAssign (DAt (DVar n) (DVar i)) vb])%list).
  assert (Hlen1 : length l1 = count 0 h) by (unfold l1; rewrite length_map, Hht, count_nat; lia).
  (* the variables the body reads are not the output array *)
  assert (Hlive_b : forall p, In p L -> live_anf (S k) (bW (VInfo k Integer None)) p ->
                    live_value k (AMap (ANat 0) (ANat h) bW) p /\ pn p <> pn o).
  { intros p Hp Hl.
    assert (Hl' : live_value k (AMap (ANat 0) (ANat h) bW) p).
    { unfold live_anf, live_value in *; simpl.
      rewrite <- (live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL eq_refl eq_refl); exact Hl. }
    split; [exact Hl' |]; intros E.
    destruct (s_owner _ _ _ _ _ _ _ Hs o p Hown Hp E) as [-> | Hn]; [| contradiction].
    unfold live_anf in Hl.
    rewrite (live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL eq_refl eq_refl) in Hl.
    congruence. }
  set (Inv := fun (z : Z) (s' : store R) (acc : list (dual R)) =>
         z = Z.of_nat (length acc) /\ fwd_frame c (Some n) None s s' /\ tapes_kept s s' /\
         store_get s' (keyv n) = Some (VArray (map dfst acc ++ skipn (length acc) l1))%list).
  assert (Hloop : exists sf, exec_up R (run bodyst) (out_dvar nat i) 0 (count 0 h) s = Some sf /\
                             Inv (0 + Z.of_nat (count 0 h))%Z sf ([] ++ xs)%list).
  { apply (map_loop_bounded (fun v => aeval (duals reals) (bD v)) (run bodyst) (out_dvar nat i) Inv
             (Z.of_nat (count 0 h))); [| lia | | exact Hxs].
    - intros z s' acc d Hz [Ez [Hfr' [Htk' Hn']]] Hbd.
      set (s'' := store_set s' (keyv i) (VInt z)).
      change (store_set s' (KVar (out_dvar nat i)) (VInt z)) with s''.
      set (ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c))) (VInt z) c).
      assert (Hix : static_ok (S k) ix) by (repeat split; simpl; auto; try lia; discriminate).
      assert (Kin : forall v, below c v -> consistent v -> keyv v <> keyv i).
      { intros v Hb Hcv K; apply keyv_inj in K; [| exact Hcv | reflexivity]; subst v; unfold i in Hb; simpl in Hb; lia. }
      assert (Hctx : actx (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar
                       (live_anf (S k) (bW (VInfo k Integer None))) (live_anf (S k) (bW (VInfo k Integer None))) Real).
      { constructor.
        - apply sctx_scalar.
          + constructor; [exact Hix |]; apply Forall_impl with (P := static_ok k); auto.
            intros p Hp; apply (static_mono k); auto.
          + intros p q [<- | Hp] [<- | Hq] E; auto;
              try (destruct (static_in _ _ _ HL Hq) as [_ [Hq' _]]; simpl in E; lia);
              try (destruct (static_in _ _ _ HL Hp) as [_ [Hp' _]]; simpl in E; lia).
            exact (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
          + intros p [<- | Hp]; simpl; [lia |]; pose proof (s_num _ _ _ _ _ _ _ Hs _ Hp); lia.
          + intros a0 E; injection E as <-; exists o; split; [reflexivity | split; [right; exact HoL |]].
            destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [? [E [_ Hg]]]; injection E as <-; exact Hg.
        - intros p [<- | Hp]; [reflexivity | exact (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp)].
        - intros p [<- | Hp] Hl.
          + unfold s''; rewrite store_get_set_same; reflexivity.
          + destruct (Hlive_b p Hp Hl) as [Hl' Hpn].
            pose proof (s_num _ _ _ _ _ _ _ Hs _ Hp) as Hpc.
            assert (Hbp : below c (stored p)) by (unfold stored; simpl; exact Hpc).
            unfold s''; rewrite store_get_set_other by (apply not_eq_sym, Kin; [exact Hbp | reflexivity]).
            rewrite (Hfr' (stored p) Hbp eq_refl ltac:(simpl; tauto)
                       ltac:(intros E; apply Hpn; unfold n, stored in E; congruence) ltac:(discriminate)).
            exact (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (live_vatoms _ _ _ _ _ p HA0 HW0 HL Hp Hl')).
        - intros p [<- | Hp] Hr; [discriminate |].
          destruct (a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr) as [lt Hlt]; destruct (Htk' _ _ Hlt) as [l' Hl'].
          exists l'; unfold s''; rewrite store_get_set_other; [exact Hl' |].
          intros K; apply keyv_inj in K; [discriminate | reflexivity | reflexivity].
        - intros o0 E; discriminate. }
      specialize (IHb ix (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar m Replay (bA (fresh k))
                    (bW (VInfo k Integer None)) (bT (open_index (DBound (c, c)))) (bD (VInt z)) Real (VReal d)
                    (H10 ix _) (H7 ix _) (H4 ix _) (H1 ix _) Hctx HtB Hbd).
      lazymatch type of IHb with context [@open_pairs ?A ?t (S c)] =>
        assert (E : @open_pairs A t (S c) = ((sb, vb), c2)) by exact Hob; rewrite E in IHb; clear E end.
      destruct IHb as [_ [s3 [R3 [F3 [T3 X3]]]]].
      assert (Hbn : below (S c) n) by (unfold n; simpl; lia).
      assert (S3n : store_get s3 (keyv n) = store_get s' (keyv n)).
      { rewrite (F3 n Hbn eq_refl ltac:(simpl; tauto) ltac:(discriminate) ltac:(discriminate)).
        unfold s''; apply store_get_set_other; apply not_eq_sym, Kin; [unfold n; simpl; exact Hj | reflexivity]. }
      assert (S3i : xev s3 (DVar i) = Some (VInt z)).
      { change (xev s3 (DVar i)) with (store_get s3 (keyv i)).
        rewrite (F3 i ltac:(unfold i; simpl; lia) eq_refl ltac:(simpl; tauto) ltac:(discriminate) ltac:(discriminate)).
        unfold s''; apply store_get_set_same. }
      assert (Hacc : (length acc < length l1)%nat) by lia.
      set (a1 := VArray (map dfst (acc ++ [d]) ++ skipn (length (acc ++ [d])) l1)%list).
      set (s4 := store_set s3 (keyv n) a1).
      assert (Hrun4 : run [DAssign (DAt (DVar n) (DVar i)) vb] s3 = Some s4).
      { apply (run_assign_at s3 n _ _ (map dfst acc ++ skipn (length acc) l1)%list z (dfst d));
          [rewrite S3n; exact Hn' | exact S3i | exact X3 |].
        rewrite Ez; apply replace_step; exact Hacc. }
      exists s4; split; [unfold bodyst; rewrite run_app, R3; exact Hrun4 |].
      split; [rewrite length_app; simpl; lia |].
      split.
      { intros v Hb Hcv Ht Hex Hvo.
        unfold s4; rewrite store_get_set_other.
        2:{ intros K; apply keyv_inj in K; [| unfold n; reflexivity | exact Hcv]; subst v; apply Hex; reflexivity. }
        rewrite (F3 v (below_mono c (S c) v Hb ltac:(lia)) Hcv Ht ltac:(discriminate) ltac:(discriminate)).
        unfold s''; rewrite store_get_set_other by (apply not_eq_sym, Kin; [exact Hb | exact Hcv]).
        exact (Hfr' v Hb Hcv Ht Hex Hvo). }
      split.
      { apply (tapes_kept_trans _ s'); [exact Htk' |].
        apply (tapes_kept_trans _ s''); [unfold s''; apply tapes_kept_set; [simpl; tauto | reflexivity] |].
        apply (tapes_kept_trans _ s3); [exact T3 |].
        unfold s4; apply tapes_kept_set; [simpl; tauto | reflexivity]. }
      unfold s4; apply store_get_set_same.
    - split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply tapes_kept_refl |]]].
      exact A1. }
  destruct Hloop as [sf [Hex [_ [Hfr [Htk Hn']]]]].
  simpl app in Hn'.
  pose proof (eval_map_length _ _ _ _ Hxs) as Hlx.
  rewrite Hlx, <- Hlen1, skipn_all, app_nil_r in Hn'.
  exists sf; split.
  { rewrite (run_for _ _ _ _ _ _ 0 h) by reflexivity.
    lazymatch goal with |- match ?r with _ => _ end = _ => replace r with (Some sf) by (symmetry; exact Hex) end; reflexivity. }
  split; [exact Hfr | split; [exact Htk | exact Hn']].
Qed.


(* The reverse sweep of a map: a loop down the indices, replaying the body and
   transposing it from the adjoint of its element. *)
Lemma arev_map (loP hiP : atom pv) (bP : pv -> anf pv bare) :
  (forall x, asim_body cv (bP x)) -> asim_rev cv (AMap loP hiP bP).
Proof.
  intros IHb L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs Hbar Htc Htail [j [Ej Hj]] Hst Hev Hvr.
  pose proof HA as HA0; pose proof HW as HW0.
  destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.
  simpl in Htc, Hst |- *.
  rename b into bA, b0 into bW, b1 into bT, b2 into bD.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  destruct pp as [| | | ix0 sx0]; simpl in Htc; try discriminate.
  destruct tail; [| discriminate].
  destruct loP as [? | ? | l0]; simpl in Htc; try discriminate.
  destruct hiP as [? | ? | h]; simpl in Htc; try discriminate.
  destruct (negb (l0 =? 0)%Z) eqn:El; [discriminate |].
  apply negb_false_iff, Z.eqb_eq in El; subst l0.
  assert (Hte : te = Array (h - 0)) by (clear - Htc; crush_match Htc).
  destruct (owner wP PTop) as [o |] eqn:Eo;
    [| destruct (s_ty _ _ _ _ _ _ _ Hs ltac:(rewrite <- (Htail eq_refl), Hte; exact I) Eo)].
  destruct wP as [[o' | |] |]; simpl in Eo; try discriminate.
  destruct (vty (pw o')) as [| | | ny] eqn:Ey; try discriminate; injection Eo as ->.
  simpl in Hst; injection Hst as Ej; subst j.
  assert (Hfacts : (exists nm r, varg (pw o) = Some (nm, r) /\ r <> Inout) /\
                   occurs_anf (vid (pw o)) (S k) (bW (anon k)) = false /\
                   typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None)) = (Real, Ok)).
  { destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [o'' [Eo'' [_ Hg]]]; injection Eo'' as <-.
    simpl in Htc; destruct (varg (pw o)) as [[nm [] ] |]; simpl in Htc; try discriminate; [| | | destruct Hg; reflexivity];
      destruct (occurs_anf (vid (pw o)) (S k) (bW (anon k))); try discriminate;
      destruct (typecheck (Some (AVar (pw o))) ScalarBody (S k) (bW (VInfo k Integer None))) as [tb [| mm]];
      simpl in Htc; try discriminate; destruct (ty_eqb tb Real) eqn:Etb; try discriminate;
      apply ty_eqb_true in Etb; subst; (split; [eexists; eexists; split; [reflexivity | discriminate] | auto]). }
  destruct Hfacts as [[nm [ro [Hro Hnio]]] [Hnocc HtB]].
  destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [o'' [Eo'' [HoL _]]]; injection Eo'' as <-.
  simpl in Hev; destruct (eval_map (fun v1 => aeval (duals reals) (bD v1)) 0 (count 0 h)) as [xs |] eqn:Hxs;
    [| discriminate]; injection Hev as <-.
  (* the written array: dependent, with a zero tangent, and its adjoint *)
  assert (Ehn : ny = (h - 0)%Z).
  { destruct (s_top _ _ _ _ _ _ _ Hs o eq_refl eq_refl ltac:(rewrite Ey; exact I)) as [Hty _].
    rewrite Ey, <- (Htail eq_refl), Hte in Hty; injection Hty as E; symmetry; exact E. }
  destruct (static_in _ _ _ HL HoL) as [_ [_ [_ [_ [_ [_ [_ [_ [Hht Hzo]]]]]]]]].
  rewrite Ey in Hht; destruct (pd o) as [| | | lo |] eqn:Epd; try contradiction; simpl in Hht.
  pose proof (eval_map_length _ _ _ _ Hxs) as Hlx.
  (* the body, opened *)
  rewrite open_pairs_sbind.
  lazymatch goal with |- context [@open_pairs ?A ?t (S c)] => destruct (@open_pairs A t (S c)) as [[fb rb] c2] eqn:Hob end.
  assert (Hc2 : (S c <= c2)%nat)
    by (lazymatch type of Hob with @open_pairs _ ?t _ = _ => pose proof (open_pairs_mono t (S c)) as Mo; rewrite Hob in Mo; exact Mo end).
  cbn [open_pairs spell amap rev_loop]; split; [lia |].
  intros s2 O Hrd Hr _ Htp.
  set (n := DBound (pn o, pn o)) in *.
  set (i := DBound (c, c)) in *.
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  pose proof (r_nodup _ _ _ _ _ _ _ Hr) as Hnd.
  assert (Hown : owner (Some (AVar o)) PTop = Some o) by (simpl; rewrite Ey; reflexivity).
  pose proof (r_owner _ _ _ _ _ _ _ Hr o Hown) as HoO; rewrite Epd in HoO.
  assert (Hav : avaried (pa o) = false).
  { destruct (r_written _ _ _ _ _ _ _ Hr o eq_refl) as [ny' [r' [Hr' Hw']]]; rewrite Hro in Hr'; injection Hr' as <- <-.
    rewrite (r_args _ _ _ _ _ _ _ Hr o nm ro HoL Hro).
    destruct ro; simpl in Hw'; try discriminate; first [reflexivity | destruct Hnio; reflexivity]. }
  pose proof (Hzo Hav) as Hzl; simpl in Hzl.
  pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ HoO) as Hsh; simpl in Hsh.
  change (barv s2 (stored o)) with (barv s2 n) in Hsh.
  destruct (barv s2 n) as [[| | | yb |] |] eqn:Eyb; try contradiction.
  rewrite length_map in Hsh.
  assert (Hcount : length xs = count 0 h) by exact Hlx.
  assert (Hlyb : length yb = count 0 h) by (rewrite <- Hsh, Hht, Ehn, count_nat; lia).
  set (O' := odel O n).
  assert (Hnd' : NoDup (map snd O')) by exact (odel_nodup O n Hnd).
  assert (HnO' : ~ In n (map snd O')) by (intros Hi; apply (odel_snd O n n Hi); reflexivity).
  (* the variables of the body *)
  assert (Hlive_b : forall p, In p L -> live_anf (S k) (bW (VInfo k Integer None)) p ->
                    live_value k (AMap (ANat 0) (ANat h) bW) p /\ pn p <> pn o).
  { intros p Hp Hl.
    assert (Hl' : live_value k (AMap (ANat 0) (ANat h) bW) p).
    { unfold live_anf, live_value in *; simpl.
      rewrite <- (live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL eq_refl eq_refl); exact Hl. }
    split; [exact Hl' |]; intros E.
    destruct (s_owner _ _ _ _ _ _ _ Hs o p Hown Hp E) as [-> | Hn]; [| contradiction].
    unfold live_anf in Hl.
    rewrite (live_cont L k bP bW (pfresh k) (VInfo k Integer None) _ H7 HL eq_refl eq_refl) in Hl.
    congruence. }
  set (body := ([] ++ fb ++ [] ++ rb)%list).
  set (N := count 0 h).
  set (P := fun (jn : nat) (s' : store R) =>
         (forall v, below c v -> consistent v -> is_primal v -> store_get s' (keyv v) = store_get s2 (keyv v)) /\
         tapes_kept s2 s' /\ rev_frame c (Some n) O' s2 s' /\ barv s' n = Some (VArray yb) /\
         (forall t m, In (t, m) O' -> shaped t (barv s' m)) /\
         pairing O' s' = pairing O' s2 + dotr (skipn jn (map dsnd xs)) (skipn jn yb)).
  assert (Hloop : exists sf, exec_down R (run body) (out_dvar nat i) (Z.of_nat N - 1) N s2 = Some sf /\ P 0%nat sf).
  { apply (exec_down_loop (run body) (out_dvar nat i) N P); [| lia |].
    - intros jn s Hjn [K0 [T0 [F0 [B0 [S0 P0]]]]].
      assert (Hreads : forall p, In p L -> tbr cv Replay (S k) (bA (fresh k)) p -> vreads cv k (AMap (ANat 0) (ANat h) bA) p).
      { intros p Hp Ht; destruct (static_in _ _ _ HL Hp) as [Eid [Hk _]].
        unfold tbr in Ht; unfold vreads; cbn [value_needs].
        destruct (needs cv Replay (S k) (bA (fresh k))) as [u l]; simpl in Ht |- *.
        rewrite atom_member_union, atom_member_remove_full, Ht.
        unfold same_term, fresh; simpl.
        replace (Nat.eqb k (aid (pa p))) with false by (symmetry; apply Nat.eqb_neq; lia).
        simpl; rewrite ?orb_true_r; reflexivity. }
      assert (Hflows : forall p, In p L -> useful cv Replay (S k) (bA (fresh k)) p -> vflows cv k (AMap (ANat 0) (ANat h) bA) p).
      { intros p Hp Ht; destruct (static_in _ _ _ HL Hp) as [Eid [Hk _]].
        unfold useful in Ht; unfold vflows; cbn [value_needs].
        destruct (needs cv Replay (S k) (bA (fresh k))) as [u l]; simpl in Ht |- *.
        rewrite atom_member_remove_full, Ht.
        unfold same_term, fresh; simpl.
        replace (Nat.eqb k (aid (pa p))) with false by (symmetry; apply Nat.eqb_neq; lia).
        reflexivity. }
      set (z := Z.of_nat jn).
      set (s'' := store_set s (keyv i) (VInt z)).
      change (store_set s (KVar (out_dvar nat i)) (VInt z)) with s''.
      set (ix := PV (fresh k) (VInfo k Integer None) (open_index (DBound (c, c))) (VInt z) c).
      assert (Hix : static_ok (S k) ix) by (repeat split; simpl; auto; try lia; discriminate).
      assert (HL' : Forall (static_ok (S k)) (ix :: L)).
      { constructor; [exact Hix |]; apply Forall_impl with (P := static_ok k); auto.
        intros p Hp; apply (static_mono k); auto. }
      assert (Kin : forall v, below c v -> consistent v -> keyv v <> keyv i).
      { intros v Hb Hcv Kk; apply keyv_inj in Kk; [| exact Hcv | reflexivity]; subst v; unfold i in Hb; simpl in Hb; lia. }
      set (d0 := Dual 0 0).
      assert (Hbd : aeval (duals reals) (bD (VInt z)) = Some (VReal (nth jn xs d0))).
      { pose proof (eval_map_nth _ 0 _ _ jn d0 Hxs Hjn) as E; cbv beta in E; rewrite Z.add_0_l in E; exact E. }
      assert (Hctx : actx (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar
                       (live_anf (S k) (bW (VInfo k Integer None))) (tbr cv Replay (S k) (bA (fresh k))) Real).
      { constructor.
        - apply sctx_scalar.
          + exact HL'.
          + intros p q [<- | Hp] [<- | Hq] E; auto;
              try (destruct (static_in _ _ _ HL Hq) as [_ [Hq' _]]; simpl in E; lia);
              try (destruct (static_in _ _ _ HL Hp) as [_ [Hp' _]]; simpl in E; lia).
            exact (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
          + intros p [<- | Hp]; simpl; [lia |]; pose proof (s_num _ _ _ _ _ _ _ Hs _ Hp); lia.
          + intros a0 E; injection E as <-; exists o; split; [reflexivity | split; [right; exact HoL |]].
            destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [? [E [_ Hg]]]; injection E as <-; exact Hg.
        - intros p [<- | Hp]; [reflexivity | exact (Hbar p Hp)].
        - intros p [<- | Hp] Ht.
          + unfold s''; rewrite store_get_set_same; reflexivity.
          + assert (Hlb : live_anf (S k) (bW (VInfo k Integer None)) p)
              by exact (tbr_occurs (ix :: L) (S k) (bP ix) (bA (fresh k)) (bW (VInfo k Integer None)) Replay p
                          (H10 ix (pa ix)) (H7 ix (pw ix)) HL' (or_intror Hp) (or_introl Ht)).
            destruct (Hlive_b p Hp Hlb) as [Hl' Hpn].
            pose proof (s_num _ _ _ _ _ _ _ Hs _ Hp) as Hpc.
            assert (Hbp : below c (stored p)) by (unfold stored; simpl; exact Hpc).
            unfold s''; rewrite store_get_set_other by (apply not_eq_sym, Kin; [exact Hbp | reflexivity]).
            rewrite (K0 (stored p) Hbp eq_refl I).
            exact (Hrd p Hp (Hreads p Hp Ht) Hl' (or_introl I)).
        - intros p [<- | Hp] Hrc; [discriminate |].
          destruct (Htp p Hp Hrc) as [lt Hlt]; destruct (T0 _ _ Hlt) as [l' Hl'].
          exists l'; unfold s''; rewrite store_get_set_other; [exact Hl' |].
          intros Kk; apply keyv_inj in Kk; [discriminate | reflexivity | reflexivity].
        - intros o0 E; discriminate. }
      specialize (IHb ix (ix :: L) (S k) (S c) s'' (Some (AVar o)) PScalar Replay (bA (fresh k))
                    (bW (VInfo k Integer None)) (bT (open_index (DBound (c, c)))) (bD (VInt z)) Real (VReal (nth jn xs d0))
                    (DAt (DVar (BarOf n)) (DVar i)) vo
                    (H10 ix _) (H7 ix _) (H4 ix _) (H1 ix _) Hctx I HtB Hbd
                    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)).
      lazymatch type of IHb with context [@open_pairs ?A ?t (S c)] =>
        assert (E : @open_pairs A t (S c) = ((fb, rb), c2)) by exact Hob; rewrite E in IHb; clear E end.
      destruct IHb as [_ [_ [s1 [R1 [F1 [T1 [_ Hrev]]]]]]].
      cbn [inplace owner option_map sweep_eqb] in F1, Hrev.
      assert (Hnb : forall v, ~ is_tape v -> below (S c) v -> consistent v -> store_get s1 (keyv v) = store_get s'' (keyv v))
        by (intros v Ht Hb Hcv; exact (F1 v Hb Hcv Ht ltac:(discriminate) ltac:(discriminate))).
      assert (Hns : forall v, below c v -> consistent v -> store_get s'' (keyv v) = store_get s (keyv v))
        by (intros v Hb Hcv; unfold s''; apply store_get_set_other; apply not_eq_sym, Kin; assumption).
      assert (B1 : barv s1 n = Some (VArray yb)).
      { unfold barv; etransitivity; [apply Hnb; [simpl; tauto | unfold n; simpl; lia | reflexivity] |].
        etransitivity; [apply Hns; [unfold n; simpl; exact Hj | reflexivity] |]; exact B0. }
      assert (I1 : store_get s1 (keyv i) = Some (VInt z)).
      { etransitivity; [apply Hnb; [simpl; tauto | unfold i; simpl; lia | reflexivity] |]; unfold s''; apply store_get_set_same. }
      assert (Hyj : xev s1 (DAt (DVar (BarOf n)) (DVar i)) = Some (VReal (nth jn yb 0))).
      { etransitivity; [exact (xev_at s1 (BarOf n) i yb z B1 I1) |]; unfold z; rewrite (nth_z_of_nat yb jn 0) by lia; reflexivity. }
      assert (Hown_b : forall t m, In (t, m) O' -> barv s1 m = barv s m).
      { intros t m Hi; apply odel_in in Hi as [Hi _].
        destruct (r_below _ _ _ _ _ _ _ Hr t m Hi) as [jm [-> Hjm]]; unfold barv.
        etransitivity; [apply Hnb; [simpl; tauto | simpl; lia | reflexivity] |].
        apply Hns; [simpl; lia | reflexivity]. }
      assert (Ts1 : tapes_kept s2 s1).
      { apply (tapes_kept_trans _ s); [exact T0 |].
        apply (tapes_kept_trans _ s''); [unfold s''; apply tapes_kept_set; [simpl; tauto | reflexivity] | exact T1]. }
      assert (Hr1 : rctx (ix :: L) (S c) (Some (AVar o)) PScalar O' (useful cv Replay (S k) (bA (fresh k))) s1).
      { constructor.
        - exact Hnd'.
        - intros t m Hi; rewrite (Hown_b t m Hi); exact (S0 t m Hi).
        - intros t m Hi; apply odel_in in Hi as [Hi _].
          destruct (r_below _ _ _ _ _ _ _ Hr t m Hi) as [jm [E Hjm]]; exists jm; split; [exact E | lia].
        - intros p [<- | Hp] Hu Hv; [discriminate |].
          apply odel_in; split; [exact (r_useful _ _ _ _ _ _ _ Hr p Hp (Hflows p Hp Hu) Hv) |].
          assert (Hlb : live_anf (S k) (bW (VInfo k Integer None)) p)
            by exact (tbr_occurs (ix :: L) (S k) (bP ix) (bA (fresh k)) (bW (VInfo k Integer None)) Replay p
                        (H10 ix (pa ix)) (H7 ix (pw ix)) HL' (or_intror Hp) (or_intror Hu)).
          destruct (Hlive_b p Hp Hlb) as [_ Hpn]; intros E; apply Hpn; unfold stored, n in E; congruence.
        - intros p t [<- | Hp] Hu Hin.
          + apply odel_in in Hin as [Hin _].
            destruct (r_below _ _ _ _ _ _ _ Hr _ _ Hin) as [jm [E Hjm]]; unfold stored in E; simpl in E.
            injection E as E1 _; lia.
          + exact (r_value _ _ _ _ _ _ _ Hr p t Hp (Hflows p Hp Hu) (proj1 (proj1 (odel_in O n t (stored p)) Hin))).
        - intros o0 E; discriminate.
        - intros p ny0 r0 [<- | Hp] Hv; [discriminate | exact (r_args _ _ _ _ _ _ _ Hr p ny0 r0 Hp Hv)].
        - exact (r_written _ _ _ _ _ _ _ Hr). }
      assert (Hseed : seed_ok (S c) Real (DAt (DVar (BarOf n)) (DVar i)) s1).
      { split; [| intros _; exists (nth jn yb 0); exact Hyj].
        intros y Hy; simpl in Hy; destruct Hy as [<- | [<- | []]]; split; unfold n, i; simpl; try lia; reflexivity. }
      assert (Htp1 : tapes_ok (ix :: L) s1).
      { intros p [<- | Hp] Hrc; [discriminate |].
        destruct (Htp p Hp Hrc) as [lt Hlt]; exact (Ts1 _ _ Hlt). }
      destruct (Hrev s1 O' (fun _ _ _ _ => eq_refl) Hr1 Hseed Htp1) as [s3 [R3 [_ [_ [T3 [F3 [S3 P3]]]]]]].
      exists s3; split.
      { unfold body; simpl app; rewrite run_app, R1; exact R3. }
      assert (Hp3 : forall v, below c v -> consistent v -> ~ is_tape v -> (forall m, v = BarOf m -> ~ In m (map snd O')) ->
                     store_get s3 (keyv v) = store_get s (keyv v)).
      { intros v Hb Hcv Ht Hbo.
        rewrite (F3 v (below_mono c (S c) v Hb ltac:(lia)) Hcv Ht ltac:(discriminate) Hbo).
        rewrite (Hnb v Ht (below_mono c (S c) v Hb ltac:(lia)) Hcv); exact (Hns v Hb Hcv). }
      split.
      { intros v Hb Hcv Hpv; rewrite (Hp3 v Hb Hcv ltac:(destruct v; simpl in Hpv |- *; tauto)
                                    ltac:(intros m0 E; subst v; destruct Hpv)).
        exact (K0 v Hb Hcv Hpv). }
      split; [exact (tapes_kept_trans _ _ _ Ts1 T3) |].
      split; [intros v Hb Hcv Ht Hex Hbo; rewrite (Hp3 v Hb Hcv Ht Hbo); exact (F0 v Hb Hcv Ht Hex Hbo) |].
      split.
      { unfold barv; etransitivity; [apply Hp3; [unfold n; simpl; exact Hj | reflexivity | simpl; tauto |] |].
        - intros m0 E; injection E as <-; exact HnO'.
        - exact B0. }
      split; [exact S3 |].
      rewrite P3; unfold result_pairing, seed_value; rewrite Hyj.
      rewrite (pairing_ext_own O' s1 s Hown_b), P0.
      rewrite (skipn_nth_cons (map dsnd xs) jn (dsnd d0)) by (rewrite length_map; lia).
      rewrite (skipn_nth_cons yb jn 0) by lia.
      rewrite dotr_cons, map_nth; ring.
    - split; [intros; reflexivity |].
      split; [apply tapes_kept_refl |].
      split; [intros ? ? ? ? ? ?; reflexivity |].
      split; [exact Eyb |].
      split; [intros t m Hi; apply odel_in in Hi as [Hi _]; exact (r_shape _ _ _ _ _ _ _ Hr t m Hi) |].
      rewrite !skipn_all2 by (rewrite ?length_map; lia); unfold dotr; simpl; ring. }
  destruct Hloop as [sf [Hex [K [T [F [B [Sh Pf]]]]]]].
  exists sf; split.
  { rewrite (run_forback _ _ _ _ _ _ 0 h) by reflexivity.
    assert (Hdown : exec_down R (run body) (out_dvar nat i) (h - 1) N s2 = Some sf).
    { destruct (Nat.eq_dec N 0) as [E0 | Hn0].
      - rewrite E0 in Hex |- *; exact Hex.
      - replace (h - 1)%Z with (Z.of_nat N - 1)%Z by (unfold N in *; rewrite count_nat in *; lia); exact Hex. }
    lazymatch goal with |- match ?r with _ => _ end = _ => replace r with (Some sf) by (symmetry; exact Hdown) end; reflexivity. }
  assert (Eput : oput O n (tangent (VArray xs)) = oset O n (tangent (VArray xs))).
  { unfold oput; destruct (in_dec dvar_eq_dec_c n (map snd O)) as [_ | Hni]; [reflexivity |].
    destruct Hni; apply in_map_iff; eexists; split; [| exact HoO]; reflexivity. }
  rewrite Eput.
  split; [intros v Hb0 Hc0 Hp0 _; exact (K v Hb0 Hc0 Hp0) |].
  split; [intros _ _ o0 _ _; exact (K n ltac:(unfold n; simpl; exact Hj) eq_refl I) |].
  split; [exact T |].
  split.
  { unfold inplace; rewrite Hown; change (Some (stored o)) with (Some n).
    apply (rev_frame_mono c c _ _ _ _ _ F (le_n c)); intros m Hm; left; rewrite oset_snd; exact (proj1 (odel_snd O n m Hm)). }
  split.
  { intros t m Hi; destruct (dvar_eq_dec_c m n) as [-> | Hne].
    - rewrite B; pose proof (r_shape _ _ _ _ _ _ _ Hr t n Hi) as Hs0; rewrite Eyb in Hs0; exact Hs0.
    - exact (Sh t m (proj2 (odel_in O n t m) (conj Hi Hne))). }
  rewrite (pairing_odel O n _ sf Hnd HoO), (pairing_oset O s2 _ n _ Hok Hnd HoO), (pairing_odel O n _ s2 Hnd HoO).
  fold O'; rewrite Pf, B, Eyb, !inner_tangent_zero by exact Hzl.
  simpl; ring.
Qed.

(* Bodies of straight lets and branches: an assignment is in no branch. *)
Fixpoint branchy (top : bool) (b : anf pv bare) : Prop :=
  match b with
  | ALet _ e b' => branchy_value top e /\ forall x, branchy top (b' x)
  | ARet _ => True
  end
with branchy_value (top : bool) (e : value pv bare) : Prop :=
  match e with
  | AOp1 _ _ | AOp2 _ _ _ | AGet _ _ => True
  | ASet _ _ _ => top = true
  | AIte _ t e => branchy false t /\ branchy false e
  | _ => False
  end.

Theorem asim_branchy :
  (forall b : anf pv bare, forall top, branchy top b ->
     asim_body cv b /\ act_body b /\ (top = false -> psim_body b)) /\
  (forall e : value pv bare, forall top, branchy_value top e ->
     asim_fwd cv e /\ asim_rev cv e /\ inplace_only e /\ act_value e /\ act_owner e /\
     (top = false -> forall wP tail, storage wP tail e = None)).
Proof.
  apply (anf_value_ind pv bare
           (fun b => forall top, branchy top b -> asim_body cv b /\ act_body b /\ (top = false -> psim_body b))
           (fun e => forall top, branchy_value top e ->
              asim_fwd cv e /\ asim_rev cv e /\ inplace_only e /\ act_value e /\ act_owner e /\
              (top = false -> forall wP tail, storage wP tail e = None))).
  - intros a e IHe b IHb top [He Hb].
    destruct (IHe top He) as [Hf [Hr [Hi [Ha [Ho Hst]]]]].
    split; [apply asim_let; auto; intros x; exact (proj1 (IHb x top (Hb x))) |].
    split; [apply act_let; auto; intros x; exact (proj1 (proj2 (IHb x top (Hb x)))) |].
    intros Et; apply psim_let; [exact Hf | exact Ha | exact (Hst Et) |].
    intros x; exact (proj2 (proj2 (IHb x top (Hb x))) Et).
  - intros x top _; split; [apply asim_ret | split; [apply act_ret | intros _; apply psim_ret]].
  - intros f x top _; split; [apply afwd_op1 |].
    split; [apply asim_rev_bars; [apply arev_op1 | apply straight_rev_bars; exact I] |].
    split; [apply inplace_straight; exact I |].
    split; [apply act_op1 | split; [apply owner_op1 | intros _ wP tail; reflexivity]].
  - intros f x y top _; split; [apply afwd_op2 |].
    split; [apply asim_rev_bars; [apply arev_op2 | apply straight_rev_bars; exact I] |].
    split; [apply inplace_straight; exact I |].
    split; [apply act_op2 | split; [apply owner_op2 | intros _ wP tail; reflexivity]].
  - intros x i top _; split; [apply afwd_get |].
    split; [apply asim_rev_bars; [apply arev_get | apply straight_rev_bars; exact I] |].
    split; [apply inplace_straight; exact I |].
    split; [apply act_get | split; [apply owner_get | intros _ wP tail; reflexivity]].
  - intros x i y top Et; simpl in Et; subst top; split; [apply afwd_set |].
    split; [apply asim_rev_bars; [apply arev_set | apply straight_rev_bars; exact I] |].
    split; [apply inplace_straight; exact I |].
    split; [apply act_set | split; [apply owner_set | discriminate]].
  - intros c t IHt e IHe top [Ht He].
    destruct (IHt false Ht) as [At [Ct Pt]], (IHe false He) as [Ae [Ce Pe]].
    split; [apply afwd_ite; auto |].
    split; [apply arev_ite; auto |].
    split; [apply inplace_ite |].
    split; [apply act_ite; auto | split; [apply owner_ite | intros _ wP tail; reflexivity]].
  - intros lo hi b _ top [].
  - intros a lo hi init b _ top [].
Qed.

End Branch.
