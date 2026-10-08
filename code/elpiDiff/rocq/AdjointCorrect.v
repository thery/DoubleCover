(* AdjointCorrect.v — the adjoint modes: the transposition.

   Running the program `adjoint cv (annotate cv (normalize f))` over the reals
   computes, in its reverse sweep, the transpose of the derivative that the
   dual numbers compute in any direction. The proof relates the adjoint
   program to the dual evaluation of the source in a direction dx (the pv
   instance of TangentCorrect.v, whose dual values carry the tangents in that
   direction), and follows the sum, over the storages that carry an adjoint,
   of the tangent of the variable they hold times its adjoint: the pairing.
   Transposing a let `x = e` moves the adjoint of x to the operands of e
   weighted by the partial derivatives, which keeps the pairing, since the
   tangent of x is the same combination of the tangents of the operands.

   This file: the operations, the pairing. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Scoping
  AnfEquiv Correctness TangentCorrect.

Import ListNotations.
Open Scope R_scope.

(* ---------------------------------------------------------------------------
   The operations: the tangent of a dual operation is linear in the tangents
   of its operands, with the partial derivatives the adjoint spells as
   coefficients. *)

Lemma dual_op1_linear f x dx y dy :
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) ->
  exists A, dy = A * dx /\ forall d, exists t, dual_op1 R reals f (Dual x d) = Some (Dual y t) /\ t = A * d.
Proof.
  intros Hd; unfold dual_op1 in Hd |- *.
  destruct (dom_op1 reals f x) as [y0 |] eqn:E1; [| discriminate].
  destruct (dual_partial1 R reals f x y0) as [p |] eqn:E2; [| discriminate].
  simpl in Hd; injection Hd as <- <-; exists p; split; [reflexivity |].
  intros d; exists (p * d); split; reflexivity.
Qed.

Lemma dual_op2_linear f x dx y dy z dz :
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z dz) ->
  exists A B, dz = A * dx + B * dy /\
    forall d e, exists t, dual_op2 R reals f (Dual x d) (Dual y e) = Some (Dual z t) /\ t = A * d + B * e.
Proof.
  intros Hd; destruct f; unfold_ops Hd; try discriminate; injection Hd as <- <-.
  - exists 1, 1; split; [ring | intros d e; eexists; split; [reflexivity | simpl; ring]].
  - exists 1, (-1); split; [ring | intros d e; eexists; split; [reflexivity | simpl; ring]].
  - exists y, x; split; [ring | intros d e; eexists; split; [reflexivity | simpl; ring]].
  - exists (/ y), (- (x / y / y)); split; [unfold Rdiv; ring |].
    intros d e; eexists; split; [reflexivity | simpl; unfold Rdiv; ring].
Qed.

(* The contribution of an operand of an operation of one argument, applied to
   the adjoint e of its result: the derivative times e. *)
Lemma adjoint_op1 s f (a : atom (tvar W)) e x dx y dy p be :
  xev s (spell a) = Some (VReal x) -> xev s e = Some (VReal be) ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) -> partial1 f a = Some p ->
  exists A, dy = A * dx /\ xev s (scale (spell_partial p) e) = Some (VReal (A * be)).
Proof.
  intros Ha He Hd Hp.
  destruct (dual_op1_linear _ _ _ _ _ Hd) as [A [-> HA]]; exists A; split; [reflexivity |].
  destruct (HA be) as [t [Ht ->]].
  exact (proj2 (tangent_op1 s f a e x be y _ p Ha He Ht Hp)).
Qed.

(* The contributions of the two operands of an operation of two arguments. *)
Lemma adjoint_op2 s f (a b : atom (tvar W)) e x dx y dy z dz pa pb be :
  xev s (spell a) = Some (VReal x) -> xev s (spell b) = Some (VReal y) -> xev s e = Some (VReal be) ->
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z dz) -> partial2 f a b = Some (pa, pb) ->
  exists A B, dz = A * dx + B * dy /\
    xev s (scale (spell_partial pa) e) = Some (VReal (A * be)) /\
    xev s (scale (spell_partial pb) e) = Some (VReal (B * be)).
Proof.
  intros Ha Hb He Hd Hp.
  destruct f; unfold_ops Hd; unfold_ops Hp; try discriminate; injection Hp as <- <-;
    injection Hd as <- <-; cbn [spell_partial].
  - exists 1, 1; split; [ring |].
    split; apply (xev_scale s); auto; rewrite xev_DReal, lit_1; reflexivity.
  - exists 1, (-1); split; [ring |].
    split; apply (xev_scale s); auto; rewrite xev_DReal; [rewrite lit_1 | rewrite lit_m1]; reflexivity.
  - exists y, x; split; [ring |]; split; apply (xev_scale s); auto.
  - exists (1 / y), (- (x / (y * y))); split; [unfold Rdiv; rewrite Rinv_mult; ring |].
    split; apply (xev_scale s); auto.
    + rewrite xev_DOp2, xev_DReal, lit_1, Hb; reflexivity.
    + rewrite xev_DOp1, xev_DOp2, Ha, xev_DOp2, Hb; reflexivity.
Qed.

(* A partial derivative that is a constant does not read its operand. *)
Definition pmentions {V : Type} (p : pexpr V) : Prop := match p with PNum _ => False | _ => True end.

Lemma adjoint_op1_gen s f (a : atom (tvar W)) e x dx y dy p be :
  partial1 f a = Some p -> xev s e = Some (VReal be) ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) ->
  (pmentions p -> xev s (spell a) = Some (VReal x)) ->
  exists A, dy = A * dx /\ xev s (scale (spell_partial p) e) = Some (VReal (A * be)).
Proof.
  intros Hp He Hd Ha.
  destruct p as [| l | |]; try (apply (adjoint_op1 s f a e x dx y dy); auto; apply Ha; exact I).
  destruct f as [| | | | | | z |]; simpl in Hp; try discriminate; try (destruct z; discriminate);
    [| destruct z; try discriminate]; injection Hp as <-; unfold_ops Hd; simpl.
  - rewrite lit_m1 in Hd; injection Hd as _ <-; exists (-1); split; [reflexivity |].
    rewrite xev_DOp1, He; simpl; f_equal; f_equal; ring.
  - rewrite lit_0 in Hd; injection Hd as _ <-; exists 0; split; [reflexivity |].
    rewrite xev_DOp2, xev_DReal, lit_0, He; reflexivity.
Qed.

(* The reverse sweep of a unary operation reads its operand when the partial
   derivative mentions it. *)
Lemma reads_op1 f (a : tvar W) (b : avar) p :
  partial1 f (AVar a) = Some p -> pmentions p -> avaried b = true ->
  atom_member (AVar b) (read_by (AVar b) (partial1 f (AVar b))) = true.
Proof.
  intros Hp Hm Hb; unfold read_by; simpl; rewrite Hb.
  destruct f as [| | | | | | z |]; simpl in Hp |- *; try discriminate;
    try (destruct z; simpl in Hp |- *); try (injection Hp as <-; contradiction);
    rewrite ?atom_member_union; simpl; rewrite ?Nat.eqb_refl; simpl; rewrite ?orb_true_r; reflexivity.
Qed.

(* The partial derivatives of the arithmetic operations, at (x, y). *)
Definition coef_a (f : binary) (x y : R) : R :=
  match f with Add | Sub => 1 | Mul => y | Divide => 1 / y | _ => 0 end.
Definition coef_b (f : binary) (x y : R) : R :=
  match f with Add => 1 | Sub => -1 | Mul => x | Divide => - (x / (y * y)) | _ => 0 end.

Lemma dual_op2_coef f x dx y dy z dz :
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z dz) ->
  dz = coef_a f x y * dx + coef_b f x y * dy.
Proof.
  intros Hd; destruct f; unfold_ops Hd; try discriminate; injection Hd as _ <-; simpl;
    unfold Rdiv; rewrite ?Rinv_mult; ring.
Qed.

(* The contribution to the first operand reads the second one (Mul, Divide). *)
Lemma contrib_a s f (a b : atom (tvar W)) e x y be pa pb :
  partial2 f a b = Some (pa, pb) -> xev s e = Some (VReal be) ->
  ((f = Mul \/ f = Divide) -> xev s (spell b) = Some (VReal y)) ->
  xev s (scale (spell_partial pa) e) = Some (VReal (coef_a f x y * be)).
Proof.
  intros Hp He Hb; destruct f; simpl in Hp; try discriminate; injection Hp as <- <-; cbn [spell_partial coef_a];
    (apply xev_scale; [| exact He]).
  - rewrite xev_DReal, lit_1; reflexivity.
  - rewrite xev_DReal, lit_1; reflexivity.
  - apply Hb; auto.
  - rewrite xev_DOp2, xev_DReal, lit_1, Hb; auto.
Qed.

(* The contribution to the second operand reads the first one (Mul, Divide)
   and the second one (Divide). *)
Lemma contrib_b s f (a b : atom (tvar W)) e x y be pa pb :
  partial2 f a b = Some (pa, pb) -> xev s e = Some (VReal be) ->
  ((f = Mul \/ f = Divide) -> xev s (spell a) = Some (VReal x)) ->
  (f = Divide -> xev s (spell b) = Some (VReal y)) ->
  xev s (scale (spell_partial pb) e) = Some (VReal (coef_b f x y * be)).
Proof.
  intros Hp He Ha Hb; destruct f; simpl in Hp; try discriminate; injection Hp as <- <-; cbn [spell_partial coef_b];
    (apply xev_scale; [| exact He]).
  - rewrite xev_DReal, lit_1; reflexivity.
  - rewrite xev_DReal, lit_m1; reflexivity.
  - apply Ha; auto.
  - rewrite xev_DOp1, xev_DOp2, Ha, xev_DOp2, Hb; auto.
Qed.

(* The primal part of a dual operation is the operation of the reals. *)
Lemma primal_eval_op1 f va ve :
  eval_op1 (duals reals) f va = Some ve -> eval_op1 reals f (primal va) = Some (primal ve).
Proof.
  destruct va as [[x dx] | | | |]; simpl; try discriminate.
  destruct (real_op1 f x) as [y |] eqn:E; simpl; [| discriminate].
  destruct (dual_partial1 R reals f x y); simpl; [| discriminate].
  intros H; injection H as <-; reflexivity.
Qed.

Lemma primal_eval_op2 f va vb ve :
  eval_op2 (duals reals) f va vb = Some ve -> eval_op2 reals f (primal va) (primal vb) = Some (primal ve).
Proof.
  destruct va as [[x dx] | za | | |], vb as [[y dy] | zb | | |]; simpl; try discriminate.
  - destruct (comparison f).
    + unfold dual_cmp; simpl; destruct (real_cmp f x y); simpl; [| discriminate].
      intros H; injection H as <-; reflexivity.
    + destruct f; simpl; try discriminate; intros H; injection H as <-; reflexivity.
  - intros H; injection H as <-; destruct f; reflexivity.
Qed.

(* The value of an atom whose variable holds its value. *)
Lemma aspell_ok k s (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p /\ store_get s (keyv (stored p)) = Some (primal (pd p))) ->
  aeval_atom (duals reals) (amap pd aP) = Some d ->
  xev s (spell (amap pt aP)) = Some (primal d).
Proof.
  intros Hs Hd; destruct aP as [q | str | z].
  - simpl in Hd; injection Hd as <-; destruct (Hs q eq_refl) as [Hst H].
    destruct Hst as [_ [_ [Hstore _]]]; unfold xev; simpl; rewrite Hstore; exact H.
  - apply aeval_literal in Hd as [x [Hx ->]]; simpl; rewrite xev_DReal, Hx; reflexivity.
  - simpl in Hd; injection Hd as <-; reflexivity.
Qed.

(* Sets of atoms. *)
Lemma same_term_trans a b c : same_term a b = true -> same_term b c = true -> same_term a c = true.
Proof.
  destruct a, b, c; simpl; try discriminate; intros H1 H2.
  apply Nat.eqb_eq in H1, H2; apply Nat.eqb_eq; congruence.
Qed.

Lemma same_term_sym a b : same_term a b = same_term b a.
Proof. destruct a, b; simpl; auto; apply Nat.eqb_sym. Qed.

Lemma atom_member_union x l l' :
  atom_member x (atom_union l l') = atom_member x l || atom_member x l'.
Proof.
  revert l; induction l' as [| y ys IH]; intros l; simpl; [rewrite orb_false_r; reflexivity |].
  destruct (atom_member y l) eqn:Ey; rewrite IH; simpl.
  - destruct (same_term x y) eqn:Exy; simpl; [| reflexivity].
    unfold atom_member in Ey |- *; apply existsb_exists in Ey as [z [Iz Ez]].
    replace (existsb (same_term x) l) with true; [reflexivity |].
    symmetry; apply existsb_exists; exists z; split; [exact Iz | eapply same_term_trans; eauto].
  - destruct (same_term x y), (atom_member x l), (atom_member x ys); reflexivity.
Qed.

Lemma atom_member_var q : atom_member (AVar q) [AVar q] = true.
Proof. simpl; rewrite Nat.eqb_refl; reflexivity. Qed.

Lemma atom_member_atoms q (a : atom avar) l :
  In a l -> a = AVar q -> atom_member (AVar q) (atoms_of_atoms l) = true.
Proof.
  intros Hi ->; induction l as [| b l IH]; simpl in Hi |- *; [contradiction |].
  rewrite atom_member_union; destruct Hi as [-> | Hi].
  - simpl; rewrite Nat.eqb_refl; reflexivity.
  - rewrite IH; auto; apply orb_true_r.
Qed.

(* ---------------------------------------------------------------------------
   The pairing: for each storage that carries an adjoint, the tangent of the
   variable it holds (a value of the reals: a real, or an array) times its
   adjoint in the store. *)

Definition barv (s : store R) (n : dvar W) : option (val R) := store_get s (keyv (BarOf n)).

Definition dotr (a b : list R) : R := fold_right Rplus 0 (map (fun '(p, q) => p * q) (combine a b)).

Definition inner (t : val R) (b : option (val R)) : R :=
  match t, b with
  | VReal x, Some (VReal y) => x * y
  | VArray l, Some (VArray m) => dotr l m
  | _, _ => 0
  end.

(* The adjoint has the shape of the tangent. *)
Definition shaped (t : val R) (b : option (val R)) : Prop :=
  match t, b with
  | VReal _, Some (VReal _) => True
  | VArray l, Some (VArray m) => length l = length m
  | _, _ => False
  end.

Definition owners := list (val R * dvar W).

Lemma dvar_eq_dec_c (a b : dvar W) : {a = b} + {a <> b}.
Proof. decide equality; decide equality; apply Nat.eq_dec. Qed.

Definition pairing (O : owners) (s : store R) : R :=
  fold_right (fun '(t, n) acc => inner t (barv s n) + acc) 0 O.

(* The storage n now holds a variable of tangent t. *)
Definition oset (O : owners) (n : dvar W) (t : val R) : owners :=
  map (fun '(t', n') => if Simplify.dvar_eq nat n n' then (t, n') else (t', n')) O.

(* The storage n now holds a variable of tangent t: it replaces the tangent of
   the owner of n, or n becomes an owner. *)
Definition oput (O : owners) (n : dvar W) (t : val R) : owners :=
  if in_dec dvar_eq_dec_c n (map snd O) then oset O n t else (t, n) :: O.

(* The storages of owners are variables opened by open_pairs. *)
Definition owners_ok (O : owners) : Prop := forall t n, In (t, n) O -> consistent n.

Lemma barv_set_other s n n' w :
  consistent n -> consistent n' -> n <> n' ->
  barv (store_set s (keyv (BarOf n)) w) n' = barv s n'.
Proof.
  intros Hn Hn' E; unfold barv; apply store_get_set_other.
  intros K; apply keyv_inj in K; simpl; auto; injection K; auto.
Qed.

Lemma barv_set_same s n w : barv (store_set s (keyv (BarOf n)) w) n = Some w.
Proof. apply store_get_set_same. Qed.

Lemma pairing_set_other O s n w :
  owners_ok O -> consistent n -> ~ In n (map snd O) ->
  pairing O (store_set s (keyv (BarOf n)) w) = pairing O s.
Proof.
  induction O as [| [t n'] O IH]; intros Ho Hn Hi; simpl; [reflexivity |].
  rewrite barv_set_other, IH; auto.
  - intros t' m I; apply (Ho t'); right; exact I.
  - intros I; apply Hi; right; exact I.
  - apply (Ho t); left; reflexivity.
  - intros ->; apply Hi; left; reflexivity.
Qed.

Lemma pairing_set_in O s t n w :
  owners_ok O -> NoDup (map snd O) -> In (t, n) O ->
  pairing O (store_set s (keyv (BarOf n)) w) = pairing O s - inner t (barv s n) + inner t (Some w).
Proof.
  induction O as [| [t' n'] O IH]; intros Ho Hd Hi; simpl in Hi |- *; [contradiction |].
  inversion Hd as [| ? ? Hn Hd']; subst.
  assert (Ho' : owners_ok O) by (intros t0 m I; apply (Ho t0); right; exact I).
  destruct Hi as [E | Hi].
  - injection E as <- <-; rewrite barv_set_same, pairing_set_other; auto; [ring |].
    apply (Ho t'); left; reflexivity.
  - rewrite barv_set_other, IH; auto; [ring | apply (Ho t); right; exact Hi | apply (Ho t'); left; reflexivity |].
    intros <-; apply Hn, in_map_iff; exists (t, n); auto.
Qed.

Lemma dvar_eq_consistent a b : consistent a -> consistent b -> Simplify.dvar_eq nat a b = true <-> a = b.
Proof.
  revert b; induction a as [[i j] | a IH | a IH | a IH |]; intros [[i' j'] | b | b | b |] Ha Hb;
    simpl in *; split; intros E; try discriminate; try reflexivity; try (inversion E; fail).
  - apply Nat.eqb_eq in E; subst; reflexivity.
  - injection E as -> ->; subst; apply Nat.eqb_refl.
  - f_equal; apply IH; auto.
  - injection E as <-; apply IH; auto.
  - f_equal; apply IH; auto.
  - injection E as <-; apply IH; auto.
  - f_equal; apply IH; auto.
  - injection E as <-; apply IH; auto.
Qed.

(* Replacing the tangent of a storage that is not an owner. *)
Lemma oset_notin O n t : owners_ok O -> consistent n -> ~ In n (map snd O) -> oset O n t = O.
Proof.
  induction O as [| [t' n'] O IH]; intros Ho Hn Hi; simpl; [reflexivity |].
  destruct (Simplify.dvar_eq nat n n') eqn:E.
  - apply dvar_eq_consistent in E; [subst; destruct Hi; left; reflexivity | exact Hn | apply (Ho t'); left; auto].
  - f_equal; apply IH; auto; [intros t0 m I; apply (Ho t0); right; exact I | intros I; apply Hi; right; exact I].
Qed.

(* Replacing the tangent of an owner by the one it has. *)
Lemma oset_same O n t :
  owners_ok O -> NoDup (map snd O) -> In (t, n) O -> oset O n t = O.
Proof.
  induction O as [| [t' n'] O IH]; intros Ho Hd Hi; simpl in Hi |- *; [reflexivity |].
  inversion Hd as [| ? ? Hn Hd']; subst.
  assert (Ho' : owners_ok O) by (intros t0 m I; apply (Ho t0); right; exact I).
  assert (Hcn : consistent n) by (apply (Ho t); exact Hi).
  assert (Hcn' : consistent n') by (apply (Ho t'); left; reflexivity).
  destruct Hi as [E | Hi].
  - injection E as -> ->; rewrite (proj2 (dvar_eq_consistent n n Hcn Hcn) eq_refl).
    f_equal; apply oset_notin; auto.
  - destruct (Simplify.dvar_eq nat n n') eqn:E.
    + apply dvar_eq_consistent in E; auto; subst; destruct Hn; apply in_map_iff; exists (t, n'); auto.
    + f_equal; apply IH; auto.
Qed.

(* ---------------------------------------------------------------------------
   What the analyses say of a variable in scope, for a body transposed in
   sweep m: its adjoint is useful (U of needs) or its value is read by the
   adjoint code (L of needs). *)

Definition useful (cv : bool) (m : sweep) (k : nat) (b : anf avar bare) (p : pv) : Prop :=
  atom_member (AVar (pa p)) (fst (needs cv m k b)) = true.

Definition tbr (cv : bool) (m : sweep) (k : nat) (b : anf avar bare) (p : pv) : Prop :=
  atom_member (AVar (pa p)) (snd (needs cv m k b)) = true.

(* The context of the forward sweep: the static facts of the tangent
   simulation (sctx, for the variables that occur, live); the variables whose
   value the adjoint code reads (tbr) hold it in the store; a variable carries
   an adjoint when it is varied; a recorded storage has a tape. *)
Record actx (L : list pv) (k c : nat) (s : store R) (wP : option (atom pv)) (pp : pplace)
  (live tb : pv -> Prop) (ty : ty) : Prop := {
  a_sctx : sctx L k c wP pp live ty;
  a_bar : forall p, In p L -> tbar (pt p) = avaried (pa p);
  a_store : forall p, In p L -> tb p -> store_get s (keyv (stored p)) = Some (primal (pd p));
  a_tape : forall p, In p L -> trecorded (pt p) = true ->
             exists l, store_get s (keyv (TapeOf (stored p))) = Some (VTape l)
}.

(* The keys of the store. A primal key holds a value of the program; a bar,
   an adjoint; a tape, recorded values. *)
Definition is_tape (v : dvar W) : Prop := match v with TapeOf _ => True | _ => False end.
Definition is_bar (v : dvar W) : Prop := match v with BarOf _ => True | _ => False end.
Definition is_primal (v : dvar W) : Prop := match v with DBound _ | ResultVar => True | _ => False end.

(* Where adjoint-value leaves the value of the function: the returned value,
   or the written argument when it is dependent (a real is assigned at the end
   of the forward sweep, an array is updated in place). *)
Definition vo_target (vo : option (aresult (tvar W))) : option (dvar W) :=
  match vo with
  | Some (AReturns _) => Some ResultVar
  | Some (AWrites y) =>
      match role_of W y, tof y with
      | Some Dependent, (Real | Array _) => Some (stored_of W y)
      | _, _ => None
      end
  | None => None
  end.

(* The forward sweep leaves the keys opened before c unchanged, but the
   tapes, the storage updated in place, and the target of the value. *)
Definition fwd_frame (c : nat) (ex : option (dvar W)) (vo : option (aresult (tvar W))) (s s' : store R) : Prop :=
  forall v, below c v -> consistent v -> ~ is_tape v -> ex <> Some v -> vo_target vo <> Some v ->
  store_get s' (keyv v) = store_get s (keyv v).

(* The reverse sweep leaves the keys opened before c unchanged, but the
   tapes, the storage updated in place, and the adjoints of the owners. *)
Definition rev_frame (c : nat) (ex : option (dvar W)) (O : owners) (s s' : store R) : Prop :=
  forall v, below c v -> consistent v -> ~ is_tape v -> ex <> Some v ->
  (forall n, v = BarOf n -> ~ In n (map snd O)) ->
  store_get s' (keyv v) = store_get s (keyv v).

(* Between the end of the forward sweep of a body and the start of its
   reverse sweep, the primal keys opened before c' keep their values, but the
   storage updated in place. *)
Definition agree_prim (c' : nat) (ex : option (dvar W)) (s1 s2 : store R) : Prop :=
  forall v, below c' v -> consistent v -> is_primal v -> ex <> Some v ->
  store_get s2 (keyv v) = store_get s1 (keyv v).

(* The owners at the start of the reverse sweep of a body: distinct
   storages, opened before c, whose adjoints have the shape of their tangent;
   every useful varied variable in scope is an owner, with its tangent; the
   storage updated in place is an owner. *)
Record rctx (L : list pv) (c : nat) (wP : option (atom pv)) (pp : pplace) (O : owners)
  (use : pv -> Prop) (s : store R) : Prop := {
  r_nodup : NoDup (map snd O);
  r_shape : forall t n, In (t, n) O -> shaped t (barv s n);
  r_below : forall t n, In (t, n) O -> exists j, n = DBound (j, j) /\ (j < c)%nat;
  r_useful : forall p, In p L -> use p -> avaried (pa p) = true -> In (tangent (pd p), stored p) O;
  r_value : forall p t, In p L -> use p -> In (t, stored p) O -> t = tangent (pd p);
  r_owner : forall o, owner wP pp = Some o -> exists t, In (t, stored o) O
}.

(* The seed: read from keys opened before c, a real for a real body. *)
Definition seed_ok (c : nat) (ty : ty) (se : dexpr W) (s : store R) : Prop :=
  (forall x, In x (dvars se) -> below c x /\ consistent x) /\
  (ty = Real -> exists b, xev s se = Some (VReal b)).

Definition seed_value (se : dexpr W) (s : store R) : R :=
  match xev s se with Some (VReal b) => b | _ => 0 end.

(* What the reverse sweep of a body of type ty, of dual value v, adds to the
   pairing: the tangent of a real result times the seed; for an array, left
   in the storage updated in place, its tangent replaces the one of the
   storage. *)
Definition result_pairing (O : owners) (ty : ty) (ex : option (dvar W)) (v : val (dual R))
  (se : dexpr W) (s : store R) : R :=
  match ty, ex, v with
  | Array _, Some n, _ => pairing (oset O n (tangent v)) s
  | Real, _, VReal d => pairing O s + dsnd d * seed_value se s
  | _, _, _ => pairing O s
  end.

(* What adjoint-value stores at the end of the forward sweep. *)
Definition vo_result (vo : option (aresult (tvar W))) (v : val (dual R)) (s : store R) : Prop :=
  forall t, vo_target vo = Some t -> store_get s (keyv t) = Some (primal v).

Section Sim.
Variable cv : bool.                               (* computes-value: mode adjoint-value *)

(* The simulation of a body, transposed in sweep m with the seed se: its
   forward sweep, run from a store holding the values the adjoint code reads,
   leaves the variables in scope unchanged (but the storage updated in place)
   and, at the top of adjoint-value, stores the value; then its reverse sweep,
   run from any store that agrees with the end of the forward sweep on the
   primal keys, changes the pairing of the owners in scope as the tangent of
   the body times the seed. *)
Definition asim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m bA bW bT bD ty v se vo,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  actx L k c s wP pp (live_anf k bW) (tbr cv m k bA) ty -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  (m = Forward -> pp = PTop /\ (vo = None <-> cv = false) /\
                  forall y, vo = Some (AWrites y) -> option_map (amap pt) wP = Some y) ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo m (rebuild _ bT (annotate_body_t cv m k bA)) se) c in
  (c <= c')%nat /\
  exists s1, run fw s = Some s1 /\
    fwd_frame c (inplace wP pp) (if sweep_eqb m Forward then vo else None) s s1 /\
    (m = Forward -> vo_result vo v s1) /\
    forall s2 O, agree_prim c' (inplace wP pp) s1 s2 -> rctx L c wP pp O (useful cv m k bA) s2 ->
      seed_ok c ty se s2 ->
      exists s3, run rv s2 = Some s3 /\ rev_frame c (inplace wP pp) O s2 s3 /\
        (forall t n, In (t, n) O -> shaped t (barv s3 n)) /\
        pairing O s3 = result_pairing O ty (inplace wP pp) v se s2.

Lemma rctx_owners_ok L c wP pp O use s : rctx L c wP pp O use s -> owners_ok O.
Proof. intros Hr t n Hi; destruct (r_below _ _ _ _ _ _ _ Hr t n Hi) as [j [-> _]]; reflexivity. Qed.

(* Writing the adjoint of an owner with a value of its shape keeps the shapes. *)
Lemma shaped_set O s t n w :
  owners_ok O -> (forall t' n', In (t', n') O -> shaped t' (barv s n')) -> In (t, n) O ->
  (forall t', In (t', n) O -> shaped t' (Some w)) ->
  forall t' n', In (t', n') O -> shaped t' (barv (store_set s (keyv (BarOf n)) w) n').
Proof.
  intros Ho Hs Hi Hw t' n' Hi'.
  destruct (dvar_eq_dec_c n n') as [<- | E].
  - rewrite barv_set_same; apply Hw; exact Hi'.
  - rewrite barv_set_other; auto; [apply (Ho t); exact Hi | apply (Ho t'); exact Hi'].
Qed.

(* The reverse sweep writes only the adjoint of an owner. *)
Lemma rev_frame_set c ex O s n w :
  In n (map snd O) -> consistent n -> rev_frame c ex O s (store_set s (keyv (BarOf n)) w).
Proof.
  intros Hn Hcn v _ Hcv _ _ Hb; apply store_get_set_other; intros K.
  apply keyv_inj in K; [| exact Hcn | exact Hcv]; subst v; exact (Hb n eq_refl Hn).
Qed.

(* The type of a body that returns a variable. *)
Lemma ret_type L k c wP pp live ty p :
  sctx L k c wP pp live ty -> In p L ->
  typecheck (option_map (amap pw) wP) (wplace pp) k (ARet (AVar (pw p))) = (ty, Ok) ->
  ty = vty (pw p) /\ (varg (pw p) = None \/ wP = Some (AVar p) \/ ~ is_array (vty (pw p))).
Proof.
  intros Hs Hp Htc; simpl in Htc.
  destruct (varg (pw p)) as [[nx r] |] eqn:Eg; [| injection Htc; auto].
  destruct (ty_is_array (vty (pw p))) eqn:Ea; simpl in Htc.
  - destruct (option_map (amap pw) wP) as [y |] eqn:Ew; simpl in Htc; [| discriminate].
    destruct wP as [y' |]; [| discriminate]; injection Ew as <-.
    destruct (match amap pw y' with AVar y0 => (vid (pw p) =? vid y0)%nat | _ => false end) eqn:Eid;
      simpl in Htc; [| discriminate].
    injection Htc as ->; split; [reflexivity |].
    right; left; eapply unique_written_s; eauto.
  - injection Htc as <-; split; [reflexivity |]; right; right.
    unfold is_array; destruct (vty (pw p)); simpl in Ea; try discriminate; tauto.
Qed.

Ltac none_case := eexists; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | intros _ ? Et'; discriminate]].

(* The forward sweep of a body that returns an atom: at the top of
   adjoint-value, the value goes where the function leaves it. *)
Lemma ret_forward L k c s wP pp m (aP : atom pv) ty v vo :
  actx L k c s wP pp (live_anf k (ARet (amap pw aP))) (tbr cv m k (ARet (amap pa aP))) ty ->
  (forall p, aP = AVar p -> In p L) ->
  typecheck (option_map (amap pw) wP) (wplace pp) k (ARet (amap pw aP)) = (ty, Ok) -> real_or_array ty ->
  aeval (duals reals) (@ARet _ bare (amap pd aP)) = Some v ->
  (m = Forward -> pp = PTop /\ (vo = None <-> cv = false) /\
                  forall y, vo = Some (AWrites y) -> option_map (amap pt) wP = Some y) ->
  exists s1, run (if sweep_eqb m Forward then value_output W vo (amap pt aP) else []) s = Some s1 /\
    fwd_frame c (inplace wP pp) (if sweep_eqb m Forward then vo else None) s s1 /\
    (m = Forward -> vo_result vo v s1).
Proof.
Proof.
  intros Hc HaL Htc Hty Hev Hvo.
  destruct m; simpl; [| exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | discriminate]]].
  destruct (Hvo eq_refl) as [Epp [Hcv Hy]]; subst pp.
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  assert (Hx : vo <> None -> xev s (spell (amap pt aP)) = Some (primal v)).
  { intros Hn; assert (Ecv : cv = true) by (destruct cv; auto; destruct Hn; apply Hcv; reflexivity).
    destruct aP as [p | str | z]; simpl in Hev |- *.
    - injection Hev as <-.
      destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (HaL p eq_refl)) as [_ [_ [Hst _]]].
      unfold xev; simpl; rewrite Hst.
      apply (a_store _ _ _ _ _ _ _ _ _ Hc _ (HaL p eq_refl)); unfold tbr; subst cv; simpl.
      rewrite Nat.eqb_refl; reflexivity.
    - apply aeval_literal in Hev as [x [Hx ->]]; rewrite xev_DReal, Hx; reflexivity.
    - injection Hev as <-; reflexivity. }
  destruct vo as [[t | y] |].
  - specialize (Hx ltac:(discriminate)).
    exists (store_set s (keyv ResultVar) (primal v)).
    split; [unfold run; simpl; unfold xev in Hx; rewrite Hx; reflexivity |].
    split; [| intros _ t' Et'; simpl in Et'; injection Et' as <-; apply store_get_set_same].
    intros v' _ Hcv' _ _ Hne; apply store_get_set_other; intros K; apply keyv_inj in K; [| exact I | exact Hcv'].
    subst v'; apply Hne; reflexivity.
  - specialize (Hx ltac:(discriminate)); specialize (Hy y eq_refl).
    destruct wP as [yP |]; simpl in Hy; [| discriminate]; injection Hy as <-.
    destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [q [-> [Hq _]]].
    destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq) as [_ [_ [Hsq [Htq _]]]].
    unfold vo_result, vo_target, role_of, stored_of; simpl; rewrite Hsq, Htq.
    destruct (targ (pt q)) as [[nm r] |] eqn:Eg; simpl; [| destruct (vty (pw q)); none_case].
    destruct r; simpl; try (destruct (vty (pw q)); none_case).
    destruct (vty (pw q)) eqn:Evq; try none_case.
    + exists (store_set s (keyv (stored q)) (primal v)).
      split; [unfold run; simpl; unfold xev in Hx; rewrite Hx; reflexivity |].
      split; [| intros _ t' Et'; injection Et' as <-; apply store_get_set_same].
      intros v' _ Hcv' _ _ Hne; apply store_get_set_other; intros K; apply keyv_inj in K; [| reflexivity | exact Hcv'].
      subst v'; apply Hne; unfold vo_target, role_of, stored_of; simpl; rewrite Eg, Hsq, Htq; reflexivity.
    + (* an array, updated in place: the result is in the written argument *)
      exists s; split; [reflexivity |].
      split; [intros ? ? ? ? ? ?; reflexivity |].
      intros _ t' Et'; injection Et' as <-.
      destruct (s_top _ _ _ _ _ _ _ Hs q eq_refl eq_refl ltac:(rewrite Evq; exact I)) as [Ety _].
      rewrite Evq in Ety; subst ty.
      destruct aP as [p | str | z]; simpl in Htc.
      * destruct (ret_type _ _ _ _ _ _ _ _ Hs (HaL p eq_refl) Htc) as [Ep Hcase].
        assert (Hl : live_anf k (ARet (amap pw (AVar p))) p) by (unfold live_anf; simpl; apply Nat.eqb_refl).
        assert (Hpq : pn p = pn q).
        { apply (s_arrays _ _ _ _ _ _ _ Hs p q (HaL p eq_refl) Hl); [rewrite <- Ep; exact I | | simpl; rewrite Evq; reflexivity].
          destruct Hcase as [H1 | [H1 | H1]]; auto; exfalso; apply H1; rewrite <- Ep; exact I. }
        destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (HaL p eq_refl)) as [_ [_ [Hsp _]]].
        unfold xev in Hx; simpl in Hx; rewrite Hsp in Hx; unfold stored in Hx |- *; rewrite <- Hpq; exact Hx.
      * discriminate.
      * discriminate.
  - exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | intros _ t' Et'; discriminate]].
Qed.

Lemma asim_ret (aP : atom pv) : asim_body (ARet aP).
Proof.
  intros L k c s wP pp m bA bW bT bD ty v se vo HA HW HT HD Hc Hty Htc Hev Hvo.
  destruct bA as [| aA], bW as [| aW], bT as [| aT], bD as [| aD]; simpl in HA, HW, HT, HD;
    try contradiction.
  graph HA; graph HW; graph HT; graph HD.
  cbn [annotate_body_t rebuild adj open_pairs].
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  split; [lia |].
  destruct (ret_forward L k c s wP pp m aP ty v vo Hc H Htc Hty Hev Hvo) as [s1 [Hrun1 [Hfr1 Hvr1]]].
  exists s1; split; [exact Hrun1 | split; [exact Hfr1 | split; [exact Hvr1 |]]].
  intros s2 O Hag Hr Hseed.
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  destruct aP as [p | str | z]; simpl in Htc, Hev |- *.
  2:{ apply aeval_literal in Hev as [x [Hx ->]]; injection Htc as <-.
      exists s2; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply (r_shape _ _ _ _ _ _ _ Hr) |]]].
      unfold result_pairing; simpl; ring. }
  2:{ injection Htc as <-; destruct Hty. }
  injection Hev as <-.
  assert (Hp : In p L) by auto.
  destruct (ret_type _ _ _ _ _ _ _ _ Hs Hp Htc) as [-> Hcase].
  assert (Hl : live_anf k (ARet (amap pw (AVar p))) p) by (unfold live_anf; simpl; apply Nat.eqb_refl).
  destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hp) as [_ [_ [Hstore [Hsty [_ [_ [_ [_ [Hht Hz]]]]]]]]].
  rewrite Hstore, Hsty, (a_bar _ _ _ _ _ _ _ _ _ Hc _ Hp).
  assert (Hu : useful cv m k (ARet (AVar (pa p))) p)
    by (unfold useful; simpl; destruct (sweep_eqb m Forward && cv); simpl; rewrite Nat.eqb_refl; reflexivity).
  destruct (vty (pw p)) eqn:Ety; try destruct Hty.
  - destruct (pd p) as [d | | | |] eqn:Ed; try (simpl in Hht; contradiction).
    destruct (avaried (pa p)) eqn:Ev.
    + pose proof (r_useful _ _ _ _ _ _ _ Hr p Hp Hu Ev) as Hin; rewrite Ed in Hin; simpl in Hin.
      pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) as Hsh; simpl in Hsh.
      destruct (barv s2 (stored p)) as [[b0 | | | |] |] eqn:Eb; try contradiction.
      destruct (proj2 Hseed eq_refl) as [sg Hsg].
      exists (store_set s2 (keyv (BarOf (stored p))) (VReal (b0 + sg))).
      split; [unfold run; simpl; unfold barv, keyv in Eb; simpl in Eb; rewrite Eb; unfold xev in Hsg; rewrite Hsg; reflexivity |].
      split; [apply rev_frame_set; [apply in_map_iff; exists (VReal (dsnd d), stored p); auto | reflexivity] |].
      split.
      * apply (shaped_set O s2 (VReal (dsnd d))); auto; [apply (r_shape _ _ _ _ _ _ _ Hr) |].
        intros t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr p t' Hp Hu Ht'), Ed; exact I.
      * rewrite (pairing_set_in O s2 (VReal (dsnd d)) (stored p)); auto; [| apply (r_nodup _ _ _ _ _ _ _ Hr)].
        unfold result_pairing, seed_value; rewrite Hsg, Eb; simpl; ring.
    + exists s2; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply (r_shape _ _ _ _ _ _ _ Hr) |]]].
      specialize (Hz eq_refl); simpl in Hz.
      unfold result_pairing; rewrite Hz; ring.
  - exists s2; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply (r_shape _ _ _ _ _ _ _ Hr) |]]].
    destruct (owner wP pp) as [o |] eqn:Eo; [| destruct (s_ty _ _ _ _ _ _ _ Hs I Eo)].
    assert (Hpo : pn p = pn o).
    { apply (s_arrays _ _ _ _ _ _ _ Hs p o Hp Hl); [rewrite Ety; exact I | | exact Eo].
      destruct Hcase as [Hc1 | [Hc1 | Hc1]]; auto; exfalso; apply Hc1; exact I. }
    destruct (r_owner _ _ _ _ _ _ _ Hr o Eo) as [t Ht].
    assert (Esp : stored p = stored o) by (unfold stored; rewrite Hpo; reflexivity).
    rewrite <- Esp in Ht.
    pose proof (r_value _ _ _ _ _ _ _ Hr p t Hp Hu Ht) as ->.
    unfold result_pairing, inplace; rewrite Eo; simpl; rewrite <- Esp.
    rewrite oset_same; auto; apply (r_nodup _ _ _ _ _ _ _ Hr).
Qed.

(* The variables the reverse sweep of an active value reads, and those its
   adjoint flows to. *)
Definition vreads (k : nat) (e : value avar bare) (p : pv) : Prop :=
  atom_member (AVar (pa p)) (fst (value_needs cv k e)) = true.
Definition vflows (k : nat) (e : value avar bare) (p : pv) : Prop :=
  atom_member (AVar (pa p)) (snd (value_needs cv k e)) = true.
Definition vatoms (k : nat) (e : value avar bare) (p : pv) : Prop :=
  atom_member (AVar (pa p)) (atoms_of_value k e) = true.

(* The forward sweep of a value, computed into the variable n (recorded when
   rec): the value is stored in n. *)
Definition asim_fwd (eP : value pv bare) : Prop :=
  forall L k c s wP pp tail eA eW eT eD te n ve ty m rec,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gT L) eP eT -> value_eq (gD L) eP eD ->
  actx L k c s wP pp (live_value k eW) (vatoms k eA) ty ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  (exists j, n = DBound (j, j) /\ (j < c)%nat) ->
  match storage wP tail eP with
  | Some m0 => n = m0
  | None => forall p, In p L -> stored p <> n
  end ->
  (rec = true -> exists l, store_get s (keyv (TapeOf n)) = Some (VTape l)) ->
  aeval_value (duals reals) eD = Some ve ->
  let '(se, c') :=
    open_pairs (fwd_value W (option_map (amap pt) wP) m (rebuild_value _ eT (annotate_value_t cv k eA)) te n rec) c in
  (c <= c')%nat /\
  exists s1, run se s = Some s1 /\ fwd_frame c (Some n) None s s1 /\
             store_get s1 (keyv n) = Some (primal ve).

(* The reverse sweep of an active value computed into n: run from a store
   holding the values it reads, it moves the adjoint of n to the operands, in
   proportion to the partial derivatives, keeping the pairing: before, n is
   an owner with the tangent of the value; after, it is not, or it holds the
   variable it held before the value (updated in place). *)
Definition asim_rev (eP : value pv bare) : Prop :=
  forall L k c wP pp tail eA eW eT eD te n ve ty vo,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gT L) eP eT -> value_eq (gD L) eP eD ->
  sctx L k c wP pp (live_value k eW) ty ->
  (forall p, In p L -> tbar (pt p) = avaried (pa p)) ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  (exists j, n = DBound (j, j) /\ (j < c)%nat) ->
  match storage wP tail eP with
  | Some m0 => n = m0
  | None => forall p, In p L -> stored p <> n
  end ->
  aeval_value (duals reals) eD = Some ve ->
  varied_value k eA = true ->
  let '(re, c') :=
    open_pairs (rev_value W (option_map (amap pt) wP) vo (rebuild_value _ eT (annotate_value_t cv k eA)) te n) c in
  (c <= c')%nat /\
  forall s2 O,
    (forall p, In p L -> vreads k eA p -> store_get s2 (keyv (stored p)) = Some (primal (pd p))) ->
    rctx L c wP pp O (vflows k eA) s2 ->
    (storage wP tail eP = None -> ~ In n (map snd O)) ->
    shaped (tangent ve) (barv s2 n) ->
    exists s3, run re s2 = Some s3 /\ rev_frame c (inplace wP pp) (oput O n (tangent ve)) s2 s3 /\
      (forall t m, In (t, m) O -> shaped t (barv s3 m)) /\
      pairing O s3 = pairing (oput O n (tangent ve)) s2.

Lemma fwd_frame_set c n vo s w :
  consistent n -> fwd_frame c (Some n) vo s (store_set s (keyv n) w).
Proof.
  intros Hn v _ Hcv _ Hex _; apply store_get_set_other; intros K.
  apply keyv_inj in K; auto; subst; apply Hex; reflexivity.
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

(* An operand of a value, read by its forward sweep, holds its value. *)
Lemma operand_store L k c s wP pp live (eA : value avar bare) ty (aP : atom pv) :
  actx L k c s wP pp live (vatoms k eA) ty ->
  (forall p, aP = AVar p -> In p L /\ vatoms k eA p) ->
  forall p, aP = AVar p -> static_ok k p /\ store_get s (keyv (stored p)) = Some (primal (pd p)).
Proof.
  intros Hc Ha p E; destruct (Ha p E) as [Hp Hv]; split.
  - exact (static_in _ _ _ (s_static _ _ _ _ _ _ _ (a_sctx _ _ _ _ _ _ _ _ _ Hc)) Hp).
  - exact (a_store _ _ _ _ _ _ _ _ _ Hc _ Hp Hv).
Qed.

Lemma afwd_op1 f (aP : atom pv) : asim_fwd (AOp1 f aP).
Proof.
  fwd_intro; simpl in Htc, Hev, Hst |- *; rename f3 into f.
  split; [lia |].
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  assert (Va : forall p, aP = AVar p -> In p L /\ vatoms k (AOp1 f (amap pa aP)) p)
    by (intros p E; split; [auto | subst; unfold vatoms; simpl; rewrite Nat.eqb_refl; reflexivity]).
  assert (Hs := aspell_ok k s aP va (operand_store _ _ _ _ _ _ _ _ _ aP Hc Va) Ha).
  exists (store_set s (keyv (DBound (j, j))) (primal ve)).
  split; [apply run_define; rewrite xev_DOp1, Hs; exact (primal_eval_op1 _ _ _ Hev) |].
  split; [apply fwd_frame_set; reflexivity | apply store_get_set_same].
Qed.

Lemma afwd_op2 f (aP bP : atom pv) : asim_fwd (AOp2 f aP bP).
Proof.
  fwd_intro; simpl in Htc, Hev, Hst |- *; rename f3 into f.
  split; [lia |].
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  destruct (aeval_atom (duals reals) (amap pd bP)) as [vb |] eqn:Hb; [| discriminate].
  assert (Va : forall p, aP = AVar p -> In p L /\ vatoms k (AOp2 f (amap pa aP) (amap pa bP)) p)
    by (intros p E; split; [auto | subst; apply (atom_member_atoms (pa p) (AVar (pa p))); simpl; auto]).
  assert (Vb : forall p, bP = AVar p -> In p L /\ vatoms k (AOp2 f (amap pa aP) (amap pa bP)) p)
    by (intros p E; split; [auto | subst; apply (atom_member_atoms (pa p) (AVar (pa p))); simpl; auto]).
  assert (Hsa := aspell_ok k s aP va (operand_store _ _ _ _ _ _ _ _ _ aP Hc Va) Ha).
  assert (Hsb := aspell_ok k s bP vb (operand_store _ _ _ _ _ _ _ _ _ bP Hc Vb) Hb).
  exists (store_set s (keyv (DBound (j, j))) (primal ve)).
  split; [apply run_define; rewrite xev_DOp2, Hsa, Hsb; exact (primal_eval_op2 _ _ _ _ Hev) |].
  split; [apply fwd_frame_set; reflexivity | apply store_get_set_same].
Qed.

Lemma afwd_get (aP iP : atom pv) : asim_fwd (AGet aP iP).
Proof.
  fwd_intro; simpl in Htc, Hev, Hst |- *.
  split; [lia |].
  destruct (aeval_atom (duals reals) (amap pd aP)) as [[| | | l |] |] eqn:Ha; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |] eqn:Hi; try discriminate.
  destruct (nth_z z l) as [d |] eqn:Ez; [| discriminate]; injection Hev as <-.
  assert (Va : forall p, aP = AVar p -> In p L /\ vatoms k (AGet (amap pa aP) (amap pa iP)) p)
    by (intros p E; split; [auto | subst; apply (atom_member_atoms (pa p) (AVar (pa p))); simpl; auto]).
  assert (Vi : forall p, iP = AVar p -> In p L /\ vatoms k (AGet (amap pa aP) (amap pa iP)) p)
    by (intros p E; split; [auto | subst; apply (atom_member_atoms (pa p) (AVar (pa p))); simpl; auto]).
  assert (Hsa := aspell_ok k s aP _ (operand_store _ _ _ _ _ _ _ _ _ aP Hc Va) Ha).
  assert (Hsi := aspell_ok k s iP _ (operand_store _ _ _ _ _ _ _ _ _ iP Hc Vi) Hi).
  exists (store_set s (keyv (DBound (j, j))) (VReal (dfst d))).
  split; [apply run_define; unfold xev in *; simpl in *; rewrite Hsa, Hsi; simpl; rewrite nth_z_map, Ez; reflexivity |].
  split; [apply fwd_frame_set; reflexivity | apply store_get_set_same].
Qed.

Lemma replace_nth_z_nth {A : Type} k (x : A) l l1 :
  replace_nth_z k x l = Some l1 -> exists y, nth_z k l = Some y.
Proof.
  unfold replace_nth_z, nth_z; destruct (k <? 0)%Z; [discriminate |].
  generalize (Z.to_nat k); clear k; intros k; revert l l1.
  induction k as [| k IH]; intros [| y l] l1; simpl; try discriminate; eauto.
  destruct (replace_nth k x l) as [l2 |] eqn:E; [| discriminate]; intros _; eapply IH; eauto.
Qed.

(* An atom reads primal keys only. *)
Lemma avoid_tape_spell k (aP : atom pv) t :
  (forall p, aP = AVar p -> static_ok k p) -> avoid (keyv (TapeOf t)) (spell (amap pt aP)).
Proof.
  intros H x Hx; destruct aP as [p | |]; simpl in Hx; try contradiction.
  destruct Hx as [<- | []]; destruct (H p eq_refl) as [_ [_ [Hs _]]]; rewrite Hs.
  unfold keyv, stored; simpl; discriminate.
Qed.

Lemma afwd_set (aP iP vP : atom pv) : asim_fwd (ASet aP iP vP).
Proof.
  fwd_intro; simpl in Htc, Hev |- *.
  destruct (aeval_atom (duals reals) (amap pd aP)) as [[| | | l |] |] eqn:Ha; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |] eqn:Hi; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd vP)) as [[[y dy] | | | |] |] eqn:Hv; try discriminate.
  destruct (replace_nth_z z (Dual y dy) l) as [l1 |] eqn:Er; [| discriminate]; injection Hev as <-.
  destruct aP as [q | | ]; simpl in Ha; try (apply aeval_literal in Ha as [? [_ E]]; discriminate); try discriminate.
  injection Ha as Eq; simpl in Hst.
  assert (Va : forall p, AVar q = AVar p -> In p L /\ vatoms k (ASet (AVar (pa q)) (amap pa iP) (amap pa vP)) p)
    by (intros p E; injection E as <-; split; [auto | apply (atom_member_atoms (pa q) (AVar (pa q))); simpl; auto]).
  assert (Vi : forall p, iP = AVar p -> In p L /\ vatoms k (ASet (AVar (pa q)) (amap pa iP) (amap pa vP)) p)
    by (intros p E; split; [auto | subst; apply (atom_member_atoms (pa p) (AVar (pa p))); simpl; auto]).
  assert (Vv : forall p, vP = AVar p -> In p L /\ vatoms k (ASet (AVar (pa q)) (amap pa iP) (amap pa vP)) p)
    by (intros p E; split; [auto | subst; apply (atom_member_atoms (pa p) (AVar (pa p))); simpl; auto]).
  destruct (operand_store _ _ _ _ _ _ _ _ _ _ Hc Va q eq_refl) as [Hsq Hq]; rewrite Eq in Hq.
  assert (Hsi := aspell_ok k s iP _ (operand_store _ _ _ _ _ _ _ _ _ iP Hc Vi) Hi).
  assert (Hsv := aspell_ok k s vP _ (operand_store _ _ _ _ _ _ _ _ _ vP Hc Vv) Hv).
  assert (Hsti : forall p, iP = AVar p -> static_ok k p) by (intros p E; apply (operand_store _ _ _ _ _ _ _ _ _ iP Hc Vi p E)).
  assert (Hstv : forall p, vP = AVar p -> static_ok k p) by (intros p E; apply (operand_store _ _ _ _ _ _ _ _ _ vP Hc Vv p E)).
  rewrite <- Hst in Hq.
  pose proof (replace_nth_z_map dfst z (Dual y dy) l) as Hm; rewrite Er in Hm; simpl in Hm.
  set (s1 := fun s0 => store_set s0 (keyv (DBound (j, j))) (VArray (map dfst l1))).
  assert (Hassign : forall s0, store_get s0 (keyv (DBound (j, j))) = Some (VArray (map dfst l)) ->
            xev s0 (spell (amap pt iP)) = Some (VInt z) -> xev s0 (spell (amap pt vP)) = Some (VReal y) ->
            run [DAssign (DAt (DVar (DBound (j, j))) (spell (amap pt iP))) (spell (amap pt vP))] s0 = Some (s1 s0)).
  { intros s0 G1 G2 G3; unfold run, xev, keyv in *; simpl in *; rewrite G3; simpl; rewrite G1, G2; simpl.
    rewrite Hm; reflexivity. }
  assert (Hframe : forall s0, fwd_frame c (Some (DBound (j, j))) None s0 (s1 s0))
    by (intros s0; apply fwd_frame_set; reflexivity).
  destruct (sweep_eqb m Forward && rec) eqn:Erec; simpl; split; try lia.
  - (* the element overwritten is recorded first *)
    apply andb_true_iff in Erec as [_ Erec]; destruct (Hrec Erec) as [lt Hlt].
    destruct (replace_nth_z_nth _ _ _ _ Er) as [old Hold].
    set (s0 := store_set s (keyv (TapeOf (DBound (j, j)))) (VTape (dfst old :: lt))).
    assert (Hn0 : store_get s0 (keyv (DBound (j, j))) = Some (VArray (map dfst l)))
      by (unfold s0; rewrite store_get_set_other; [exact Hq | unfold keyv; simpl; discriminate]).
    exists (s1 s0); split.
    + change ([DPush (TapeOf (DBound (j, j))) (DAt (DVar (DBound (j, j))) (spell (amap pt iP)));
               DAssign (DAt (DVar (DBound (j, j))) (spell (amap pt iP))) (spell (amap pt vP))])
        with (app [DPush (TapeOf (DBound (j, j))) (DAt (DVar (DBound (j, j))) (spell (amap pt iP)))]
                  [DAssign (DAt (DVar (DBound (j, j))) (spell (amap pt iP))) (spell (amap pt vP))]).
      rewrite run_app.
      replace (run [DPush (TapeOf (DBound (j, j))) (DAt (DVar (DBound (j, j))) (spell (amap pt iP)))] s) with (Some s0).
      * apply Hassign; [exact Hn0 | unfold s0; rewrite xev_set_other; [exact Hsi | apply (avoid_tape_spell k); exact Hsti]
                       | unfold s0; rewrite xev_set_other; [exact Hsv | apply (avoid_tape_spell k); exact Hstv]].
      * unfold run, xev, keyv in *; simpl in *; rewrite Hq, Hsi; simpl; rewrite nth_z_map, Hold; simpl.
        rewrite Hlt; reflexivity.
    + split; [| unfold s1; apply store_get_set_same].
      intros v Hb Hcv Ht Hex Hvo; rewrite (Hframe s0 v Hb Hcv Ht Hex Hvo).
      unfold s0; apply store_get_set_other; intros K; apply keyv_inj in K; [| reflexivity | exact Hcv].
      subst v; apply Ht; exact I.
  - exists (s1 s); split; [apply Hassign; auto | split; [apply Hframe | unfold s1; apply store_get_set_same]].
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

(* An accumulation into a real variable. *)
Lemma run_increment s x e b v :
  store_get s (keyv x) = Some (VReal b) -> xev s e = Some (VReal v) ->
  run [DIncrement (DVar x) e] s = Some (store_set s (keyv x) (VReal (b + v))).
Proof.
  intros H1 H2; unfold run, xev, keyv in *.
  change (map (Simplify.out_dstmt nat) [DIncrement (DVar x) e])
    with [DIncrement (DVar (Simplify.out_dvar nat x)) (Simplify.out_dexpr nat e)].
  cbn [exec_stmts exec]; cbn [xeval]; rewrite H1, H2; reflexivity.
Qed.

(* What the reverse sweep of a binary operation reads. *)
Lemma reads_op2 f (a b : atom avar) (q : avar) :
  comparison f = false -> (f = Mul \/ f = Divide) ->
  ((varied a = true /\ b = AVar q) \/ (varied b = true /\ a = AVar q)) ->
  atom_member (AVar q) (fst (match partial2 f a b with
                             | Some (pa, pb) => (atom_union (read_by a (Some pa)) (read_by b (Some pb)), atoms_of_atoms [a; b])
                             | None => ([], atoms_of_atoms [a; b]) end)) = true.
Proof.
  intros _ Hf Hv; destruct Hf as [-> | ->]; simpl; rewrite atom_member_union; unfold read_by;
    destruct Hv as [[Ha ->] | [Hb ->]]; rewrite ?Ha, ?Hb; simpl;
    repeat (rewrite ?atom_member_union; simpl); rewrite ?Nat.eqb_refl; simpl;
    rewrite ?orb_true_r; try reflexivity;
    destruct (varied a); destruct (varied b); simpl; rewrite ?atom_member_union; simpl;
    rewrite ?Nat.eqb_refl; simpl; rewrite ?orb_true_r; reflexivity.
Qed.

Lemma reads_op2_div (a b : atom avar) (q : avar) :
  varied b = true -> b = AVar q ->
  atom_member (AVar q) (fst (match partial2 Divide a b with
                             | Some (pa, pb) => (atom_union (read_by a (Some pa)) (read_by b (Some pb)), atoms_of_atoms [a; b])
                             | None => ([], atoms_of_atoms [a; b]) end)) = true.
Proof.
  intros Hb ->; simpl; rewrite atom_member_union; unfold read_by; simpl in Hb |- *; rewrite Hb.
  apply orb_true_iff; right; simpl; rewrite !atom_member_union; simpl; rewrite Nat.eqb_refl.
  destruct (atom_member _ (atoms_of_atom a)); simpl; rewrite ?Nat.eqb_refl; reflexivity.
Qed.

(* One contribution, to a varied operand q, an owner of tangent t: its
   adjoint grows by w, the pairing by t * w. *)
Lemma contrib_step c ex O O' s (q : pv) p x t b0 w :
  owners_ok O -> NoDup (map snd O) -> In (VReal t, stored q) O ->
  (forall m, In m (map snd O) -> In m (map snd O')) ->
  (forall t' n', In (t', n') O -> shaped t' (barv s n')) ->
  (forall t', In (t', stored q) O -> t' = VReal t) ->
  tbar (pt q) = true -> tstored (pt q) = stored q ->
  barv s (stored q) = Some (VReal b0) -> xev s (scale (spell_partial p) (DVar x)) = Some (VReal w) ->
  let s' := store_set s (keyv (BarOf (stored q))) (VReal (b0 + w)) in
  run (contribution W (AVar (pt q)) p x) s = Some s' /\
  rev_frame c ex O' s s' /\ (forall t' n', In (t', n') O -> shaped t' (barv s' n')) /\
  pairing O s' = pairing O s + t * w.
Proof.
  intros Hok Hnd Hin Hsub Hsh Huq Hb Hs Eb Ew s'.
  unfold contribution; simpl; rewrite Hb, Hs.
  split; [apply run_increment; [exact Eb | exact Ew] |].
  split; [apply rev_frame_set; [apply Hsub, in_map_iff; exists (VReal t, stored q); auto | apply (Hok (VReal t)); exact Hin] |].
  split.
  - apply (shaped_set O s (VReal t)); auto; intros t' Ht'; rewrite (Huq t' Ht'); exact I.
  - unfold s'; rewrite (pairing_set_in O s (VReal t) (stored q)); auto; rewrite Eb; simpl; ring.
Qed.

Lemma rev_frame_trans c ex O s s1 s2 :
  rev_frame c ex O s s1 -> rev_frame c ex O s1 s2 -> rev_frame c ex O s s2.
Proof. intros F1 F2 v H1 H2 H3 H4 H5; rewrite (F2 v H1 H2 H3 H4 H5); apply F1; auto. Qed.

(* An atom reads primal keys only: writing an adjoint keeps its value. *)
Lemma avoid_bar_spell k (aP : atom pv) t :
  (forall p, aP = AVar p -> static_ok k p) -> avoid (keyv (BarOf t)) (spell (amap pt aP)).
Proof.
  intros H x Hx; destruct aP as [p | |]; simpl in Hx; try contradiction.
  destruct Hx as [<- | []]; destruct (H p eq_refl) as [_ [_ [Hs _]]]; rewrite Hs.
  unfold keyv, stored; simpl; discriminate.
Qed.

Lemma oput_notin O n t : ~ In n (map snd O) -> oput O n t = (t, n) :: O.
Proof. intros H; unfold oput; destruct (in_dec dvar_eq_dec_c n (map snd O)); [contradiction | reflexivity]. Qed.

Lemma arev_op1 f (aP : atom pv) : asim_rev (AOp1 f aP).
Proof.
  rev_intro; simpl in Htc, Hst, Hvr |- *; rename f3 into f.
  split; [lia |]; intros s2 O Hrd Hr Hn Hsh.
  destruct aP as [q | |]; simpl in Hvr; try discriminate.
  assert (Hq : In q L) by auto.
  destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq) as [_ [_ [Hsq _]]].
  cbn [amap aeval_atom aeval_value] in Hev; destruct (pd q) as [[x dx] | | | |] eqn:Eq;
    cbn [eval_op1 dom_op1 duals] in Hev; try discriminate.
  destruct (dual_op1 R reals f (Dual x dx)) as [[y dy] |] eqn:Hd; [| discriminate].
  injection Hev as <-.
  rewrite (oput_notin O _ _ (Hn eq_refl)); cbn [amap] in *.
  simpl in Hsh; destruct (barv s2 (DBound (j, j))) as [[be | | | |] |] eqn:Ebn; try contradiction.
  assert (Hfl : vflows k (AOp1 f (AVar (pa q))) q) by (unfold vflows; simpl; rewrite Nat.eqb_refl; reflexivity).
  pose proof (r_useful _ _ _ _ _ _ _ Hr q Hq Hfl Hvr) as Hin; rewrite Eq in Hin; simpl in Hin.
  pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) as Hshq; simpl in Hshq.
  destruct (barv s2 (stored q)) as [[b0 | | | |] |] eqn:Eb; try contradiction.
  destruct (partial1 f (AVar (pt q))) as [p |] eqn:Hp;
    [| destruct f as [| | | | | | z |]; simpl in Hp; try discriminate; try (destruct z; discriminate);
       unfold_ops Hd; discriminate].
  assert (He : xev s2 (DVar (BarOf (DBound (j, j)))) = Some (VReal be)) by exact Ebn.
  destruct (adjoint_op1_gen s2 f (AVar (pt q)) _ x dx y dy p be Hp He Hd) as [A [Edy Hc]].
  { intros Hm; assert (Hrq : store_get s2 (keyv (stored q)) = Some (primal (pd q))).
    { apply (Hrd q Hq); unfold vreads; simpl; exact (reads_op1 f (pt q) (pa q) p Hp Hm Hvr). }
    rewrite Eq in Hrq; unfold xev; simpl; rewrite Hsq; exact Hrq. }
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  unfold contribution; simpl; rewrite (Hbar q Hq), Hvr, Hsq.
  exists (store_set s2 (keyv (BarOf (stored q))) (VReal (b0 + A * be))).
  split; [apply run_increment; [exact Eb | exact Hc] |].
  split; [apply rev_frame_set; [right; apply in_map_iff; exists (VReal dx, stored q); auto | reflexivity] |].
  split.
  - apply (shaped_set O s2 (VReal dx)); auto; [apply (r_shape _ _ _ _ _ _ _ Hr) |].
    intros t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr q t' Hq Hfl Ht'), Eq; exact I.
  - rewrite (pairing_set_in O s2 (VReal dx) (stored q)); auto; [| apply (r_nodup _ _ _ _ _ _ _ Hr)].
    rewrite Eb, Ebn, Edy; simpl; ring.
Qed.

Lemma rctx_shapes L c wP pp O use s s' :
  rctx L c wP pp O use s -> (forall t n, In (t, n) O -> shaped t (barv s' n)) -> rctx L c wP pp O use s'.
Proof. intros Hr Hs; destruct Hr; constructor; auto. Qed.

(* The contribution to an operand, varied or not. *)
Lemma operand_contrib L k c wP pp ex O O' s (aP : atom pv) p xv x dx w (use : pv -> Prop) :
  Forall (static_ok k) L -> (forall q, aP = AVar q -> In q L /\ use q) -> rctx L c wP pp O use s ->
  (forall q, In q L -> tbar (pt q) = avaried (pa q)) ->
  aeval_atom (duals reals) (amap pd aP) = Some (VReal (Dual x dx)) ->
  (forall m, In m (map snd O) -> In m (map snd O')) ->
  (varied (amap pa aP) = true -> xev s (scale (spell_partial p) (DVar xv)) = Some (VReal w)) ->
  exists s', run (contribution W (amap pt aP) p xv) s = Some s' /\ rev_frame c ex O' s s' /\
    (forall t n, In (t, n) O -> shaped t (barv s' n)) /\ pairing O s' = pairing O s + dx * w /\
    forall e, (forall y, In y (dvars e) -> consistent y /\ forall m, In m (map snd O) -> y <> BarOf m) ->
      xev s' e = xev s e.
Proof.
  intros HL HaL Hr Hbar Ha Hsub Hw.
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  destruct (varied (amap pa aP)) eqn:Ev.
  - destruct aP as [q | |]; simpl in Ev; try discriminate.
    destruct (HaL q eq_refl) as [Hq Hu].
    destruct (static_in _ _ _ HL Hq) as [_ [_ [Hsq _]]].
    simpl in Ha; injection Ha as Eq.
    pose proof (r_useful _ _ _ _ _ _ _ Hr q Hq Hu Ev) as Hin; rewrite Eq in Hin; simpl in Hin.
    pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) as Hsh; simpl in Hsh.
    destruct (barv s (stored q)) as [[b0 | | | |] |] eqn:Eb; try contradiction.
    destruct (contrib_step c ex O O' s q p xv dx b0 w Hok (r_nodup _ _ _ _ _ _ _ Hr) Hin Hsub
                (r_shape _ _ _ _ _ _ _ Hr)
                (fun t' Ht' => eq_trans (r_value _ _ _ _ _ _ _ Hr q t' Hq Hu Ht') (f_equal tangent Eq))
                (eq_trans (Hbar q Hq) Ev) Hsq Eb (Hw eq_refl)) as [R1 [R2 [R3 R4]]].
    eexists; split; [exact R1 | split; [exact R2 | split; [exact R3 | split; [exact R4 |]]]].
    intros e He; apply xev_set_other; intros y Hy K; destruct (He y Hy) as [Hcy Hny].
    apply keyv_inj in K; [| exact Hcy | exact (Hok _ _ Hin)].
    apply (Hny (stored q)); [apply in_map_iff; exists (VReal dx, stored q); auto | exact K].
  - assert (Hz : dx = 0).
    { assert (Hst : forall q, aP = AVar q -> static_ok k q) by (intros q E; apply (static_in _ _ _ HL), HaL, E).
      pose proof (atom_zero k aP _ Hst Ev Ha) as Hz; exact Hz. }
    assert (Hn : bar (amap pt aP) = None).
    { destruct aP as [q | |]; simpl; auto; simpl in Ev; rewrite (Hbar q (proj1 (HaL q eq_refl))), Ev; reflexivity. }
    unfold contribution; rewrite Hn.
    exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply (r_shape _ _ _ _ _ _ _ Hr) |]]].
    split; [rewrite Hz; ring | auto].
Qed.

Lemma arev_op2 f (aP bP : atom pv) : asim_rev (AOp2 f aP bP).
Proof.
  rev_intro; simpl in Htc, Hst, Hvr |- *; rename f3 into f.
  split; [lia |]; intros s2 O Hrd Hr Hn Hsh.
  destruct (comparison f) eqn:Ecmp; [discriminate |].
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  assert (HaL : forall q, aP = AVar q -> In q L) by auto.
  assert (HbL : forall q, bP = AVar q -> In q L) by auto.
  cbn [aeval_value] in Hev.
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  destruct (aeval_atom (duals reals) (amap pd bP)) as [vb |] eqn:Hb; [| discriminate].
  assert (Hnint : forall (rP : atom pv) z, varied (amap pa rP) = true -> aeval_atom (duals reals) (amap pd rP) = Some (VInt z) ->
                    (forall q, rP = AVar q -> In q L) -> False).
  { intros rP z Hv Hd HrL; destruct rP as [q | |]; simpl in Hv; try discriminate.
    simpl in Hd; injection Hd as Ed.
    destruct (static_in _ _ _ HL (HrL q eq_refl)) as [_ [_ [_ [_ [_ [_ [_ [Hra [Hht _]]]]]]]]].
    specialize (Hra Hv); rewrite Ed in Hht; destruct (vty (pw q)); simpl in Hra, Hht; auto. }
  destruct va as [[x dx] | za | | |], vb as [[y dy] | zb | | |]; cbn [eval_op2] in Hev; try discriminate.
  2:{ exfalso; apply orb_true_iff in Hvr as [Hv | Hv]; [exact (Hnint _ _ Hv Ha HaL) | exact (Hnint _ _ Hv Hb HbL)]. }
  rewrite Ecmp in Hev; cbn [dom_op2 duals] in Hev.
  destruct (dual_op2 R reals f (Dual x dx) (Dual y dy)) as [[z dz] |] eqn:Hd; [| discriminate].
  injection Hev as <-.
  rewrite (oput_notin O _ _ (Hn eq_refl)).
  simpl in Hsh; destruct (barv s2 (DBound (j, j))) as [[be | | | |] |] eqn:Ebn; try contradiction.
  destruct (partial2 f (amap pt aP) (amap pt bP)) as [[p1 p2] |] eqn:Hp;
    [| destruct f; simpl in Hp; try discriminate; unfold_ops Hd; discriminate].
  pose proof (dual_op2_coef _ _ _ _ _ _ _ Hd) as Edz.
  assert (Hrq : forall (rP : atom pv), (forall q, rP = AVar q -> In q L) ->
            (forall q, rP = AVar q -> vreads k (AOp2 f (amap pa aP) (amap pa bP)) q) ->
            forall d, aeval_atom (duals reals) (amap pd rP) = Some d -> xev s2 (spell (amap pt rP)) = Some (primal d)).
  { intros rP HrL Hrr d Hdd; apply (aspell_ok k s2 rP d); auto.
    intros q E; split; [exact (static_in _ _ _ HL (HrL q E)) | exact (Hrd q (HrL q E) (Hrr q E))]. }
  assert (Hxa : (f = Mul \/ f = Divide) -> varied (amap pa bP) = true -> xev s2 (spell (amap pt aP)) = Some (VReal x)).
  { intros Hf Hv; refine (Hrq aP HaL _ _ Ha).
    intros q E; unfold vreads; simpl; rewrite Ecmp; apply reads_op2; auto; right; subst; auto. }
  assert (Hyb : ((f = Mul \/ f = Divide) /\ varied (amap pa aP) = true) \/
                (f = Divide /\ varied (amap pa bP) = true) -> xev s2 (spell (amap pt bP)) = Some (VReal y)).
  { intros Hc; refine (Hrq bP HbL _ _ Hb).
    intros q E; unfold vreads; simpl; rewrite Ecmp.
    destruct Hc as [[Hf Hv] | [-> Hv]]; [apply reads_op2; auto; left; subst; auto | apply reads_op2_div; subst; auto]. }
  assert (Hfl : forall (rP : atom pv), (rP = aP \/ rP = bP) -> forall q, rP = AVar q ->
            In q L /\ vflows k (AOp2 f (amap pa aP) (amap pa bP)) q).
  { intros rP Hr0 q E; split; [destruct Hr0; subst; auto |].
    unfold vflows; simpl; rewrite Ecmp.
    destruct (partial2 f (amap pa aP) (amap pa bP)) as [[] |]; simpl; rewrite atom_member_union;
      (destruct Hr0 as [E0 | E0]; rewrite <- E0, E; simpl; rewrite Nat.eqb_refl; simpl; rewrite ?orb_true_r; reflexivity). }
  set (O' := (tangent (VReal (Dual z dz)), DBound (j, j)) :: O).
  assert (Hsub : forall m, In m (map snd O) -> In m (map snd O')) by (intros m Hm; right; exact Hm).
  assert (Hsp : forall (rP : atom pv), (forall q, rP = AVar q -> In q L) -> forall y0, In y0 (dvars (spell (amap pt rP))) ->
            consistent y0 /\ forall m, In m (map snd O) -> y0 <> BarOf m).
  { intros rP HrL y0 Hy; destruct rP as [q | |]; simpl in Hy; try contradiction.
    destruct Hy as [<- | []]; destruct (static_in _ _ _ HL (HrL q eq_refl)) as [_ [_ [Hsq _]]]; rewrite Hsq.
    split; [reflexivity | intros m _; unfold stored; discriminate]. }
  assert (Hbn : forall y0, In y0 (dvars (DVar (BarOf (DBound (j, j))))) ->
            consistent y0 /\ forall m, In m (map snd O) -> y0 <> BarOf m).
  { intros y0 [<- | []]; split; [reflexivity | intros m Hm E; injection E as <-; exact (Hn eq_refl Hm)]. }
  assert (He : xev s2 (DVar (BarOf (DBound (j, j)))) = Some (VReal be)) by exact Ebn.
  destruct (operand_contrib L k c wP pp (inplace wP pp) O O' s2 aP p1 (BarOf (DBound (j, j))) x dx (coef_a f x y * be) _
              HL (Hfl aP (or_introl eq_refl)) Hr Hbar Ha Hsub) as [s' [R1 [F1 [S1 [P1 T1]]]]].
  { intros Hv; apply (contrib_a s2 f _ _ _ x y be p1 p2 Hp He); intros Hf; apply Hyb; left; auto. }
  destruct (operand_contrib L k c wP pp (inplace wP pp) O O' s' bP p2 (BarOf (DBound (j, j))) y dy (coef_b f x y * be) _
              HL (Hfl bP (or_intror eq_refl)) (rctx_shapes _ _ _ _ _ _ _ _ Hr S1) Hbar Hb Hsub) as [s3 [R2 [F2 [S2 [P2 _]]]]].
  { intros Hv; apply (contrib_b s' f _ _ _ x y be p1 p2 Hp).
    - rewrite T1; [exact Ebn | exact Hbn].
    - intros Hf; rewrite T1; [exact (Hxa Hf Hv) | exact (Hsp aP HaL)].
    - intros Hf; rewrite T1; [apply Hyb; right; auto | exact (Hsp bP HbL)]. }
  exists s3; split.
  { rewrite run_app; lazymatch goal with |- match ?r with _ => _ end = _ => replace r with (Some s') by (symmetry; exact R1) end.
    exact R2. }
  split; [exact (rev_frame_trans _ _ _ _ _ _ F1 F2) |].
  split; [exact S2 |].
  rewrite P2, P1; unfold O'; simpl; rewrite Ebn, Edz; ring.
Qed.

End Sim.
