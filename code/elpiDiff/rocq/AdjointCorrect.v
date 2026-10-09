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

Lemma atom_member_remove x y l :
  same_term x y = false -> atom_member y (atom_remove x l) = atom_member y l.
Proof.
  intros H; unfold atom_member, atom_remove; induction l as [| z l IH]; simpl; [reflexivity |].
  destruct (same_term x z) eqn:E; simpl; rewrite IH.
  - destruct (same_term y z) eqn:E'; simpl; [| reflexivity].
    rewrite same_term_sym in E'; pose proof (same_term_trans _ _ _ E E') as T; rewrite T in H; discriminate.
  - reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   The pairing: for each storage that carries an adjoint, the tangent of the
   variable it holds (a value of the reals: a real, or an array) times its
   adjoint in the store. *)

Definition barv (s : store R) (n : dvar W) : option (val R) := store_get s (keyv (BarOf n)).

Definition dotr (a b : list R) : R := fold_right Rplus 0 (map (fun '(p, q) => p * q) (combine a b)).

Lemma dotr_cons a l b m : dotr (a :: l) (b :: m) = a * b + dotr l m.
Proof. reflexivity. Qed.

(* Changing one element of the second vector. *)
Lemma dotr_replace n l m m' lk mk w :
  nth_error l n = Some lk -> nth_error m n = Some mk -> replace_nth n w m = Some m' ->
  dotr l m' = dotr l m + lk * (w - mk).
Proof.
  revert l m m'; induction n as [| n IH]; intros [| a l] [| b m] m' Hl Hm Hr; simpl in *; try discriminate.
  - injection Hl as <-; injection Hm as <-; injection Hr as <-; rewrite !dotr_cons; ring.
  - destruct (replace_nth n w m) as [m1 |] eqn:E; [| discriminate]; injection Hr as <-.
    rewrite !dotr_cons, (IH l m m1 Hl Hm E); ring.
Qed.

Lemma dotr_sym l m : dotr l m = dotr m l.
Proof.
  revert m; induction l as [| a l IH]; intros [| b m]; try reflexivity.
  rewrite !dotr_cons, IH; ring.
Qed.

Lemma replace_nth_nth {A : Type} n (w : A) m m' :
  replace_nth n w m = Some m' -> exists mk, nth_error m n = Some mk /\ nth_error m' n = Some w /\ length m' = length m.
Proof.
  revert m m'; induction n as [| n IH]; intros [| b m] m' Hr; simpl in *; try discriminate.
  - injection Hr as <-; eauto.
  - destruct (replace_nth n w m) as [m1 |] eqn:E; [| discriminate]; injection Hr as <-.
    destruct (IH m m1 E) as [mk [A1 [A2 A3]]]; exists mk; simpl; auto.
Qed.

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
             exists l, store_get s (keyv (TapeOf (stored p))) = Some (VTape l);
  a_owner : forall o, owner wP pp = Some o -> store_get s (keyv (stored o)) = Some (primal (pd o))
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

(* The tapes stay tapes. *)
Definition tapes_kept (s s' : store R) : Prop :=
  forall v l, store_get s (keyv (TapeOf v)) = Some (VTape l) -> exists l', store_get s' (keyv (TapeOf v)) = Some (VTape l').

Lemma tapes_kept_refl s : tapes_kept s s.
Proof. intros v l H; eauto. Qed.

Lemma tapes_kept_trans s s1 s2 : tapes_kept s s1 -> tapes_kept s1 s2 -> tapes_kept s s2.
Proof. intros H1 H2 v l H; destruct (H1 v l H) as [l1 E]; exact (H2 v l1 E). Qed.

(* Writing a key that is not a tape. *)
Lemma tapes_kept_set s x w : ~ is_tape x -> consistent x -> tapes_kept s (store_set s (keyv x) w).
Proof.
  intros Ht Hc v l H; exists l; rewrite store_get_set_other; auto.
  intros K; destruct x as [[i j] | x | x | x |]; unfold keyv in K; simpl in K; try discriminate.
  destruct Ht; exact I.
Qed.

Lemma tapes_kept_set_tape s v0 l0 : tapes_kept s (store_set s (keyv (TapeOf v0)) (VTape l0)).
Proof.
  intros v l H; rewrite store_get_set; destruct (key_eqb (keyv (TapeOf v0)) (keyv (TapeOf v))) eqn:E; eauto.
Qed.

(* The reverse sweep leaves the keys opened before c unchanged, but the
   tapes, the storage updated in place, and the adjoints of the owners. *)
Definition rev_frame (c : nat) (ex : option (dvar W)) (O : owners) (s s' : store R) : Prop :=
  forall v, below c v -> consistent v -> ~ is_tape v -> ex <> Some v ->
  (forall n, v = BarOf n -> ~ In n (map snd O)) ->
  store_get s' (keyv v) = store_get s (keyv v).

(* Between the end of the forward sweep of a body and the start of its
   reverse sweep, the primal keys opened before c' keep their values (the
   reverse sweep of a loop replays the body before transposing it). *)
Definition agree_prim (c' : nat) (ex : option (dvar W)) (s1 s2 : store R) : Prop :=
  forall v, below c' v -> consistent v -> is_primal v ->
  store_get s2 (keyv v) = store_get s1 (keyv v).

(* The owners at the start of the reverse sweep of a body: distinct
   storages, opened before c, whose adjoints have the shape of their tangent;
   every useful varied variable in scope is an owner, with its tangent; the
   storage updated in place is an owner, with the tangent of the variable it
   holds. *)
Record rctx (L : list pv) (c : nat) (wP : option (atom pv)) (pp : pplace) (O : owners)
  (use : pv -> Prop) (s : store R) : Prop := {
  r_nodup : NoDup (map snd O);
  r_shape : forall t n, In (t, n) O -> shaped t (barv s n);
  r_below : forall t n, In (t, n) O -> exists j, n = DBound (j, j) /\ (j < c)%nat;
  r_useful : forall p, In p L -> use p -> avaried (pa p) = true -> In (tangent (pd p), stored p) O;
  r_value : forall p t, In p L -> use p -> In (t, stored p) O -> t = tangent (pd p);
  r_owner : forall o, owner wP pp = Some o -> In (tangent (pd o), stored o) O;
  r_args : forall p ny r, In p L -> varg (pw p) = Some (ny, r) -> avaried (pa p) = varied_role r;
  r_written : forall y, wP = Some (AVar y) -> exists ny r, varg (pw y) = Some (ny, r) /\ written_role r = true
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

(* Code that writes only adjoints: it leaves the other keys unchanged. *)
Definition bar_target (l : dexpr W) : Prop :=
  match l with DVar x => is_bar x | DAt (DVar x) _ => is_bar x | _ => False end.

Definition bar_stmt (st : dstmt W) : Prop :=
  match st with
  | DIncrement l _ | DAssign l _ => bar_target l
  | DDefine _ x _ => is_bar x
  | _ => False
  end.

(* The reverse sweep leaves the value of adjoint-value where it is. *)
Definition vo_kept (vo : option (aresult (tvar W))) (s s' : store R) : Prop :=
  forall t, vo_target vo = Some t -> ~ is_bar t -> store_get s' (keyv t) = store_get s (keyv t).

Lemma keyv_bar_other x v : is_bar x -> ~ is_bar v -> keyv x <> keyv v.
Proof.
  unfold keyv; intros H1 H2 E; injection E as E; destruct x; simpl in H1; try contradiction.
  destruct v as [[? ?] | | | |]; simpl in E; try discriminate; apply H2; exact I.
Qed.

Lemma assign_bar s l w s1 :
  bar_target l -> assign reals s (Simplify.out_dexpr nat l) w = Some s1 ->
  exists x w', is_bar x /\ s1 = store_set s (keyv x) w'.
Proof.
  intros Hb Ha; destruct l as [x | | | a i | |]; simpl in Hb, Ha; try contradiction.
  - injection Ha as <-; exists x, w; auto.
  - destruct a as [x | | | | |]; try contradiction; simpl in Ha.
    repeat match type of Ha with context [match ?e with _ => _ end] => destruct e end; try discriminate.
    injection Ha as <-; eexists x, _; split; [exact Hb | reflexivity].
Qed.

Lemma run_bars ss s s' :
  Forall bar_stmt ss -> run ss s = Some s' -> forall v, ~ is_bar v -> store_get s' (keyv v) = store_get s (keyv v).
Proof.
  revert s; induction ss as [| st ss IH]; intros s Hf Hr v Hv; [injection Hr as <-; reflexivity |].
  inversion Hf as [| ? ? Hst Hf']; subst.
  rewrite run_cons in Hr; destruct (exec reals (Simplify.out_dstmt nat st) s) as [s1 |] eqn:E; [| discriminate].
  rewrite (IH s1 Hf' Hr v Hv).
  destruct st; simpl in Hst; try contradiction; simpl in E;
    repeat match type of E with context [match ?e with _ => _ end] =>
      lazymatch e with assign _ _ _ _ => fail | _ => destruct e end end; try discriminate.
  - injection E as <-; apply store_get_set_other; exact (keyv_bar_other _ _ Hst Hv).
  - destruct (assign_bar _ _ _ _ Hst E) as [xb [wb [Hx ->]]]; apply store_get_set_other; exact (keyv_bar_other _ _ Hx Hv).
  - destruct (assign_bar _ _ _ _ Hst E) as [xb [wb [Hx ->]]]; apply store_get_set_other; exact (keyv_bar_other _ _ Hx Hv).
Qed.

Lemma vo_kept_bars vo ss s s' : Forall bar_stmt ss -> run ss s = Some s' -> vo_kept vo s s'.
Proof. intros Hf Hr t _ Hb; exact (run_bars ss s s' Hf Hr t Hb). Qed.

Lemma vo_kept_refl vo s : vo_kept vo s s.
Proof. intros t _ _; reflexivity. Qed.

Lemma vo_kept_trans vo s s1 s2 : vo_kept vo s s1 -> vo_kept vo s1 s2 -> vo_kept vo s s2.
Proof. intros H1 H2 t E B; rewrite (H2 t E B); exact (H1 t E B). Qed.

Lemma vo_kept_set_bar vo s x w : is_bar x -> vo_kept vo s (store_set s (keyv x) w).
Proof. intros Hx t _ Hb; apply store_get_set_other; exact (keyv_bar_other _ _ Hx Hb). Qed.

Lemma bar_some (a : atom (tvar W)) bx : @bar W a = Some bx -> exists x, bx = DVar x /\ is_bar x.
Proof. destruct a as [y | |]; simpl; try discriminate; destruct (tbar y); intros E; try discriminate; injection E as <-; eexists; split; [reflexivity | exact I]. Qed.

Lemma contribution_bars (a : atom (tvar W)) p x : Forall bar_stmt (contribution W a p x).
Proof.
  unfold contribution; destruct (@bar W a) as [bx |] eqn:E; [| constructor].
  destruct (bar_some a bx E) as [y [-> Hy]]; repeat constructor; exact Hy.
Qed.

(* Adds the clause of the value to the reverse sweep of bar-only code. *)
Lemma keep_add (Q : Prop) vo rv s2 (P : store R -> Prop) :
  Forall bar_stmt rv -> (exists s3, run rv s2 = Some s3 /\ P s3) ->
  exists s3, run rv s2 = Some s3 /\ (Q -> vo_kept vo s2 s3) /\ P s3.
Proof. intros Hf [s3 [R H]]; exists s3; split; [exact R | split; [intros _; exact (vo_kept_bars vo rv s2 s3 Hf R) | exact H]]. Qed.

Section Sim.
Variable cv : bool.                               (* computes-value: mode adjoint-value *)

(* The simulation of a body, transposed in sweep m with the seed se: its
   forward sweep, run from a store holding the values the adjoint code reads,
   leaves the variables in scope unchanged (but the storage updated in place)
   and, at the top of adjoint-value, stores the value; then its reverse sweep,
   run from any store that agrees with the end of the forward sweep on the
   primal keys, changes the pairing of the owners in scope as the tangent of
   the body times the seed. *)
(* Outside the body of an in-place loop, the storage updated in place is
   given back when its owner is varied (an inout array): the forward sweep of
   a body leaves it, or its reverse sweep restores it. A map writes a
   dependent array, which is not varied and which no body reads. *)
Definition not_in_loop (pp : pplace) : Prop := match pp with PArray _ _ => False | _ => True end.

Definition same_ex (pp : pplace) (wP : option (atom pv)) (s s' : store R) : Prop :=
  not_in_loop pp -> forall o, owner wP pp = Some o -> avaried (pa o) = true ->
  store_get s' (keyv (stored o)) = store_get s (keyv (stored o)).

(* The recorded variables in scope have their tapes. *)
Definition tapes_ok (L : list pv) (s : store R) : Prop :=
  forall p, In p L -> trecorded (pt p) = true -> exists l, store_get s (keyv (TapeOf (stored p))) = Some (VTape l).

(* The storage updated in place is a primal key opened before c. *)
Lemma ex_below L k c wP pp live ty e :
  sctx L k c wP pp live ty -> inplace wP pp = Some e -> below c e /\ consistent e /\ is_primal e.
Proof.
  intros Hs He; unfold inplace in He; destruct (owner wP pp) as [o |] eqn:Eo; [| discriminate].
  injection He as <-.
  assert (Ho : In o L).
  { destruct pp as [| | | ix sx]; simpl in Eo; try discriminate.
    - destruct wP as [[y | |] |]; try discriminate; destruct (vty (pw y)); try discriminate; injection Eo as <-.
      destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [y' [E [Hy _]]]; injection E as <-; exact Hy.
    - injection Eo as <-; exact (proj1 (proj2 (s_place _ _ _ _ _ _ _ Hs))). }
  unfold stored; simpl; split; [exact (s_num _ _ _ _ _ _ _ Hs o Ho) | split; [reflexivity | exact I]].
Qed.

(* Outside a loop, a live variable stored in place is the owner, a varied array. *)
Lemma same_ex_read L k c wP pp (live : pv -> Prop) ty p o :
  sctx L k c wP pp live ty -> not_in_loop pp -> owner wP pp = Some o -> In p L -> stored p = stored o -> live p ->
  p = o /\ avaried (pa o) = true.
Proof.
  intros Hs Hl Ho Hp E Hlv.
  assert (Epn : pn p = pn o) by (unfold stored in E; injection E as E; exact E).
  destruct (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Epn) as [Epo | H]; [subst p | contradiction].
  split; [reflexivity |].
  destruct pp as [| | | ix sx]; simpl in Hl, Ho; try discriminate; try contradiction.
  destruct wP as [[y | |] |]; try discriminate.
  destruct (vty (pw y)) eqn:Ey; try discriminate; injection Ho as Eyo; subst y.
  exact (proj2 (s_top _ _ _ _ _ _ _ Hs o eq_refl eq_refl ltac:(rewrite Ey; exact I)) Hlv).
Qed.

(* Bar-only reverse code gives the storage updated in place back. *)
Lemma keep_add2 (Q : Prop) L k c c' wP pp live ty vo rv s s1 s2 (P : store R -> Prop) :
  sctx L k c wP pp live ty -> (c <= c')%nat -> agree_prim c' (inplace wP pp) s1 s2 -> same_ex pp wP s s1 ->
  Forall bar_stmt rv -> (exists s3, run rv s2 = Some s3 /\ P s3) ->
  exists s3, run rv s2 = Some s3 /\ (Q -> vo_kept vo s2 s3) /\ same_ex pp wP s s3 /\
    tapes_kept s2 s3 /\ P s3.
Proof.
  intros Hs Hcc Hag Hsx Hf [s3 [R H]]; exists s3; split; [exact R |].
  split; [intros _; exact (vo_kept_bars vo rv s2 s3 Hf R) |]; split; [| split; [| exact H]].
  2:{ intros v l Hv; exists l; rewrite (run_bars rv s2 s3 Hf R (TapeOf v) ltac:(simpl; tauto)); exact Hv. }
  intros Hl o Ho Hav.
  assert (He : inplace wP pp = Some (stored o)) by (unfold inplace; rewrite Ho; reflexivity).
  destruct (ex_below _ _ _ _ _ _ _ _ Hs He) as [Hb [Hc Hp]].
  rewrite (run_bars rv s2 s3 Hf R (stored o) ltac:(simpl; tauto)).
  rewrite (Hag (stored o) (below_mono c c' _ Hb Hcc) Hc Hp); exact (Hsx Hl o Ho Hav).
Qed.

Definition asim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m bA bW bT bD ty v se vo,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  actx L k c s wP pp (live_anf k bW) (tbr cv m k bA) ty -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  (m = Forward -> pp = PTop /\ (vo = None <-> cv = false) /\
                  (forall y, vo = Some (AWrites y) -> option_map (amap pt) wP = Some y) /\
                  (forall t, vo = Some (AReturns t) -> wP = None)) ->
  (m = Forward -> forall p, In p L -> live_anf k bW p -> vo_target vo <> Some (stored p)) ->
  (m = Forward -> forall t, vo_target vo = Some t -> below c t /\ consistent t /\ is_primal t) ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo m (rebuild _ bT (annotate_body_t cv m k bA)) se) c in
  (c <= c')%nat /\ has_type ty v /\
  exists s1, run fw s = Some s1 /\
    fwd_frame c (inplace wP pp) (if sweep_eqb m Forward then vo else None) s s1 /\ tapes_kept s s1 /\
    (m = Forward -> vo_result vo v s1) /\
    forall s2 O, agree_prim c' (inplace wP pp) s1 s2 -> rctx L c wP pp O (useful cv m k bA) s2 ->
      seed_ok c ty se s2 -> tapes_ok L s2 ->
      exists s3, run rv s2 = Some s3 /\ (m = Forward -> vo_kept vo s2 s3) /\
        same_ex pp wP s s3 /\ tapes_kept s2 s3 /\
        rev_frame c (inplace wP pp) O s2 s3 /\
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

Ltac none_case := eexists; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity |
                     split; [intros _ ? Et'; discriminate | split; [apply tapes_kept_refl | intros _ ? _; reflexivity]]]].

(* The forward sweep of a body that returns an atom: at the top of
   adjoint-value, the value goes where the function leaves it. *)
Lemma ret_forward L k c s wP pp m (aP : atom pv) ty v vo :
  actx L k c s wP pp (live_anf k (ARet (amap pw aP))) (tbr cv m k (ARet (amap pa aP))) ty ->
  (forall p, aP = AVar p -> In p L) ->
  typecheck (option_map (amap pw) wP) (wplace pp) k (ARet (amap pw aP)) = (ty, Ok) -> real_or_array ty ->
  aeval (duals reals) (@ARet _ bare (amap pd aP)) = Some v ->
  (m = Forward -> pp = PTop /\ (vo = None <-> cv = false) /\
                  (forall y, vo = Some (AWrites y) -> option_map (amap pt) wP = Some y) /\
                  (forall t, vo = Some (AReturns t) -> wP = None)) ->
  exists s1, run (if sweep_eqb m Forward then value_output W vo (amap pt aP) else []) s = Some s1 /\
    fwd_frame c (inplace wP pp) (if sweep_eqb m Forward then vo else None) s s1 /\
    (m = Forward -> vo_result vo v s1) /\ tapes_kept s s1 /\ same_ex pp wP s s1.
Proof.
Proof.
  intros Hc HaL Htc Hty Hev Hvo.
  destruct m; simpl; [| exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity |
                                                        split; [discriminate | split; [apply tapes_kept_refl | intros _ o _ _; reflexivity]]]]].
  destruct (Hvo eq_refl) as [Epp [Hcv [Hy _]]]; subst pp.
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
    split; [| split; [intros _ t' Et'; simpl in Et'; injection Et' as <-; apply store_get_set_same
                     | split; [apply tapes_kept_set; [simpl; tauto | exact I] |]]].
    2:{ intros _ o _ _; apply store_get_set_other; unfold keyv, stored; discriminate. }
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
      split; [| split; [intros _ t' Et'; injection Et' as <-; apply store_get_set_same
                       | split; [apply tapes_kept_set; [simpl; tauto | reflexivity] |]]].
      2:{ intros _ o Ho _; simpl in Ho; rewrite Evq in Ho; discriminate. }
      intros v' _ Hcv' _ _ Hne; apply store_get_set_other; intros K; apply keyv_inj in K; [| reflexivity | exact Hcv'].
      subst v'; apply Hne; unfold vo_target, role_of, stored_of; simpl; rewrite Eg, Hsq, Htq; reflexivity.
    + (* an array, updated in place: the result is in the written argument *)
      exists s; split; [reflexivity |].
      split; [intros ? ? ? ? ? ?; reflexivity |].
      split; [| split; [apply tapes_kept_refl | intros _ o _ _; reflexivity]].
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
  - exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity |
                                              split; [intros _ t' Et'; discriminate | split; [apply tapes_kept_refl | intros _ o _ _; reflexivity]]]].
Qed.

Lemma asim_ret (aP : atom pv) : asim_body (ARet aP).
Proof.
  intros L k c s wP pp m bA bW bT bD ty v se vo HA HW HT HD Hc Hty Htc Hev Hvo _.
  destruct bA as [| aA], bW as [| aW], bT as [| aT], bD as [| aD]; simpl in HA, HW, HT, HD;
    try contradiction.
  graph HA; graph HW; graph HT; graph HD.
  cbn [annotate_body_t rebuild adj open_pairs].
  pose proof (a_sctx _ _ _ _ _ _ _ _ _ Hc) as Hs.
  assert (Hhty : has_type ty v).
  { destruct aP as [p | str | z]; simpl in Htc, Hev.
    - injection Hev as <-; destruct (ret_type _ _ _ _ _ _ _ _ Hs (H p eq_refl) Htc) as [-> _].
      destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (H p eq_refl)) as [_ [_ [_ [_ [_ [_ [_ [_ [Hht _]]]]]]]]].
      exact Hht.
    - apply aeval_literal in Hev as [x' [_ ->]]; injection Htc as <-; exact I.
    - injection Htc as <-; destruct Hty. }
  split; [lia | split; [exact Hhty |]].
  destruct (ret_forward L k c s wP pp m aP ty v vo Hc H Htc Hty Hev Hvo) as [s1 [Hrun1 [Hfr1 [Hvr1 [Htk Hsx]]]]].
  exists s1; split; [exact Hrun1 | split; [exact Hfr1 | split; [exact Htk | split; [exact Hvr1 |]]]].
  intros s2 O Hag Hr Hseed _.
  apply (keep_add2 _ L k c c wP pp _ ty vo _ s s1 s2 _ Hs (le_n c) Hag Hsx).
  { destruct (tof (amap pt aP)); try constructor.
    destruct (@bar W (amap pt aP)) as [bx |] eqn:Eb; [| constructor].
    destruct (bar_some _ _ Eb) as [y [-> Hy]]; repeat constructor; exact Hy. }
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
    pose proof (r_owner _ _ _ _ _ _ _ Hr o Eo) as Ht.
    assert (Esp : stored p = stored o) by (unfold stored; rewrite Hpo; reflexivity).
    rewrite <- Esp in Ht.
    pose proof (r_value _ _ _ _ _ _ _ Hr p _ Hp Hu Ht) as Ev.
    unfold result_pairing, inplace; rewrite Eo; simpl; rewrite <- Esp, <- Ev.
    rewrite oset_same; [reflexivity | exact Hok | apply (r_nodup _ _ _ _ _ _ _ Hr) | rewrite Esp; exact (r_owner _ _ _ _ _ _ _ Hr o Eo)].
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
  exists s1, run se s = Some s1 /\ fwd_frame c (Some n) None s s1 /\ tapes_kept s s1 /\
             store_get s1 (keyv n) = Some (primal ve).

(* The reverse sweep of an active value computed into n: run from a store
   holding the values it reads, it moves the adjoint of n to the operands, in
   proportion to the partial derivatives, keeping the pairing: before, n is
   an owner with the tangent of the value; after, it is not, or it holds the
   variable it held before the value (updated in place). *)
(* The reverse sweep of a value, as proved for the operations: it reads the
   scalars it needs. *)
Definition asim_rev0 (eP : value pv bare) : Prop :=
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
    (forall p, In p L -> vreads k eA p -> live_value k eW p -> ~ is_array (vty (pw p)) ->
       store_get s2 (keyv (stored p)) = Some (primal (pd p))) ->
    rctx L c wP pp O (vflows k eA) s2 ->
    (storage wP tail eP = None -> ~ In n (map snd O) /\ shaped (tangent ve) (barv s2 n)) ->
    exists s3, run re s2 = Some s3 /\ rev_frame c (inplace wP pp) (oput O n (tangent ve)) s2 s3 /\
      (forall t m, In (t, m) O -> shaped t (barv s3 m)) /\
      pairing O s3 = pairing (oput O n (tangent ve)) s2.

(* The reverse sweep of a value: it reads the values it needs (arrays too,
   but the storage updated in place inside a loop), and writes no primal key
   opened before it but its own storage. *)
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
    (forall p, In p L -> vreads k eA p -> live_value k eW p ->
       (not_in_loop pp \/ inplace wP pp <> Some (stored p)) ->
       store_get s2 (keyv (stored p)) = Some (primal (pd p))) ->
    rctx L c wP pp O (vflows k eA) s2 ->
    (storage wP tail eP = None -> ~ In n (map snd O) /\ shaped (tangent ve) (barv s2 n)) ->
    tapes_ok L s2 ->
    exists s3, run re s2 = Some s3 /\
      (forall v, below c v -> consistent v -> is_primal v -> v <> n -> store_get s3 (keyv v) = store_get s2 (keyv v)) /\
      (not_in_loop pp -> storage wP tail eP <> None -> forall o, owner wP pp = Some o -> avaried (pa o) = false ->
         store_get s3 (keyv n) = store_get s2 (keyv n)) /\
      tapes_kept s2 s3 /\
      rev_frame c (inplace wP pp) (oput O n (tangent ve)) s2 s3 /\
      (forall t m, In (t, m) O -> shaped t (barv s3 m)) /\
      pairing O s3 = pairing (oput O n (tangent ve)) s2.

(* A value updated in place outside the body of an in-place loop (a map)
   writes an argument that is not inout, and does not read it. *)
Definition inplace_only (eP : value pv bare) : Prop :=
  forall L k wP pp tail eW te, value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  storage wP tail eP <> None -> not_in_loop pp ->
  forall o, owner wP pp = Some o ->
    (forall ny r, varg (pw o) = Some (ny, r) -> r <> Inout) /\ ~ live_value k eW o.

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
  split; [apply fwd_frame_set; reflexivity |
          split; [apply tapes_kept_set; [simpl; tauto | reflexivity] | apply store_get_set_same]].
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
  split; [apply fwd_frame_set; reflexivity |
          split; [apply tapes_kept_set; [simpl; tauto | reflexivity] | apply store_get_set_same]].
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
  split; [apply fwd_frame_set; reflexivity |
          split; [apply tapes_kept_set; [simpl; tauto | reflexivity] | apply store_get_set_same]].
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
    + split; [| split; [apply (tapes_kept_trans _ s0); [apply tapes_kept_set_tape | apply tapes_kept_set; [simpl; tauto | reflexivity]]
                       | unfold s1; apply store_get_set_same]].
      intros v Hb Hcv Ht Hex Hvo; rewrite (Hframe s0 v Hb Hcv Ht Hex Hvo).
      unfold s0; apply store_get_set_other; intros K; apply keyv_inj in K; [| reflexivity | exact Hcv].
      subst v; apply Ht; exact I.
  - exists (s1 s); split; [apply Hassign; auto | split; [apply Hframe |
      split; [apply tapes_kept_set; [simpl; tauto | reflexivity] | unfold s1; apply store_get_set_same]]].
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

(* An accumulation into an element of an array. *)
Lemma run_increment_at s x ei e bm z bk w bm' :
  store_get s (keyv x) = Some (VArray bm) -> xev s ei = Some (VInt z) -> nth_z z bm = Some bk ->
  xev s e = Some (VReal w) -> replace_nth_z z (bk + w) bm = Some bm' ->
  run [DIncrement (DAt (DVar x) ei) e] s = Some (store_set s (keyv x) (VArray bm')).
Proof.
  intros H1 H2 H3 H4 H5; unfold run, xev, keyv in *.
  change (map (Simplify.out_dstmt nat) [DIncrement (DAt (DVar x) ei) e])
    with [DIncrement (DAt (DVar (Simplify.out_dvar nat x)) (Simplify.out_dexpr nat ei)) (Simplify.out_dexpr nat e)].
  cbn [exec_stmts exec]; cbn [xeval]; rewrite H1, H2; cbn; rewrite H3; cbn; rewrite H4; cbn.
  rewrite H1, H2, H5; reflexivity.
Qed.

Lemma nth_z_length {A B : Type} z (l : list A) (m : list B) d :
  nth_z z l = Some d -> length l = length m -> exists e, nth_z z m = Some e.
Proof.
  unfold nth_z; destruct (z <? 0)%Z; [discriminate |]; intros H Hl.
  destruct (nth_error m (Z.to_nat z)) as [e |] eqn:E; [eauto |].
  apply nth_error_None in E; assert (nth_error l (Z.to_nat z) <> None) by congruence.
  apply nth_error_Some in H0; lia.
Qed.

Lemma replace_exists {A : Type} z (m : list A) e w :
  nth_z z m = Some e -> exists m', replace_nth_z z w m = Some m'.
Proof.
  unfold nth_z, replace_nth_z; destruct (z <? 0)%Z; [discriminate |].
  generalize (Z.to_nat z); clear z; intros n; revert m; induction n as [| n IH]; intros [| b m] H; simpl in *;
    try discriminate; eauto.
  destruct (IH m H) as [m' E]; rewrite E; eauto.
Qed.

(* Replacing the tangent of an owner. *)
Lemma pairing_oset O s t n t' :
  owners_ok O -> NoDup (map snd O) -> In (t, n) O ->
  pairing (oset O n t') s = pairing O s - inner t (barv s n) + inner t' (barv s n).
Proof.
  induction O as [| [t0 n0] O IH]; intros Hok Hnd Hin; simpl in Hin |- *; [contradiction |].
  inversion Hnd as [| ? ? Hn Hnd']; subst.
  assert (Hok' : owners_ok O) by (intros t1 m I; apply (Hok t1); right; exact I).
  assert (Hcn : consistent n) by (apply (Hok t); exact Hin).
  assert (Hcn0 : consistent n0) by (apply (Hok t0); left; reflexivity).
  destruct Hin as [E | Hin].
  - injection E as -> ->; rewrite (proj2 (dvar_eq_consistent n n Hcn Hcn) eq_refl); simpl.
    rewrite oset_notin; auto; ring.
  - destruct (Simplify.dvar_eq nat n n0) eqn:E.
    + apply dvar_eq_consistent in E; auto; subst; destruct Hn; apply in_map_iff; exists (t, n0); auto.
    + simpl; rewrite IH; auto; ring.
Qed.

Lemma dotr_zero l m : Forall (fun x => x = 0) m -> dotr l m = 0.
Proof.
  intros H; revert l; induction H as [| x m Hx Hm IH]; intros [| a l]; try reflexivity.
  rewrite dotr_cons, IH, Hx; ring.
Qed.

Lemma oset_snd O n t : map snd (oset O n t) = map snd O.
Proof.
  unfold oset; rewrite map_map; apply map_ext; intros [t' n']; destruct (Simplify.dvar_eq nat n n'); reflexivity.
Qed.

Lemma oput_in O n t : In n (map snd (oput O n t)).
Proof.
  unfold oput; destruct (in_dec dvar_eq_dec_c n (map snd O)) as [I | I]; [rewrite oset_snd; exact I | left; reflexivity].
Qed.

Lemma oput_sub O n t m : In m (map snd O) -> In m (map snd (oput O n t)).
Proof.
  unfold oput; destruct (in_dec dvar_eq_dec_c n (map snd O)); [rewrite oset_snd; auto | intros H; right; exact H].
Qed.

(* A variable that holds a real or an integer is not an array. *)
Lemma not_array_val k p :
  static_ok k p -> (match pd p with VArray _ => False | _ => True end) -> ~ is_array (vty (pw p)).
Proof.
  intros [_ [_ [_ [_ [_ [_ [_ [_ [Hht _]]]]]]]]] Hv Ha.
  destruct (vty (pw p)); try destruct Ha; destruct (pd p); simpl in Hht; auto.
Qed.

Lemma oput_notin O n t : ~ In n (map snd O) -> oput O n t = (t, n) :: O.
Proof. intros H; unfold oput; destruct (in_dec dvar_eq_dec_c n (map snd O)); [contradiction | reflexivity]. Qed.

Lemma arev_op1 f (aP : atom pv) : asim_rev0 (AOp1 f aP).
Proof.
  rev_intro; simpl in Htc, Hst, Hvr |- *; rename f3 into f.
  split; [lia |]; intros s2 O Hrd Hr Hns.
  destruct aP as [q | |]; simpl in Hvr; try discriminate.
  assert (Hq : In q L) by auto.
  destruct (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq) as [_ [_ [Hsq _]]].
  cbn [amap aeval_atom aeval_value] in Hev; destruct (pd q) as [[x dx] | | | |] eqn:Eq;
    cbn [eval_op1 dom_op1 duals] in Hev; try discriminate.
  destruct (dual_op1 R reals f (Dual x dx)) as [[y dy] |] eqn:Hd; [| discriminate].
  injection Hev as <-.
  destruct (Hns eq_refl) as [Hn Hsh].
  rewrite (oput_notin O _ _ Hn); cbn [amap] in *.
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
    { apply (Hrd q Hq); [unfold vreads; simpl; exact (reads_op1 f (pt q) (pa q) p Hp Hm Hvr)
                         | unfold live_value; simpl; apply Nat.eqb_refl
                         | apply (not_array_val k); [exact (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq) | rewrite Eq; exact I]]. }
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

Lemma arev_op2 f (aP bP : atom pv) : asim_rev0 (AOp2 f aP bP).
Proof.
  rev_intro; simpl in Htc, Hst, Hvr |- *; rename f3 into f.
  split; [lia |]; intros s2 O Hrd Hr Hns.
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
  destruct (Hns eq_refl) as [Hn' Hsh].
  rewrite (oput_notin O _ _ Hn').
  simpl in Hsh; destruct (barv s2 (DBound (j, j))) as [[be | | | |] |] eqn:Ebn; try contradiction.
  destruct (partial2 f (amap pt aP) (amap pt bP)) as [[p1 p2] |] eqn:Hp;
    [| destruct f; simpl in Hp; try discriminate; unfold_ops Hd; discriminate].
  pose proof (dual_op2_coef _ _ _ _ _ _ _ Hd) as Edz.
  assert (Hrq : forall (rP : atom pv), (forall q, rP = AVar q -> In q L) -> (rP = aP \/ rP = bP) ->
            (forall q, rP = AVar q -> vreads k (AOp2 f (amap pa aP) (amap pa bP)) q) ->
            forall x' dx', aeval_atom (duals reals) (amap pd rP) = Some (VReal (Dual x' dx')) ->
            xev s2 (spell (amap pt rP)) = Some (VReal x')).
  { intros rP HrL Hab Hrr x' dx' Hdd; refine (aspell_ok k s2 rP _ _ Hdd).
    intros q E; split; [exact (static_in _ _ _ HL (HrL q E)) |].
    apply (Hrd q (HrL q E) (Hrr q E)).
    - unfold live_value; simpl; destruct Hab as [<- | <-]; subst rP; simpl; rewrite Nat.eqb_refl; simpl;
        rewrite ?orb_true_r; reflexivity.
    - apply (not_array_val k); [exact (static_in _ _ _ HL (HrL q E)) |].
      subst rP; simpl in Hdd; injection Hdd as ->; exact I. }
  assert (Hxa : (f = Mul \/ f = Divide) -> varied (amap pa bP) = true -> xev s2 (spell (amap pt aP)) = Some (VReal x)).
  { intros Hf Hv; refine (Hrq aP HaL (or_introl eq_refl) _ _ _ Ha).
    intros q E; unfold vreads; simpl; rewrite Ecmp; apply reads_op2; auto; right; subst; auto. }
  assert (Hyb : ((f = Mul \/ f = Divide) /\ varied (amap pa aP) = true) \/
                (f = Divide /\ varied (amap pa bP) = true) -> xev s2 (spell (amap pt bP)) = Some (VReal y)).
  { intros Hc; refine (Hrq bP HbL (or_intror eq_refl) _ _ _ Hb).
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
  { intros y0 [<- | []]; split; [reflexivity | intros m Hm E; injection E as <-; exact (Hn' Hm)]. }
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

Lemma arev_get (aP iP : atom pv) : asim_rev0 (AGet aP iP).
Proof.
  rev_intro; simpl in Htc, Hst, Hvr |- *.
  split; [lia |]; intros s2 O Hrd Hr Hns.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  destruct aP as [q | |]; simpl in Hvr; try discriminate.
  assert (Hq : In q L) by auto.
  assert (HiL : forall p, iP = AVar p -> In p L) by auto.
  destruct (static_in _ _ _ HL Hq) as [_ [_ [Hsq _]]].
  cbn [aeval_value amap aeval_atom] in Hev.
  destruct (pd q) as [| | | l |] eqn:Eq; try discriminate.
  destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |] eqn:Hi; try discriminate.
  destruct (nth_z z l) as [[x dx] |] eqn:Ez; [| discriminate]; injection Hev as <-.
  destruct (Hns eq_refl) as [Hn Hsh].
  rewrite (oput_notin O _ _ Hn); cbn [amap] in *.
  simpl in Hsh; destruct (barv s2 (DBound (j, j))) as [[be | | | |] |] eqn:Ebn; try contradiction.
  assert (Hfl : vflows k (AGet (AVar (pa q)) (amap pa iP)) q) by (unfold vflows; simpl; rewrite Nat.eqb_refl; reflexivity).
  pose proof (r_useful _ _ _ _ _ _ _ Hr q Hq Hfl Hvr) as Hin; rewrite Eq in Hin; simpl in Hin.
  pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) as Hshq; simpl in Hshq.
  destruct (barv s2 (stored q)) as [[| | | bm |] |] eqn:Eb; try contradiction.
  assert (Hsi : xev s2 (spell (amap pt iP)) = Some (VInt z)).
  { refine (aspell_ok k s2 iP _ _ Hi); intros p E; split; [exact (static_in _ _ _ HL (HiL p E)) |].
    apply (Hrd p (HiL p E)); subst; [unfold vreads; simpl; rewrite Nat.eqb_refl; reflexivity
                                    | unfold live_value; simpl; rewrite Nat.eqb_refl; rewrite ?orb_true_r; reflexivity
                                    | apply (not_array_val k); [exact (static_in _ _ _ HL (HiL p eq_refl)) |];
                                      simpl in Hi; injection Hi as ->; exact I]. }
  pose proof (nth_z_map dsnd z l) as Ezt; rewrite Ez in Ezt; simpl in Ezt.
  rewrite length_map in Hshq.
  destruct (nth_z_length z l bm _ Ez Hshq) as [bk Ebk].
  destruct (replace_exists z bm bk (bk + be) Ebk) as [bm' Ebm'].
  unfold contribution; simpl; rewrite (Hbar q Hq), Hvr, Hsq.
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  exists (store_set s2 (keyv (BarOf (stored q))) (VArray bm')).
  split; [apply (run_increment_at _ _ _ _ bm z bk be); auto |].
  split; [apply rev_frame_set; [right; apply in_map_iff; eexists; split; [| exact Hin]; reflexivity | reflexivity] |].
  assert (Hlen : length bm' = length bm).
  { unfold replace_nth_z in Ebm'; destruct (z <? 0)%Z; [discriminate |].
    destruct (replace_nth_nth _ _ _ _ Ebm') as [_ [_ [_ E]]]; exact E. }
  split.
  - apply (shaped_set O s2 (VArray (map dsnd l))); auto; [apply (r_shape _ _ _ _ _ _ _ Hr) |].
    intros t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr q t' Hq Hfl Ht'), Eq; simpl; rewrite length_map; lia.
  - rewrite (pairing_set_in O s2 (VArray (map dsnd l)) (stored q)); auto; [| apply (r_nodup _ _ _ _ _ _ _ Hr)].
    rewrite Eb, Ebn; simpl.
    unfold nth_z, replace_nth_z in Ezt, Ebk, Ebm'; destruct (z <? 0)%Z; [discriminate |].
    rewrite (dotr_replace _ _ _ _ _ _ _ Ezt Ebk Ebm'); ring.
Qed.

Lemma arev_set (aP iP vP : atom pv) : asim_rev0 (ASet aP iP vP).
Proof.
  rev_intro; simpl in Htc, Hvr |- *.
  split; [lia |]; intros s2 O Hrd Hr Hns.
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  pose proof (r_nodup _ _ _ _ _ _ _ Hr) as Hnd.
  cbn [aeval_value] in Hev.
  destruct (aeval_atom (duals reals) (amap pd aP)) as [[| | | l |] |] eqn:Ha; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |] eqn:Hi; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd vP)) as [[[y dy] | | | |] |] eqn:Hv; try discriminate.
  destruct (replace_nth_z z (Dual y dy) l) as [l1 |] eqn:Er; [| discriminate]; injection Hev as <-.
  destruct aP as [qa | | ]; simpl in Ha; try (apply aeval_literal in Ha as [? [_ E]]; discriminate); try discriminate.
  injection Ha as Eqa; simpl in Hst.
  assert (Hqa : In qa L) by auto.
  assert (HiL : forall p, iP = AVar p -> In p L) by auto.
  assert (HvL : forall p, vP = AVar p -> In p L) by auto.
  repeat match goal with H : forall p : pv, _ = AVar p -> In p L |- _ =>
    lazymatch H with HiL => fail | HvL => fail | _ => clear H end end.
  assert (Hsi : xev s2 (spell (amap pt iP)) = Some (VInt z)).
  { refine (aspell_ok k s2 iP _ _ Hi); intros p E; split; [exact (static_in _ _ _ HL (HiL p E)) |].
    apply (Hrd p (HiL p E)); subst; [unfold vreads; simpl; rewrite Nat.eqb_refl; reflexivity
                                    | unfold live_value; simpl; rewrite Nat.eqb_refl; rewrite ?orb_true_r; reflexivity
                                    | apply (not_array_val k); [exact (static_in _ _ _ HL (HiL p eq_refl)) |];
                                      simpl in Hi; injection Hi as ->; exact I]. }
  pose proof (replace_nth_z_map dsnd z (Dual y dy) l) as Ert; rewrite Er in Ert; simpl in Ert.
  assert (Hown : owner wP pp = Some qa).
  { destruct pp as [| | | ix sx]; simpl in Htc; try discriminate.
    destruct (vty (pw qa)); try discriminate.
    destruct (vid (pw qa) =? vid (pw sx))%nat eqn:E; [| rewrite andb_false_r in Htc; simpl in Htc; discriminate].
    pose proof (s_place _ _ _ _ _ _ _ Hs) as [_ [Hsx _]].
    rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs Hqa Hsx E); reflexivity. }
  pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ (r_owner _ _ _ _ _ _ _ Hr qa Hown)) as Hsh.
  rewrite Eqa, <- Hst in Hsh; simpl in Hsh.
  destruct (barv s2 (DBound (j, j))) as [[| | | bn |] |] eqn:Ebn; try contradiction.
  rewrite length_map, <- (replace_nth_z_length _ _ _ _ Er) in Hsh.
  rewrite Hst in *.
  unfold replace_nth_z in Er, Ert; destruct (z <? 0)%Z eqn:Ez0; [discriminate |].
  destruct (replace_nth_nth _ _ _ _ Ert) as [ta_z [Etz [_ Elen]]].
  pose proof (replace_nth_length _ _ _ _ Er) as Elen1.
  destruct (nth_error bn (Z.to_nat z)) as [bk |] eqn:Ebk.
  2:{ exfalso; apply nth_error_None in Ebk.
      assert (Hne : nth_error (map dsnd l) (Z.to_nat z) <> None) by congruence.
      apply nth_error_Some in Hne; rewrite length_map in Hne; lia. }
  destruct (replace_exists z bn bk 0) as [bn0 Ebn0]; [unfold nth_z; rewrite Ez0; exact Ebk |].
  set (ei := spell (amap pt iP)) in *.
  set (n := stored qa) in *.
  assert (Hcn : consistent n) by (rewrite <- Hst; reflexivity).
  assert (Helem : forall s, barv s n = Some (VArray bn) -> xev s ei = Some (VInt z) ->
                    xev s (DAt (DVar (BarOf n)) ei) = Some (VReal bk)).
  { intros s0 G1 G2; unfold xev, barv, keyv in *; simpl in *; rewrite G1, G2; unfold nth_z; rewrite Ez0; simpl; rewrite Ebk; reflexivity. }
  assert (Hzero : forall s, barv s n = Some (VArray bn) -> xev s ei = Some (VInt z) ->
                    run [DAssign (DAt (DVar (BarOf n)) ei) (DReal "0")] s = Some (store_set s (keyv (BarOf n)) (VArray bn0))).
  { intros s0 G1 G2; apply (run_assign_at s0 (BarOf n) ei (DReal "0") bn z 0 bn0 G1 G2); [rewrite xev_DReal, lit_0; reflexivity | exact Ebn0]. }
  assert (Hdot0 : dotr (map dsnd l) bn0 = dotr (map dsnd l) bn + ta_z * (0 - bk)).
  { apply (dotr_replace _ _ _ _ _ _ _ Etz Ebk); unfold replace_nth_z in Ebn0; rewrite Ez0 in Ebn0; exact Ebn0. }
  assert (Hdot1 : dotr (map dsnd l1) bn = dotr (map dsnd l) bn + bk * (dy - ta_z)).
  { rewrite (dotr_sym (map dsnd l1)), (dotr_sym (map dsnd l)); exact (dotr_replace _ _ _ _ _ _ _ Ebk Etz Ert). }
  assert (Hfla : vflows k (ASet (amap pa (AVar qa)) (amap pa iP) (amap pa vP)) qa)
    by (unfold vflows; cbn [value_needs fst snd atoms_of_atoms atoms_of_atom amap];
        rewrite atom_member_union, atom_member_var; reflexivity).
  assert (Hta : forall t, In (t, n) O -> t = VArray (map dsnd l)).
  { intros t Ht; rewrite (r_value _ _ _ _ _ _ _ Hr qa t Hqa Hfla Ht), Eqa; reflexivity. }
  assert (Hstep : exists s', run (match bar (amap pt vP) with
                                  | Some bv => [DIncrement bv (DAt (DVar (BarOf n)) ei)] | None => [] end) s2 = Some s' /\
            rev_frame c (inplace wP pp) (oput O n (tangent (VArray l1))) s2 s' /\
            (forall t m, In (t, m) O -> shaped t (barv s' m)) /\
            pairing O s' = pairing O s2 + dy * bk /\ barv s' n = Some (VArray bn) /\ xev s' ei = Some (VInt z)).
  { destruct (varied (amap pa vP)) eqn:Evv.
    - destruct vP as [qv | |]; simpl in Evv; try discriminate.
      assert (Hqv : In qv L) by auto.
      destruct (static_in _ _ _ HL Hqv) as [_ [_ [Hsqv _]]].
      assert (Hflv : vflows k (ASet (amap pa (AVar qa)) (amap pa iP) (amap pa (AVar qv))) qv)
        by (unfold vflows; cbn [value_needs fst snd atoms_of_atoms atoms_of_atom amap];
            rewrite atom_member_union, atom_member_union, atom_member_var, !orb_true_r; reflexivity).
      simpl in Hv; injection Hv as Eqv.
      pose proof (r_useful _ _ _ _ _ _ _ Hr qv Hqv Hflv Evv) as Hin; rewrite Eqv in Hin; simpl in Hin.
      pose proof (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) as Hshv; simpl in Hshv.
      destruct (barv s2 (stored qv)) as [[bv0 | | | |] |] eqn:Eb; try contradiction.
      assert (Hne : stored qv <> n) by (intros E; rewrite E, Ebn in Eb; discriminate).
      assert (Hcv : consistent (stored qv)) by (apply (Hok (VReal dy)); exact Hin).
      simpl; rewrite (Hbar qv Hqv), Evv, Hsqv.
      exists (store_set s2 (keyv (BarOf (stored qv))) (VReal (bv0 + bk))).
      split; [apply run_increment; [exact Eb | exact (Helem s2 Ebn Hsi)] |].
      split; [apply rev_frame_set; [apply oput_sub, in_map_iff; exists (VReal dy, stored qv); auto | exact Hcv] |].
      split; [apply (shaped_set O s2 (VReal dy)); auto; [apply (r_shape _ _ _ _ _ _ _ Hr) |];
              intros t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr qv t' Hqv Hflv Ht'), Eqv; exact I |].
      split; [rewrite (pairing_set_in O s2 (VReal dy) (stored qv)); auto; rewrite Eb; simpl; ring |].
      split; [rewrite barv_set_other; auto |].
      rewrite xev_set_other; [exact Hsi | apply (avoid_bar_spell k); intros p E; exact (static_in _ _ _ HL (HiL p E))].
    - assert (Hz : dy = 0).
      { assert (Hst' : forall q, vP = AVar q -> static_ok k q) by (intros q E; exact (static_in _ _ _ HL (HvL q E))).
        exact (atom_zero k vP _ Hst' Evv Hv). }
      assert (Hnb : bar (amap pt vP) = None).
      { destruct vP as [q | |]; simpl; auto; simpl in Evv; rewrite (Hbar q (HvL q eq_refl)), Evv; reflexivity. }
      rewrite Hnb; exists s2; split; [reflexivity |].
      split; [intros ? ? ? ? ? ?; reflexivity | split; [apply (r_shape _ _ _ _ _ _ _ Hr) |]].
      split; [rewrite Hz; ring | auto]. }
  destruct Hstep as [s' [R1 [F1 [S1 [P1 [B1 X1]]]]]].
  exists (store_set s' (keyv (BarOf n)) (VArray bn0)).
  split.
  { destruct (bar (amap pt vP)) as [bv |].
    - change [DIncrement bv (DAt (DVar (BarOf n)) ei); DAssign (DAt (DVar (BarOf n)) ei) (DReal "0")]
        with (app [DIncrement bv (DAt (DVar (BarOf n)) ei)] [DAssign (DAt (DVar (BarOf n)) ei) (DReal "0")]).
      rewrite run_app; lazymatch goal with |- match ?r with _ => _ end = _ => replace r with (Some s') by (symmetry; exact R1) end.
      exact (Hzero s' B1 X1).
    - injection R1 as <-; exact (Hzero s2 B1 X1). }
  split; [exact (rev_frame_trans _ _ _ _ _ _ F1 (rev_frame_set _ _ _ _ _ _ (oput_in O n _) Hcn)) |].
  assert (Hlen0 : length bn0 = length bn) by exact (replace_nth_z_length _ _ _ _ Ebn0).
  split.
  { intros t m Htm; destruct (dvar_eq_dec_c n m) as [<- | Enm].
    - rewrite barv_set_same, (Hta t Htm); simpl; rewrite length_map; lia.
    - rewrite barv_set_other; auto; [apply (Hok t); exact Htm]. }
  destruct (in_dec dvar_eq_dec_c n (map snd O)) as [Inn | Inn].
  - apply in_map_iff in Inn as [[t n'] [En Itn]]; simpl in En; subst n'.
    pose proof (Hta t Itn) as ->.
    rewrite (pairing_set_in O s' (VArray (map dsnd l)) n); auto.
    unfold oput; destruct (in_dec dvar_eq_dec_c n (map snd O)) as [_ | Nn];
      [| destruct Nn; apply in_map_iff; exists (VArray (map dsnd l), n); auto].
    rewrite (pairing_oset O s2 (VArray (map dsnd l)) n); auto.
    rewrite B1, Ebn, P1; simpl; rewrite Hdot0, Hdot1; ring.
  - rewrite pairing_set_other; auto.
    rewrite (oput_notin O _ _ Inn); simpl; rewrite Ebn, P1, Hdot1.
    assert (Hva : avaried (pa qa) = false).
    { destruct (avaried (pa qa)) eqn:E; [| reflexivity]; exfalso; apply Inn.
      apply in_map_iff; exists (tangent (pd qa), stored qa); split; [reflexivity |].
      exact (r_useful _ _ _ _ _ _ _ Hr qa Hqa Hfla E). }
    destruct (static_in _ _ _ HL Hqa) as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hzq]]]]]]]]].
    specialize (Hzq Hva); rewrite Eqa in Hzq; simpl in Hzq.
    assert (Hz0 : Forall (fun x => x = 0) (map dsnd l)) by (apply Forall_map; exact Hzq).
    rewrite dotr_sym, (dotr_zero bn _ Hz0).
    assert (ta_z = 0) as -> by (rewrite Forall_forall in Hz0; apply Hz0; eapply nth_error_In; eauto).
    ring.
Qed.

(* ---------------------------------------------------------------------------
   What needs says at a let, of a variable in scope (an identity below k):
   from the rest of the body, and from the value. *)

Lemma same_term_below (q : avar) k vr : (aid q < k)%nat -> same_term (AVar (AV k vr)) (AVar q) = false.
Proof. intros H; simpl; apply Nat.eqb_neq; lia. Qed.

Lemma needs_let m k a eA (cA : avar -> anf avar bare) :
  needs cv m k (ALet a eA cA) =
  let x := let_binder k eA in
  let '(ub, lb) := needs cv m (S k) (cA x) in
  let useful := atom_member (AVar x) ub in
  let needed := atom_member (AVar x) lb in
  let '(reads_e, flows_e) := if varied_value k eA && useful then value_needs cv k eA else ([], []) in
  let atoms_e := if needed || (sweep_eqb m Forward && records cv k eA) then atoms_of_value k eA else [] in
  (atom_union (atom_remove (AVar x) ub) flows_e,
   atom_union (atom_union (atom_remove (AVar x) lb) reads_e) atoms_e).
Proof. reflexivity. Qed.

Section NeedsLet.
Variables (m : sweep) (k : nat) (a : bare) (eA : value avar bare) (cA : avar -> anf avar bare) (p : pv).
Hypothesis Hp : (aid (pa p) < k)%nat.
Let x := let_binder k eA.

Ltac needs_let_tac := rewrite needs_let; unfold x in *; destruct (needs cv m (S k) (cA (let_binder k eA))) as [ub lb]; cbv zeta.
Ltac split_reads := destruct (varied_value k eA && _); [destruct (value_needs cv k eA) as [r f] |]; cbn [fst snd].
Ltac below_tac := apply same_term_below; exact Hp.

Lemma useful_let_cont : useful cv m (S k) (cA x) p -> useful cv m k (ALet a eA cA) p.
Proof.
  unfold useful; needs_let_tac; intros H; cbn [fst] in H; split_reads;
    (rewrite atom_member_union, atom_member_remove; [rewrite H; reflexivity | below_tac]).
Qed.

Lemma tbr_let_cont : tbr cv m (S k) (cA x) p -> tbr cv m k (ALet a eA cA) p.
Proof.
  unfold tbr; needs_let_tac; intros H; cbn [snd] in H; split_reads;
    (rewrite !atom_member_union, atom_member_remove; [rewrite H; reflexivity | below_tac]).
Qed.

Lemma useful_let_flows :
  varied_value k eA && atom_member (AVar x) (fst (needs cv m (S k) (cA x))) = true ->
  vflows k eA p -> useful cv m k (ALet a eA cA) p.
Proof.
  unfold useful, vflows; needs_let_tac; intros Ha Hf; cbn [fst] in Ha; rewrite Ha.
  destruct (value_needs cv k eA) as [r f]; cbn [fst snd] in Hf |- *.
  rewrite atom_member_union, Hf, orb_true_r; reflexivity.
Qed.

Lemma tbr_let_reads :
  varied_value k eA && atom_member (AVar x) (fst (needs cv m (S k) (cA x))) = true ->
  vreads k eA p -> tbr cv m k (ALet a eA cA) p.
Proof.
  unfold tbr, vreads; needs_let_tac; intros Ha Hf; cbn [fst] in Ha; rewrite Ha.
  destruct (value_needs cv k eA) as [r f]; cbn [fst snd] in Hf |- *.
  rewrite !atom_member_union, Hf, orb_true_r; reflexivity.
Qed.

Lemma tbr_let_atoms :
  atom_member (AVar x) (snd (needs cv m (S k) (cA x))) || (sweep_eqb m Forward && records cv k eA) = true ->
  vatoms k eA p -> tbr cv m k (ALet a eA cA) p.
Proof.
  unfold tbr, vatoms; needs_let_tac; intros Hc Hf; cbn [snd] in Hc; rewrite Hc.
  split_reads; rewrite !atom_member_union, Hf, orb_true_r; reflexivity.
Qed.

End NeedsLet.

(* ---------------------------------------------------------------------------
   A let. *)

(* The activity analysis is sound for a value: a value that is not varied
   has a zero tangent. *)
Definition act_value (eP : value pv bare) : Prop :=
  forall L k wP pp tail eA eW eD te ve,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gD L) eP eD -> Forall (static_ok k) L ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  aeval_value (duals reals) eD = Some ve ->
  has_type te ve /\ (varied_value k eA = false -> zero ve) /\ (varied_value k eA = true -> real_or_array te).

Ltac act_intro :=
  let L := fresh "L" in let k := fresh "k" in
  intros L k wP pp tail eA eW eD te ve HA HW HD HL Htc Hev;
  destruct eA, eW, eD; simpl in HA, HW, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.

Lemma act_op1 f (aP : atom pv) : act_value (AOp1 f aP).
Proof.
  act_intro; simpl in Htc, Hev |- *; rename f2 into f.
  assert (Ha1 : forall p, aP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  assert (Hty : te = Real /\ of_atom (amap pw aP) = Real).
  { destruct f; simpl in Htc; crush_match Htc; split; congruence. }
  destruct Hty as [-> Hta].
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  pose proof (atom_type k aP va Ha1 Ha) as Htv; rewrite Hta in Htv.
  destruct va as [[x dx] | | | |]; try contradiction; cbn [eval_op1 dom_op1 duals] in Hev.
  destruct (dual_op1 R reals f (Dual x dx)) as [[y dy] |] eqn:Hd; [| discriminate]; injection Hev as <-.
  split; [exact I | split; [| intros _; exact I]].
  intros Hv; pose proof (atom_zero k aP _ Ha1 Hv Ha) as Hz; simpl in Hz; subst dx.
  exact (dual_op1_zero f x y dy Hd).
Qed.

Lemma act_op2 f (aP bP : atom pv) : act_value (AOp2 f aP bP).
Proof.
  act_intro; simpl in Htc, Hev |- *; rename f2 into f.
  assert (Ha1 : forall p, aP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  assert (Hb1 : forall p, bP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  destruct (aeval_atom (duals reals) (amap pd bP)) as [vb |] eqn:Hb; [| discriminate].
  destruct (operation2 f) eqn:Ho2; [| discriminate].
  destruct (operation2_typed f (of_atom (amap pw aP)) (of_atom (amap pw bP))) as [[t0 sp] |] eqn:Ht2;
    [| discriminate].
  injection Htc as <-.
  pose proof (atom_type k aP va Ha1 Ha) as Hta; pose proof (atom_type k bP vb Hb1 Hb) as Htb.
  destruct va as [[x dx] | za | | |], vb as [[y dy] | zb | | |]; cbn [eval_op2] in Hev; try discriminate.
  - simpl in Hta, Htb; destruct (of_atom (amap pw aP)) eqn:Ea; try contradiction.
    destruct (of_atom (amap pw bP)) eqn:Eb; try contradiction.
    apply op2_real_type in Ht2; subst t0.
    destruct (comparison f) eqn:Hcmp; simpl.
    + cbn [dom_cmp duals dual_cmp] in Hev.
      destruct (dom_cmp reals f x y) as [bo |]; [| discriminate]; injection Hev as <-.
      split; [exact I | split; [intros _; exact I | discriminate]].
    + cbn [dom_op2 duals] in Hev.
      destruct (dual_op2 R reals f (Dual x dx) (Dual y dy)) as [[z dz] |] eqn:Hd; [| discriminate].
      injection Hev as <-.
      split; [exact I | split; [| intros _; exact I]].
      intros Hv; apply orb_false_iff in Hv as [Hva Hvb].
      pose proof (atom_zero k aP _ Ha1 Hva Ha) as Hza; pose proof (atom_zero k bP _ Hb1 Hvb Hb) as Hzb.
      simpl in Hza, Hzb; subst dx dy; exact (dual_op2_zero f x y z dz Hd).
  - injection Hev as <-; simpl in Hta, Htb; apply has_type_int in Hta, Htb.
    rewrite Hta, Htb in Ht2.
    rewrite (int_not_varied k aP za Ha1 Ha), (int_not_varied k bP zb Hb1 Hb).
    split; [exact (int_op2_type f za zb t0 sp Ht2) |].
    split; [intros _; destruct f; exact I | destruct (comparison f); discriminate].
Qed.

Lemma act_get (aP iP : atom pv) : act_value (AGet aP iP).
Proof.
  act_intro; simpl in Htc, Hev |- *.
  assert (Ha1 : forall p, aP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  destruct (ty_is_array (of_atom (amap pw aP)) && ty_eqb (of_atom (amap pw iP)) Integer); [| discriminate].
  injection Htc as <-.
  destruct (aeval_atom (duals reals) (amap pd aP)) as [[| | | l |] |] eqn:Ha; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |]; try discriminate.
  destruct (nth_z z l) as [d |] eqn:Ez; [| discriminate]; injection Hev as <-.
  split; [exact I | split; [| intros _; exact I]].
  intros Hv; pose proof (atom_zero k aP _ Ha1 Hv Ha) as Hz; simpl in Hz.
  exact (nth_z_Forall _ _ _ _ Hz Ez).
Qed.

Lemma act_set (aP iP vP : atom pv) : act_value (ASet aP iP vP).
Proof.
  act_intro; simpl in Htc, Hev |- *.
  assert (Ha1 : forall p, aP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  assert (Hv1 : forall p, vP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  destruct (aeval_atom (duals reals) (amap pd aP)) as [[| | | l |] |] eqn:Ha; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |]; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd vP)) as [[d | | | |] |] eqn:Hv; try discriminate.
  destruct (replace_nth_z z d l) as [l1 |] eqn:Er; [| discriminate]; injection Hev as <-.
  pose proof (atom_type k aP _ Ha1 Ha) as Hta.
  assert (Hte : exists n, te = Array n /\ of_atom (amap pw aP) = Array n).
  { destruct (wplace pp); simpl in Htc; try discriminate.
    destruct (of_atom (amap pw aP)) eqn:Ea; try discriminate.
    destruct (_ && _); [injection Htc as <-; eauto | discriminate]. }
  destruct Hte as [n [-> Ea]]; rewrite Ea in Hta; simpl in Hta.
  split; [simpl; rewrite (replace_nth_z_length _ _ _ _ Er); exact Hta |].
  split; [| intros _; exact I].
  intros Hvr; apply orb_false_iff in Hvr as [Hva Hvv].
  pose proof (atom_zero k aP _ Ha1 Hva Ha) as Hza; pose proof (atom_zero k vP _ Hv1 Hvv Hv) as Hzv.
  simpl in Hza, Hzv; exact (replace_nth_z_Forall _ _ _ _ _ Hzv Hza Er).
Qed.

Lemma sctx_weaken L k c c' wP pp (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> (forall p, live' p -> live p) -> (c <= c')%nat -> sctx L k c' wP pp live' ty.
Proof.
  intros Hc Hl Hcc; constructor.
  - exact (s_static _ _ _ _ _ _ _ Hc).
  - exact (s_unique _ _ _ _ _ _ _ Hc).
  - intros p Hp; pose proof (s_num _ _ _ _ _ _ _ Hc p Hp); lia.
  - exact (s_written _ _ _ _ _ _ _ Hc).
  - exact (s_place _ _ _ _ _ _ _ Hc).
  - intros o p Ho Hp E; destruct (s_owner _ _ _ _ _ _ _ Hc o p Ho Hp E) as [H | H];
      [left; exact H | right; intros Hl'; apply H, Hl, Hl'].
  - intros p o Hp Hl' Ha Hg Ho; exact (s_arrays _ _ _ _ _ _ _ Hc p o Hp (Hl _ Hl') Ha Hg Ho).
  - exact (s_ty _ _ _ _ _ _ _ Hc).
  - intros y H1 H2 H3; destruct (s_top _ _ _ _ _ _ _ Hc y H1 H2 H3) as [A B];
      split; [exact A | intros Hl'; apply B, Hl, Hl'].
Qed.

Lemma actx_weaken L k c c' s wP pp (live live' tb tb' : pv -> Prop) ty :
  actx L k c s wP pp live tb ty -> (forall p, live' p -> live p) -> (forall p, In p L -> tb' p -> tb p) ->
  (c <= c')%nat -> actx L k c' s wP pp live' tb' ty.
Proof.
  intros Hc Hl Ht Hcc; constructor.
  - exact (sctx_weaken _ _ _ _ _ _ _ _ _ (a_sctx _ _ _ _ _ _ _ _ _ Hc) Hl Hcc).
  - exact (a_bar _ _ _ _ _ _ _ _ _ Hc).
  - intros p Hp H; exact (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (Ht p Hp H)).
  - exact (a_tape _ _ _ _ _ _ _ _ _ Hc).
  - exact (a_owner _ _ _ _ _ _ _ _ _ Hc).
Qed.

(* The variable updated in place is an array. *)
Lemma owner_array L k c wP pp live ty o :
  sctx L k c wP pp live ty -> owner wP pp = Some o -> is_array (vty (pw o)).
Proof.
  intros Hs Ho; destruct pp as [| | | ix sx]; simpl in Ho; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate; destruct (vty (pw y)) eqn:E; try discriminate.
    injection Ho as <-; rewrite E; exact I.
  - injection Ho as <-; destruct (s_place _ _ _ _ _ _ _ Hs) as [_ [_ [_ [H _]]]]; exact H.
Qed.

(* A scalar that occurs is not stored in the storage updated in place. *)
Lemma scalar_not_inplace L k c wP pp (live : pv -> Prop) ty p :
  sctx L k c wP pp live ty -> In p L -> live p -> ~ is_array (vty (pw p)) -> inplace wP pp <> Some (stored p).
Proof.
  intros Hs Hp Hl Ha; unfold inplace; destruct (owner wP pp) as [o |] eqn:Eo; simpl; [| discriminate].
  intros E; unfold stored in E; injection E as E.
  destruct (s_owner _ _ _ _ _ _ _ Hs o p Eo Hp (eq_sym E)) as [-> | Hn]; [| contradiction].
  exact (Ha (owner_array _ _ _ _ _ _ _ _ Hs Eo)).
Qed.

Lemma inner_zero t : inner t (Some (VReal 0)) = 0.
Proof. destruct t; simpl; ring. Qed.

Lemma oset_ok O e t : owners_ok O -> owners_ok (oset O e t).
Proof.
  intros Hok t' n' Hi.
  assert (Hm : In n' (map snd (oset O e t))) by (apply in_map_iff; exists (t', n'); auto).
  rewrite oset_snd in Hm; apply in_map_iff in Hm as [[t0 n0] [E Hi0]]; simpl in E; subst n0.
  exact (Hok t0 n' Hi0).
Qed.

(* A fresh owner, whose adjoint is 0, adds nothing to the result pairing. *)
Lemma result_pairing_fresh O ty ex v se s n t :
  owners_ok O -> consistent n -> ~ In n (map snd O) ->
  (forall x, In x (dvars se) -> consistent x /\ x <> BarOf n) ->
  result_pairing ((t, n) :: O) ty ex v se (store_set s (keyv (BarOf n)) (VReal 0)) =
  result_pairing O ty ex v se s.
Proof.
  intros Hok Hn Hni Hse.
  assert (Hp : forall O', owners_ok O' -> map snd O' = map snd O ->
                 pairing O' (store_set s (keyv (BarOf n)) (VReal 0)) = pairing O' s).
  { intros O' Hok' E; apply pairing_set_other; auto; rewrite E; exact Hni. }
  assert (Hsv : seed_value se (store_set s (keyv (BarOf n)) (VReal 0)) = seed_value se s).
  { unfold seed_value; rewrite xev_set_other; [reflexivity |].
    intros x Hx K; destruct (Hse x Hx) as [Hcx Hxn]; apply keyv_inj in K; [| exact Hcx | exact Hn]; auto. }
  unfold result_pairing; destruct ty; destruct ex as [e |]; destruct v as [d | | | |]; simpl.
  all: rewrite ?barv_set_same, ?inner_zero.
  all: try (rewrite (Hp O Hok eq_refl), ?Hsv; ring).
  all: destruct (Simplify.dvar_eq nat e n); cbv beta iota;
         rewrite barv_set_same, inner_zero, (Hp _ (oset_ok _ _ _ Hok) (oset_snd _ _ _)); ring.
Qed.

(* A reverse frame for more owners and a larger counter, seen from fewer. *)
Lemma rev_frame_mono c c' ex O O' s s' :
  rev_frame c' ex O' s s' -> (c <= c')%nat ->
  (forall m, In m (map snd O') -> In m (map snd O) \/ ~ below c (BarOf m)) ->
  rev_frame c ex O s s'.
Proof.
  intros F Hc HO v Hb Hcv Ht Hex Hbar; apply F; auto.
  - exact (below_mono _ _ _ Hb Hc).
  - intros m -> Hm; destruct (HO m Hm) as [H | H]; [exact (Hbar m eq_refl H) | exact (H Hb)].
Qed.

(* Writing an adjoint keeps the primal keys. *)
Lemma agree_prim_set_bar c ex s1 s2 n w :
  agree_prim c ex s1 s2 -> consistent n -> agree_prim c ex s1 (store_set s2 (keyv (BarOf n)) w).
Proof.
  intros A Hn v Hb Hcv Hp; rewrite store_get_set_other; [exact (A v Hb Hcv Hp) |].
  intros K; apply keyv_inj in K; auto; subst v; exact Hp.
Qed.

Lemma agree_prim_mono c c' ex s1 s2 : agree_prim c' ex s1 s2 -> (c <= c')%nat -> agree_prim c ex s1 s2.
Proof. intros A Hc v Hb; apply A; exact (below_mono _ _ _ Hb Hc). Qed.

(* A value updated in place that is not varied leaves the tangent of the
   storage as it was: zero. *)
Definition act_owner (eP : value pv bare) : Prop :=
  forall L k c wP pp (live : pv -> Prop) ty tail eA eW eD ve o,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gD L) eP eD ->
  sctx L k c wP pp live ty -> (forall p, live_value k eW p -> live p) ->
  storage wP tail eP = Some (stored o) -> owner wP pp = Some o ->
  aeval_value (duals reals) eD = Some ve -> varied_value k eA = false -> tangent (pd o) = tangent ve.

Lemma zeros_eq (a b : list R) :
  Forall (fun x => x = 0) a -> Forall (fun x => x = 0) b -> length a = length b -> a = b.
Proof.
  intros Ha; revert b; induction Ha as [| x a Hx Ha IH]; intros [| y b] Hb E; simpl in E; try discriminate; auto.
  inversion Hb; subst; f_equal; auto.
Qed.

Lemma owner_op1 f (aP : atom pv) : act_owner (AOp1 f aP).
Proof. intros L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es; discriminate. Qed.
Lemma owner_op2 f (aP bP : atom pv) : act_owner (AOp2 f aP bP).
Proof. intros L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es; discriminate. Qed.
Lemma owner_get (aP iP : atom pv) : act_owner (AGet aP iP).
Proof. intros L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es; discriminate. Qed.

Lemma owner_set (aP iP vP : atom pv) : act_owner (ASet aP iP vP).
Proof.
  intros L k c wP pp live ty tail eA eW eD ve o HA HW HD Hs Hlv Es Ho Hev Hvr.
  destruct eA, eW, eD; simpl in HA, HW, HD; try contradiction.
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.
  destruct aP as [q | |]; simpl in Es; try discriminate; injection Es as Eq.
  assert (Hq : In q L) by auto.
  assert (Hqo : q = o).
  { assert (Hl : live q) by (apply Hlv; unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity).
    assert (E2 : pn q = pn o) by (try unfold stored in Eq; try injection Eq as Eq; congruence).
    destruct (s_owner _ _ _ _ _ _ _ Hs o q Ho Hq E2) as [-> | Hnl]; [reflexivity | contradiction]. }
  subst o; simpl in Hev, Hvr |- *.
  apply orb_false_iff in Hvr as [Hva Hvv].
  pose proof (s_static _ _ _ _ _ _ _ Hs) as HL.
  destruct (static_in _ _ _ HL Hq) as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hzq]]]]]]]]].
  specialize (Hzq Hva).
  destruct (pd q) as [| | | l |] eqn:Eq'; try discriminate.
  destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |]; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd vP)) as [[d | | | |] |] eqn:Hv; try discriminate.
  destruct (replace_nth_z z d l) as [l1 |] eqn:Er; [| discriminate]; injection Hev as <-.
  assert (Hv1 : forall p, vP = AVar p -> static_ok k p) by (intros p E; apply (static_in _ _ _ HL); auto).
  pose proof (atom_zero k vP _ Hv1 Hvv Hv) as Hzv; simpl in Hzq, Hzv |- *.
  f_equal; apply zeros_eq.
  - apply Forall_map; exact Hzq.
  - apply Forall_map; exact (replace_nth_z_Forall _ _ _ _ _ Hzv Hzq Er).
  - rewrite !length_map; symmetry; exact (replace_nth_z_length _ _ _ _ Er).
Qed.

Lemma adj_let w vo m a e b se :
  adj W w vo m (ALet a e b) se =
  let '(vr, ac, cp) := let_ann a in
  with_storage w e b (fun n rec =>
    sbind (adj W w vo m (b (open_let (Transform.type_of e) n vr rec)) se) (fun '(fb, rb) =>
    sbind (if cp then fwd_value W w m e (Transform.type_of e) n rec else Done []) (fun fe =>
    sbind (if ac then rev_value W w vo e (Transform.type_of e) n else Done []) (fun re =>
    Done (app fe fb, app (if ac then bar_declaration W (Transform.type_of e) n else []) (app rb re)))))).
Proof. reflexivity. Qed.

(* with_storage, opened: as in the tangent simulation, and a fresh storage
   is not recorded. *)
Lemma open_with_storage' {A : Type} L k wP (eP : value pv bare) eT vt
  (bT : tvar W -> anf (tvar W) ann) (K : dvar W -> bool -> scoped W A) c :
  value_eq (gT L) eP eT -> Forall (static_ok k) L ->
  (forall a, wP = Some a -> exists y, a = AVar y /\ In y L) ->
  exists n rec c0,
    open_pairs (with_storage (option_map (amap pt) wP) (rebuild_value _ eT vt) bT K) c =
    open_pairs (K n rec) c0 /\
    match storage wP (Transform.is_tail bT) eP with
    | Some m => n = m /\ c0 = c /\ exists q, In q L /\ stored q = m /\ rec = trecorded (pt q)
    | None => n = DBound (c, c) /\ c0 = S c /\ rec = false
    end.
Proof.
  intros HT HL Hw.
  assert (Hst : forall p, In p L -> tstored (pt p) = stored p /\ tty (pt p) = vty (pw p))
    by (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [_ [H1 [H2 _]]]]; auto).
  Local Ltac fresh_case' := solve [eexists (DBound (_, _)), false, (S _); simpl; auto].
  destruct eP as [f a | f a b | a i | a i x | cnd t e | lo hi b | an lo hi init b], eT;
    simpl in HT; try contradiction; simpl;
    try fresh_case'; try (destruct vt; fresh_case').
  - destruct HT as [Ha _]; destruct a as [p | |]; destruct a0; simpl in Ha; try contradiction;
      try fresh_case'.
    apply in_gT in Ha as [Hp ->]; destruct (Hst _ Hp) as [E _].
    exists (stored p), (trecorded (pt p)), c; simpl; rewrite E; split; [reflexivity | split; [reflexivity | split; [reflexivity | exists p; auto]]].
  - destruct (vt); simpl;
      (destruct (Transform.is_tail bT); [| fresh_case']);
      (destruct wP as [[y | |] |]; simpl;
       [| fresh_case'
        | fresh_case'
        | fresh_case']);
      (destruct (Hw _ eq_refl) as [y' [E Hy]]; injection E as <-;
       destruct (Hst _ Hy) as [E _]; exists (stored y), (trecorded (pt y)), c; rewrite E;
       split; [reflexivity | split; [reflexivity | split; [reflexivity | exists y; auto]]]).
  - destruct HT as [_ [_ [Hi _]]]; destruct init as [p | |], init0; simpl in Hi; try contradiction;
      destruct vt; simpl; try fresh_case';
      (apply in_gT in Hi as [Hp ->]; destruct (Hst _ Hp) as [E1 E2]; rewrite E2;
       destruct (vty (pw p)); try fresh_case';
       exists (stored p), (trecorded (pt p)), c; rewrite E1;
       split; [reflexivity | split; [reflexivity | split; [reflexivity | exists p; auto]]]).
Qed.

Lemma option_dec_ex (o : option (dvar W)) (v : dvar W) : {o = Some v} + {o <> Some v}.
Proof. destruct o as [w |]; [destruct (dvar_eq_dec_c w v) as [-> | H]; [left; reflexivity | right; congruence] | right; discriminate]. Qed.

Lemma asim_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  asim_fwd eP -> asim_rev eP -> inplace_only eP -> act_value eP -> act_owner eP -> (forall x, asim_body (cP x)) ->
  asim_body (ALet a eP cP).
Proof.
  intros IHf IHr IHi IHa IHo IHb L k c s wP pp m bA bW bT bD ty v se vo HA HW HT HD Hc Hty Htc Hev Hvo Hvt Hvb.
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
  destruct (needs cv m (S k) (cA (let_binder k eA))) as [u l] eqn:Hneeds.
  set (vr := varied_value k eA). set (vt := annotate_value_t cv k eA).
  set (rest := annotate_body_t cv m (S k) (cA (let_binder k eA))).
  set (ac := vr && atom_member (AVar (let_binder k eA)) u).
  set (cp := atom_member (AVar (let_binder k eA)) l || sweep_eqb m Forward && records cv k eA).
  cbn [rebuild]. rewrite adj_let. cbv [let_ann].
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
  unfold Kf; rewrite open_pairs_sbind.
  destruct (open_pairs (adj W (option_map (amap pt) wP) vo m (rebuild (tvar W) (cT (open_let te n vr rec)) rest) se) c0)
    as [[fb rb] c1] eqn:Hb.
  rewrite open_pairs_sbind.
  destruct (open_pairs (if cp then fwd_value W (option_map (amap pt) wP) m (rebuild_value (tvar W) eT vt) te n rec else Done []) c1)
    as [fe c2] eqn:Hfe.
  rewrite open_pairs_sbind.
  destruct (open_pairs (if ac then rev_value W (option_map (amap pt) wP) vo (rebuild_value (tvar W) eT vt) te n else Done []) c2)
    as [re c3] eqn:Hre.
  cbn [open_pairs].
  assert (Hc01 : (c0 <= c1)%nat).
  { pose proof (open_pairs_mono (adj W (option_map (amap pt) wP) vo m (rebuild (tvar W) (cT (open_let te n vr rec)) rest) se) c0) as H0.
    rewrite Hb in H0; exact H0. }
  assert (Hc12 : (c1 <= c2)%nat).
  { pose proof (open_pairs_mono (if cp then fwd_value W (option_map (amap pt) wP) m (rebuild_value (tvar W) eT vt) te n rec else Done []) c1) as H0.
    rewrite Hfe in H0; exact H0. }
  assert (Hc23 : (c2 <= c3)%nat).
  { pose proof (open_pairs_mono (if ac then rev_value W (option_map (amap pt) wP) vo (rebuild_value (tvar W) eT vt) te n else Done []) c2) as H0.
    rewrite Hre in H0; exact H0. }
  pose proof (aids_below L k HL) as Haid.
  assert (Hlv_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p)
    by (intros p H0; unfold live_value, live_anf in *; simpl; rewrite H0; reflexivity).
  destruct (storage wP tail eP) as [m0 |] eqn:Es.
  { (* stored in place: the let ends the body, which returns the variable *)
    destruct Hn as [-> [-> [qr [Hqr [Esr Erec]]]]].
    assert (Hsn : storage wP tail eP <> None) by (rewrite Es; discriminate).
    destruct (inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn)) as [Ht [o [Ho Es']]].
    rewrite Es in Es'; injection Es' as Em0; subst m0.
    pose proof (inplace_array _ _ _ _ _ _ _ _ HeW Hte Hsn) as Harr.
    pose proof (Htail_ty Ht) as Ety; subst ty.
    set (x := PV (let_binder k eA) (VInfo k te None) (open_let te (stored o) vr rec) ve (pn o)).
    assert (Hx : aid (pa x) = k) by reflexivity.
    assert (HxL : ~ In x L) by exact (fresh_notin L k x Haid Hx).
    destruct (tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht) as [Hcx EW].
    assert (ET : cT (pt x) = ARet (AVar (pt x))).
    { specialize (HcT x (pt x)); rewrite Hcx in HcT.
      destruct (cT (pt x)) as [? ? ? | [t' | |]]; simpl in HcT; try contradiction.
      destruct HcT as [E | I]; [injection E as E; rewrite <- E; reflexivity | apply in_gT in I as [I _]; contradiction]. }
    assert (ED : cD (pd x) = ARet (AVar (pd x))).
    { specialize (HcD x (pd x)); rewrite Hcx in HcD.
      destruct (cD (pd x)) as [? ? ? | [t' | |]]; simpl in HcD; try contradiction.
      destruct HcD as [E | I]; [injection E as E; rewrite <- E; reflexivity | apply in_gD in I as [I _]; contradiction]. }
    assert (EA : cA (pa x) = ARet (AVar (pa x))).
    { specialize (HcA x (pa x)); rewrite Hcx in HcA.
      destruct (cA (pa x)) as [? ? ? | [t' | |]]; simpl in HcA; try contradiction.
      destruct HcA as [E | I]; [injection E as E; rewrite <- E; reflexivity | apply in_gA in I as [I _]; contradiction]. }
    simpl in ET, ED, EA; rewrite ED in Hev; simpl in Hev; injection Hev as <-.
    rewrite EA in Hneeds; simpl in Hneeds.
    rewrite Em0 in *.
    unfold rest in Hb; rewrite EA in Hb; cbn [annotate_body_t rebuild] in Hb; rewrite ET in Hb; cbn [rebuild adj] in Hb.
    simpl in Hb.
    destruct te as [| | | z]; try destruct Harr.
    assert (Hfb : (if sweep_eqb m Forward then value_output W vo (AVar (open_let (Array z) (stored o) vr rec)) else []) = []).
    { destruct m; [| reflexivity]; simpl.
      destruct (Hvo eq_refl) as [Epp [_ [Hy Hr0]]]; subst pp.
      destruct vo as [[t0 | y] |]; [| | reflexivity].
      - specialize (Hr0 t0 eq_refl); subst wP; discriminate.
      - specialize (Hy y eq_refl).
        destruct wP as [[y' | |] |]; simpl in Ho; try discriminate.
        simpl in Hy; injection Hy as <-.
        destruct (vty (pw y')) eqn:Evy; try discriminate; injection Ho as <-.
        destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [y'' [E [Hy' _]]]; injection E as <-.
        destruct (static_in _ _ _ HL Hy') as [_ [_ [_ [Htq _]]]].
        unfold value_output; simpl; rewrite Htq, Evy; reflexivity. }
    rewrite Hfb in Hb; injection Hb as <- <- <-.
    assert (Hoin : In o L) by exact (owner_in_s _ _ _ _ _ _ _ _ Hs Ho).
    assert (Hj : exists j, stored o = DBound (j, j) /\ (j < c)%nat)
      by (exists (pn o); split; [reflexivity | exact (s_num _ _ _ _ _ _ _ Hs o Hoin)]).
    assert (Hst0 : match storage wP tail eP with
                   | Some m0 => stored o = m0
                   | None => forall p, In p L -> stored p <> stored o end) by (rewrite Es; reflexivity).
    assert (Hrec : rec = true -> exists l0, store_get s (keyv (TapeOf (stored o))) = Some (VTape l0)).
    { intros Hr0; rewrite <- Em0; apply (a_tape _ _ _ _ _ _ _ _ _ Hc qr Hqr); rewrite <- Erec; exact Hr0. }
    assert (Hex : inplace wP pp = Some (stored o)) by (unfold inplace; rewrite Ho; reflexivity).
    assert (Hio : not_in_loop pp -> (forall ny r, varg (pw o) = Some (ny, r) -> r <> Inout) /\ ~ live_value k eW o)
      by (intros Hl; exact (IHi L k wP pp tail eW _ HeW Hte Hsn Hl o Ho)).
    assert (Hn0 : needs cv m (S k) (cA (let_binder k eA)) = (u, l)) by (rewrite EA; exact Hneeds).
    assert (Hfw : exists se1, run fe s = Some se1 /\ fwd_frame c (Some (stored o)) None s se1 /\
                    tapes_kept s se1 /\ (cp = true -> store_get se1 (keyv (stored o)) = Some (primal ve))).
    { destruct cp eqn:Ecp.
      - assert (Hc1 : actx L k c s wP pp (live_value k eW) (vatoms k eA) (Array z)).
        { apply (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); [| lia].
          intros p Hp Hv; apply (tbr_let_atoms m k aA eA cA p); [| exact Hv].
          rewrite Hn0; exact Ecp. }
        pose proof (IHf L k c s wP pp tail eA eW eT eD (Array z) (stored o) ve (Array z) m rec HeA HeW HeT HeD Hc1 Hte
                      Htail_ty Hj Hst0 Hrec Hve) as IH.
        cbv zeta in IH; fold vt in IH; rewrite Hfe in IH.
        destruct IH as [_ [se1 [R1 [F1 [T1 S1]]]]]; exists se1; auto.
      - simpl in Hfe; injection Hfe as <- <-.
        exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply tapes_kept_refl | discriminate]]]. }
    destruct Hfw as [se1 [R1 [F1 [T1 S1]]]].
    split; [lia |].
    split; [exact (proj1 (IHa L k wP pp tail eA eW eD (Array z) ve HeA HeW HeD HL Hte Hve)) |].
    exists se1; split; [rewrite app_nil_r; exact R1 |].
    split; [intros v0 Hb0 Hc0 Ht0 He0 _; apply F1; auto; [rewrite <- Hex; exact He0 | discriminate] |].
    split; [exact T1 |].
    split.
    { intros Hm t0' Hvt0; destruct (Hvo Hm) as [Epp [Hcv [Hy Hr0]]]; subst pp m.
      destruct vo as [[t0 | y] |]; simpl in Hvt0; try discriminate.
      assert (Ecv : cv = true) by (destruct cv; [reflexivity | exfalso; specialize (proj2 Hcv eq_refl); discriminate]).
      assert (Ecp : cp = true).
      { unfold cp; rewrite Ecv in Hneeds; simpl in Hneeds; injection Hneeds as <- <-; simpl; rewrite Nat.eqb_refl; reflexivity. }
      specialize (Hy y eq_refl).
      destruct wP as [[y' | |] |]; simpl in Ho; try discriminate.
      destruct (vty (pw y')) eqn:Evy; try discriminate; injection Ho as <-.
      simpl in Hy; injection Hy as <-.
      destruct (static_in _ _ _ HL Hoin) as [_ [_ [Hso _]]].
      unfold role_of, stored_of in Hvt0; simpl in Hvt0; rewrite Hso in Hvt0.
      destruct (targ (pt y')) as [[? []] |]; simpl in Hvt0; try discriminate;
        destruct (tty (pt y')); try discriminate; injection Hvt0 as <-; exact (S1 Ecp). }
    intros s2 O Hag Hr Hseed Htp.
    assert (Hbd : (if ac then bar_declaration W (Array z) (stored o) else []) = []) by (destruct ac; reflexivity).
    rewrite Hbd, !app_nil_l.
    pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
    pose proof (r_owner _ _ _ _ _ _ _ Hr o Ho) as Hown.
    assert (Hav : not_in_loop pp -> avaried (pa o) = false).
    { intros Hl; destruct (Hio Hl) as [Hni _].
      assert (Ewo : wP = Some (AVar o)).
      { destruct pp as [| | | ix sx]; simpl in Ho, Hl; try discriminate; [| destruct Hl].
        destruct wP as [[y | |] |]; try discriminate; destruct (vty (pw y)); try discriminate; injection Ho as <-; reflexivity. }
      destruct (r_written _ _ _ _ _ _ _ Hr o Ewo) as [ny [r [Hvg Hwr]]].
      rewrite (r_args _ _ _ _ _ _ _ Hr o ny r Hoin Hvg).
      specialize (Hni ny r Hvg); destruct r; simpl in Hwr; try discriminate; [reflexivity | destruct Hni; reflexivity]. }
    assert (Hres : result_pairing O (Array z) (inplace wP pp) ve se s2 = pairing (oset O (stored o) (tangent ve)) s2)
      by (rewrite Hex; reflexivity).
    rewrite Hres.
    assert (Hu : atom_member (AVar (let_binder k eA)) u = true).
    { destruct (sweep_eqb m Forward && cv); injection Hneeds as <- _; simpl; rewrite Nat.eqb_refl; reflexivity. }
    destruct ac eqn:Eac.
    - assert (Hcond : varied_value k eA && atom_member (AVar (let_binder k eA)) (fst (needs cv m (S k) (cA (let_binder k eA)))) = true)
        by (rewrite Hn0; exact Eac).
      assert (Hvr : vr = true) by (apply andb_true_iff in Hcond; tauto).
      assert (Hj2 : exists j, stored o = DBound (j, j) /\ (j < c2)%nat)
        by (destruct Hj as [j0 [E Hj0]]; exists j0; split; [exact E | lia]).
      pose proof (IHr L k c2 wP pp tail eA eW eT eD (Array z) (stored o) ve (Array z) vo HeA HeW HeT HeD
                    (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlv_e Hc12) (a_bar _ _ _ _ _ _ _ _ _ Hc) Hte Htail_ty Hj2 Hst0 Hve Hvr)
        as IHr'.
      cbv zeta in IHr'; fold vt in IHr'.
      lazymatch type of IHr' with context [@open_pairs ?A ?t c2] =>
        assert (E : @open_pairs A t c2 = (re, c3)) by exact Hre; rewrite E in IHr'; clear E end.
      destruct IHr' as [_ Hrv].
      assert (Hrd : forall p, In p L -> vreads k eA p -> live_value k eW p ->
                      (not_in_loop pp \/ inplace wP pp <> Some (stored p)) ->
                      store_get s2 (keyv (stored p)) = Some (primal (pd p))).
      { intros p Hp Hrd0 Hlv Hdj.
        assert (Hne : inplace wP pp <> Some (stored p)).
        { destruct Hdj as [Hl | Hne]; [| exact Hne].
          rewrite Hex; intros E.
          assert (Epn : pn p = pn o) by (unfold stored in E; congruence).
          destruct (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Epn) as [Epo | Hnl']; [subst p; exact (proj2 (Hio Hl) Hlv) | exact (Hnl' (Hlv_e p Hlv))]. }
        assert (Hbp : below c (stored p)) by (unfold stored; simpl; exact (s_num _ _ _ _ _ _ _ Hs p Hp)).
        rewrite (Hag (stored p) (below_mono c c3 _ Hbp ltac:(lia)) eq_refl I).
        rewrite (F1 (stored p) Hbp eq_refl ltac:(simpl; tauto) ltac:(rewrite <- Hex; exact Hne) ltac:(discriminate)).
        exact (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (tbr_let_reads m k aA eA cA p Hcond Hrd0)). }
      assert (Hr2 : rctx L c2 wP pp O (vflows k eA) s2).
      { constructor.
        - exact (r_nodup _ _ _ _ _ _ _ Hr).
        - exact (r_shape _ _ _ _ _ _ _ Hr).
        - intros t0 m0 Hin; destruct (r_below _ _ _ _ _ _ _ Hr _ _ Hin) as [j0 [E Hj0]]; exists j0; split; [exact E | lia].
        - intros p Hp Hf Hv; exact (r_useful _ _ _ _ _ _ _ Hr p Hp (useful_let_flows m k aA eA cA p Hcond Hf) Hv).
        - intros p t0 Hp Hf Hin; exact (r_value _ _ _ _ _ _ _ Hr p t0 Hp (useful_let_flows m k aA eA cA p Hcond Hf) Hin).
        - exact (r_owner _ _ _ _ _ _ _ Hr).
        - exact (r_args _ _ _ _ _ _ _ Hr).
        - exact (r_written _ _ _ _ _ _ _ Hr). }
      assert (Hns : storage wP tail eP = None -> ~ In (stored o) (map snd O) /\ shaped (tangent ve) (barv s2 (stored o)))
        by (intros E; rewrite Es in E; discriminate).
      destruct (Hrv s2 O Hrd Hr2 Hns Htp) as [s3 [R3 [K3 [Kn3 [T3 [F3 [S3 P3]]]]]]].
      assert (Hoin' : In (stored o) (map snd O)) by (apply in_map_iff; eexists; split; [| exact Hown]; reflexivity).
      assert (Eput : oput O (stored o) (tangent ve) = oset O (stored o) (tangent ve)).
      { unfold oput; destruct (in_dec dvar_eq_dec_c (stored o) (map snd O)); [reflexivity | contradiction]. }
      rewrite Eput in F3, P3.
      exists s3; split; [exact R3 |].
      split.
      { intros Hm t0 Ht0 _; destruct (Hvb Hm t0 Ht0) as [Hb0 [Hc0 Hp0]].
        assert (Hl : not_in_loop pp) by (rewrite (proj1 (Hvo Hm)); exact I).
        destruct (dvar_eq_dec_c t0 (stored o)) as [-> | Hne0].
        - exact (Kn3 Hl Hsn o Ho (Hav Hl)).
        - exact (K3 t0 (below_mono c c2 t0 Hb0 ltac:(lia)) Hc0 Hp0 Hne0). }
      split; [intros Hl o0 Ho0 Hav0; rewrite Ho in Ho0; injection Ho0 as <-; rewrite (Hav Hl) in Hav0; discriminate |].
      split; [exact T3 |].
      split; [apply (rev_frame_mono c c2 _ _ _ _ _ F3 Hc12); intros m0 Hm; left; rewrite oset_snd in Hm; exact Hm |].
      split; [exact S3 | exact P3].
    - simpl in Hre; injection Hre as <- <-.
      assert (Hvr : vr = false).
      { pose proof Eac as E'; change (vr && atom_member (AVar (let_binder k eA)) u = false) in E'.
        rewrite Hu, andb_true_r in E'; exact E'. }
      exists s2; split; [reflexivity |].
      split; [intros _; apply vo_kept_refl |].
      split; [intros Hl o0 Ho0 Hav0; rewrite Ho in Ho0; injection Ho0 as <-; rewrite (Hav Hl) in Hav0; discriminate |].
      split; [apply tapes_kept_refl |].
      split; [intros ? ? ? ? ? ?; reflexivity | split; [exact (r_shape _ _ _ _ _ _ _ Hr) |]].
      rewrite <- (IHo L k c wP pp _ (Array z) tail eA eW eD ve o HeA HeW HeD Hs Hlv_e Es Ho Hve Hvr).
      rewrite oset_same; [reflexivity | exact Hok | exact (r_nodup _ _ _ _ _ _ _ Hr) | exact Hown]. }
  destruct Hn as [-> [-> ->]].
  destruct (IHa L k wP pp tail eA eW eD te ve HeA HeW HeD HL Hte Hve) as [Hht [Hz Hra]].
  assert (Hnotin : forall p, In p L -> stored p <> DBound (c, c)).
  { intros p Hp E; pose proof (s_num _ _ _ _ _ _ _ Hs p Hp) as H0; unfold stored in E; injection E as E; lia. }
  set (x := PV (let_binder k eA) (VInfo k te None) (open_let te (DBound (c, c)) vr false) ve c).
  assert (Hx : aid (pa x) = k) by reflexivity.
  assert (HxL : ~ In x L) by exact (fresh_notin L k x Haid Hx).
  (* the forward sweep of the value *)
  assert (Hfw : exists se1, run fe s = Some se1 /\ fwd_frame c1 (Some (DBound (c, c))) None s se1 /\
                  tapes_kept s se1 /\ (cp = true -> store_get se1 (keyv (DBound (c, c))) = Some (primal ve))).
  { destruct cp eqn:Ecp.
    - assert (Hc1 : actx L k c1 s wP pp (live_value k eW) (vatoms k eA) ty).
      { apply (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); [| lia].
        intros p Hp Hv; apply (tbr_let_atoms m k aA eA cA p); [| exact Hv].
        rewrite Hneeds; exact Ecp. }
      assert (Hj1 : exists j, DBound (c, c) = DBound (j, j) /\ (j < c1)%nat) by (exists c; split; [reflexivity | lia]).
      assert (Hst1 : match storage wP tail eP with
                     | Some m0 => DBound (c, c) = m0
                     | None => forall p, In p L -> stored p <> DBound (c, c) end) by (rewrite Es; exact Hnotin).
      assert (Hr1 : false = true -> exists l0, store_get s (keyv (TapeOf (DBound (c, c)))) = Some (VTape l0))
        by discriminate.
      pose proof (IHf L k c1 s wP pp tail eA eW eT eD te (DBound (c, c)) ve ty m false HeA HeW HeT HeD Hc1 Hte
                    Htail_ty Hj1 Hst1 Hr1 Hve) as IH.
      cbv zeta in IH; fold vt in IH; rewrite Hfe in IH.
      destruct IH as [_ [se1 [R1 [F1 [T1 S1]]]]]; exists se1; auto.
    - simpl in Hfe; injection Hfe as <- <-.
      exists s; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity | split; [apply tapes_kept_refl | discriminate]]]. }
  destruct Hfw as [se1 [R1 [F1 [T1 S1]]]].
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
  assert (Hc' : actx (x :: L) (S k) (S c) se1 wP pp (live_anf (S k) (cW (VInfo k te None)))
                  (tbr cv m (S k) (cA (let_binder k eA))) ty).
  { constructor; [exact Hs' | | | |].
    - intros p [<- | Hp]; [reflexivity | exact (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp)].
    - intros p [<- | Hp] Ht.
      + apply S1; unfold tbr in Ht; rewrite Hneeds in Ht; simpl in Ht; unfold cp; rewrite Ht; reflexivity.
      + rewrite Hold; [| exact Hp]; apply (a_store _ _ _ _ _ _ _ _ _ Hc p Hp).
        exact (tbr_let_cont m k aA eA cA p (Haid p Hp) Ht).
    - intros p [<- | Hp] Hr; [discriminate |].
      destruct (a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr) as [lt Hlt]; exact (T1 _ _ Hlt).
    - intros o Ho; rewrite Hold; [exact (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho) | exact (owner_in_s _ _ _ _ _ _ _ _ Hs Ho)]. }
  assert (Hvt' : m = Forward -> forall p, In p (x :: L) -> live_anf (S k) (cW (VInfo k te None)) p ->
                   vo_target vo <> Some (stored p)).
  { intros Hm p [<- | Hp] Hl Ht.
    - exfalso; destruct (Hvo Hm) as [_ [_ [Hy _]]].
      destruct vo as [[t0 | y] |]; simpl in Ht; try discriminate.
      specialize (Hy y eq_refl); destruct wP as [yP |]; simpl in Hy; [| discriminate]; injection Hy as <-.
      destruct (s_written _ _ _ _ _ _ _ Hs _ eq_refl) as [q [-> [Hq _]]].
      destruct (static_in _ _ _ HL Hq) as [_ [_ [Hsq _]]].
      unfold vo_target, stored_of in Ht; simpl in Ht; rewrite Hsq in Ht.
      destruct (targ (pt q)) as [[? []] |]; simpl in Ht; try discriminate;
        destruct (tty (pt q)); try discriminate; apply (Hnotin q Hq); unfold x, stored in *; cbn in Ht; congruence.
    - exact (Hvt Hm p Hp (Hlive_c p Hp Hl) Ht). }
  assert (Hvb' : m = Forward -> forall t, vo_target vo = Some t -> below (S c) t /\ consistent t /\ is_primal t).
  { intros Hm t0 Ht0; destruct (Hvb Hm t0 Ht0) as [H1 H2]; split; [exact (below_mono c (S c) t0 H1 (Nat.le_succ_diag_r c)) | exact H2]. }
  pose proof (IHb x (x :: L) (S k) (S c) se1 wP pp m (cA (pa x)) (cW (pw x)) (cT (pt x)) (cD (pd x)) ty v se vo
                (HcA x _) (HcW x _) (HcT x _) (HcD x _) Hc' Hty Htc Hev Hvo Hvt' Hvb') as IH.
  unfold x in IH; cbn [pt pa pd pw] in IH; fold rest in IH.
  lazymatch type of IH with context [@open_pairs ?A ?t (S c)] =>
    assert (E : @open_pairs A t (S c) = (fb, rb, c1)) by exact Hb; rewrite E in IH; clear E end.
  destruct IH as [_ [Hhtv [s1 [Rb [Fb [Tb [Vb Hrev]]]]]]].
  split; [lia | split; [exact Hhtv |]].
  exists s1; split.
  { rewrite run_app, R1; exact Rb. }
  split.
  { intros v0 Hb0 Hc0 Ht0 He0 Hv0.
    assert (Hc1' : (c <= c1)%nat) by lia.
    rewrite (Fb v0 (below_mono c (S c) v0 Hb0 (Nat.le_succ_diag_r c)) Hc0 Ht0 He0 Hv0).
    apply F1; [exact (below_mono c c1 v0 Hb0 Hc1') | exact Hc0 | exact Ht0 |
               intros E; injection E as <-; simpl in Hb0; lia | discriminate]. }
  split; [exact (tapes_kept_trans _ _ _ T1 Tb) |].
  split; [exact Vb |].
  intros s2 O Hag Hr Hseed Htp.
  pose proof (rctx_owners_ok _ _ _ _ _ _ _ Hr) as Hok.
  assert (Hn_notin : ~ In (DBound (c, c)) (map snd O)).
  { intros Hin; apply in_map_iff in Hin as [[t0 m0] [E Hin]]; simpl in E; subst m0.
    destruct (r_below _ _ _ _ _ _ _ Hr _ _ Hin) as [j0 [E Hj]]; injection E as <- _; lia. }
  assert (Hsel : forall y0, In y0 (dvars se) -> consistent y0 /\ y0 <> BarOf (DBound (c, c))).
  { intros y0 Hy; destruct (proj1 Hseed y0 Hy) as [Hb0 Hc0]; split; [exact Hc0 |].
    intros ->; simpl in Hb0; lia. }
  assert (Hux : useful cv m (S k) (cA (let_binder k eA)) x -> vr = true -> ac = true).
  { unfold useful; rewrite Hneeds; simpl; intros H1 H2; unfold ac; rewrite H2, H1; reflexivity. }
  (* the rctx of the rest of the body, for the owners O and possibly x *)
  assert (Hr' : forall O' sa, (O' = O /\ ac = false /\ sa = s2) \/
                    (O' = (tangent ve, DBound (c, c)) :: O /\ ac = true /\
                     sa = store_set s2 (keyv (BarOf (DBound (c, c)))) (VReal 0) /\
                     shaped (tangent ve) (Some (VReal 0))) ->
                rctx (x :: L) (S c) wP pp O' (useful cv m (S k) (cA (let_binder k eA))) sa).
  { intros O' sa HO.
    assert (Hshb : forall t0 m0, In (t0, m0) O -> shaped t0 (barv sa m0)).
    { intros t0 m0 Hin; destruct HO as [[-> [_ ->]] | [-> [_ [-> _]]]]; [exact (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) |].
      rewrite barv_set_other; [exact (r_shape _ _ _ _ _ _ _ Hr _ _ Hin) | reflexivity | exact (Hok _ _ Hin) |].
      intros E; apply Hn_notin; rewrite E; apply in_map_iff; exists (t0, m0); auto. }
    assert (HinO : forall t0 m0, In (t0, m0) O -> In (t0, m0) O')
      by (intros t0 m0 Hin; destruct HO as [[-> _] | [-> _]]; [exact Hin | right; exact Hin]).
    assert (HO' : forall t0 m0, In (t0, m0) O' -> In (t0, m0) O \/ (t0 = tangent ve /\ m0 = DBound (c, c) /\ ac = true)).
    { intros t0 m0 Hin; destruct HO as [[-> _] | [-> [Ea _]]]; [left; exact Hin |].
      destruct Hin as [E | Hin]; [injection E as <- <-; right; auto | left; exact Hin]. }
    constructor.
    - destruct HO as [[-> _] | [-> _]]; [exact (r_nodup _ _ _ _ _ _ _ Hr) |].
      constructor; [exact Hn_notin | exact (r_nodup _ _ _ _ _ _ _ Hr)].
    - intros t0 m0 Hin; destruct (HO' t0 m0 Hin) as [Hin0 | [-> [-> Ea]]]; [exact (Hshb _ _ Hin0) |].
      destruct HO as [[_ [E _]] | [_ [_ [-> Hsh0]]]]; [rewrite E in Ea; discriminate |].
      rewrite barv_set_same; exact Hsh0.
    - intros t0 m0 Hin; destruct (HO' t0 m0 Hin) as [Hin0 | [_ [-> _]]].
      + destruct (r_below _ _ _ _ _ _ _ Hr _ _ Hin0) as [j0 [E Hj]]; exists j0; split; [exact E | lia].
      + exists c; split; [reflexivity | lia].
    - intros p [<- | Hp] Hu Hv.
      + assert (Ea : ac = true) by exact (Hux Hu Hv).
        destruct HO as [[_ [E _]] | [-> _]]; [rewrite E in Ea; discriminate | left; reflexivity].
      + apply HinO, (r_useful _ _ _ _ _ _ _ Hr p Hp); [| exact Hv].
        exact (useful_let_cont m k aA eA cA p (Haid p Hp) Hu).
    - intros p t0 [<- | Hp] Hu Hin.
      + destruct (HO' _ _ Hin) as [Hin0 | [-> _]]; [| reflexivity].
        exfalso; apply Hn_notin, in_map_iff; exists (t0, DBound (c, c)); auto.
      + destruct (HO' _ _ Hin) as [Hin0 | [_ [E _]]]; [| exfalso; exact (Hnotin p Hp E)].
        exact (r_value _ _ _ _ _ _ _ Hr p t0 Hp (useful_let_cont m k aA eA cA p (Haid p Hp) Hu) Hin0).
    - intros o Ho; apply HinO, (r_owner _ _ _ _ _ _ _ Hr o Ho).
    - intros p ny r [<- | Hp] Hv; [discriminate | exact (r_args _ _ _ _ _ _ _ Hr p ny r Hp Hv)].
    - exact (r_written _ _ _ _ _ _ _ Hr). }
  destruct ac eqn:Eac.
  - (* x is active: its adjoint is declared, then transposed *)
    assert (Hcond : varied_value k eA && atom_member (AVar (let_binder k eA)) (fst (needs cv m (S k) (cA (let_binder k eA)))) = true)
      by (rewrite Hneeds; exact Eac).
    assert (Hvr : vr = true) by (apply andb_true_iff in Hcond; tauto).
    assert (Ete : te = Real).
    { destruct te; try destruct (Hra Hvr); [reflexivity |].
      destruct (inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_intror I)) as [_ [o' [_ Es']]].
      rewrite Es in Es'; discriminate. }
    subst te. destruct ve as [d | | | |]; try (simpl in Hht; contradiction).
    set (s2a := store_set s2 (keyv (BarOf (DBound (c, c)))) (VReal 0)).
    assert (Hd : run (bar_declaration W Real (DBound (c, c))) s2 = Some s2a).
    { apply run_define; rewrite xev_DReal, lit_0; reflexivity. }
    assert (Hr2 := Hr' ((tangent (VReal d), DBound (c, c)) :: O) s2a
                     (or_intror (conj eq_refl (conj eq_refl (conj eq_refl I))))).
    assert (Hc13 : (c1 <= c3)%nat) by lia.
    assert (Hag2 : agree_prim c1 (inplace wP pp) s1 s2a)
      by exact (agree_prim_set_bar c1 (inplace wP pp) s1 s2 (DBound (c, c)) (VReal 0)
                  (agree_prim_mono _ _ _ _ _ Hag Hc13) (eq_refl c)).
    assert (Hseed2 : seed_ok (S c) ty se s2a).
    { split.
      - intros y0 Hy; destruct (proj1 Hseed y0 Hy) as [H1 H2].
        split; [exact (below_mono c (S c) y0 H1 (Nat.le_succ_diag_r c)) | exact H2].
      - intros Ety; destruct (proj2 Hseed Ety) as [b0 Hb0]; exists b0; unfold s2a; rewrite xev_set_other; [exact Hb0 |].
        intros y0 Hy K; destruct (Hsel y0 Hy) as [Hcy Hny]; apply keyv_inj in K; [exact (Hny K) | exact Hcy | reflexivity]. }
    assert (Htp2 : tapes_ok (x :: L) s2a).
    { intros p [<- | Hp] Hrp; [discriminate |]; destruct (Htp p Hp Hrp) as [lt Hlt]; exists lt.
      unfold s2a; rewrite store_get_set_other; [exact Hlt |]; intros K; apply keyv_inj in K; [discriminate | reflexivity | reflexivity]. }
    destruct (Hrev s2a _ Hag2 Hr2 Hseed2 Htp2) as [sb [Rrb [Krb [Ksx [Trb [Frb [Srb Prb]]]]]]].
    assert (Hj2 : exists j, DBound (c, c) = DBound (j, j) /\ (j < c2)%nat) by (exists c; split; [reflexivity | lia]).
    assert (Hst2 : match storage wP tail eP with
                   | Some m0 => DBound (c, c) = m0
                   | None => forall p, In p L -> stored p <> DBound (c, c) end) by (rewrite Es; exact Hnotin).
    assert (Hcc2 : (c <= c2)%nat) by lia.
    pose proof (IHr L k c2 wP pp tail eA eW eT eD Real (DBound (c, c)) (VReal d) ty vo HeA HeW HeT HeD
                  (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlv_e Hcc2) (a_bar _ _ _ _ _ _ _ _ _ Hc) Hte Htail_ty Hj2 Hst2 Hve Hvr)
      as IHr'.
    cbv zeta in IHr'; fold vt in IHr'.
    lazymatch type of IHr' with context [@open_pairs ?A ?t c2] =>
      assert (E : @open_pairs A t c2 = (re, c3)) by exact Hre; rewrite E in IHr'; clear E end.
    destruct IHr' as [_ Hrv].
    assert (Hrd : forall p, In p L -> vreads k eA p -> live_value k eW p ->
                    (not_in_loop pp \/ inplace wP pp <> Some (stored p)) ->
                    store_get sb (keyv (stored p)) = Some (primal (pd p))).
    { intros p Hp Hrd0 Hlv Hdj.
      assert (Hbp : below c (stored p)) by (unfold stored; simpl; exact (s_num _ _ _ _ _ _ _ Hs p Hp)).
      destruct (option_dec_ex (inplace wP pp) (stored p)) as [Hex | Hne].
      { destruct Hdj as [Hl | Hne]; [| contradiction].
        unfold inplace in Hex; destruct (owner wP pp) as [o |] eqn:Ho; [| discriminate]; injection Hex as Hex.
        destruct (same_ex_read _ _ _ _ _ _ _ p o Hs Hl Ho Hp ltac:(unfold stored; rewrite Hex; reflexivity) (Hlv_e p Hlv)) as [Epo Hav]; subst o.
        rewrite (Ksx Hl p Ho Hav), Hold by exact Hp.
        exact (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (tbr_let_reads m k aA eA cA p Hcond Hrd0)). }
      rewrite (Frb (stored p) (below_mono c (S c) _ Hbp (Nat.le_succ_diag_r c)) eq_refl ltac:(simpl; tauto) Hne
                 ltac:(intros m0 E; discriminate)).
      unfold s2a; rewrite store_get_set_other; [| unfold keyv, stored; simpl; discriminate].
      rewrite (Hag (stored p) (below_mono c c3 _ Hbp ltac:(lia)) eq_refl I).
      assert (Hvt0 : vo_target (if sweep_eqb m Forward then vo else None) <> Some (stored p)).
      { destruct m; simpl; [| discriminate].
        exact (Hvt eq_refl p Hp (Hlv_e p Hlv)). }
      rewrite (Fb (stored p) (below_mono c (S c) _ Hbp (Nat.le_succ_diag_r c)) eq_refl ltac:(simpl; tauto) Hne Hvt0).
      rewrite Hold; [| exact Hp].
      exact (a_store _ _ _ _ _ _ _ _ _ Hc p Hp (tbr_let_reads m k aA eA cA p Hcond Hrd0)). }
    assert (Hr3 : rctx L c2 wP pp O (vflows k eA) sb).
    { constructor.
      - exact (r_nodup _ _ _ _ _ _ _ Hr).
      - intros t0 m0 Hin; apply Srb; right; exact Hin.
      - intros t0 m0 Hin; destruct (r_below _ _ _ _ _ _ _ Hr _ _ Hin) as [j0 [E Hj]]; exists j0; split; [exact E | lia].
      - intros p Hp Hf Hv; exact (r_useful _ _ _ _ _ _ _ Hr p Hp (useful_let_flows m k aA eA cA p Hcond Hf) Hv).
      - intros p t0 Hp Hf Hin; exact (r_value _ _ _ _ _ _ _ Hr p t0 Hp (useful_let_flows m k aA eA cA p Hcond Hf) Hin).
      - exact (r_owner _ _ _ _ _ _ _ Hr).
      - exact (r_args _ _ _ _ _ _ _ Hr).
        - exact (r_written _ _ _ _ _ _ _ Hr). }
    assert (Htpb : tapes_ok L sb).
    { intros p Hp Hrp; destruct (Htp2 p (or_intror Hp) Hrp) as [lt Hlt]; exact (Trb _ _ Hlt). }
    destruct (Hrv sb O Hrd Hr3 (fun _ => conj Hn_notin (Srb _ _ (or_introl eq_refl))) Htpb) as [s3 [R3 [K3 [Kn3 [T3 [F3 [S3 P3]]]]]]].
    exists s3; split.
    { rewrite run_app, Hd, run_app.
      lazymatch goal with |- match ?r with _ => _ end = _ => replace r with (Some sb) by (symmetry; exact Rrb) end.
      exact R3. }
    split.
    { intros Hm; apply (vo_kept_trans _ _ s2a); [apply vo_kept_set_bar; exact I |].
      apply (vo_kept_trans _ _ sb); [exact (Krb Hm) |].
      intros t0 Ht0 _; destruct (Hvb Hm t0 Ht0) as [Hb0 [Hc0 Hp0]].
      apply K3; [exact (below_mono c c2 t0 Hb0 Hcc2) | exact Hc0 | exact Hp0 |].
      intros ->; simpl in Hb0; lia. }
    split.
    { intros Hl o Ho Hav; assert (He : inplace wP pp = Some (stored o)) by (unfold inplace; rewrite Ho; reflexivity).
      remember (stored o) as e eqn:Ee; destruct (ex_below _ _ _ _ _ _ _ _ Hs He) as [Hb0 [Hc0 Hp0]].
      rewrite (K3 e (below_mono c c2 e Hb0 Hcc2) Hc0 Hp0) by (intros ->; simpl in Hb0; lia).
      rewrite Ee, (Ksx Hl o Ho Hav), <- Ee; clear Ee.
      apply (F1 e (below_mono c c1 e Hb0 ltac:(lia)) Hc0); [destruct e; simpl in Hp0 |- *; tauto | intros E; injection E as E; subst e; simpl in Hb0; lia | discriminate]. }
    split.
    { apply (tapes_kept_trans _ s2a); [unfold s2a; apply tapes_kept_set; [simpl; tauto | reflexivity] |].
      exact (tapes_kept_trans _ _ _ Trb T3). }
    assert (HO'b : forall m0, In m0 (map snd ((tangent (VReal d), DBound (c, c)) :: O)) ->
                     In m0 (map snd O) \/ ~ below c (BarOf m0)).
    { intros m0 [<- | Hm]; [right; simpl; lia | left; exact Hm]. }
    split.
    { apply (rev_frame_trans _ _ _ _ s2a).
      - intros v0 Hb0 Hc0 _ _ _; unfold s2a; apply store_get_set_other; intros K.
        apply keyv_inj in K; [| reflexivity | exact Hc0]; subst v0; simpl in Hb0; lia.
      - apply (rev_frame_trans _ _ _ _ sb).
        + exact (rev_frame_mono c (S c) _ _ _ _ _ Frb (Nat.le_succ_diag_r c) HO'b).
        + rewrite (oput_notin O _ _ Hn_notin) in F3; exact (rev_frame_mono c c2 _ _ _ _ _ F3 Hcc2 HO'b). }
    split; [exact S3 |].
    rewrite P3, (oput_notin O _ _ Hn_notin).
    etransitivity; [exact Prb |].
    exact (result_pairing_fresh O ty _ v se s2 (DBound (c, c)) _ Hok eq_refl Hn_notin Hsel).
  - (* x is not active *)
    simpl in Hre; injection Hre as <- <-.
    assert (Hc13 : (c1 <= c2)%nat) by lia.
    assert (Hseed' : seed_ok (S c) ty se s2).
    { split; [| exact (proj2 Hseed)]; intros y0 Hy; destruct (proj1 Hseed y0 Hy) as [H1 H2].
      split; [exact (below_mono c (S c) y0 H1 (Nat.le_succ_diag_r c)) | exact H2]. }
    assert (Htp2 : tapes_ok (x :: L) s2) by (intros p [<- | Hp] Hrp; [discriminate | exact (Htp p Hp Hrp)]).
    destruct (Hrev s2 O (agree_prim_mono _ _ _ _ _ Hag Hc13) (Hr' O s2 (or_introl (conj eq_refl (conj eq_refl eq_refl)))) Hseed' Htp2)
      as [sb [Rrb [Krb [Ksx [Trb [Frb [Srb Prb]]]]]]].
    exists sb; split; [rewrite app_nil_r; exact Rrb |].
    split; [exact Krb |].
    split.
    { intros Hl o Ho Hav; assert (He : inplace wP pp = Some (stored o)) by (unfold inplace; rewrite Ho; reflexivity).
      remember (stored o) as e eqn:Ee; destruct (ex_below _ _ _ _ _ _ _ _ Hs He) as [Hb0 [Hc0 Hp0]].
      rewrite Ee, (Ksx Hl o Ho Hav), <- Ee; clear Ee.
      apply (F1 e (below_mono c c1 e Hb0 ltac:(lia)) Hc0); [destruct e; simpl in Hp0 |- *; tauto | intros E; injection E as E; subst e; simpl in Hb0; lia | discriminate]. }
    split; [exact Trb |].
    split; [| split; [exact Srb | exact Prb]].
    apply (rev_frame_mono c (S c) _ _ _ _ _ Frb (Nat.le_succ_diag_r c)); auto.
Qed.

(* ---------------------------------------------------------------------------
   Straight-line bodies: the lets bind operations, reads and updates of
   arrays (no branch, no loop). *)

Definition straight_value {V I : Type} (e : value V I) : Prop :=
  match e with AOp1 _ _ | AOp2 _ _ _ | AGet _ _ | ASet _ _ _ => True | _ => False end.

Fixpoint straight {V I : Type} (b : anf V I) : Prop :=
  match b with
  | ALet _ e b' => straight_value e /\ forall x, straight (b' x)
  | ARet _ => True
  end.

(* The reverse sweep of a straight value writes only adjoints. *)
Lemma straight_rev_bars (eP : value pv bare) : straight_value eP ->
  forall L eT tr wt vo te n c, value_eq (gT L) eP eT ->
  Forall bar_stmt (fst (open_pairs (rev_value W wt vo (rebuild_value _ eT tr) te n) c)).
Proof.
  intros Hs L eT tr wt vo te n c HT.
  destruct eP, eT; simpl in Hs, HT; try contradiction; cbn [rebuild_value rev_value open_pairs fst].
  - destruct (partial1 _ _) as [p |]; [apply contribution_bars | constructor].
  - destruct (partial2 _ _ _) as [[pa pb] |]; [apply Forall_app; split; apply contribution_bars | constructor].
  - destruct (@bar W _) as [bx |] eqn:Eb; [| constructor].
    destruct (bar_some _ _ Eb) as [y [-> Hy]]; repeat constructor; exact Hy.
  - destruct (@bar W _) as [bx |] eqn:Eb; [destruct (bar_some _ _ Eb) as [y [-> Hy]] |]; repeat constructor; exact Hy.
Qed.

(* A value whose reverse code writes only adjoints, proved as the operations
   are (asim_rev0), satisfies asim_rev. *)
Lemma asim_rev_bars (eP : value pv bare) :
  asim_rev0 eP ->
  (forall L eT tr wt vo te n c, value_eq (gT L) eP eT ->
     Forall bar_stmt (fst (open_pairs (rev_value W wt vo (rebuild_value _ eT tr) te n) c))) ->
  asim_rev eP.
Proof.
  intros H0 Hb L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs Hbar Htc Htail Hn Hst Hve Hvr.
  specialize (H0 L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs Hbar Htc Htail Hn Hst Hve Hvr).
  specialize (Hb L eT (annotate_value_t cv k eA) (option_map (amap pt) wP) vo te n c HT).
  destruct (open_pairs (rev_value W (option_map (amap pt) wP) vo (rebuild_value (tvar W) eT (annotate_value_t cv k eA)) te n) c)
    as [re c'] eqn:E; simpl in Hb.
  destruct H0 as [Hc Hrv]; split; [exact Hc |]; intros s2 O Hrd Hr Hns _.
  destruct (Hrv s2 O (fun p Hp Hrd0 Hlv Hsc => Hrd p Hp Hrd0 Hlv (or_intror (scalar_not_inplace _ _ _ _ _ _ _ _ Hs Hp Hlv Hsc)))
              Hr Hns) as [s3 [R3 [F3 [S3 P3]]]].
  exists s3; split; [exact R3 |]; split; [| split; [| split; [| auto]]].
  - intros v Hb0 Hc0 Hp0 _; apply (run_bars re s2 s3 Hb R3); destruct v; simpl in Hp0 |- *; tauto.
  - intros _ _ o _ _; destruct Hn as [jn [-> _]]; apply (run_bars re s2 s3 Hb R3); simpl; tauto.
  - intros v l Hv; exists l; rewrite (run_bars re s2 s3 Hb R3 (TapeOf v) ltac:(simpl; tauto)); exact Hv.
Qed.

(* A straight value is updated in place only in the body of an in-place loop. *)
Lemma inplace_straight (eP : value pv bare) : straight_value eP -> inplace_only eP.
Proof.
  intros Hs L k wP pp tail eW te HW Htc Hst Hl.
  destruct eP as [| | | aP iP vP | | |]; simpl in Hs; try contradiction; simpl in Hst; try (destruct Hst; reflexivity).
  destruct eW; simpl in HW; try contradiction; simpl in Htc.
  destruct pp; simpl in Htc, Hl; [| | | destruct Hl];
    repeat match type of Htc with context [match ?e with _ => _ end] => destruct e end; discriminate.
Qed.

Theorem asim_straight : forall bP : anf pv bare, straight bP -> asim_body bP.
Proof.
  enough (H : (forall b : anf pv bare, straight b -> asim_body b) /\
               (forall e : value pv bare, straight_value e -> asim_fwd e /\ asim_rev e /\ act_value e /\ act_owner e))
    by exact (proj1 H).
  apply (anf_value_ind pv bare (fun b => straight b -> asim_body b)
           (fun e => straight_value e -> asim_fwd e /\ asim_rev e /\ act_value e /\ act_owner e)).
  - intros a e IHe b IHb [He Hb]; destruct (IHe He) as [Hf [Hr [Ha Ho]]].
    apply asim_let; auto; apply inplace_straight; exact He.
  - intros x _; apply asim_ret.
  - intros f x Hs; split; [apply afwd_op1 | split; [apply asim_rev_bars; [apply arev_op1 | exact (straight_rev_bars _ Hs)] | split; [apply act_op1 | apply owner_op1]]].
  - intros f x y Hs; split; [apply afwd_op2 | split; [apply asim_rev_bars; [apply arev_op2 | exact (straight_rev_bars _ Hs)] | split; [apply act_op2 | apply owner_op2]]].
  - intros x i Hs; split; [apply afwd_get | split; [apply asim_rev_bars; [apply arev_get | exact (straight_rev_bars _ Hs)] | split; [apply act_get | apply owner_get]]].
  - intros x i y Hs; split; [apply afwd_set | split; [apply asim_rev_bars; [apply arev_set | exact (straight_rev_bars _ Hs)] | split; [apply act_set | apply owner_set]]].
  - intros c t _ e _ []. 
  - intros lo hi b _ [].
  - intros a lo hi init b _ [].
Qed.

End Sim.
