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

Definition pairing (O : owners) (s : store R) : R :=
  fold_right (fun '(t, n) acc => inner t (barv s n) + acc) 0 O.

(* The storage n now holds a variable of tangent t. *)
Definition oset (O : owners) (n : dvar W) (t : val R) : owners :=
  map (fun '(t', n') => if Simplify.dvar_eq nat n n' then (t, n') else (t', n')) O.

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

Lemma dvar_eq_dec_c (a b : dvar W) : {a = b} + {a <> b}.
Proof. decide equality; decide equality; apply Nat.eq_dec. Qed.

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

End Sim.
