(* AdjointTop.v — the adjoint simulation at the level of a function: the
   arguments are opened, their adjoints given (AdjointSpec.v), the body
   simulated (AdjointCorrect.v) from the forward sweep to the reverse sweep,
   and the final adjoints read back as the gradient. The pairing of the owners
   (the arguments that carry an adjoint) at the end of the reverse sweep, minus
   the initial adjoints, is the dot product of the tangent of the seed with
   the gradient; the simulation of the body makes it the tangent of the
   result times the seed. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint Simplify Scoping
  AnfEquiv Correctness TangentCorrect TangentTop AdjointCorrect AdjointSpec DualsDerive.

Import ListNotations.
Open Scope list_scope.

(* The analyses open the arguments as open_P does, in either mode. *)
Lemma annotate_open_cv cv (dP : adefinition pv bare) : forall L k xs L' res bP dA,
  adefinition_eq (gA L) dP dA -> open_P dP k xs L = Some (L', res, bP) ->
  exists bA, anf_eq (gA L') bP bA /\
             annotate_definition_t cv k dA = annotate_body_t cv Forward (k + length xs) bA.
Proof.
  induction dP as [n t r f IH | rP bP0]; intros L k xs L' res bP dA HA Ho.
  - destruct dA as [n' t' r' fA |]; simpl in HA; [| contradiction].
    destruct HA as [<- [<- [<- HA]]]; destruct xs as [| x xs]; simpl in Ho; [discriminate |].
    destruct (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP (fA (AV k (varied_role r)))
                (HA _ _) Ho) as [bA [H1 H2]].
    exists bA; split; [exact H1 |]; simpl; rewrite H2; f_equal; lia.
  - destruct dA as [| rA bA]; simpl in HA; [contradiction |].
    destruct xs; simpl in Ho; [| discriminate]; injection Ho as <- <- <-.
    exists bA; split; [exact (proj2 HA) | simpl; rewrite Nat.add_0_r; reflexivity].
Qed.

(* ---------------------------------------------------------------------------
   Stores with distinct keys. *)

Lemma store_get_in (s : store R) k v : NoDup (map fst s) -> In (k, v) s -> store_get s k = Some v.
Proof.
  induction s as [| [k0 v0] s IH]; intros Hnd Hin; [destruct Hin |].
  inversion Hnd as [| ? ? Hk Hnd']; subst; simpl.
  destruct Hin as [E | Hin].
  - injection E as -> ->; rewrite key_eqb_refl; reflexivity.
  - destruct (key_eqb k0 k) eqn:E; [| apply IH; auto].
    apply key_eqb_eq in E; subst k0; exfalso; apply Hk, in_map_iff; exists (k, v); auto.
Qed.

Lemma store_get_notin (s : store R) k : ~ In k (map fst s) -> store_get s k = None.
Proof.
  induction s as [| [k0 v0] s IH]; intros Hn; simpl; [reflexivity |].
  destruct (key_eqb k0 k) eqn:E; [apply key_eqb_eq in E; subst; destruct Hn; left; reflexivity |].
  apply IH; intros H; apply Hn; right; exact H.
Qed.

(* The store exec_scoped builds from the parameters and the arguments. *)
Definition param_store (ps : list (dparam nat)) (args : list (val R)) : store R :=
  map (fun '(DParam _ _ x, a) => (KVar x, a)) (combine ps args).

Definition pvar (p : dparam nat) : dvar nat := let 'DParam _ _ x := p in x.

Lemma param_store_keys ps args :
  length ps = length args -> map fst (param_store ps args) = map (fun p => KVar (pvar p)) ps.
Proof.
  revert args; induction ps as [| [pw t y] ps IH]; intros [| a args] Hl; simpl in *; try discriminate; auto.
  f_equal; apply IH; lia.
Qed.

Lemma param_store_get ps args i pw t y a :
  length ps = length args -> NoDup (map pvar ps) -> nth_error ps i = Some (DParam pw t y) -> nth_error args i = Some a ->
  store_get (param_store ps args) (KVar y) = Some a.
Proof.
  intros Hl Hnd Hp Ha; apply store_get_in.
  - rewrite param_store_keys by exact Hl.
    rewrite <- map_map with (f := pvar) (g := fun x => KVar x).
    apply NoDup_map_inv with (f := fun k0 => match k0 with KVar x => x | Returned => ResultVar end).
    rewrite map_map; simpl; rewrite map_id; exact Hnd.
  - unfold param_store; apply in_map_iff; exists (DParam pw t y, a); split; [reflexivity |].
    revert args i Hl Ha Hp; clear Hnd; induction ps as [| q ps IH]; intros [| b args] [| i] Hl Ha Hp;
      simpl in *; try discriminate.
    + injection Hp as ->; injection Ha as ->; left; reflexivity.
    + right; apply (IH args i); auto.
Qed.

(* The adjoint function, opened at the numbers simplify uses, from the
   primal arguments, their adjoints and the seed: it computes the gradient,
   the transpose of the tangent of the dual evaluation applied to the seed. *)
Theorem adjoint_simulates_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) ->
     asim_body cv bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
  intros Hpar Hwf Hfit Hlxb Hlyb Hsim Hev.
  set (xs := seed_args (decls f) x dx) in *.
  pose proof (normalize_parametric f Hpar) as Hnp.
  set (dP := afdef (normalize f) pv).
  assert (HD := Hnp pv (val (dual R))); fold dP in HD.
  unfold aeval_function in Hev.
  destruct (open_P_some dP [] 0 xs _ v HD Hev) as [L [res [bP Ho]]].
  specialize (Hsim L res bP Ho).
  destruct (open_P_args dP 0 xs [] L res bP Ho) as [new [EL [Hlen Hargs]]].
  rewrite app_nil_r in EL; subst new.
  destruct (annotate_open_cv cv dP [] 0 xs L res bP _ (Hnp pv avar) Ho) as [bA [HbA Htr]].
  destruct (wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho) as [resW [bW [HrW [HbW Hwfd]]]].
  destruct (eval_open dP [] 0 xs L res bP _ HD Ho) as [bD [HbD HevD]].
  rewrite HevD in Hev.
  assert (Hds := decls_open dP (map (fun p => (p, tt)) []) [] 0 xs L res bP _ (Hnp pv unit) Ho).
  assert (Hds' : decls f = map (fun p => fst (arg_entry p)) (rev L)) by exact Hds.
  clear Hds; rename Hds' into Hds.
  rewrite Nat.add_0_l in Htr, Hwfd.
  set (n := length xs) in *.
  set (tr := annotate_definition_t cv 0 (afdef (normalize f) avar)) in *.
  destruct (tangent_open dP [] 0 xs L res bP (afdef (normalize f) (tvar W)) tr (adjoint_body W cv)
              (Hnp pv (tvar W)) Ho) as [resT [bT [HrT [HbT Hopen]]]].
  rewrite Nat.add_0_l in Hopen; fold n in Hopen.
  unfold well_formed in Hwf; fold (decls f) in Hwf.
  destruct (non_real_varied (decls f)) eqn:Hnrv; [discriminate |].
  rewrite Hwfd in Hwf.
  change (open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0)
    with (open_pairs (open_arguments W (rebuild_definition (tvar W) (afdef (normalize f) (tvar W)) tr) 0
                        (map arg_entry []) (adjoint_body W cv)) 0).
  rewrite Hopen; unfold adjoint_body; rewrite Htr.
  (* the arguments *)
  assert (Hargs' : forall p, In p L -> exists i nm t r x0, p = arg_pv nm t r i x0 /\ nth_error xs i = Some x0 /\
                                       nth_error (decls f) i = Some (Decl nm t r) /\ (i < n)%nat).
  { intros p Hp; apply in_rev in Hp; apply In_nth_error in Hp as [i Hi].
    destruct (Hargs i p Hi) as [nm [t [r [x0 [-> Hx0]]]]]; exists i, nm, t, r, x0.
    split; [reflexivity | split; [exact Hx0 | split]].
    - rewrite Hds, nth_error_map, Hi; reflexivity.
    - apply nth_error_Some; congruence. }
  assert (HnL : NoDup (map pn (rev L))).
  { apply NoDup_nth_error; intros i j Hi E.
    rewrite length_map in Hi; destruct (nth_error (rev L) i) as [p |] eqn:Ep; [| apply nth_error_None in Ep; lia].
    rewrite !nth_error_map, Ep in E; simpl in E.
    destruct (nth_error (rev L) j) as [q |] eqn:Eq; [| discriminate]; injection E as E.
    destruct (Hargs i p Ep) as [? [? [? [? [-> _]]]]]; destruct (Hargs j q Eq) as [? [? [? [? [-> _]]]]].
    simpl in E; lia. }
  assert (Hstat : Forall (static_ok n) L).
  { apply Forall_forall; intros p Hp.
    destruct (Hargs' p Hp) as [i [nm [t [r [x0 [-> [Hx0 [Hd Hi]]]]]]]].
    destruct (seed_args_nth (decls f) x dx i nm t r Hfit Hd) as [v0 [tg [_ [Hxs [Hf0 Hz0]]]]].
    fold xs in Hxs; rewrite Hx0 in Hxs; injection Hxs as ->.
    repeat split; simpl; auto; try discriminate.
    - intros Hv; apply (non_real_varied_none (decls f) nm t r Hnrv); [apply nth_error_In with i; exact Hd | exact Hv].
    - exact (fits_type nm t r v0 tg Hf0). }
  assert (Huniq : ids_unique L).
  { intros p q Hp Hq E; destruct (Hargs' p Hp) as [i [nm [t [r [x0 [-> [Hx [Hd _]]]]]]]].
    destruct (Hargs' q Hq) as [i' [nm' [t' [r' [x0' [-> [Hx' [Hd' _]]]]]]]]; simpl in E; subst i'.
    rewrite Hx in Hx'; injection Hx' as <-; rewrite Hd in Hd'; injection Hd' as <- <- <-; reflexivity. }
  assert (Hnum : forall p, In p L -> (pn p < n)%nat)
    by (intros p Hp; destruct (Hargs' p Hp) as [? [? [? [? [? [-> [_ [_ Hi]]]]]]]]; exact Hi).
  assert (Hxs : xs = map pd (rev L)).
  { apply nth_error_ext; intros i.
    destruct (nth_error (rev L) i) as [p |] eqn:Ep.
    - destruct (Hargs i p Ep) as [nm [t [r [x0 [-> Hx0]]]]]; rewrite Hx0, nth_error_map, Ep; reflexivity.
    - rewrite nth_error_map, Ep; apply nth_error_None; apply nth_error_None in Ep.
      rewrite length_rev in Ep; lia. }
  destruct (wf_result_facts _ _ _ _ Hwf) as [[EW [Hnw HtcB]] | [w [nm [role [EW [Hg [Hwr [H1w [Hraw [HtcB [Hdep Hinout]]]]]]]]]]].
  - (* the function returns a real *)
    admit.
  - (* the function writes an argument *)
    admit.
Admitted.
