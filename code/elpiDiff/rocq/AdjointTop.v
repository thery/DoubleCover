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

(* A key in the store stays in it: the statements only set keys. *)
Definition keeps (s s' : store R) : Prop := forall k, store_get s k <> None -> store_get s' k <> None.

Lemma keeps_set s k v : keeps s (store_set s k v).
Proof. intros k' H; rewrite store_get_set; destruct (key_eqb k k'); [discriminate | exact H]. Qed.

Lemma keeps_trans s1 s2 s3 : keeps s1 s2 -> keeps s2 s3 -> keeps s1 s3.
Proof. intros H1 H2 k H; exact (H2 k (H1 k H)). Qed.

Lemma assign_keeps s l v s' : assign reals s l v = Some s' -> keeps s s'.
Proof.
  unfold assign; intros E.
  repeat match type of E with context [match ?e with _ => _ end] => destruct e end; try discriminate;
    injection E as <-; apply keeps_set.
Qed.

Lemma exec_up_keeps (body : store R -> option (store R)) i lo n s s' :
  (forall s1 s2, body s1 = Some s2 -> keeps s1 s2) -> exec_up R body i lo n s = Some s' -> keeps s s'.
Proof.
  intros Hb; revert lo s; induction n as [| n IH]; intros lo s E; simpl in E.
  - injection E as <-; intros k H; exact H.
  - destruct (body _) as [s1 |] eqn:E1; [| discriminate].
    apply (keeps_trans _ (store_set s (KVar i) (VInt lo))); [apply keeps_set |].
    apply (keeps_trans _ s1); [exact (Hb _ _ E1) | exact (IH _ _ E)].
Qed.

Lemma exec_down_keeps (body : store R -> option (store R)) i hi n s s' :
  (forall s1 s2, body s1 = Some s2 -> keeps s1 s2) -> exec_down R body i hi n s = Some s' -> keeps s s'.
Proof.
  intros Hb; revert hi s; induction n as [| n IH]; intros hi s E; simpl in E.
  - injection E as <-; intros k H; exact H.
  - destruct (body _) as [s1 |] eqn:E1; [| discriminate].
    apply (keeps_trans _ (store_set s (KVar i) (VInt hi))); [apply keeps_set |].
    apply (keeps_trans _ s1); [exact (Hb _ _ E1) | exact (IH _ _ E)].
Qed.

Fixpoint exec_keeps (st : dstmt nat) : forall s s', exec reals st s = Some s' -> keeps s s'.
Proof.
  assert (Hl : forall l s s', (fix exec_stmts (l : list (dstmt nat)) (s : store R) : option (store R) :=
                                 match l with
                                 | [] => Some s
                                 | st' :: l' => match exec reals st' s with Some s1 => exec_stmts l' s1 | None => None end
                                 end) l s = Some s' -> keeps s s').
  { induction l as [| st0 l IHl]; intros s s' E; [injection E as <-; intros k H; exact H |].
    destruct (exec reals st0 s) as [s1 |] eqn:E1; [| discriminate].
    exact (keeps_trans _ _ _ (exec_keeps st0 s s1 E1) (IHl s1 s' E)). }
  intros sa sb E; destruct st; cbn [exec] in E;
    repeat match type of E with
           | context [match ?e with _ => _ end] =>
               lazymatch e with
               | assign _ _ _ _ => fail
               | exec_up _ _ _ _ _ _ => fail
               | exec_down _ _ _ _ _ _ => fail
               | _ => destruct e
               end
           end; try discriminate;
    try (injection E as <-; apply keeps_set);
    try (exact (Hl _ _ _ E));
    try (exact (assign_keeps _ _ _ _ E)).
  - exact (exec_up_keeps _ _ _ _ _ _ (Hl _) E).
  - exact (exec_down_keeps _ _ _ _ _ _ (Hl _) E).
  - eapply keeps_trans; [apply keeps_set | exact (assign_keeps _ _ _ _ E)].
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

(* ---------------------------------------------------------------------------
   Dot products. *)

Lemma dotl_nil_l b : dotl [] b = 0.
Proof. reflexivity. Qed.

Lemma dotl_cons a l b m : dotl (a :: l) (b :: m) = (a * b + dotl l m)%R.
Proof. reflexivity. Qed.

Lemma dotl_app a1 a2 b1 b2 :
  length a1 = length b1 -> dotl (a1 ++ a2) (b1 ++ b2) = (dotl a1 b1 + dotl a2 b2)%R.
Proof.
  revert b1; induction a1 as [| a a1 IH]; intros [| b b1] H; simpl in H; try discriminate.
  - rewrite !app_nil_l; change (dotl [] []) with 0%R; ring.
  - rewrite <- !app_comm_cons, !dotl_cons, IH by lia; ring.
Qed.

Lemma dotl_lsub a r q :
  length a = length r -> length r = length q -> dotl a (lsub r q) = (dotl a r - dotl a q)%R.
Proof.
  revert r q; induction a as [| a l IH]; intros [| r rs] [| q qs] H1 H2; simpl in H1, H2; try discriminate.
  - unfold dotl, lsub; simpl; ring.
  - change (lsub (r :: rs) (q :: qs)) with ((r - q)%R :: lsub rs qs); rewrite !dotl_cons, IH by lia; ring.
Qed.

Lemma dotl_repeat0 a m : dotl a (repeat 0%R m) = 0%R.
Proof.
  revert m; induction a as [| a l IH]; intros [| m]; try reflexivity.
  simpl repeat; rewrite dotl_cons, IH; ring.
Qed.

Lemma inner_dotl t b : shaped t (Some b) -> inner t (Some b) = dotl (reals_of_val t) (reals_of_val b).
Proof.
  intros H; destruct t, b; simpl in H |- *; try contradiction; unfold dotl; simpl; try ring; reflexivity.
Qed.

Lemma nreals_length v : nreals v = length (reals_of_val v).
Proof. destruct v; reflexivity. Qed.

(* The tangents of the seeded arguments, laid in one list, are the seed. *)
Lemma pair_with_tangent l B : length B = length l -> map dsnd (pair_with l B) = B.
Proof.
  revert B; induction l as [| r l IH]; intros [| b B] H; simpl in H; try discriminate; auto.
  simpl; f_equal; apply IH; lia.
Qed.

Lemma tangent_val_dual v B : length B = nreals v -> reals_of_val (TangentCorrect.tangent (val_dual v B)) = B.
Proof.
  destruct v as [r | z | bo | l | l]; simpl; intros H.
  - destruct B as [| b [| ]]; simpl in H; try discriminate; reflexivity.
  - destruct B; [reflexivity | discriminate].
  - destruct B; [reflexivity | discriminate].
  - apply pair_with_tangent; exact H.
  - destruct B; [reflexivity | discriminate].
Qed.

Lemma seed_tangents ds x dx :
  Forall2 fits ds x -> length dx = in_dim x ->
  seed ds x dx = concat (map (fun d => reals_of_val (TangentCorrect.tangent d)) (seed_args ds x dx)).
Proof.
  unfold in_dim, reals_of_args; intros H; revert dx; induction H as [| [nm t r] v ds x Hf Hfs IH]; intros dx Hl;
    [reflexivity |].
  cbn [map concat] in Hl |- *; rewrite length_app in Hl.
  change (seed (Decl nm t r :: ds) (v :: x) dx) with
    ((if varied_role r then firstn (nreals v) dx else repeat 0%R (nreals v)) ++ seed ds x (skipn (nreals v) dx)).
  change (seed_args (Decl nm t r :: ds) (v :: x) dx) with
    (val_dual v (if varied_role r then firstn (nreals v) dx else repeat 0%R (nreals v)) :: seed_args ds x (skipn (nreals v) dx)).
  cbn [map concat]; rewrite tangent_val_dual.
  - f_equal; apply IH; rewrite length_skipn; rewrite nreals_length in *; lia.
  - destruct (varied_role r); [rewrite length_firstn; rewrite nreals_length; lia | apply repeat_length].
Qed.

(* ---------------------------------------------------------------------------
   The gradient against the seed. *)

Definition decl_role (d : decl) : role := let 'Decl _ _ r := d in r.

Definition slice (d : decl) (v : val R) (dx : list R) : list R :=
  if varied_role (decl_role d) then firstn (nreals v) dx else repeat 0%R (nreals v).

(* The sum the gradient computes against the seed: for each argument with an
   adjoint, the tangent times its final adjoint, minus the tangent times its
   initial adjoint (the seed of a written argument excepted). *)
Fixpoint grad_rhs (ds : list decl) (x : list (val R)) (xb dx : list R) (bars : list (val R)) : R :=
  match ds, x with
  | d :: ds', v :: x' =>
      let m := nreals v in
      if has_dot d then
        match bars with
        | b :: bars' =>
            (dotl (slice d v dx) (reals_of_val b) - (if written_decl d then 0 else dotl (slice d v dx) (firstn m xb))
             + grad_rhs ds' x' (skipn m xb) (skipn m dx) bars')%R
        | [] => 0%R
        end
      else grad_rhs ds' x' (skipn m xb) (skipn m dx) bars
  | _, _ => 0%R
  end.

(* The final adjoints have the shape of their arguments. *)
Fixpoint bars_fit (ds : list decl) (x : list (val R)) (bars : list (val R)) : Prop :=
  match ds, x with
  | d :: ds', v :: x' =>
      if has_dot d then
        match bars with
        | b :: bars' => length (reals_of_val b) = nreals v /\ bars_fit ds' x' bars'
        | [] => False
        end
      else bars_fit ds' x' bars
  | [], [] => bars = []
  | _, _ => False
  end.

Lemma gradient_dotl ds x xb dx bars :
  Forall2 fits ds x -> length xb = in_dim x -> length dx = in_dim x -> bars_fit ds x bars ->
  exists g, gradient ds x xb bars = Some g /\ length g = in_dim x /\
            dotl (seed ds x dx) g = grad_rhs ds x xb dx bars.
Proof.
  unfold in_dim, reals_of_args; intros H; revert xb dx bars.
  induction H as [| [nm t r] v ds x Hf Hfs IH]; intros xb dx bars Hxb Hdx Hb.
  - simpl in Hb; subst bars; exists []; split; [reflexivity | split; reflexivity].
  - cbn [map concat] in Hxb, Hdx; rewrite length_app in Hxb, Hdx.
    set (m := nreals v).
    assert (Hm : m = length (reals_of_val v)) by apply nreals_length.
    assert (Hsl : length (slice (Decl nm t r) v dx) = m).
    { unfold slice; simpl; destruct (varied_role r); [rewrite length_firstn; lia | apply repeat_length]. }
    change (seed (Decl nm t r :: ds) (v :: x) dx) with (slice (Decl nm t r) v dx ++ seed ds x (skipn m dx)).
    cbn [gradient grad_rhs bars_fit] in Hb |- *.
    destruct (has_dot (Decl nm t r)) eqn:Hd.
    + destruct bars as [| b bars]; [contradiction |]; destruct Hb as [Hlb Hb].
      destruct (IH (skipn m xb) (skipn m dx) bars ltac:(rewrite length_skipn; lia) ltac:(rewrite length_skipn; lia) Hb)
        as [g [Hg [Hlg Hdg]]].
      fold m; rewrite Hg.
      set (piece := if written_decl (Decl nm t r) then reals_of_val b else lsub (reals_of_val b) (firstn m xb)).
      assert (Hlp : length piece = m).
      { unfold piece; destruct (written_decl (Decl nm t r)); [lia |].
        unfold lsub; rewrite length_map, length_combine, length_firstn; lia. }
      exists (piece ++ g); split; [reflexivity |].
      split; [cbn [map concat]; rewrite !length_app; lia |].
      rewrite dotl_app by lia; rewrite Hdg; unfold piece.
      destruct (written_decl (Decl nm t r)); [ring |].
      rewrite dotl_lsub by (rewrite ?length_firstn; lia); ring.
    + destruct (IH (skipn m xb) (skipn m dx) bars ltac:(rewrite length_skipn; lia) ltac:(rewrite length_skipn; lia) Hb)
        as [g [Hg [Hlg Hdg]]].
      fold m; rewrite Hg; simpl.
      exists (repeat 0%R m ++ g); split; [reflexivity |].
      split; [cbn [map concat]; rewrite !length_app, repeat_length; lia |].
      rewrite dotl_app by (rewrite repeat_length; lia); rewrite dotl_repeat0, Hdg; ring.
Qed.

Lemma run_keeps ss s s' : run ss s = Some s' -> keeps s s'.
Proof.
  unfold run; generalize (map (Simplify.out_dstmt nat) ss); clear ss; intros l; revert s.
  induction l as [| st l IH]; intros s E; simpl in E; [injection E as <-; intros k H; exact H |].
  destruct (exec reals st s) as [s1 |] eqn:E1; [| discriminate].
  exact (keeps_trans _ _ _ (exec_keeps st s s1 E1) (IH s1 E)).
Qed.

(* ---------------------------------------------------------------------------
   The arguments that carry an adjoint, the owners of the pairing. *)

Definition dname (p : pv) : decl := fst (arg_entry p).

Fixpoint owners_of (Ls : list pv) : owners :=
  match Ls with
  | [] => []
  | p :: Ls' => (if has_dot (dname p) then [(TangentCorrect.tangent (pd p), stored p)] else []) ++ owners_of Ls'
  end.

(* The tangents times the initial adjoints, the seed excepted. *)
Fixpoint init_sum (Ls : list pv) (s : store R) : R :=
  match Ls with
  | [] => 0%R
  | p :: Ls' =>
      ((if has_dot (dname p) && negb (written_decl (dname p))
        then inner (TangentCorrect.tangent (pd p)) (barv s (stored p)) else 0) + init_sum Ls' s)%R
  end.

(* The adjoints of the arguments, in order, have the shape of their tangents. *)
Fixpoint bars_in (Ls : list pv) (s : store R) (bars : list (val R)) : Prop :=
  match Ls with
  | [] => bars = []
  | p :: Ls' =>
      if has_dot (dname p) then
        match bars with
        | b :: bars' => barv s (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b) /\ bars_in Ls' s bars'
        | [] => False
        end
      else bars_in Ls' s bars
  end.

Lemma pairing_app O1 O2 s : pairing (O1 ++ O2) s = (pairing O1 s + pairing O2 s)%R.
Proof. induction O1 as [| [t n] O1 IH]; simpl; [ring | rewrite IH; ring]. Qed.

Lemma shaped_length t b : shaped t (Some b) -> length (reals_of_val b) = length (reals_of_val t).
Proof. destruct t, b; simpl; try contradiction; auto. Qed.


Lemma grad_rhs_pairing ds x xb yb dx Ls s0 s3 bars :
  Forall2 fits ds x -> length xb = in_dim x -> length dx = in_dim x ->
  map dname Ls = ds -> map pd Ls = seed_args ds x dx ->
  bars_in Ls s3 bars -> bars_in Ls s0 (bar_inputs ds x xb yb) ->
  grad_rhs ds x xb dx bars = (pairing (owners_of Ls) s3 - init_sum Ls s0)%R.
Proof.
  unfold in_dim, reals_of_args; intros H; revert xb dx Ls bars.
  induction H as [| [nm t r] v ds x Hf Hfs IH]; intros xb dx Ls bars Hxb Hdx Hd Hp H3 H0.
  - destruct Ls; [| discriminate]; simpl in H3 |- *; subst bars; ring.
  - destruct Ls as [| p Ls]; [discriminate |]; injection Hd as Hd1 Hd.
    cbn [seed_args map] in Hp; injection Hp as Hp1 Hp.
    cbn [map concat] in Hxb, Hdx; rewrite length_app in Hxb, Hdx.
    set (m := nreals v) in *.
    assert (Hm : m = length (reals_of_val v)) by apply nreals_length.
    assert (Hsl : reals_of_val (TangentCorrect.tangent (pd p)) = slice (Decl nm t r) v dx).
    { rewrite Hp1; apply tangent_val_dual; unfold slice; simpl.
      destruct (varied_role r); [rewrite length_firstn; lia | apply repeat_length]. }
    assert (Hm' : length (slice (Decl nm t r) v dx) = m).
    { unfold slice; simpl; destruct (varied_role r); [rewrite length_firstn; lia | apply repeat_length]. }
    cbn [bars_in owners_of init_sum] in H3, H0 |- *; rewrite Hd1 in H3, H0 |- *.
    change (bar_inputs (Decl nm t r :: ds) (v :: x) xb yb) with
      ((if has_dot (Decl nm t r) then [with_list v (if written_decl (Decl nm t r) then yb else firstn m xb)] else []) ++
       bar_inputs ds x (skipn m xb) yb) in H0.
    cbn [grad_rhs]; fold m.
    destruct (has_dot (Decl nm t r)) eqn:Edot.
    + destruct bars as [| b bars]; [contradiction |]; destruct H3 as [B3 [S3 H3]].
      simpl app in H0; destruct H0 as [B0 [S0 H0]].
      rewrite (IH (skipn m xb) (skipn m dx) Ls bars ltac:(rewrite length_skipn; lia) ltac:(rewrite length_skipn; lia)
                 Hd Hp H3 H0).
      rewrite pairing_app; cbn [pairing fold_right]; rewrite B3, (inner_dotl _ _ S3), Hsl.
      change (written_decl (Decl nm t r)) with (written_role r) in *.
      destruct (written_role r); simpl negb; cbn [andb]; [ring |].
      rewrite B0, (inner_dotl _ _ S0), Hsl.
      assert (Hw : reals_of_val (with_list v (firstn m xb)) = firstn m xb).
      { rewrite Hp1 in S0; destruct v as [rv | | | l |]; simpl in S0; try contradiction; simpl.
        - destruct xb as [| x0 xb]; simpl in Hxb; [lia | reflexivity].
        - unfold m; simpl; rewrite firstn_firstn, Nat.min_id; reflexivity. }
      rewrite Hw; ring.
    + rewrite (IH (skipn m xb) (skipn m dx) Ls bars ltac:(rewrite length_skipn; lia) ltac:(rewrite length_skipn; lia)
                 Hd Hp H3 H0).
      cbn [andb app]; ring.
Qed.

(* The final adjoints fit the arguments. *)
Lemma bars_in_fit ds x dx Ls s bars :
  Forall2 fits ds x -> map dname Ls = ds -> map pd Ls = seed_args ds x dx -> bars_in Ls s bars -> bars_fit ds x bars.
Proof.
  intros H; revert dx Ls bars; induction H as [| [nm t r] v ds x Hf Hfs IH]; intros dx Ls bars Hd Hp Hb.
  - destruct Ls; [| discriminate]; simpl in Hb |- *; exact Hb.
  - destruct Ls as [| p Ls]; [discriminate |]; injection Hd as Hd1 Hd.
    cbn [seed_args map] in Hp; injection Hp as Hp1 Hp.
    cbn [bars_in] in Hb; rewrite Hd1 in Hb; cbn [bars_fit].
    destruct (has_dot (Decl nm t r)); [| exact (IH _ _ _ Hd Hp Hb)].
    destruct bars as [| b bars]; [contradiction |]; destruct Hb as [_ [Sb Hb]].
    split; [| exact (IH _ _ _ Hd Hp Hb)].
    rewrite (shaped_length _ _ Sb), Hp1; rewrite Hp1 in Sb.
    destruct v as [rv | | | l |]; simpl in Sb |- *; try contradiction; [reflexivity |].
    rewrite length_map, pair_with_length; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   The store at the start of the adjoint function: the primal arguments, the
   adjoints of the arguments that carry one, then the seed of a returned real. *)

Lemma param_store_app ps1 ps2 a1 a2 :
  length ps1 = length a1 -> param_store (ps1 ++ ps2) (a1 ++ a2) = param_store ps1 a1 ++ param_store ps2 a2.
Proof. intros H; unfold param_store; rewrite combine_app by exact H; apply map_app. Qed.

Lemma primal_store cv Ls :
  param_store (map (out_dparam nat) (map (adjoint_primal W cv) (map arg_entry Ls))) (map (fun p => primal (pd p)) Ls) =
  prim_entries Ls.
Proof.
  induction Ls as [| p Ls IH]; [reflexivity |]; simpl; unfold param_store in *; simpl; rewrite IH; f_equal.
  unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; simpl;
    [destruct (vty (pw p)), r, cv |]; reflexivity.
Qed.

Lemma adjoint_bar_entry p :
  varg (pw p) <> None ->
  exists pw0 t0, @map (dparam W) _ (out_dparam nat) (adjoint_bar W (arg_entry p)) =
                 if has_dot (dname p) then [DParam pw0 t0 (BarOf (DBound (pn p)))] else [].
Proof.
  intros Hg; unfold dname, arg_entry; destruct (varg (pw p)) as [[nm r] |]; [| contradiction].
  destruct (vty (pw p)), r; simpl; first [exists ByValue, Real; reflexivity | eexists _, _; reflexivity].
Qed.

Definition decl_ty (d : decl) : ty := let 'Decl _ t _ := d in t.

(* The adjoints given to the function are in the store, in order. *)
Lemma bar_store ds x xb yb dx Ls s :
  Forall2 fits ds x -> length xb = in_dim x ->
  Forall2 (fun d v => written_decl d = true -> (nreals v <= length yb)%nat) ds x ->
  Forall (fun d => has_dot d = true -> real_or_array (decl_ty d)) ds ->
  map dname Ls = ds -> map pd Ls = seed_args ds x dx -> Forall (fun p => varg (pw p) <> None) Ls ->
  (forall k v, In (k, v) (param_store (map (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))
                                     (bar_inputs ds x xb yb)) -> store_get s k = Some v) ->
  length (concat (map (adjoint_bar W) (map arg_entry Ls))) = length (bar_inputs ds x xb yb) /\
  bars_in Ls s (bar_inputs ds x xb yb).
Proof.
  unfold in_dim, reals_of_args; intros H; revert xb dx Ls.
  induction H as [| [nm t r] v ds x Hf Hfs IH]; intros xb dx Ls Hxb Hyb Hra Hd Hp Hg Hs.
  - destruct Ls; [| discriminate]; split; reflexivity.
  - destruct Ls as [| p Ls]; [discriminate |]; injection Hd as Hd1 Hd.
    cbn [seed_args map] in Hp; injection Hp as Hp1 Hp.
    inversion Hyb as [| ? ? ? ? Hy Hyb']; subst.
    inversion Hg as [| ? ? Hg1 Hg']; subst.
    inversion Hra as [| ? ? Hra1 Hra']; subst.
    cbn [map concat] in Hxb; rewrite length_app in Hxb.
    set (m := nreals v) in *.
    assert (Hm : m = length (reals_of_val v)) by apply nreals_length.
    change (bar_inputs (Decl nm t r :: dname p :: [] ++ []) (v :: x) xb yb) with
      (bar_inputs (Decl nm t r :: map dname Ls) (v :: x) xb yb) in *.
    change (bar_inputs (Decl nm t r :: map dname Ls) (v :: x) xb yb) with
      ((if has_dot (Decl nm t r) then [with_list v (if written_decl (Decl nm t r) then yb else firstn m xb)] else []) ++
       bar_inputs (map dname Ls) x (skipn m xb) yb) in *.
    cbn [map concat] in Hs |- *.
    destruct (adjoint_bar_entry p Hg1) as [pw0 [t0 Eb]].
    rewrite map_app, Eb in Hs; rewrite length_app.
    assert (Hlb : length (adjoint_bar W (arg_entry p)) = if has_dot (Decl nm t r) then 1%nat else 0%nat).
    { transitivity (length (@map (dparam W) _ (out_dparam nat) (adjoint_bar W (arg_entry p))));
        [symmetry; apply length_map |].
      rewrite Eb, Hd1; destruct (has_dot (Decl nm t r)); reflexivity. }
    rewrite Hd1 in Hs.
    rewrite param_store_app in Hs by (destruct (has_dot _); reflexivity).
    destruct (IH (skipn m xb) (skipn m dx) Ls ltac:(rewrite length_skipn; lia) Hyb' Hra' eq_refl Hp Hg')
      as [IHl IHb]; [intros k0 v0 Hin; apply Hs, in_or_app; right; exact Hin |].
    rewrite Hlb, IHl; cbn [bars_in]; rewrite Hd1.
    destruct (has_dot (Decl nm t r)) eqn:Edot; [| split; [reflexivity | exact IHb]].
    split; [reflexivity |].
    split; [| split; [| exact IHb]].
    + unfold barv, keyv, stored; simpl; apply Hs; simpl; left; reflexivity.
    + specialize (Hra1 eq_refl); simpl in Hra1.
      rewrite Hp1; destruct v as [rv | | | l |]; simpl; auto;
        try (destruct t; simpl in Hra1, Hf; try contradiction; try discriminate; fail).
      * rewrite length_map, pair_with_length, length_firstn.
        change (written_decl (Decl nm t r)) with (written_role r) in *.
        destruct (written_role r); [specialize (Hy eq_refl); unfold m in Hy; simpl in Hy; lia |].
        rewrite length_firstn; unfold m in *; simpl in *; lia.
Qed.

Lemma map_primal_seed ds x dx : Forall2 fits ds x -> map TangentCorrect.primal (seed_args ds x dx) = x.
Proof.
  intros H; revert dx; induction H as [| [nm t r] v ds x _ _ IH]; intros dx; [reflexivity |].
  simpl; rewrite primal_val_dual, IH; reflexivity.
Qed.

(* The keys of the adjoints given to the function. *)
Lemma bar_keys Ls :
  Forall (fun p => varg (pw p) <> None) Ls ->
  map pvar (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))) =
  map (fun p => BarOf (DBound (pn p))) (filter (fun p => has_dot (dname p)) Ls).
Proof.
  induction 1 as [| p Ls Hg _ IH]; [reflexivity |].
  cbn [map concat]; rewrite map_app, map_app.
  destruct (adjoint_bar_entry p Hg) as [pw0 [t0 E]]; rewrite E, IH; simpl.
  destruct (has_dot (dname p)); reflexivity.
Qed.

(* The pairing of the owners: the initial part, and the written argument. *)
Fixpoint written_sum (Ls : list pv) (s : store R) : R :=
  match Ls with
  | [] => 0%R
  | p :: Ls' =>
      ((if has_dot (dname p) && written_decl (dname p)
        then inner (TangentCorrect.tangent (pd p)) (barv s (stored p)) else 0) + written_sum Ls' s)%R
  end.

Lemma pairing_split Ls s : pairing (owners_of Ls) s = (init_sum Ls s + written_sum Ls s)%R.
Proof.
  induction Ls as [| p Ls IH]; simpl; [ring |]; rewrite pairing_app, IH.
  destruct (has_dot (dname p)), (written_decl (dname p)); simpl; ring.
Qed.

Lemma init_sum_ext Ls s s' :
  (forall p, In p Ls -> has_dot (dname p) = true -> written_decl (dname p) = false -> barv s' (stored p) = barv s (stored p)) ->
  init_sum Ls s' = init_sum Ls s.
Proof.
  induction Ls as [| p Ls IH]; intros H; simpl; [reflexivity |].
  rewrite IH by (intros q Hq; apply H; right; exact Hq).
  destruct (has_dot (dname p)) eqn:E1, (written_decl (dname p)) eqn:E2; simpl; try reflexivity.
  rewrite (H p (or_introl eq_refl) E1 E2); reflexivity.
Qed.

Lemma written_sum_none Ls s : (forall p, In p Ls -> written_decl (dname p) = false) -> written_sum Ls s = 0%R.
Proof.
  induction Ls as [| p Ls IH]; intros H; simpl; [reflexivity |].
  rewrite (H p (or_introl eq_refl)), andb_false_r, IH by (intros q Hq; apply H; right; exact Hq); ring.
Qed.

Lemma written_sum_one Ls s w :
  NoDup Ls -> In w Ls -> has_dot (dname w) = true -> written_decl (dname w) = true ->
  (forall p, In p Ls -> written_decl (dname p) = true -> p = w) ->
  written_sum Ls s = inner (TangentCorrect.tangent (pd w)) (barv s (stored w)).
Proof.
  induction Ls as [| p Ls IH]; intros Hnd Hw Hd Hwd H; [destruct Hw |].
  inversion Hnd as [| ? ? Hp Hnd']; subst; simpl.
  destruct Hw as [-> | Hw].
  - assert (Hz : written_sum Ls s = 0%R).
    { apply written_sum_none; intros q Hq; destruct (written_decl (dname q)) eqn:E; [| reflexivity].
      rewrite (H q (or_intror Hq) E) in Hq; contradiction. }
    rewrite Hz, Hd, Hwd; simpl; ring.
  - rewrite (IH Hnd' Hw Hd Hwd (fun q Hq => H q (or_intror Hq))).
    destruct (has_dot (dname p) && written_decl (dname p)) eqn:E; [| ring].
    apply andb_true_iff in E as [_ E]; rewrite (H p (or_introl eq_refl) E) in Hp; contradiction.
Qed.

(* The final adjoints of the arguments, in order. *)
Definition bars_list (Ls : list pv) (s : store R) : list (val R) :=
  concat (map (fun p => if has_dot (dname p) then match barv s (stored p) with Some b => [b] | None => [] end else []) Ls).

Lemma bars_from_store Ls s :
  (forall p, In p Ls -> has_dot (dname p) = true ->
     exists b, barv s (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b)) ->
  bars_in Ls s (bars_list Ls s).
Proof.
  induction Ls as [| p Ls IH]; intros H; [reflexivity |].
  unfold bars_list; cbn [map concat bars_in]; fold (bars_list Ls s).
  destruct (has_dot (dname p)) eqn:E; [| apply IH; intros q Hq; apply H; right; exact Hq].
  destruct (H p (or_introl eq_refl) E) as [b [Hb Hs]]; rewrite Hb; simpl.
  split; [reflexivity | split; [exact Hs | apply IH; intros q Hq; apply H; right; exact Hq]].
Qed.

Lemma bar_inputs_length ds x xb yb :
  length ds = length x -> length (bar_inputs ds x xb yb) = length (filter has_dot ds).
Proof.
  revert x xb; induction ds as [| d ds IH]; intros [| v x] xb Hl; simpl in Hl; try discriminate; [reflexivity |].
  cbn [bar_inputs filter]; rewrite length_app, IH by lia.
  destruct (has_dot d); reflexivity.
Qed.

Lemma bar_params_length Ls :
  Forall (fun p => varg (pw p) <> None) Ls ->
  length (concat (map (adjoint_bar W) (map arg_entry Ls))) = length (filter (fun p => has_dot (dname p)) Ls).
Proof.
  intros H.
  transitivity (length (map pvar (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))));
    [rewrite !length_map; reflexivity |].
  rewrite bar_keys by exact H; apply length_map.
Qed.

Lemma filter_dname Ls : length (filter has_dot (map dname Ls)) = length (filter (fun p => has_dot (dname p)) Ls).
Proof. induction Ls as [| p Ls IH]; simpl; [reflexivity |]; destruct (has_dot (dname p)); simpl; auto. Qed.

(* The store at the start, laid out. *)
Lemma s0_shape cv Ls ds x xb yb eps ein :
  Forall (fun p => varg (pw p) <> None) Ls -> map dname Ls = ds -> length Ls = length x ->
  param_store (map (out_dparam nat) (map (adjoint_primal W cv) (map arg_entry Ls) ++
                                     concat (map (adjoint_bar W) (map arg_entry Ls)) ++ eps))
              (map (fun p => TangentCorrect.primal (pd p)) Ls ++ bar_inputs ds x xb yb ++ ein) =
  prim_entries Ls ++ param_store (map (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))
                                 (bar_inputs ds x xb yb) ++
  param_store (map (out_dparam nat) eps) ein.
Proof.
  intros Hg Hd Hl; rewrite !map_app.
  rewrite param_store_app by (rewrite !length_map; reflexivity).
  rewrite primal_store; f_equal.
  apply param_store_app; rewrite length_map, bar_params_length, bar_inputs_length by (subst; rewrite ?length_map; auto).
  subst ds; symmetry; apply filter_dname.
Qed.

Lemma bar_params_inputs Ls ds x xb yb :
  Forall (fun p => varg (pw p) <> None) Ls -> map dname Ls = ds -> length Ls = length x ->
  length (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))) =
  length (bar_inputs ds x xb yb).
Proof.
  intros Hg Hd Hl; rewrite length_map, bar_params_length, bar_inputs_length by (subst; rewrite ?length_map; auto).
  subst ds; symmetry; apply filter_dname.
Qed.

Lemma prim_entries_bar Ls v : store_get (prim_entries Ls) (KVar (BarOf v)) = None.
Proof. apply store_get_notin; unfold prim_entries; rewrite map_map; intros H; apply in_map_iff in H as [? [E _]]; discriminate. Qed.

Lemma bar_entries_nodup Ls ds x xb yb :
  Forall (fun p => varg (pw p) <> None) Ls -> NoDup (map pn Ls) -> map dname Ls = ds -> length Ls = length x ->
  NoDup (map fst (param_store (map (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls))))
                              (bar_inputs ds x xb yb))).
Proof.
  intros Hg Hnd Hd Hl.
  rewrite param_store_keys.
  2: { rewrite length_map, bar_params_length, bar_inputs_length by (subst; rewrite ?length_map; auto).
       subst ds; symmetry; apply filter_dname. }
  rewrite <- map_map with (f := pvar) (g := fun y => KVar y), bar_keys by exact Hg.
  rewrite map_map; apply NoDup_map_inv with (f := fun k => match k with KVar (BarOf (DBound i)) => i | _ => 0%nat end).
  rewrite map_map; simpl.
  clear - Hnd; induction Ls as [| p Ls IH]; simpl; [constructor |].
  inversion Hnd as [| ? ? Hp Hnd']; subst.
  destruct (has_dot (dname p)); simpl; [constructor; [| exact (IH Hnd')] | exact (IH Hnd')].
  intros H; apply Hp; apply in_map_iff in H as [q [E Hq]]; apply filter_In in Hq as [Hq _].
  rewrite <- E; apply in_map; exact Hq.
Qed.

Lemma store_get_mid (A B E : store R) k v :
  store_get A k = None -> NoDup (map fst B) -> In (k, v) B -> store_get (A ++ B ++ E) k = Some v.
Proof. intros HA HB Hin; rewrite store_get_app, HA, store_get_app, (store_get_in B k v HB Hin); reflexivity. Qed.

(* The arguments that carry an adjoint are reals or arrays. *)
Lemma has_dot_ra ds :
  non_real_varied ds = None -> (forall d, In d ds -> written_decl d = true -> real_or_array (decl_ty d)) ->
  Forall (fun d => has_dot d = true -> real_or_array (decl_ty d)) ds.
Proof.
  intros Hn Hw; apply Forall_forall; intros [nm t r] Hin Hd.
  destruct r; [| apply (Hw _ Hin); reflexivity | | destruct t; discriminate].
  - exact (non_real_varied_none ds nm t Independent Hn Hin eq_refl).
  - exact (non_real_varied_none ds nm t Inout Hn Hin eq_refl).
Qed.

Lemma bars_in_get Ls s bars p :
  bars_in Ls s bars -> In p Ls -> has_dot (dname p) = true ->
  exists b, barv s (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b).
Proof.
  revert bars; induction Ls as [| q Ls IH]; intros bars Hb Hp Hd; [destruct Hp |].
  cbn [bars_in] in Hb; destruct Hp as [-> | Hp].
  - rewrite Hd in Hb; destruct bars as [| b bars]; [contradiction |]; destruct Hb as [B [S _]]; eauto.
  - destruct (has_dot (dname q)); [destruct bars as [| b bars]; [contradiction |]; destruct Hb as [_ [_ Hb]] |];
      exact (IH _ Hb Hp Hd).
Qed.

Lemma in_owners Ls t m :
  In (t, m) (owners_of Ls) -> exists p, In p Ls /\ has_dot (dname p) = true /\ t = TangentCorrect.tangent (pd p) /\ m = stored p.
Proof.
  induction Ls as [| p Ls IH]; simpl; [intros [] |]; intros H; apply in_app_or in H as [H | H].
  - destruct (has_dot (dname p)) eqn:E; [destruct H as [H | []]; injection H as <- <-; exists p; auto | destruct H].
  - destruct (IH H) as [q [Hq R]]; exists q; auto.
Qed.

Lemma owners_intro Ls p :
  In p Ls -> has_dot (dname p) = true -> In (TangentCorrect.tangent (pd p), stored p) (owners_of Ls).
Proof.
  induction Ls as [| q Ls IH]; intros Hp Hd; [destruct Hp |]; simpl; apply in_or_app.
  destruct Hp as [-> | Hp]; [left; rewrite Hd; left; reflexivity | right; exact (IH Hp Hd)].
Qed.

Lemma owners_nodup Ls : NoDup (map pn Ls) -> NoDup (map snd (owners_of Ls)).
Proof.
  induction Ls as [| p Ls IH]; intros Hnd; simpl; [constructor |].
  inversion Hnd as [| ? ? Hp Hnd']; subst; rewrite map_app.
  destruct (has_dot (dname p)); simpl; [constructor; [| exact (IH Hnd')] | exact (IH Hnd')].
  intros H; apply in_map_iff in H as [[t m] [E H]]; simpl in E; subst m.
  destruct (in_owners _ _ _ H) as [q [Hq [_ [_ E]]]]; unfold stored in E; injection E as E.
  apply Hp; rewrite E; apply in_map; exact Hq.
Qed.

Lemma pairing_ext O s s' : (forall t m, In (t, m) O -> barv s' m = barv s m) -> pairing O s' = pairing O s.
Proof.
  induction O as [| [t m] O IH]; intros H; simpl; [reflexivity |].
  rewrite (H t m (or_introl eq_refl)), IH; [reflexivity |].
  intros t' m' Hi; apply (H t'); right; exact Hi.
Qed.

Lemma store_get_in_map (s : store R) k : store_get s k <> None -> exists v, In (k, v) s.
Proof.
  induction s as [| [k0 v0] s IH]; simpl; intros H; [contradiction |].
  destruct (key_eqb k0 k) eqn:E; [apply key_eqb_eq in E; subst; eauto |].
  destruct (IH H) as [v1 Hv]; eauto.
Qed.

Lemma key_some (s : store R) k : In k (map fst s) -> store_get s k <> None.
Proof.
  induction s as [| [k0 v0] s IH]; simpl; [intros [] |]; intros [E | H]; destruct (key_eqb k0 k) eqn:Ek; try discriminate.
  - subst; rewrite key_eqb_refl in Ek; discriminate.
  - exact (IH H).
Qed.

(* The final values of the parameters, as a map. *)
Definition final_of (s : store R) (q : dparam nat) : val R :=
  match store_get s (KVar (pvar q)) with Some w => w | None => VInt 0 end.

Lemma finals_map (s : store R) ps fs :
  length fs = length ps -> (forall i pw t x, nth_error ps i = Some (DParam pw t x) -> nth_error fs i = store_get s (KVar x)) ->
  (forall q, In q ps -> store_get s (KVar (pvar q)) <> None) -> fs = map (final_of s) ps.
Proof.
  intros Hl Hn Hs; apply nth_error_ext; intros i; rewrite nth_error_map.
  destruct (nth_error ps i) as [[pw t y] |] eqn:E.
  - rewrite (Hn i pw t y E); unfold final_of; simpl.
    pose proof (Hs _ (nth_error_In _ _ E)) as H; simpl in H.
    destruct (store_get s (KVar y)); [reflexivity | contradiction].
  - apply nth_error_None; apply nth_error_None in E; lia.
Qed.

Lemma bars_list_map Ls s :
  Forall (fun p => varg (pw p) <> None) Ls ->
  (forall p, In p Ls -> has_dot (dname p) = true -> barv s (stored p) <> None) ->
  bars_list Ls s = map (final_of s) (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))).
Proof.
  induction 1 as [| p Ls Hg HL IH]; intros H; [reflexivity |].
  unfold bars_list; cbn [map concat]; fold (bars_list Ls s); rewrite map_app, map_app.
  rewrite IH by (intros q Hq; apply H; right; exact Hq); f_equal.
  destruct (adjoint_bar_entry p Hg) as [pw0 [t0 E]]; rewrite E.
  destruct (has_dot (dname p)) eqn:Ed; [| reflexivity].
  specialize (H p (or_introl eq_refl) Ed); unfold barv, keyv, stored in H |- *; simpl in H |- *.
  unfold final_of; simpl; destruct (store_get s (KVar (BarOf (DBound (pn p))))); [reflexivity | contradiction].
Qed.

(* Running the body of a function: the finals of the parameters. *)
Lemma finish_exec (ps : list (dparam W)) (ss : list (dstmt W)) args s0 sF r :
  length (map (out_dparam nat) ps) = length args -> param_store (map (out_dparam nat) ps) args = s0 ->
  run ss s0 = Some sF ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0 args =
  match r with
  | DReturnsReal => option_map (fun w => (map (final_of sF) (map (out_dparam nat) ps), [w])) (store_get sF Returned)
  | DVoid => Some (map (final_of sF) (map (out_dparam nat) ps), [])
  end.
Proof.
  intros Hl Hs0 Hr; cbn [exec_scoped]; rewrite Hl, Nat.eqb_refl; cbv iota beta; simpl negb; cbv iota.
  change (map (fun '(DParam _ _ x, a) => (KVar x, a)) (combine (map (out_dparam nat) ps) args)) with
    (param_store (map (out_dparam nat) ps) args).
  rewrite Hs0; change (exec_stmts reals (map (out_dstmt nat) ss) s0) with (run ss s0); rewrite Hr.
  assert (Hin : forall q, In q (map (out_dparam nat) ps) -> store_get sF (KVar (pvar q)) <> None).
  { intros q Hq; apply (run_keeps ss s0 sF Hr); rewrite <- Hs0; apply key_some.
    rewrite param_store_keys by exact Hl; apply in_map_iff; exists q; split; [reflexivity | exact Hq]. }
  destruct (finals_some sF (map (out_dparam nat) ps)) as [fs [Hfs [Hlfs Hnth]]].
  { intros pw0 t0 y Hy; pose proof (Hin _ Hy) as H; simpl in H.
    destruct (store_get sF (KVar y)) as [w |]; [eauto | contradiction]. }
  cbv zeta; rewrite Hfs.
  rewrite (finals_map sF (map (out_dparam nat) ps) fs Hlfs Hnth Hin).
  destruct r; [destruct (store_get sF Returned) |]; reflexivity.
Qed.

(* The final adjoints of the arguments, read from the finals. *)
Lemma output_bars cv Ls ds eps (sF : store R) :
  Forall (fun p => varg (pw p) <> None) Ls -> map dname Ls = ds ->
  (forall p, In p Ls -> has_dot (dname p) = true -> barv sF (stored p) <> None) ->
  firstn (length (filter has_dot ds)) (skipn (length ds)
    (map (final_of sF) (@map (dparam W) _ (out_dparam nat)
       (map (adjoint_primal W cv) (map arg_entry Ls) ++ concat (map (adjoint_bar W) (map arg_entry Ls)) ++ eps)))) =
  bars_list Ls sF.
Proof.
  intros Hg Hd Hb; rewrite !map_app.
  rewrite skipn_app, skipn_all2 by (rewrite !length_map; subst; rewrite length_map; lia).
  rewrite !length_map; subst ds; rewrite length_map, Nat.sub_diag, skipn_O, app_nil_l.
  rewrite firstn_app.
  assert (E : length (filter has_dot (map dname Ls)) = length (map (final_of sF) (@map (dparam W) _ (out_dparam nat) (concat (map (adjoint_bar W) (map arg_entry Ls)))))).
  { rewrite length_map, length_map, bar_params_length, filter_dname by exact Hg; reflexivity. }
  rewrite E, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
  symmetry; apply bars_list_map; assumption.
Qed.

(* ---------------------------------------------------------------------------
   The written argument. *)

Lemma filter_none {A : Type} (P : A -> bool) l c : length (filter P l) = 0%nat -> In c l -> P c = true -> False.
Proof.
  intros H Hc Hp; destruct (filter P l) eqn:E; [| discriminate].
  assert (Hin : In c (filter P l)) by (apply filter_In; auto); rewrite E in Hin; destruct Hin.
Qed.

Lemma written_unique (Ls : list pv) a b :
  NoDup Ls -> length (filter written_decl (map dname Ls)) = 1%nat -> In a Ls -> In b Ls ->
  written_decl (dname a) = true -> written_decl (dname b) = true -> a = b.
Proof.
  induction Ls as [| q Ls IH]; intros Hnd H1 Ha Hb Wa Wb; [destruct Ha |].
  inversion Hnd as [| ? ? Hq Hnd']; subst; simpl in H1.
  destruct (written_decl (dname q)) eqn:Eq; simpl in H1.
  - injection H1 as H0.
    assert (Hr : forall c, In c Ls -> written_decl (dname c) = true -> False)
      by (intros c Hc Wc; apply (filter_none written_decl (map dname Ls) (dname c) H0); [apply in_map; exact Hc | exact Wc]).
    destruct Ha as [<- | Ha]; [| destruct (Hr a Ha Wa)].
    destruct Hb as [<- | Hb]; [reflexivity | destruct (Hr b Hb Wb)].
  - destruct Ha as [<- | Ha]; [congruence |]; destruct Hb as [<- | Hb]; [congruence |].
    exact (IH Hnd' H1 Ha Hb Wa Wb).
Qed.

Lemma oset_app O1 O2 m t : oset (O1 ++ O2) m t = oset O1 m t ++ oset O2 m t.
Proof. unfold oset; apply map_app. Qed.

(* The pairing where the written argument holds the result. *)
Lemma pairing_oset_owners Ls w tv s :
  NoDup (map pn Ls) -> In w Ls -> has_dot (dname w) = true -> written_decl (dname w) = true ->
  (forall p, In p Ls -> written_decl (dname p) = true -> p = w) ->
  pairing (oset (owners_of Ls) (stored w) tv) s = (init_sum Ls s + inner tv (barv s (stored w)))%R.
Proof.
  induction Ls as [| p Ls IH]; intros Hnd Hw Hd Hwd Hu; [destruct Hw |].
  inversion Hnd as [| ? ? Hp Hnd']; subst.
  cbn [owners_of init_sum]; rewrite oset_app, pairing_app.
  destruct Hw as [-> | Hw].
  - rewrite Hd, Hwd; cbn [negb andb]; unfold oset at 1; cbn [map pairing fold_right].
    unfold stored at 1 2; cbn [Simplify.dvar_eq]; rewrite Nat.eqb_refl.
    rewrite oset_notin.
    + rewrite pairing_split, written_sum_none; [ring |].
      intros q Hq; destruct (written_decl (dname q)) eqn:E; [| reflexivity].
      rewrite (Hu q (or_intror Hq) E) in Hq; exfalso; apply Hp, in_map, Hq.
    + intros t m Hi; destruct (in_owners _ _ _ Hi) as [q [_ [_ [_ ->]]]]; reflexivity.
    + reflexivity.
    + intros Hi; apply in_map_iff in Hi as [[t m] [E Hi]]; simpl in E; subst m.
      destruct (in_owners _ _ _ Hi) as [q [Hq [_ [_ E]]]]; unfold stored in E; injection E as E.
      apply Hp; rewrite E; apply in_map, Hq.
  - assert (Hpw : written_decl (dname p) = false).
    { destruct (written_decl (dname p)) eqn:E; [| reflexivity].
      rewrite (Hu p (or_introl eq_refl) E) in Hp; exfalso; apply Hp, in_map, Hw. }
    rewrite (IH Hnd' Hw Hd Hwd (fun q Hq => Hu q (or_intror Hq))), Hpw.
    destruct (has_dot (dname p)); unfold oset at 1; cbn [map pairing fold_right negb andb]; [| ring].
    unfold stored at 1 2 3; cbn [Simplify.dvar_eq].
    destruct (Nat.eqb (pn w) (pn p)) eqn:E; [apply Nat.eqb_eq in E; exfalso; apply Hp; rewrite <- E; apply in_map, Hw |].
    cbv zeta beta iota; fold (stored p); ring.
Qed.

(* The initial adjoint of the written argument is the seed. *)
Lemma bars_in_written ds x xb yb dx Ls s w :
  Forall2 fits ds x -> map dname Ls = ds -> map pd Ls = seed_args ds x dx ->
  bars_in Ls s (bar_inputs ds x xb yb) -> In w Ls -> has_dot (dname w) = true -> written_decl (dname w) = true ->
  barv s (stored w) = Some (with_list (TangentCorrect.primal (pd w)) yb).
Proof.
  intros H; revert xb dx Ls; induction H as [| [nm t r] v ds x Hf Hfs IH]; intros xb dx Ls Hd Hp Hb Hw Hdw Hww.
  - destruct Ls; [destruct Hw | discriminate].
  - destruct Ls as [| p Ls]; [discriminate |]; injection Hd as Hd1 Hd.
    cbn [seed_args map] in Hp; injection Hp as Hp1 Hp.
    change (bar_inputs (Decl nm t r :: ds) (v :: x) xb yb) with
      ((if has_dot (Decl nm t r) then [with_list v (if written_decl (Decl nm t r) then yb else firstn (nreals v) xb)] else []) ++
       bar_inputs ds x (skipn (nreals v) xb) yb) in Hb.
    cbn [bars_in] in Hb; rewrite Hd1 in Hb.
    destruct Hw as [<- | Hw].
    + rewrite Hd1 in Hdw, Hww; rewrite Hdw, Hww in Hb; destruct Hb as [B _ ].
      rewrite B, Hp1, primal_val_dual; reflexivity.
    + destruct (has_dot (Decl nm t r)); [destruct Hb as [_ [_ Hb]] |]; exact (IH _ _ _ Hd Hp Hb Hw Hdw Hww).
Qed.

Definition ty_size (t : ty) : nat := match t with Real => 1 | Array z => Z.to_nat z | _ => 0 end.

Lemma has_type_size t v : has_type t v -> real_or_array t -> length (reals_of_val (TangentCorrect.primal v)) = ty_size t.
Proof. destruct t, v; simpl; try contradiction; auto; intros H _; rewrite length_map; exact H. Qed.

Lemma fits_size nm t r v : fits (Decl nm t r) v -> real_or_array t -> nreals v = ty_size t.
Proof. destruct t, v; simpl; try contradiction; auto. Qed.

Lemma pvar_primal cv p : pvar (out_dparam nat (adjoint_primal W cv (arg_entry p))) = DBound (pn p).
Proof. unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; simpl; [destruct (vty (pw p)), r, cv |]; reflexivity. Qed.

Lemma forall2_map {A B C : Type} (f : A -> B) (g : A -> C) (P : B -> C -> Prop) l :
  Forall (fun a => P (f a) (g a)) l -> Forall2 P (map f l) (map g l).
Proof. induction 1; constructor; auto. Qed.

(* The arguments of a function are inout as its declarations say. *)
Lemma has_inout_eq {V1 : Type} (G : list (V1 * unit)) (d1 : adefinition V1 bare) (d2 : adefinition unit bare) x1 :
  adefinition_eq G d1 d2 -> has_inout d1 x1 = writes_inout (declarations d2).
Proof.
  revert G d2; induction d1 as [n t r f IH | rr b]; intros G [n' t' r' f2 | rr' b'] H; simpl in H; try contradiction.
  - destruct H as [<- [<- [<- H]]]; simpl; destruct r; try reflexivity; apply (IH x1 ((x1, tt) :: G)); apply H.
  - reflexivity.
Qed.

Lemma annotate_cv_decls cv f :
  parametric f -> annotate_cv cv (normalize f) = (cv && negb (writes_inout (decls f)))%bool.
Proof.
  intros Hp; unfold annotate_cv, decls; f_equal; f_equal.
  apply (has_inout_eq []); exact (normalize_parametric f Hp avar unit).
Qed.

(* The adjoint function, opened at the numbers simplify uses, from the
   primal arguments, their adjoints and the seed: it computes the gradient,
   the transpose of the tangent of the dual evaluation applied to the seed. *)
Theorem adjoint_simulates_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) ->
     asim_body (annotate_cv cv (normalize f)) bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
  intros Hpar Hwf Hfit Hlxb Hlyb Hldx Hsim Hev.
  assert (Ecva := annotate_cv_decls cv f Hpar).
  set (cva := annotate_cv cv (normalize f)) in *.
  set (xs := seed_args (decls f) x dx) in *.
  pose proof (normalize_parametric f Hpar) as Hnp.
  set (dP := afdef (normalize f) pv).
  assert (HD := Hnp pv (val (dual R))); fold dP in HD.
  unfold aeval_function in Hev.
  destruct (open_P_some dP [] 0 xs _ v HD Hev) as [L [res [bP Ho]]].
  specialize (Hsim L res bP Ho).
  destruct (open_P_args dP 0 xs [] L res bP Ho) as [new [EL [Hlen Hargs]]].
  rewrite app_nil_r in EL; subst new.
  destruct (annotate_open_cv cva dP [] 0 xs L res bP _ (Hnp pv avar) Ho) as [bA [HbA Htr]].
  destruct (wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho) as [resW [bW [HrW [HbW Hwfd]]]].
  destruct (eval_open dP [] 0 xs L res bP _ HD Ho) as [bD [HbD HevD]].
  rewrite HevD in Hev.
  assert (Hds := decls_open dP (map (fun p => (p, tt)) []) [] 0 xs L res bP _ (Hnp pv unit) Ho).
  assert (Hds' : decls f = map (fun p => fst (arg_entry p)) (rev L)) by exact Hds.
  clear Hds; rename Hds' into Hds.
  rewrite Nat.add_0_l in Htr, Hwfd.
  set (n := length xs) in *.
  set (tr := annotate_definition_t cva 0 (afdef (normalize f) avar)) in *.
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
  assert (HAL : Forall (fun p => tstored (pt p) = stored p /\ varg (pw p) <> None) (rev L)).
  { apply Forall_forall; intros p Hp; rewrite in_rev_iff in Hp.
    destruct (Hargs' p Hp) as [? [? [? [? [? [-> _]]]]]]; split; [reflexivity | discriminate]. }
  assert (HAL' : Forall (fun p => varg (pw p) <> None) (rev L))
    by (apply Forall_impl with (2 := HAL); intros p [_ H]; exact H).
  assert (Hpn_inj : forall p q, In p L -> In q L -> pn p = pn q -> p = q).
  { intros p q Hp Hq E; destruct (Hargs' p Hp) as [i [? [? [? [? [-> [Hx [Hd _]]]]]]]].
    destruct (Hargs' q Hq) as [i' [? [? [? [? [-> [Hx' [Hd' _]]]]]]]]; simpl in E; subst i'.
    rewrite Hx in Hx'; injection Hx' as <-; rewrite Hd in Hd'; injection Hd' as <- <- <-; reflexivity. }
  assert (Hnd : NoDup (rev L)) by (apply NoDup_map_inv with (f := pn); exact HnL).
  assert (Hdn : map dname (rev L) = decls f) by (rewrite Hds; reflexivity).
  assert (Hpd : map pd (rev L) = seed_args (decls f) x dx) by (rewrite <- Hxs; reflexivity).
  assert (Hxp : map (fun p => TangentCorrect.primal (pd p)) (rev L) = x).
  { rewrite <- (map_primal_seed (decls f) x dx Hfit), <- Hpd, map_map; reflexivity. }
  assert (HLn : length (rev L) = length x) by (rewrite <- Hxp, length_map; reflexivity).
  assert (Hprim : forall p, In p L -> store_get (prim_entries (rev L)) (keyv (stored p)) = Some (TangentCorrect.primal (pd p))).
  { intros p Hp; apply prim_lookup; [exact HnL | apply in_rev_iff; exact Hp]. }
  assert (HBnd := bar_entries_nodup (rev L) (decls f) x xb yb HAL' HnL Hdn HLn).
  rewrite <- map_rev.
  destruct (wf_result_facts _ _ _ _ Hwf) as [[EW [Hnw HtcB]] | [w [nm [role [EW [Hg [Hwr [H1w [Hraw [HtcB [Hdep Hinout]]]]]]]]]]].
  - (* the function returns a real *)
    subst resW; destruct res as [tR | yP]; simpl in HrW; [subst tR | contradiction].
    destruct resT as [tT | yT]; simpl in HrT; [subst tT | contradiction].
    assert (Hwio : writes_inout (decls f) = false).
    { destruct (writes_inout (decls f)) eqn:E; [| reflexivity].
      apply existsb_exists in E as [[nm0 t0 r0] [Hd0 E]]; destruct r0; try discriminate.
      assert (existsb written_decl (decls f) = true) by (apply existsb_exists; exists (Decl nm0 t0 Inout); auto).
      congruence. }
    assert (Ecv' : cva = cv) by (rewrite Ecva, Hwio, andb_true_r; reflexivity).
    clearbody cva; clear Ecva; subst cva.
    cbn [adjoint_seed inout_result negb]; rewrite andb_true_r, open_pairs_sbind.
    set (vo := (if cv then Some (AReturns Real) else None) : option (aresult (tvar W))).
    set (se := DVar (BarOf (@ResultVar W))).
    destruct (open_pairs (adj W None vo Forward (rebuild (tvar W) bT (annotate_body_t cv Forward n bA)) se) n)
      as [[fw rv] c'] eqn:Hob.
    (* the store at the start *)
    set (bps := concat (map (adjoint_bar W) (map arg_entry (rev L)))) in *.
    set (B := param_store (map (out_dparam nat) bps) (bar_inputs (decls f) x xb yb)) in *.
    set (s0 := prim_entries (rev L) ++ B ++ [(KVar (BarOf ResultVar), VReal (hd 0%R yb))]).
    set (ps := map (adjoint_primal W cv) (map arg_entry (rev L)) ++ bps ++ [DParam ByValue Real (BarOf ResultVar)]).
    assert (Hin : adjoint_inputs (decls f) x xb yb =
                  map (fun p => TangentCorrect.primal (pd p)) (rev L) ++ bar_inputs (decls f) x xb yb ++ [VReal (hd 0%R yb)])
      by (unfold adjoint_inputs; rewrite Hnw, Hxp; reflexivity).
    assert (Hs0eq : param_store (map (out_dparam nat) ps) (adjoint_inputs (decls f) x xb yb) = s0)
      by (rewrite Hin; unfold ps; rewrite s0_shape by assumption; reflexivity).
    assert (Hkey_bar : forall k w0, In (k, w0) B -> exists i, k = KVar (BarOf (DBound i))).
    { intros k w0 Hk; apply (in_map fst) in Hk; simpl in Hk; unfold B in Hk.
      rewrite param_store_keys in Hk by exact (bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn).
      rewrite <- map_map with (f := pvar) (g := fun y => KVar y) in Hk; unfold bps in Hk; rewrite bar_keys in Hk by exact HAL'.
      apply in_map_iff in Hk as [y [<- Hy]]; apply in_map_iff in Hy as [p [<- _]]; eauto. }
    assert (HB : forall k w0, In (k, w0) B -> store_get s0 k = Some w0).
    { intros k w0 Hk; destruct (Hkey_bar k w0 Hk) as [i ->]; apply store_get_mid; [apply prim_entries_bar | exact HBnd | exact Hk]. }
    assert (Hs0p : forall p, In p L -> store_get s0 (keyv (stored p)) = Some (TangentCorrect.primal (pd p)))
      by (intros p Hp; unfold s0; rewrite store_get_app, (Hprim p Hp); reflexivity).
    assert (Hra_ds : Forall (fun d => has_dot d = true -> real_or_array (decl_ty d)) (decls f)).
    { apply has_dot_ra; [exact Hnrv |]; intros d Hd Hw.
      assert (existsb written_decl (decls f) = true) by (apply existsb_exists; eauto); congruence. }
    assert (Hnw' : forall p, In p (rev L) -> written_decl (dname p) = false).
    { intros p Hp; destruct (written_decl (dname p)) eqn:E; [| reflexivity].
      assert (existsb written_decl (decls f) = true)
        by (apply existsb_exists; exists (dname p); split; [rewrite <- Hdn; apply in_map; exact Hp | exact E]); congruence. }
    assert (Hwyb : Forall2 (fun d v0 => written_decl d = true -> (nreals v0 <= length yb)%nat) (decls f) x).
    { assert (Hw0 : forall d, In d (decls f) -> written_decl d = false).
      { intros d Hd; destruct (written_decl d) eqn:E; [| reflexivity].
        assert (existsb written_decl (decls f) = true) by (apply existsb_exists; eauto); congruence. }
      clear - Hfit Hw0; induction Hfit as [| d v0 ds x0 _ _ IH]; constructor.
      - intros Hw; rewrite (Hw0 d (or_introl eq_refl)) in Hw; discriminate.
      - apply IH; intros d' Hd'; apply Hw0; right; exact Hd'. }
    destruct (bar_store (decls f) x xb yb dx (rev L) s0 Hfit Hlxb Hwyb Hra_ds Hdn Hpd HAL' HB) as [_ Hbars0].
    (* the forward sweep *)
    assert (Hparg : forall p, In p L -> exists nm0 t0 r0 i0 x0, p = arg_pv nm0 t0 r0 i0 x0)
      by (intros p Hp; destruct (Hargs' p Hp) as [i0 [nm0 [t0 [r0 [x0 [-> _]]]]]]; do 5 eexists; reflexivity).
    assert (Hactx : actx L n n s0 None PTop (live_anf n bW) (tbr cv Forward n bA) Real).
    { constructor.
      - constructor; auto; try (intros; discriminate); try exact I; intros H; destruct H.
      - intros p Hp; destruct (Hparg p Hp) as [? [? [? [? [? ->]]]]]; reflexivity.
      - intros p Hp _; exact (Hs0p p Hp).
      - intros p Hp; destruct (Hparg p Hp) as [? [? [? [? [? ->]]]]]; discriminate. }
    assert (Hvo : Forward = Forward -> PTop = PTop /\ (vo = None <-> cv = false) /\
                  (forall y, vo = Some (AWrites y) -> option_map (amap pt) None = Some y) /\
                  (forall t, vo = Some (AReturns t) -> @None (atom pv) = None)).
    { intros _; unfold vo; split; [reflexivity | split; [destruct cv; split; intros; congruence |]].
      split; [intros y E; destruct cv; discriminate | reflexivity]. }
    assert (Hvt : Forward = Forward -> forall p, In p L -> live_anf n bW p -> vo_target vo <> Some (stored p)).
    { intros _ p _ _ E; unfold vo in E; destruct cv; simpl in E; [injection E as E; discriminate | discriminate]. }
    assert (Hvb : Forward = Forward -> forall t, vo_target vo = Some t -> below n t /\ consistent t /\ is_primal t).
    { intros _ t E; unfold vo in E; destruct cv; simpl in E; [injection E as <-; repeat split | discriminate]. }
    pose proof (Hsim L n n s0 None PTop Forward bA bW bT bD Real v se vo HbA HbW HbT HbD Hactx I HtcB Hev Hvo Hvt Hvb)
      as HS.
    cbn [option_map] in HS.
    lazymatch type of HS with context [@open_pairs ?A ?t n] =>
      assert (E : @open_pairs A t n = ((fw, rv), c')) by exact Hob; rewrite E in HS; clear E end.
    destruct HS as [Hcc [Hhty [s1 [R1 [F1 [T1 [V1 Hrev]]]]]]].
    (* the reverse sweep *)
    set (O := owners_of (rev L)).
    assert (HinL : forall p, In p (rev L) -> In p L) by (intros p Hp; apply in_rev_iff; exact Hp).
    assert (Hvt0 : forall y, vo_target vo <> Some (BarOf y)) by (intros y; unfold vo; destruct cv; discriminate).
    assert (Hbars1 : forall p, In p (rev L) -> barv s1 (stored p) = barv s0 (stored p)).
    { intros p Hp; unfold barv; apply F1; [simpl; exact (Hnum p (HinL p Hp)) | reflexivity | simpl; tauto | discriminate | apply Hvt0]. }
    assert (Hs0r : store_get s0 (keyv (BarOf ResultVar)) = Some (VReal (hd 0%R yb))).
    { unfold s0, keyv; simpl; rewrite store_get_app, prim_entries_bar, store_get_app.
      destruct (store_get B (KVar (BarOf ResultVar))) eqn:EB.
      - exfalso; assert (Hn : store_get B (KVar (BarOf ResultVar)) <> None) by (rewrite EB; discriminate).
        destruct (in_map_iff fst B (KVar (BarOf ResultVar))) as [H _].
        destruct (store_get_in_map B _ Hn) as [w0 Hk]; destruct (Hkey_bar _ _ Hk) as [i E]; discriminate.
      - cbn [store_get]; rewrite key_eqb_refl; reflexivity. }
    assert (Hs1r : store_get s1 (keyv (BarOf ResultVar)) = Some (VReal (hd 0%R yb)))
      by (rewrite F1; [exact Hs0r | exact I | exact I | simpl; tauto | discriminate | apply Hvt0]).
    assert (Hag : agree_prim c' (inplace None PTop) s1 s1) by (intros ? ? ? ?; reflexivity).
    assert (Hr : rctx L n None PTop O (useful cv Forward n bA) s1).
    { constructor.
      - apply owners_nodup; exact HnL.
      - intros t m Hi; destruct (in_owners _ _ _ Hi) as [p [Hp [Hd [-> ->]]]].
        rewrite (Hbars1 p Hp); destruct (bars_in_get _ _ _ p Hbars0 Hp Hd) as [b [Eb Sb]]; rewrite Eb; exact Sb.
      - intros t m Hi; destruct (in_owners _ _ _ Hi) as [p [Hp [_ [_ ->]]]]; exists (pn p).
        split; [reflexivity | exact (Hnum p (HinL p Hp))].
      - intros p Hp _ Hv; apply owners_intro; [apply in_rev_iff; exact Hp |].
        destruct (Hargs' p Hp) as [i0 [nm0 [t0 [r0 [x0 [-> [_ [Hd _]]]]]]]]; simpl in Hv.
        pose proof (non_real_varied_none (decls f) nm0 t0 r0 Hnrv (nth_error_In _ _ Hd) Hv) as Hra.
        unfold dname, arg_entry; simpl.
        destruct t0; try destruct Hra; destruct r0; simpl in Hv; try discriminate; reflexivity.
      - intros p t Hp _ Hi; destruct (in_owners _ _ _ Hi) as [q [Hq [_ [-> E]]]].
        unfold stored in E; injection E as E; rewrite (Hpn_inj q p (HinL q Hq) Hp (eq_sym E)); reflexivity.
      - intros o E; discriminate. }
    assert (Hseed : seed_ok n Real se s1).
    { split; [intros y [<- | []]; split; exact I |].
      intros _; exists (hd 0%R yb); exact Hs1r. }
    assert (Htp : tapes_ok L s1) by (intros p Hp Hrp; destruct (Hparg p Hp) as [? [? [? [? [? ->]]]]]; discriminate).
    destruct (Hrev s1 O Hag Hr Hseed Htp) as [s3 [R3 [K3 [X3 [T3 [F3 [S3 P3]]]]]]].
    destruct v as [d | | | |]; try (simpl in Hhty; contradiction).
    assert (P3' : pairing O s3 = (init_sum (rev L) s0 + dsnd d * hd 0%R yb)%R).
    { rewrite P3; unfold result_pairing, seed_value; simpl inplace.
      change (xev s1 se) with (store_get s1 (keyv (BarOf ResultVar))); rewrite Hs1r.
      unfold O; rewrite pairing_split, written_sum_none by exact Hnw'.
      rewrite (init_sum_ext (rev L) s0 s1) by (intros p Hp _ _; apply Hbars1; exact Hp); ring. }
    (* the end of the function *)
    set (sF := if cv then store_set s3 Returned (VReal (dfst d)) else s3).
    assert (Hres3 : cv = true -> store_get s3 (keyv ResultVar) = Some (VReal (dfst d))).
    { intros Ecv; rewrite (K3 eq_refl ResultVar); [| unfold vo; rewrite Ecv; reflexivity | simpl; tauto].
      apply (V1 eq_refl); unfold vo; rewrite Ecv; reflexivity. }
    set (ss := if cv then fw ++ [] ++ rv ++ [DReturn (DVar ResultVar)] else fw ++ [] ++ rv).
    assert (Hss : run ss s0 = Some sF).
    { unfold ss, sF; destruct cv eqn:Ecv.
      - rewrite run_app, R1, run_app, run_nil, run_app, R3.
        unfold run; cbn [map Simplify.out_dstmt Simplify.out_dexpr Simplify.out_dvar exec_stmts exec xeval].
        change (KVar ResultVar) with (keyv ResultVar); rewrite (Hres3 eq_refl); reflexivity.
      - rewrite run_app, R1, run_app, run_nil, R3; reflexivity. }
    assert (Hb3F : forall m, barv sF m = barv s3 m)
      by (intros m; unfold sF, barv; destruct cv; [rewrite store_get_set_other by discriminate |]; reflexivity).
    assert (HbF : forall p, In p (rev L) -> has_dot (dname p) = true ->
                  exists b, barv sF (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b)).
    { intros p Hp Hd; rewrite Hb3F; pose proof (S3 _ _ (owners_intro _ _ Hp Hd)) as Sh.
      destruct (barv s3 (stored p)) as [b |]; [eauto | simpl in Sh; destruct (TangentCorrect.tangent (pd p)); contradiction]. }
    assert (HbinF := bars_from_store (rev L) sF HbF).
    assert (Hfb := bars_in_fit (decls f) x dx (rev L) sF (bars_list (rev L) sF) Hfit Hdn Hpd HbinF).
    destruct (gradient_dotl (decls f) x xb dx (bars_list (rev L) sF) Hfit Hlxb Hldx Hfb) as [g [Hg [Hlg Hdg]]].
    assert (Hgr := grad_rhs_pairing (decls f) x xb yb dx (rev L) s0 sF (bars_list (rev L) sF) Hfit Hlxb Hldx Hdn Hpd HbinF Hbars0).
    assert (HpF : pairing O sF = pairing O s3) by (apply pairing_ext; intros t m _; apply Hb3F).
    assert (Hlen_ps : length (map (out_dparam nat) ps) = length (adjoint_inputs (decls f) x xb yb)).
    { rewrite Hin; unfold ps; rewrite map_app, map_app, !length_app.
      pose proof (bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn) as Hbl.
      change (length (map (out_dparam nat) bps) = length (bar_inputs (decls f) x xb yb)) in Hbl.
      rewrite !length_map in Hbl |- *; simpl; rewrite !length_map; do 2 f_equal; exact Hbl. }
    pose proof (finish_exec ps ss (adjoint_inputs (decls f) x xb yb) s0 sF (if cv then DReturnsReal else DVoid)
                  Hlen_ps Hs0eq Hss) as Hex.
    exists (if cv then DReturnsReal else DVoid), ps, ss, c',
      (map (final_of sF) (map (out_dparam nat) ps), if cv then [VReal (dfst d)] else []), g.
    split; [unfold ss, ps, bps; destruct cv; reflexivity |].
    split; [rewrite Hex; unfold sF; destruct cv; [rewrite store_get_set_same; reflexivity | reflexivity] |].
    split.
    { unfold adjoint_output, ps, bps.
      cbn beta iota; rewrite <- Hg; f_equal.
      apply (output_bars cv (rev L) (decls f) [DParam ByValue Real (BarOf ResultVar)] sF HAL' Hdn).
      intros p Hp Hd; destruct (HbF p Hp Hd) as [b [Eb _]]; rewrite Eb; discriminate. }
    split; [exact Hlg |].
    split.
    { rewrite Hdg, Hgr; fold O; rewrite HpF, P3'; simpl in Hlyb.
      destruct yb as [| y0 [| ]]; simpl in Hlyb; try discriminate.
      unfold dotl; simpl; ring. }
    intros Ecv _; unfold value_given; rewrite index_of_written_none by exact Hnw; rewrite Ecv; reflexivity.
  - (* the function writes an argument *)
    subst resW; destruct res as [tR | yP]; simpl in HrW; [contradiction |].
    destruct yP as [y | | ]; simpl in HrW; try contradiction.
    apply in_gW in HrW as [HyL Ew]; subst w.
    destruct resT as [tT | yT]; simpl in HrT; [contradiction |].
    destruct yT as [yt | | ]; simpl in HrT; try contradiction.
    apply in_gT in HrT as [_ ->].
    destruct (Hargs' y HyL) as [j [nm' [t [r [x0 [Ey [Hxj [Hdj Hj]]]]]]]].
    assert (Hvy : vty (pw y) = t) by (rewrite Ey; reflexivity).
    rewrite Ey in Hg; simpl in Hg; injection Hg as <- <-.
    assert (Hdecl_y : dname y = Decl nm' t r) by (rewrite Ey; reflexivity).
    rewrite Hvy in Hraw, HtcB.
    assert (Hnw : existsb written_decl (decls f) = true).
    { apply existsb_exists; exists (Decl nm' t r); split; [apply nth_error_In with j; exact Hdj | exact Hwr]. }
    assert (Hywr : written_decl (dname y) = true) by (rewrite Hdecl_y; exact Hwr).
    assert (Hdy : has_dot (dname y) = true).
    { rewrite Hdecl_y; destruct t; try destruct Hraw; destruct r; simpl in Hwr |- *; try discriminate; reflexivity. }
    assert (HinL : forall p, In p (rev L) -> In p L) by (intros p Hp; apply in_rev_iff; exact Hp).
    assert (HyR : In y (rev L)) by (apply in_rev_iff; exact HyL).
    assert (Hu : forall p, In p (rev L) -> written_decl (dname p) = true -> p = y).
    { intros p Hp Wp; apply (written_unique (rev L) p y Hnd); [rewrite Hdn; exact H1w | exact Hp | exact HyR | exact Wp | exact Hywr]. }
    assert (Hwio : writes_inout (decls f) = match r with Inout => true | _ => false end).
    { destruct r; [| | apply existsb_exists; exists (Decl nm' t Inout); split; [apply nth_error_In with j; exact Hdj | reflexivity] |].
      all: destruct (writes_inout (decls f)) eqn:E; [| reflexivity].
      all: apply existsb_exists in E as [[nm0 t0 r0] [Hd0 E]]; destruct r0; try discriminate.
      all: rewrite <- Hdn in Hd0; apply in_map_iff in Hd0 as [p [Ep Hp]].
      all: assert (Wp : written_decl (dname p) = true) by (rewrite Ep; reflexivity).
      all: rewrite (Hu p Hp Wp), Hdecl_y in Ep; discriminate. }
    assert (Hir : inout_result W (AWrites (AVar (pt y))) = match r with Inout => true | _ => false end)
      by (rewrite Ey; destruct r; reflexivity).
    rewrite Hir.
    remember (cv && negb (match r with Inout => true | _ => false end))%bool as cvw eqn:Hcvw.
    assert (Ecvw : cva = cvw) by (rewrite Ecva, Hwio; symmetry; exact Hcvw).
    clearbody cva; clear Ecva; subst cva.
    set (vo := (if cvw then Some (AWrites (AVar (pt y))) else None) : option (aresult (tvar W))).
    destruct (adjoint_seed W (AWrites (AVar (pt y)))) as [[extra pro] se] eqn:Eseed.
    assert (Hextra : extra = []).
    { unfold adjoint_seed in Eseed; rewrite Ey in Eseed; simpl in Eseed.
      destruct t, r; simpl in Eseed; injection Eseed as <- _ _; reflexivity. }
    subst extra; rewrite open_pairs_sbind.
    destruct (open_pairs (adj W (Some (AVar (pt y))) vo Forward (rebuild (tvar W) bT (annotate_body_t cvw Forward n bA)) se) n)
      as [[fw rv] c'] eqn:Hob.
    (* the store at the start *)
    set (bps := concat (map (adjoint_bar W) (map arg_entry (rev L)))) in *.
    set (B := param_store (map (out_dparam nat) bps) (bar_inputs (decls f) x xb yb)) in *.
    set (s0 := prim_entries (rev L) ++ B ++ []).
    set (ps := map (adjoint_primal W cv) (map arg_entry (rev L)) ++ bps ++ []).
    assert (Hin : adjoint_inputs (decls f) x xb yb =
                  map (fun p => TangentCorrect.primal (pd p)) (rev L) ++ bar_inputs (decls f) x xb yb ++ [])
      by (unfold adjoint_inputs; rewrite Hnw, Hxp; reflexivity).
    assert (Hs0eq : param_store (map (out_dparam nat) ps) (adjoint_inputs (decls f) x xb yb) = s0)
      by (rewrite Hin; unfold ps; rewrite s0_shape by assumption; reflexivity).
    assert (Hkey_bar : forall k w0, In (k, w0) B -> exists i, k = KVar (BarOf (DBound i))).
    { intros k w0 Hk; apply (in_map fst) in Hk; simpl in Hk; unfold B in Hk.
      rewrite param_store_keys in Hk by exact (bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn).
      rewrite <- map_map with (f := pvar) (g := fun y => KVar y) in Hk; unfold bps in Hk; rewrite bar_keys in Hk by exact HAL'.
      apply in_map_iff in Hk as [y0 [<- Hy]]; apply in_map_iff in Hy as [p [<- _]]; eauto. }
    assert (HB : forall k w0, In (k, w0) B -> store_get s0 k = Some w0).
    { intros k w0 Hk; destruct (Hkey_bar k w0 Hk) as [i ->]; apply store_get_mid; [apply prim_entries_bar | exact HBnd | exact Hk]. }
    assert (Hs0p : forall p, In p L -> store_get s0 (keyv (stored p)) = Some (TangentCorrect.primal (pd p)))
      by (intros p Hp; unfold s0; rewrite store_get_app, (Hprim p Hp); reflexivity).
    assert (Hra_ds : Forall (fun d => has_dot d = true -> real_or_array (decl_ty d)) (decls f)).
    { apply has_dot_ra; [exact Hnrv |]; intros d Hd Wd.
      rewrite <- Hdn in Hd; apply in_map_iff in Hd as [p [<- Hp]]; rewrite (Hu p Hp Wd), Hdecl_y; exact Hraw. }
    (* the forward sweep *)
    assert (Hparg : forall p, In p L -> exists nm0 t0 r0 i0 x1, p = arg_pv nm0 t0 r0 i0 x1)
      by (intros p Hp; destruct (Hargs' p Hp) as [i0 [nm0 [t0 [r0 [x1 [-> _]]]]]]; do 5 eexists; reflexivity).
    assert (Hown_cases : owner (Some (AVar y)) PTop = match t with Array _ => Some y | _ => None end)
      by (simpl; rewrite Hvy; reflexivity).
    assert (Hactx : actx L n n s0 (Some (AVar y)) PTop (live_anf n bW) (tbr cvw Forward n bA) t).
    { constructor.
      - constructor.
        + exact Hstat.
        + exact Huniq.
        + exact Hnum.
        + intros a0 E; injection E as <-; exists y; split; [reflexivity | split; [exact HyL | rewrite Ey; discriminate]].
        + exact I.
        + intros o p Hw0 Hp E; rewrite Hown_cases in Hw0; destruct t; try discriminate; injection Hw0 as <-.
          left; exact (Hpn_inj p y Hp HyL E).
        + intros p o Hp Lp Ha Hg' Hw0; rewrite Hown_cases in Hw0; destruct t; try discriminate; injection Hw0 as <-.
          destruct Hg' as [Hg' | Hg'];
            [destruct (Hargs' p Hp) as [? [? [? [? [? [-> _]]]]]]; discriminate | injection Hg' as ->; reflexivity].
        + intros Ha; rewrite Hown_cases; destruct t; try destruct Ha; discriminate.
        + intros y' _ E Ha; injection E as <-; split; [symmetry; exact Hvy |].
          intros Ly; destruct r; simpl in Hwr; try discriminate.
          * unfold live_anf in Ly; rewrite Hdep in Ly by reflexivity; discriminate.
          * rewrite Ey; reflexivity.
      - intros p Hp; destruct (Hparg p Hp) as [? [? [? [? [? ->]]]]]; reflexivity.
      - intros p Hp _; exact (Hs0p p Hp).
      - intros p Hp; destruct (Hparg p Hp) as [? [? [? [? [? ->]]]]]; discriminate. }
    assert (Hvo : Forward = Forward -> PTop = PTop /\ (vo = None <-> cvw = false) /\
                  (forall y', vo = Some (AWrites y') -> option_map (amap pt) (Some (AVar y)) = Some y') /\
                  (forall t', vo = Some (AReturns t') -> Some (AVar y) = None)).
    { intros _; unfold vo; split; [reflexivity | split; [destruct cvw; split; intros; congruence |]].
      split; [intros y' E; destruct cvw; [injection E as <-; reflexivity | discriminate] |].
      intros t' E; destruct cvw; discriminate. }
    assert (Hvtg : vo_target vo = if cvw then match r, t with Dependent, (Real | Array _) => Some (stored y) | _, _ => None end else None).
    { unfold vo; destruct cvw; [| reflexivity]; rewrite Ey; simpl; destruct r, t; reflexivity. }
    assert (Hvt : Forward = Forward -> forall p, In p L -> live_anf n bW p -> vo_target vo <> Some (stored p)).
    { intros _ p Hp Lp E; rewrite Hvtg in E; destruct cvw; [| discriminate].
      destruct r; try discriminate; destruct t; try discriminate;
        assert (Epn : pn p = pn y) by (unfold stored in E; congruence);
        rewrite (Hpn_inj p y Hp HyL Epn) in Lp;
        unfold live_anf in Lp; rewrite Hdep in Lp by reflexivity; discriminate. }
    assert (Hvb : Forward = Forward -> forall t', vo_target vo = Some t' -> below n t' /\ consistent t' /\ is_primal t').
    { intros _ t' E; rewrite Hvtg in E; destruct cvw; [| discriminate].
      destruct r; try discriminate; destruct t; try discriminate.
      all: injection E as <-; unfold stored; simpl; split; [exact (Hnum y HyL) | split; [reflexivity | exact I]]. }
    pose proof (Hsim L n n s0 (Some (AVar y)) PTop Forward bA bW bT bD t v se vo HbA HbW HbT HbD Hactx Hraw HtcB Hev Hvo Hvt Hvb)
      as HS.
    cbn [option_map amap] in HS.
    lazymatch type of HS with context [@open_pairs ?A ?t0 n] =>
      assert (E : @open_pairs A t0 n = ((fw, rv), c')) by exact Hob; rewrite E in HS; clear E end.
    destruct HS as [Hcc [Hhty [s1 [R1 [F1 [T1 [V1 Hrev]]]]]]].
    (* the adjoints at the start *)
    destruct (static_in _ _ _ Hstat HyL) as [_ [_ [_ [_ [_ [_ [_ [_ [Hhy _]]]]]]]]].
    rewrite Hvy in Hhy.
    assert (Hwyb : Forall2 (fun d v0 => written_decl d = true -> (nreals v0 <= length yb)%nat) (decls f) x).
    { rewrite <- Hdn, <- Hxp; apply forall2_map; apply Forall_forall; intros p Hp Wp; rewrite (Hu p Hp Wp).
      rewrite nreals_length, (has_type_size t (pd y) Hhy Hraw), Hlyb, (has_type_size t v Hhty Hraw); lia. }
    destruct (bar_store (decls f) x xb yb dx (rev L) s0 Hfit Hlxb Hwyb Hra_ds Hdn Hpd HAL' HB) as [_ Hbars0].
    (* the prologue *)
    set (OW := owners_of (rev L)).
    set (ex := inplace (Some (AVar y)) PTop).
    assert (Hex_bar : forall m, ex <> Some (BarOf m)) by (intros m; unfold ex, inplace; rewrite Hown_cases; destruct t; discriminate).
    assert (Hvt0 : forall m, vo_target vo <> Some (BarOf m))
      by (intros m; rewrite Hvtg; destruct cvw, r, t; discriminate).
    assert (Hbars1 : forall p, In p (rev L) -> barv s1 (stored p) = barv s0 (stored p)).
    { intros p Hp; unfold barv; apply F1; [simpl; exact (Hnum p (HinL p Hp)) | reflexivity | simpl; tauto | apply Hex_bar | apply Hvt0]. }
    assert (Hcase : exists s2, run pro s1 = Some s2 /\ agree_prim c' ex s1 s2 /\ seed_ok n t se s2 /\
              (forall p, In p (rev L) -> p <> y -> barv s2 (stored p) = barv s1 (stored p)) /\
              (exists b, barv s2 (stored y) = Some b /\ shaped (TangentCorrect.tangent (pd y)) (Some b)) /\
              vo_kept vo s1 s2 /\
              result_pairing OW t ex v se s2 = (init_sum (rev L) s0 + dotl (reals_of_val (TangentCorrect.tangent v)) yb)%R).
    { assert (Hby1 : barv s1 (stored y) = Some (with_list (TangentCorrect.primal (pd y)) yb)).
      { rewrite (Hbars1 y HyR); exact (bars_in_written (decls f) x xb yb dx (rev L) s0 y Hfit Hdn Hpd Hbars0 HyR Hdy Hywr). }
      assert (Hpt : tstored (pt y) = stored y /\ tty (pt y) = t /\ targ (pt y) = Some (nm', r))
        by (rewrite Ey; repeat split; reflexivity).
      destruct Hpt as [Htst [Htty Htarg]].
      unfold adjoint_seed, role_of, stored_of, tof in Eseed; rewrite Htty, Htarg, Htst in Eseed.
      destruct (static_in _ _ _ Hstat HyL) as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hzy]]]]]]]]].
      assert (Hav : avaried (pa y) = varied_role r) by (rewrite Ey; reflexivity).
      assert (Hseedv : forall s, barv s (stored y) = Some (VReal (hd 0%R yb)) ->
                         xev s (DVar (BarOf (stored y))) = Some (VReal (hd 0%R yb))) by (intros s Hs; exact Hs).
      destruct t as [| | | z]; try destruct Hraw.
      - (* a real *)
        assert (Hexn : ex = None) by (unfold ex, inplace; rewrite Hown_cases; reflexivity).
        destruct v as [d | | | |]; try (simpl in Hhty; contradiction).
        destruct (pd y) as [dy | | | |] eqn:Epd; try (simpl in Hhy; contradiction).
        simpl in Hby1.
        assert (Hyb1 : dotl (reals_of_val (TangentCorrect.tangent (VReal d))) yb = (dsnd d * hd 0%R yb)%R).
        { simpl in Hlyb; destruct yb as [| y0 [| ]]; simpl in Hlyb; try discriminate; unfold dotl; simpl; ring. }
        destruct r; simpl in Hwr; try discriminate.
        + (* dependent *)
          simpl in Eseed; injection Eseed as <- <-.
          exists s1; split; [reflexivity |].
          split; [intros ? ? ? ?; reflexivity |].
          split.
          { split; [intros y0 [<- | []]; split; [simpl; exact (Hnum y HyL) | reflexivity] |].
            intros _; exists (hd 0%R yb); exact (Hseedv s1 Hby1). }
          split; [intros; reflexivity |].
          split; [exists (VReal (hd 0%R yb)); split; [exact Hby1 | exact I] |].
          split; [apply vo_kept_refl |].
          unfold result_pairing; try rewrite Hexn; unfold seed_value; rewrite (Hseedv s1 Hby1), Hyb1.
          unfold OW; rewrite pairing_split, (written_sum_one (rev L) s1 y Hnd HyR Hdy Hywr Hu), Epd, Hby1.
          rewrite (init_sum_ext (rev L) s0 s1) by (intros p Hp _ _; apply Hbars1; exact Hp).
          specialize (Hzy Hav); simpl in Hzy; simpl; rewrite Hzy; ring.
        + (* inout *)
          simpl in Eseed; injection Eseed as <- <-.
          set (sa := store_set s1 (keyv (BarOf ResultVar)) (VReal (hd 0%R yb))).
          set (s2 := store_set sa (keyv (BarOf (stored y))) (VReal 0%R)).
          assert (Hky : forall p, In p (rev L) -> p <> y -> keyv (BarOf (stored y)) <> keyv (BarOf (stored p))).
          { intros p Hp Hne E; unfold keyv, stored in E; simpl in E; injection E as E.
            apply Hne; exact (Hpn_inj p y (HinL p Hp) HyL (eq_sym E)). }
          exists s2; split.
          { change [DDefine (DConstant Real) (BarOf ResultVar) (DVar (BarOf (stored y)));
                    DAssign (DVar (BarOf (stored y))) (DReal "0")]
              with ([DDefine (DConstant Real) (BarOf ResultVar) (DVar (BarOf (stored y)))] ++
                    [DAssign (DVar (BarOf (stored y))) (DReal "0")]).
            rewrite run_app, (run_define s1 _ _ _ (VReal (hd 0%R yb)) (Hseedv s1 Hby1)).
            fold sa; rewrite run_assign_var with (v := VReal 0%R) by (rewrite xev_DReal, lit_0; reflexivity).
            reflexivity. }
          split; [exact (agree_prim_set_bar c' ex s1 sa (stored y) (VReal 0%R)
                           (agree_prim_set_bar c' ex s1 s1 ResultVar _ (fun _ _ _ _ => eq_refl) I) eq_refl) |].
          split.
          { split; [intros y0 [<- | []]; split; exact I |].
            intros _; exists (hd 0%R yb); change (xev s2 (DVar (BarOf ResultVar))) with (store_get s2 (keyv (BarOf ResultVar))).
            unfold s2; rewrite store_get_set_other by discriminate; unfold sa; apply store_get_set_same. }
          split.
          { intros p Hp Hne; unfold barv, s2, sa.
            rewrite store_get_set_other by exact (Hky p Hp Hne).
            rewrite store_get_set_other by discriminate; reflexivity. }
          split; [exists (VReal 0%R); split; [unfold barv, s2; apply store_get_set_same | exact I] |].
          split; [apply (vo_kept_trans _ _ sa); apply vo_kept_set_bar; exact I |].
          unfold result_pairing; try rewrite Hexn; unfold seed_value.
          change (xev s2 (DVar (BarOf ResultVar))) with (store_get s2 (keyv (BarOf ResultVar))).
          unfold s2; rewrite store_get_set_other by discriminate; unfold sa; rewrite store_get_set_same; fold sa; fold s2.
          rewrite Hyb1.
          unfold OW; rewrite pairing_split, (written_sum_one (rev L) s2 y Hnd HyR Hdy Hywr Hu).
          assert (Hb2y : barv s2 (stored y) = Some (VReal 0%R)) by (unfold barv, s2; apply store_get_set_same).
          rewrite Hb2y, inner_zero.
          rewrite (init_sum_ext (rev L) s0 s2); [ring |].
          intros p Hp _ Wp; assert (Hne : p <> y) by (intros ->; congruence).
          unfold barv, s2, sa; rewrite store_get_set_other by exact (Hky p Hp Hne).
          rewrite store_get_set_other by discriminate; exact (Hbars1 p Hp).
      - (* an array *)
        assert (Hexa : ex = Some (stored y)) by (unfold ex, inplace; rewrite Hown_cases; reflexivity).
        destruct r; simpl in Hwr; try discriminate; simpl in Eseed; injection Eseed as <- <-.
        all: exists s1; split; [reflexivity |].
        all: split; [intros ? ? ? ?; reflexivity |].
        all: split; [split; [intros y0 [] | intros E; discriminate] |].
        all: split; [intros; reflexivity |].
        all: split; [destruct (bars_in_get _ _ _ y Hbars0 HyR Hdy) as [b [Eb Sb]]; exists b; rewrite (Hbars1 y HyR); auto |].
        all: split; [apply vo_kept_refl |].
        all: unfold result_pairing; rewrite Hexa.
        all: unfold OW; rewrite (pairing_oset_owners (rev L) y _ s1 HnL HyR Hdy Hywr Hu), Hby1.
        all: rewrite (init_sum_ext (rev L) s0 s1) by (intros p Hp _ _; apply Hbars1; exact Hp).
        all: f_equal.
        all: destruct v as [| | | lv |]; try (simpl in Hhty; contradiction).
        all: destruct (pd y) as [| | | ly |] eqn:Epd; try (simpl in Hhy; contradiction).
        all: simpl in Hhty, Hhy, Hlyb |- *; rewrite length_map in Hlyb; rewrite length_map, Hhy, <- Hhty, <- Hlyb, firstn_all.
        all: reflexivity. }
    destruct Hcase as [s2 [R2 [Hag [Hseed [Hb2 [Hby [K2 Hres]]]]]]].
    (* the reverse sweep *)
    assert (Hr : rctx L n (Some (AVar y)) PTop OW (useful cvw Forward n bA) s2).
    { constructor.
      - apply owners_nodup; exact HnL.
      - intros t0 m Hi; destruct (in_owners _ _ _ Hi) as [p [Hp [Hd [-> ->]]]].
        destruct (Nat.eq_dec (pn p) (pn y)) as [Epy | Hne'].
        { rewrite (Hpn_inj p y (HinL p Hp) HyL Epy); destruct Hby as [b [Eb Sb]]; rewrite Eb; exact Sb. }
        assert (Hne : p <> y) by (intros ->; contradiction).
        rewrite (Hb2 p Hp Hne), (Hbars1 p Hp); destruct (bars_in_get _ _ _ p Hbars0 Hp Hd) as [b [Eb Sb]]; rewrite Eb; exact Sb.
      - intros t0 m Hi; destruct (in_owners _ _ _ Hi) as [p [Hp [_ [_ ->]]]]; exists (pn p).
        split; [reflexivity | exact (Hnum p (HinL p Hp))].
      - intros p Hp _ Hv; apply owners_intro; [apply in_rev_iff; exact Hp |].
        destruct (Hargs' p Hp) as [i0 [nm0 [t0 [r0 [x1 [-> [_ [Hd _]]]]]]]]; simpl in Hv.
        pose proof (non_real_varied_none (decls f) nm0 t0 r0 Hnrv (nth_error_In _ _ Hd) Hv) as Hra.
        unfold dname, arg_entry; simpl.
        destruct t0; try destruct Hra; destruct r0; simpl in Hv; try discriminate; reflexivity.
      - intros p t0 Hp _ Hi; destruct (in_owners _ _ _ Hi) as [q [Hq [_ [-> E]]]].
        unfold stored in E; injection E as E; rewrite (Hpn_inj q p (HinL q Hq) Hp (eq_sym E)); reflexivity.
      - intros o E; rewrite Hown_cases in E; destruct t; try discriminate; injection E as <-.
        exact (owners_intro _ _ HyR Hdy). }
    assert (Htp : tapes_ok L s2) by (intros p Hp Hrp; destruct (Hparg p Hp) as [? [? [? [? [? ->]]]]]; discriminate).
    destruct (Hrev s2 OW Hag Hr Hseed Htp) as [s3 [R3 [K3 [X3 [T3 [F3 [S3 P3]]]]]]].
    fold ex in P3; rewrite Hres in P3.
    (* the end of the function *)
    set (ss := fw ++ pro ++ rv).
    assert (Hss : run ss s0 = Some s3) by (unfold ss; rewrite run_app, R1, run_app, R2; exact R3).
    assert (HbF : forall p, In p (rev L) -> has_dot (dname p) = true ->
                  exists b, barv s3 (stored p) = Some b /\ shaped (TangentCorrect.tangent (pd p)) (Some b)).
    { intros p Hp Hd; pose proof (S3 _ _ (owners_intro _ _ Hp Hd)) as Sh.
      destruct (barv s3 (stored p)) as [b |]; [eauto | simpl in Sh; destruct (TangentCorrect.tangent (pd p)); contradiction]. }
    assert (HbinF := bars_from_store (rev L) s3 HbF).
    assert (Hfb := bars_in_fit (decls f) x dx (rev L) s3 (bars_list (rev L) s3) Hfit Hdn Hpd HbinF).
    destruct (gradient_dotl (decls f) x xb dx (bars_list (rev L) s3) Hfit Hlxb Hldx Hfb) as [g [Hg [Hlg Hdg]]].
    assert (Hgr := grad_rhs_pairing (decls f) x xb yb dx (rev L) s0 s3 (bars_list (rev L) s3) Hfit Hlxb Hldx Hdn Hpd HbinF Hbars0).
    assert (Hlen_ps : length (map (out_dparam nat) ps) = length (adjoint_inputs (decls f) x xb yb)).
    { rewrite Hin; unfold ps; rewrite map_app, map_app, !length_app.
      pose proof (bar_params_inputs (rev L) (decls f) x xb yb HAL' Hdn HLn) as Hbl.
      change (length (map (out_dparam nat) bps) = length (bar_inputs (decls f) x xb yb)) in Hbl.
      rewrite !length_map in Hbl |- *; simpl; rewrite !length_map; do 2 f_equal; exact Hbl. }
    pose proof (finish_exec ps ss (adjoint_inputs (decls f) x xb yb) s0 s3 DVoid Hlen_ps Hs0eq Hss) as Hex.
    exists DVoid, ps, ss, c', (map (final_of s3) (map (out_dparam nat) ps), []), g.
    split; [unfold ss, ps, bps; destruct cv; reflexivity |].
    split; [exact Hex |].
    split.
    { unfold adjoint_output, ps, bps.
      cbn beta iota; rewrite <- Hg; f_equal.
      apply (output_bars cv (rev L) (decls f) [] s3 HAL' Hdn).
      intros p Hp Hd; destruct (HbF p Hp Hd) as [b [Eb _]]; rewrite Eb; discriminate. }
    split; [exact Hlg |].
    split; [rewrite Hdg, Hgr; fold OW; rewrite P3; ring |].
    (* the value in adjoint-value *)
    intros Ecv Hio.
    assert (Er : r = Dependent).
    { destruct r; simpl in Hwr; try discriminate; [reflexivity |].
      assert (writes_inout (decls f) = true) by (apply existsb_exists; exists (Decl nm' t Inout); split; [apply nth_error_In with j; exact Hdj | reflexivity]).
      congruence. }
    subst r.
    assert (Ecw : cvw = true) by (rewrite Hcvw, Ecv; reflexivity).
    unfold value_given.
    rewrite (index_of_written_unique (decls f) j _ 0 Hdj Hwr H1w), Nat.add_0_l, Hdj.
    rewrite !nth_error_map; unfold ps.
    rewrite nth_error_app1 by (rewrite !length_map, length_rev; lia).
    rewrite !nth_error_map.
    assert (Hry : nth_error (rev L) j = Some y).
    { destruct (nth_error (rev L) j) as [q |] eqn:Eq.
      - destruct (Hargs j q Eq) as [? [? [? [? [-> Hx']]]]]; rewrite Hxj in Hx'; injection Hx' as <-.
        rewrite Hds, nth_error_map, Eq in Hdj; simpl in Hdj; injection Hdj as -> -> ->; rewrite Ey; reflexivity.
      - apply nth_error_None in Eq; rewrite length_rev in Eq; lia. }
    rewrite Hry; cbn [option_map]; unfold final_of; rewrite pvar_primal.
    assert (Hvt_y : vo_target vo = Some (stored y)) by (rewrite Hvtg, Ecw; destruct t; try destruct Hraw; reflexivity).
    change (KVar (DBound (pn y))) with (keyv (stored y)).
    rewrite (K3 eq_refl (stored y) Hvt_y ltac:(simpl; tauto)), (K2 (stored y) Hvt_y ltac:(simpl; tauto)).
    rewrite (V1 eq_refl (stored y) Hvt_y); reflexivity.
Qed.

(* Milestone M1: the adjoint function of a straight-line function (lets of
   operations, reads and updates of arrays) computes the gradient. *)
Corollary adjoint_straight_duals (cv : bool) (f : function) (x : list (val R)) (xb yb dx : list R)
  (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) -> length dx = in_dim x ->
  (forall L res bP, open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] = Some (L, res, bP) -> straight bP) ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 = (DBody r ps ss, k) /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb = dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
  intros Hp Hw Hf Hxb Hyb Hdx Hs Hev.
  apply adjoint_simulates_duals; auto.
  intros L res bP Ho; apply asim_straight, (Hs L res bP Ho).
Qed.
