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
  - destruct (varied_role r); [rewrite firstn_length; rewrite nreals_length; lia | apply repeat_length].
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
    { unfold slice; simpl; destruct (varied_role r); [rewrite firstn_length; lia | apply repeat_length]. }
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
        unfold lsub; rewrite length_map, length_combine, firstn_length; lia. }
      exists (piece ++ g); split; [reflexivity |].
      split; [cbn [map concat]; rewrite !length_app; lia |].
      rewrite dotl_app by lia; rewrite Hdg; unfold piece.
      destruct (written_decl (Decl nm t r)); [ring |].
      rewrite dotl_lsub by (rewrite ?firstn_length; lia); ring.
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
      destruct (varied_role r); [rewrite firstn_length; lia | apply repeat_length]. }
    assert (Hm' : length (slice (Decl nm t r) v dx) = m).
    { unfold slice; simpl; destruct (varied_role r); [rewrite firstn_length; lia | apply repeat_length]. }
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
