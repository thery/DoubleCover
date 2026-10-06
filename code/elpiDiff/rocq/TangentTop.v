(* TangentTop.v — theorem 1 at the level of a function
   (tangent_simulates_duals): the arguments are opened, the body simulated
   (TangentLoops.v), the statements checked to follow the scoping discipline
   (TangentGood.v), and the result stored as tangent_result says. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Tangent Simplify Scoping
  AnfEquiv Correctness SimplifyCorrect TangentCorrect TangentLoops TangentGood
  Smooth.

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   Opening the arguments of a definition of L1 at the pv instance: the k-th
   argument has identity k, is stored in the k-th parameter, and has the k-th
   dual argument as its value. The arguments are accumulated last first. *)

Definition arg_pv (n : string) (t : ty) (r : role) (k : nat) (x : val (dual R)) : pv :=
  let vr := varied_role r in
  PV (AV k vr) (VInfo k t (Some (n, r))) (TVar (DBound (k, k)) t (Some (n, r)) vr vr vr false (Some (S k))) x k.

Fixpoint open_P (d : adefinition pv bare) (k : nat) (xs : list (val (dual R))) (L : list pv)
  : option (list pv * aresult pv * anf pv bare) :=
  match d, xs with
  | AArg n t r f, x :: xs' => open_P (f (arg_pv n t r k x)) (S k) xs' (arg_pv n t r k x :: L)
  | ABody res b, [] => Some (L, res, b)
  | _, _ => None
  end.

(* The analyses open the arguments as open_P does. *)
Lemma annotate_open (dP : adefinition pv bare) : forall L k xs L' res bP dA,
  adefinition_eq (gA L) dP dA -> open_P dP k xs L = Some (L', res, bP) ->
  exists bA, anf_eq (gA L') bP bA /\
             annotate_definition_t false k dA = annotate_body_t false Forward (k + length xs) bA.
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

Lemma wf_open (dP : adefinition pv bare) : forall L k xs L' res bP dW decls,
  adefinition_eq (gW L) dP dW -> open_P dP k xs L = Some (L', res, bP) ->
  exists resW bW, aresult_eq (gW L') res resW /\ anf_eq (gW L') bP bW /\
    well_formed_definition decls k dW = well_formed_result decls resW bW (k + length xs).
Proof.
  induction dP as [n t r f IH | rP bP0]; intros L k xs L' res bP dW decls HW Ho.
  - destruct dW as [n' t' r' fW |]; simpl in HW; [| contradiction].
    destruct HW as [<- [<- [<- HW]]]; destruct xs as [| x xs]; simpl in Ho; [discriminate |].
    destruct (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP (fW (VInfo k t (Some (n, r))))
                decls (HW _ _) Ho) as [resW [bW [H1 [H2 H3]]]].
    exists resW, bW; split; [exact H1 | split; [exact H2 |]]; simpl; rewrite H3; f_equal; lia.
  - destruct dW as [| rW bW]; simpl in HW; [contradiction |].
    destruct xs; simpl in Ho; [| discriminate]; injection Ho as <- <- <-.
    exists rW, bW; split; [exact (proj1 HW) | split; [exact (proj2 HW) |]]; simpl; rewrite Nat.add_0_r.
    reflexivity.
Qed.

Lemma eval_open (dP : adefinition pv bare) : forall L k xs L' res bP dD,
  adefinition_eq (gD L) dP dD -> open_P dP k xs L = Some (L', res, bP) ->
  exists bD, anf_eq (gD L') bP bD /\ aeval_definition (duals reals) dD xs = aeval (duals reals) bD.
Proof.
  induction dP as [n t r f IH | rP bP0]; intros L k xs L' res bP dD HD Ho.
  - destruct dD as [n' t' r' fD |]; simpl in HD; [| contradiction].
    destruct HD as [<- [<- [<- HD]]]; destruct xs as [| x xs]; simpl in Ho; [discriminate |].
    exact (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP (fD x) (HD _ _) Ho).
  - destruct dD as [| rD bD]; simpl in HD; [contradiction |].
    destruct xs; simpl in Ho; [| discriminate]; injection Ho as <- <- <-.
    exists bD; split; [exact (proj2 HD) | reflexivity].
Qed.

(* An argument as the tangent pass records it: its declaration and its
   stored variable. *)
Definition arg_entry (p : pv) : decl * dvar W :=
  match varg (pw p) with
  | Some (n, r) => (Decl n (vty (pw p)) r, stored p)
  | None => (Decl "" Real Passive, stored p)
  end.

Lemma tangent_open {A : Type} (dP : adefinition pv bare) : forall L k xs L' res bP dT tr
  (K : list (decl * dvar W) -> aresult (tvar W) -> anf (tvar W) ann -> option (atom (tvar W)) -> scoped W A),
  adefinition_eq (gT L) dP dT -> open_P dP k xs L = Some (L', res, bP) ->
  exists resT bT, aresult_eq (gT L') res resT /\ anf_eq (gT L') bP bT /\
    open_pairs (open_arguments W (rebuild_definition _ dT tr) k (map arg_entry L) K) k =
    open_pairs (K (rev (map arg_entry L')) resT (rebuild _ bT tr)
                  (match resT with AWrites y => Some y | AReturns _ => None end)) (k + length xs).
Proof.
  induction dP as [n t r f IH | rP bP0]; intros L k xs L' res bP dT tr K HT Ho.
  - destruct dT as [n' t' r' fT |]; simpl in HT; [| contradiction].
    destruct HT as [<- [<- [<- HT]]]; destruct xs as [| x xs]; simpl in Ho; [discriminate |].
    destruct (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs L' res bP
                (fT (pt (arg_pv n t r k x))) tr K (HT _ _) Ho) as [resT [bT [H1 [H2 H3]]]].
    exists resT, bT; split; [exact H1 | split; [exact H2 |]].
    simpl; replace (k + S (length xs))%nat with (S k + length xs)%nat by lia.
    rewrite <- H3; reflexivity.
  - destruct dT as [| rT bT]; simpl in HT; [contradiction |].
    destruct xs; simpl in Ho; [| discriminate]; injection Ho as <- <- <-.
    exists rT, bT; split; [exact (proj1 HT) | split; [exact (proj2 HT) |]].
    rewrite Nat.add_0_r; simpl; destruct rT; reflexivity.
Qed.

Lemma decls_open (dP : adefinition pv bare) : forall (G : list (pv * unit)) L k xs L' res bP dU,
  adefinition_eq G dP dU -> open_P dP k xs L = Some (L', res, bP) ->
  map (fun p => fst (arg_entry p)) (rev L) ++ declarations dU = map (fun p => fst (arg_entry p)) (rev L').
Proof.
  induction dP as [n t r f IH | rP bP0]; intros G L k xs L' res bP dU HU Ho.
  - destruct dU as [n' t' r' fU |]; simpl in HU; [| contradiction].
    destruct HU as [<- [<- [<- HU]]]; destruct xs as [| x xs]; simpl in Ho; [discriminate |].
    rewrite <- (IH (arg_pv n t r k x) _ (arg_pv n t r k x :: L) (S k) xs L' res bP (fU tt) (HU _ _) Ho).
    simpl; rewrite map_app, <- app_assoc; reflexivity.
  - destruct dU as [| rU bU]; simpl in HU; [contradiction |].
    destruct xs; simpl in Ho; [| discriminate]; injection Ho as <- <- <-.
    simpl; apply app_nil_r.
Qed.

(* What open_P gives: the arguments, last first, each opened by arg_pv. *)
Lemma open_P_args (dP : adefinition pv bare) : forall k xs L L' res bP,
  open_P dP k xs L = Some (L', res, bP) ->
  exists new, L' = new ++ L /\ length new = length xs /\
    forall i p, nth_error (rev new) i = Some p ->
    exists n t r x, p = arg_pv n t r (k + i) x /\ nth_error xs i = Some x.
Proof.
  induction dP as [n t r f IH | rP bP0]; intros k xs L L' res bP Ho.
  - destruct xs as [| x xs]; simpl in Ho; [discriminate |].
    destruct (IH _ _ _ _ _ _ _ Ho) as [new [-> [Hl Hn]]].
    exists (new ++ [arg_pv n t r k x]); split; [rewrite <- app_assoc; reflexivity |].
    split; [rewrite length_app; simpl; lia |].
    intros i p Hi; rewrite rev_app_distr in Hi; simpl in Hi.
    destruct i as [| i]; simpl in Hi.
    + injection Hi as <-; exists n, t, r, x; split; [f_equal; lia | reflexivity].
    + destruct (Hn i p Hi) as [n' [t' [r' [x' [E1 E2]]]]]; exists n', t', r', x'.
      split; [rewrite E1; f_equal; lia | exact E2].
  - destruct xs; simpl in Ho; [| discriminate]; injection Ho as <- <- <-.
    exists []; repeat split; auto; intros i p Hi; destruct i; discriminate.
Qed.

(* ---------------------------------------------------------------------------
   The layout of the tangent function: its arguments and its outputs. *)

(* The declarations of the arguments of f, in order. *)
Definition decls (f : function) : list decl := declarations (afdef (normalize f) unit).

(* An argument with a tangent parameter (tangent_dot). *)
Definition has_dot (d : decl) : bool :=
  let 'Decl _ t r := d in
  match t, r with Integer, _ => false | _, Passive => false | _, _ => true end.

(* The arguments fit their declarations: an array has its extent. *)
Definition fits (d : decl) (v : val R) : Prop :=
  let 'Decl _ t _ := d in
  match t, v with
  | Real, VReal _ | Integer, VInt _ | Boolean, VBool _ => True
  | Array n, VArray l => length l = Z.to_nat n
  | _, _ => False
  end.

(* The number of reals of a value: one for a real, the extent of an array. *)
Definition nreals (v : val R) : nat :=
  match v with VReal _ => 1 | VArray l => length l | _ => 0 end.

(* The seed of the tangents: dx on the reals of the independent and inout
   arguments, 0 on the others (dependent and passive). *)
Fixpoint seed (ds : list decl) (x : list (val R)) (dx : list R) : list R :=
  match ds, x with
  | Decl _ _ r :: ds', v :: x' =>
      let m := nreals v in
      (if varied_role r then firstn m dx else repeat 0%R m) ++ seed ds' x' (skipn m dx)
  | _, _ => []
  end.

(* The reals l with the tangents t, 0 when t is short. *)
Fixpoint pair_with (l t : list R) : list (dual R) :=
  match l with
  | [] => []
  | r :: l' => Dual r (hd 0%R t) :: pair_with l' (tl t)
  end.

(* A value with the tangents t on its reals. *)
Definition val_dual (v : val R) (t : list R) : val (dual R) :=
  match v with
  | VReal r => VReal (Dual r (hd 0%R t))
  | VInt z => VInt z
  | VBool b => VBool b
  | VArray l => VArray (pair_with l t)
  | VTape l => VTape (map (fun r => Dual r 0%R) l)
  end.

(* The arguments as dual numbers, seeded. *)
Fixpoint seed_args (ds : list decl) (x : list (val R)) (dx : list R) : list (val (dual R)) :=
  match ds, x with
  | Decl _ _ r :: ds', v :: x' =>
      let m := nreals v in
      val_dual v (if varied_role r then firstn m dx else repeat 0%R m) :: seed_args ds' x' (skipn m dx)
  | _, _ => []
  end.

(* The arguments of the tangent function: the primal arguments x, then the
   tangent of each argument that has one, then the tangent of a returned
   real (its initial value is not read). *)
Definition tangent_inputs (ds : list decl) (x : list (val R)) (dx : list R) : list (val R) :=
  let xs := seed_args ds x dx in
  map primal xs ++
  concat (map (fun '(d, v) => if has_dot d then [tangent v] else []) (combine ds xs)) ++
  (if existsb written_decl ds then [] else [VReal 0%R]).

Fixpoint index_of_written (ds : list decl) (i : nat) : option nat :=
  match ds with
  | [] => None
  | d :: ds' => if written_decl d then Some i else index_of_written ds' (S i)
  end.

(* The value and the tangent the tangent function computes: the returned
   value and the last parameter (result_dot), or the written argument and its
   tangent parameter. *)
Definition tangent_output (ds : list decl) (out : list (val R) * list (val R)) : option (val R * val R) :=
  let '(finals, rets) := out in
  match index_of_written ds 0 with
  | None => match rets, last finals (VInt 0) with [v], d => Some (v, d) | _, _ => None end
  | Some j =>
      match nth_error finals j, nth_error finals (length ds + length (filter has_dot (firstn j ds))) with
      | Some v, Some d => Some (v, d)
      | _, _ => None
      end
  end.

(* ---------------------------------------------------------------------------
   Theorem 1, for a function. *)

Lemma open_P_some (dP : adefinition pv bare) : forall L k xs dD v,
  adefinition_eq (gD L) dP dD -> aeval_definition (duals reals) dD xs = Some v ->
  exists L' res bP, open_P dP k xs L = Some (L', res, bP).
Proof.
  induction dP as [n t r f IH | rP bP0]; intros L k xs dD v HD He.
  - destruct dD as [n' t' r' fD |]; simpl in HD; [| contradiction].
    destruct HD as [<- [<- [<- HD]]]; destruct xs as [| x xs]; simpl in He |- *; [discriminate |].
    exact (IH (arg_pv n t r k x) (arg_pv n t r k x :: L) (S k) xs (fD x) v (HD _ _) He).
  - destruct dD as [| rD bD]; simpl in HD; [contradiction |].
    destruct xs; simpl in He |- *; [eauto | discriminate].
Qed.



(* ---------------------------------------------------------------------------
   The seeded arguments. *)

Lemma primal_val_dual v t : primal (val_dual v t) = v.
Proof.
  destruct v as [r | z | b | l | l]; simpl; auto.
  - f_equal; revert t; induction l as [| r l IH]; intros t; simpl; [reflexivity | f_equal; apply IH].
  - f_equal; induction l as [| r l IH]; simpl; [reflexivity | f_equal; apply IH].
Qed.

Lemma pair_with_length l t : length (pair_with l t) = length l.
Proof. revert t; induction l; intros t; simpl; auto. Qed.

Lemma fits_type n t r v tg : fits (Decl n t r) v -> has_type t (val_dual v tg).
Proof. destruct t, v; simpl; auto; intros H; rewrite pair_with_length; exact H. Qed.

Lemma zero_val_dual v m : zero (val_dual v (repeat 0%R m)).
Proof.
  destruct v as [r | z | b | l | l]; simpl; auto.
  - destruct m; reflexivity.
  - revert m; induction l as [| r l IH]; intros m; simpl; constructor; [destruct m; reflexivity |].
    destruct m; simpl; [apply (IH 0%nat) | apply IH].
Qed.

Lemma seed_args_nth ds x dx i n t r :
  Forall2 fits ds x -> nth_error ds i = Some (Decl n t r) ->
  exists v tg, nth_error x i = Some v /\ nth_error (seed_args ds x dx) i = Some (val_dual v tg) /\
               fits (Decl n t r) v /\ (varied_role r = false -> zero (val_dual v tg)).
Proof.
  intros H; revert i dx; induction H as [| [n' t' r'] v ds x Hf Hfs IH]; intros i dx Hi;
    [destruct i; discriminate |].
  destruct i as [| i]; simpl in Hi |- *.
  - injection Hi as <- <- <-; eexists v, _; split; [reflexivity | split; [reflexivity |]].
    split; [exact Hf | intros Hv; rewrite Hv; apply zero_val_dual].
  - exact (IH i _ Hi).
Qed.

Lemma seed_args_length ds x dx : Forall2 fits ds x -> length (seed_args ds x dx) = length ds.
Proof.
  intros H; revert dx; induction H as [| [n t r] v ds x Hf Hfs IH]; intros dx; simpl; [reflexivity |].
  f_equal; apply IH.
Qed.

(* ---------------------------------------------------------------------------
   The initial store of the tangent function. *)

Definition prim_entries (AL : list pv) : store R :=
  map (fun p => (KVar (DBound (pn p)), primal (pd p))) AL.

Definition dot_in (p : pv) : list (val R) :=
  if has_dot (fst (arg_entry p)) then [tangent (pd p)] else [].

Definition dot_entries (AL : list pv) : store R :=
  concat (map (fun p => if has_dot (fst (arg_entry p)) then [(KVar (DotOf (DBound (pn p))), tangent (pd p))]
                        else []) AL).

Lemma combine_app {A B : Type} (a1 a2 : list A) (b1 b2 : list B) :
  length a1 = length b1 -> combine (a1 ++ a2) (b1 ++ b2) = combine a1 b1 ++ combine a2 b2.
Proof.
  revert b1; induction a1 as [| x a1 IH]; intros [| y b1] H; simpl in *; try discriminate; auto.
  f_equal; apply IH; lia.
Qed.

Lemma tangent_dot_entry p :
  varg (pw p) <> None ->
  tangent_dot W (arg_entry p) =
  if has_dot (fst (arg_entry p)) then [match tangent_dot W (arg_entry p) with
                                       | [d] => d | _ => DParam ByValue Real ResultVar end] else [].
Proof.
  intros Hg; unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; [| contradiction].
  destruct (vty (pw p)), r; reflexivity.
Qed.

(* The store exec_scoped builds from the parameters and the arguments of the
   tangent function. *)
Lemma initial_store (AL : list pv) eps ein :
  Forall (fun p => tstored (pt p) = stored p /\ varg (pw p) <> None) AL ->
  length eps = length ein ->
  map (fun '(DParam _ _ x, a) => (KVar x, a))
    (combine (map (out_dparam nat)
                (map (tangent_primal W) (map arg_entry AL) ++ concat (map (tangent_dot W) (map arg_entry AL)) ++ eps))
             (map (fun p => primal (pd p)) AL ++ concat (map dot_in AL) ++ ein)) =
  prim_entries AL ++ dot_entries AL ++
  map (fun '(DParam _ _ x, a) => (KVar x, a)) (combine (map (out_dparam nat) eps) ein).
Proof.
  intros HAL Hl.
  rewrite !map_app, combine_app by (rewrite !length_map; reflexivity).
  rewrite combine_app.
  2: { rewrite length_map; clear - HAL; induction HAL as [| p AL [_ Hg] HAL IH]; simpl; auto.
       rewrite !length_app, IH, tangent_dot_entry by exact Hg; unfold dot_in;
         destruct (has_dot (fst (arg_entry p))); simpl; lia. }
  rewrite !map_app; f_equal; [| f_equal].
  - unfold prim_entries; induction AL as [| p AL IH]; simpl; [reflexivity |].
    inversion HAL as [| ? ? [_ Hg] HAL']; subst; f_equal; [| apply IH; auto].
    unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; [| contradiction].
    unfold stored; destruct (vty (pw p)); simpl; try destruct (written_role r); reflexivity.
  - unfold dot_entries; induction AL as [| p AL IH]; simpl; [reflexivity |].
    inversion HAL as [| ? ? [_ Hg] HAL']; subst.
    rewrite map_app, <- IH by auto; unfold dot_in.
    rewrite tangent_dot_entry by exact Hg.
    unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; [| contradiction].
    destruct (vty (pw p)), r; simpl; reflexivity.
Qed.

Lemma store_get_app (s1 s2 : store R) k :
  store_get (s1 ++ s2) k = match store_get s1 k with Some v => Some v | None => store_get s2 k end.
Proof. induction s1 as [| [k0 v0] s1 IH]; simpl; [reflexivity |]; destruct (key_eqb k0 k); auto. Qed.

Lemma prim_lookup AL p :
  NoDup (map pn AL) -> In p AL -> store_get (prim_entries AL) (KVar (DBound (pn p))) = Some (primal (pd p)).
Proof.
  induction AL as [| q AL IH]; intros Hnd Hp; [destruct Hp |].
  inversion Hnd as [| ? ? Hq Hnd']; subst; simpl.
  destruct Hp as [-> | Hp].
  - rewrite Nat.eqb_refl; reflexivity.
  - destruct (Nat.eqb_spec (pn q) (pn p)) as [E | E]; [| apply IH; auto].
    exfalso; apply Hq; rewrite E; apply in_map, Hp.
Qed.

Lemma prim_lookup_dot AL v : store_get (prim_entries AL) (KVar (DotOf v)) = None.
Proof. induction AL; simpl; auto. Qed.

Lemma prim_lookup_none AL j : (forall p, In p AL -> pn p <> j) -> store_get (prim_entries AL) (KVar (DBound j)) = None.
Proof.
  induction AL as [| q AL IH]; intros H; simpl; auto.
  destruct (Nat.eqb_spec (pn q) j); [destruct (H q (or_introl eq_refl)); auto |].
  apply IH; intros p Hp; apply H; right; exact Hp.
Qed.

Lemma dot_lookup AL p :
  NoDup (map pn AL) -> In p AL -> has_dot (fst (arg_entry p)) = true ->
  store_get (dot_entries AL) (KVar (DotOf (DBound (pn p)))) = Some (tangent (pd p)).
Proof.
  induction AL as [| q AL IH]; intros Hnd Hp Hd; [destruct Hp |].
  inversion Hnd as [| ? ? Hq Hnd']; subst; unfold dot_entries in *; simpl; rewrite store_get_app.
  destruct Hp as [-> | Hp].
  - rewrite Hd; simpl; rewrite Nat.eqb_refl; reflexivity.
  - destruct (has_dot (fst (arg_entry q))); simpl; [| apply IH; auto].
    destruct (Nat.eqb_spec (pn q) (pn p)) as [E | E]; [| apply IH; auto].
    exfalso; apply Hq; rewrite E; apply in_map, Hp.
Qed.

Lemma dot_lookup_none AL k : (forall j, k <> KVar (DotOf (DBound j))) -> store_get (dot_entries AL) k = None.
Proof.
  intros H; induction AL as [| q AL IH]; unfold dot_entries in *; simpl; auto.
  rewrite store_get_app, IH; destruct (has_dot (fst (arg_entry q))); simpl; auto.
  destruct k as [[x | [x | | | |] | | |] |]; simpl; auto.
  destruct (Nat.eqb_spec (pn q) x) as [<- | E]; [destruct (H (pn q)); reflexivity | reflexivity].
Qed.

Lemma dot_lookup_absent AL j : (forall p, In p AL -> pn p <> j) ->
  store_get (dot_entries AL) (KVar (DotOf (DBound j))) = None.
Proof.
  induction AL as [| q AL IH]; intros H; unfold dot_entries in *; simpl; auto.
  rewrite store_get_app, IH by (intros p Hp; apply H; right; exact Hp).
  destruct (has_dot (fst (arg_entry q))); simpl; auto.
  destruct (Nat.eqb_spec (pn q) j); [destruct (H q (or_introl eq_refl)); auto | reflexivity].
Qed.

Lemma non_real_varied_none ds nm t r :
  non_real_varied ds = None -> In (Decl nm t r) ds -> varied_role r = true -> real_or_array t.
Proof.
  induction ds as [| [nm' t' r'] ds IH]; intros H Hin Hv; [destruct Hin |]; simpl in H.
  destruct (varied_role r' && negb (ty_eqb t' Real || ty_is_array t')) eqn:E; [discriminate |].
  destruct Hin as [E' | Hin]; [| apply IH; auto].
  injection E' as -> -> ->; rewrite Hv in E; simpl in E.
  destruct t; simpl in E; try discriminate; exact I.
Qed.

(* What well_formed says of the result of a function. *)
Lemma wf_result_facts ds resW bW k :
  well_formed_result ds resW bW k = Ok ->
  (resW = AReturns Real /\ existsb written_decl ds = false /\ typecheck None Top k bW = (Real, Ok)) \/
  (exists w nm role, resW = AWrites (AVar w) /\ varg w = Some (nm, role) /\ written_role role = true /\
     length (filter written_decl ds) = 1%nat /\ real_or_array (vty w) /\
     typecheck (Some (AVar w)) Top k bW = (vty w, Ok) /\
     (role = Dependent -> occurs_anf (vid w) k bW = false) /\ (role = Inout -> occurs_anf (vid w) k bW = true)).
Proof.
  intros H; destruct resW as [[| | | z] | [w | | ]]; simpl in H; try discriminate.
  - left; destruct (existsb written_decl ds); [discriminate |].
    destruct (typecheck None Top k bW) as [t [| mm]]; simpl in H; [| discriminate].
    destruct (ty_eqb t Real) eqn:E; [| discriminate]; apply ty_eqb_true in E; subst; auto.
  - right; destruct (varg w) as [[nm role] |] eqn:Eg; [| discriminate].
    destruct (written_role role) eqn:Er; [| discriminate].
    destruct (Nat.eqb_spec (length (filter written_decl ds)) 1) as [El | El]; simpl in H; [| discriminate].
    destruct (ty_eqb (vty w) Real || ty_is_array (vty w)) eqn:Et; simpl in H; [| discriminate].
    destruct (typecheck (Some (AVar w)) Top k bW) as [t [| mm]] eqn:Htc; simpl in H; [| discriminate].
    destruct (ty_eqb t (vty w)) eqn:Etw; simpl in H; [| discriminate]; apply ty_eqb_true in Etw; subst t.
    exists w, nm, role; repeat split; auto.
    + destruct (vty w); simpl in Et; try discriminate; exact I.
    + intros ->; destruct (occurs_anf (vid w) k bW); [discriminate | reflexivity].
    + intros ->; destruct (occurs_anf (vid w) k bW); [reflexivity | discriminate].
Qed.

(* Running the tangent program over the reals, from the primal arguments and
   the seeded tangents, computes the value and the tangent of the dual
   evaluation of the normal form of f; its statements follow the discipline
   of simplify. *)
Theorem tangent_simulates_duals (f : function) (x : list (val R)) (dx : list R) (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) = Some v ->
  exists r ps ss k out,
    open_pairs (dfbody (Tangent.tangent (annotate false (normalize f))) W) 0 = (DBody r ps ss, k) /\
    Forall consistent (params ps) /\ good (params ps) (params ps) ss /\ existsb has_tape_op ss = false /\
    exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (tangent_inputs (decls f) x dx) = Some out /\
    tangent_output (decls f) out = Some (primal v, tangent v).
Proof.
  intros Hpar Hwf Hfit Hev.
  set (xs := seed_args (decls f) x dx) in *.
  pose proof (normalize_parametric f Hpar) as Hnp.
  set (dP := afdef (normalize f) pv).
  assert (HD := Hnp pv (val (dual R))); fold dP in HD.
  unfold aeval_function in Hev.
  destruct (open_P_some dP [] 0 xs _ v HD Hev) as [L [res [bP Ho]]].
  destruct (open_P_args dP 0 xs [] L res bP Ho) as [new [EL [Hlen Hargs]]].
  rewrite app_nil_r in EL; subst new.
  (* the bodies of the five instances *)
  destruct (annotate_open dP [] 0 xs L res bP _ (Hnp pv avar) Ho) as [bA [HbA Htr]].
  destruct (wf_open dP [] 0 xs L res bP _ (decls f) (Hnp pv vinfo) Ho) as [resW [bW [HrW [HbW Hwfd]]]].
  destruct (eval_open dP [] 0 xs L res bP _ HD Ho) as [bD [HbD HevD]].
  rewrite HevD in Hev.
  assert (Hds := decls_open dP (map (fun p => (p, tt)) []) [] 0 xs L res bP _ (Hnp pv unit) Ho).
  assert (Hds' : decls f = map (fun p => fst (arg_entry p)) (rev L)) by exact Hds.
  clear Hds; rename Hds' into Hds.
  rewrite Nat.add_0_l in Htr, Hwfd; set (n := length xs) in *.
  set (tr := annotate_definition_t false 0 (afdef (normalize f) avar)) in *.
  destruct (tangent_open dP [] 0 xs L res bP (afdef (normalize f) (tvar W)) tr (tangent_body W)
              (Hnp pv (tvar W)) Ho) as [resT [bT [HrT [HbT Hopen]]]].
  (* well_formed *)
  unfold well_formed in Hwf; fold (decls f) in Hwf.
  destruct (non_real_varied (decls f)) eqn:Hnrv; [discriminate |].
  rewrite Hwfd in Hwf.
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
  admit.
Admitted.
