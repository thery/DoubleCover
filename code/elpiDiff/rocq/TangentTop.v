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

(* The final values of the parameters, when each is in the store. *)
Lemma finals_some (s : store R) (ps : list (dparam nat)) :
  (forall pw t x, In (DParam pw t x) ps -> exists v, store_get s (KVar x) = Some v) ->
  exists fs, fold_right (fun o acc => match o with
                                      | Some v => match acc with Some l => Some (v :: l) | None => None end
                                      | None => None end) (Some [])
               (map (fun '(DParam _ _ x) => store_get s (KVar x)) ps) = Some fs /\
             length fs = length ps /\
             forall i pw t x, nth_error ps i = Some (DParam pw t x) -> nth_error fs i = store_get s (KVar x).
Proof.
  induction ps as [| [pw t x] ps IH]; intros H; simpl.
  - exists []; split; [reflexivity | split; [reflexivity | intros [|i]; discriminate]].
  - destruct (H pw t x (or_introl eq_refl)) as [v Hv]; rewrite Hv.
    destruct IH as [fs [Hf [Hl Hn]]]; [intros pw' t' x' Hin; apply (H pw' t' x'); right; exact Hin |].
    rewrite Hf; exists (v :: fs); split; [reflexivity | split; [simpl; f_equal; exact Hl |]].
    intros [| i] pw' t' x' Hi; simpl in Hi |- *; [injection Hi as <- <- <-; symmetry; exact Hv | apply Hn with pw' t'; exact Hi].
Qed.

Lemma nth_error_last {A : Type} (l : list A) d x :
  nth_error l (length l - 1) = Some x -> last l d = x.
Proof.
  induction l as [| a l IH]; [discriminate |].
  destruct l as [| b l]; [simpl; intros E; injection E; auto |].
  intros E; change (last (a :: b :: l) d) with (last (b :: l) d); apply IH.
  simpl in E |- *; rewrite Nat.sub_0_r in *; exact E.
Qed.

Lemma params_app ps1 ps2 : params (ps1 ++ ps2) = params ps1 ++ params ps2.
Proof. unfold params; apply map_app. Qed.

Lemma params_primal AL : params (map (tangent_primal W) (map arg_entry AL)) = map stored AL.
Proof.
  induction AL as [| p AL IH]; simpl; [reflexivity |]; unfold params in *; simpl; rewrite IH; f_equal.
  unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; simpl;
    [destruct (vty (pw p)); try destruct (written_role r) | ]; reflexivity.
Qed.

Lemma params_dots AL :
  Forall (fun p => varg (pw p) <> None) AL ->
  params (concat (map (tangent_dot W) (map arg_entry AL))) =
  concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) AL).
Proof.
  induction 1 as [| p AL Hg HAL IH]; simpl; [reflexivity |].
  rewrite params_app, IH; f_equal.
  unfold arg_entry; destruct (varg (pw p)) as [[nm r] |]; [| contradiction].
  destruct (vty (pw p)), r; reflexivity.
Qed.

Lemma in_dots AL p :
  In p AL -> has_dot (fst (arg_entry p)) = true ->
  In (DotOf (stored p)) (concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) AL)).
Proof.
  intros Hp Hd; apply in_concat; exists [DotOf (stored p)]; split; [| left; reflexivity].
  apply in_map_iff; exists p; rewrite Hd; auto.
Qed.

Lemma in_dots_inv AL y :
  In y (concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) AL)) ->
  exists p, In p AL /\ y = DotOf (stored p) /\ has_dot (fst (arg_entry p)) = true.
Proof.
  intros Hy; apply in_concat in Hy as [l [Hl Hy]]; apply in_map_iff in Hl as [p [<- Hp]].
  destruct (has_dot (fst (arg_entry p))) eqn:E; [destruct Hy as [<- | []]; eauto | destruct Hy].
Qed.

Lemma in_rev_iff {A : Type} (x : A) l : In x (rev l) <-> In x l.
Proof. symmetry; apply in_rev. Qed.

Lemma dvar_eq_dec (a b : dvar W) : {a = b} + {a <> b}.
Proof. decide equality; destruct x, x0; decide equality; apply Nat.eq_dec. Qed.

Lemma index_of_written_none ds i : existsb written_decl ds = false -> index_of_written ds i = None.
Proof.
  revert i; induction ds as [| d ds IH]; intros i H; simpl in *; [reflexivity |].
  destruct (written_decl d); [discriminate | apply IH; exact H].
Qed.

Lemma inputs_eq ds x dx (AL : list pv) :
  seed_args ds x dx = map pd AL -> ds = map (fun p => fst (arg_entry p)) AL ->
  tangent_inputs ds x dx =
  map (fun p => primal (pd p)) AL ++ concat (map dot_in AL) ++
  (if existsb written_decl ds then [] else [VReal 0%R]).
Proof.
  intros Hx Hd; unfold tangent_inputs; rewrite Hx; f_equal; [apply map_map |].
  f_equal; rewrite Hd; clear; induction AL as [| p AL IH]; simpl; [reflexivity |].
  rewrite IH; reflexivity.
Qed.

Lemma index_of_written_unique ds j d k :
  nth_error ds j = Some d -> written_decl d = true -> length (filter written_decl ds) = 1%nat ->
  index_of_written ds k = Some (k + j)%nat.
Proof.
  revert j k; induction ds as [| d0 ds IH]; intros j k Hj Hw H1; [destruct j; discriminate |].
  destruct j as [| j]; simpl in Hj, H1 |- *.
  - injection Hj as ->; rewrite Hw; f_equal; lia.
  - destruct (written_decl d0) eqn:E0.
    + simpl in H1; injection H1 as H1.
      assert (Hin : In d (filter written_decl ds)) by (apply filter_In; split; [apply nth_error_In with j; exact Hj | exact Hw]).
      destruct (filter written_decl ds); [destruct Hin | discriminate].
    + rewrite (IH j (S k) Hj Hw H1); f_equal; lia.
Qed.

Lemma dot_param_position (AL : list pv) j p :
  Forall (fun p => varg (pw p) <> None) AL -> nth_error AL j = Some p -> has_dot (fst (arg_entry p)) = true ->
  exists pw0 t0, nth_error (concat (map (tangent_dot W) (map arg_entry AL)))
                   (length (filter has_dot (firstn j (map (fun q => fst (arg_entry q)) AL)))) =
                 Some (DParam pw0 t0 (DotOf (stored p))).
Proof.
  intros HAL; revert j; induction HAL as [| q AL Hg HAL IH]; intros j Hj Hd; [destruct j; discriminate |].
  destruct j as [| j]; simpl in Hj |- *.
  - injection Hj as ->; rewrite tangent_dot_entry by exact Hg; rewrite Hd; simpl.
    unfold arg_entry in *; destruct (varg (pw p)) as [[nm r] |]; [| contradiction].
    destruct (vty (pw p)), r; simpl in Hd |- *; try discriminate; eauto.
  - rewrite tangent_dot_entry by exact Hg.
    destruct (has_dot (fst (arg_entry q))) eqn:Eq; simpl; [| apply IH; auto].
    destruct (IH j Hj Hd) as [pw0 [t0 H]]; eauto.
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
  rewrite Nat.add_0_l in Htr, Hwfd.
  set (n := length xs) in *.
  set (tr := annotate_definition_t false 0 (afdef (normalize f) avar)) in *.
  destruct (tangent_open dP [] 0 xs L res bP (afdef (normalize f) (tvar W)) tr (tangent_body W)
              (Hnp pv (tvar W)) Ho) as [resT [bT [HrT [HbT Hopen]]]].
  rewrite Nat.add_0_l in Hopen; fold n in Hopen.
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
  assert (Huniq : ids_unique L).
  { intros p q Hp Hq E; destruct (Hargs' p Hp) as [i [nm [t [r [x0 [-> [Hx [Hd _]]]]]]]].
    destruct (Hargs' q Hq) as [i' [nm' [t' [r' [x0' [-> [Hx' [Hd' _]]]]]]]]; simpl in E; subst i'.
    rewrite Hx in Hx'; injection Hx' as <-; rewrite Hd in Hd'; injection Hd' as <- <- <-; reflexivity. }
  assert (Hnum : forall p, In p L -> (pn p < n)%nat)
    by (intros p Hp; destruct (Hargs' p Hp) as [? [? [? [? [? [-> [_ [_ Hi]]]]]]]]; exact Hi).
  assert (Hdot : forall p, In p L -> tdot (pt p) = true -> has_dot (fst (arg_entry p)) = true).
  { intros p Hp Ht; destruct (Hargs' p Hp) as [i [nm [t [r [x0 [-> [_ [Hd _]]]]]]]].
    simpl in Ht |- *; pose proof (non_real_varied_none (decls f) nm t r Hnrv (nth_error_In _ _ Hd) Ht) as Hra.
    destruct t; simpl in Hra |- *; try contradiction; destruct r; simpl in Ht; try discriminate; reflexivity. }
  set (ext := if existsb written_decl (decls f) then [] else [(KVar (DotOf ResultVar), VReal 0%R)]).
  set (s0 := prim_entries (rev L) ++ dot_entries (rev L) ++ ext).
  assert (Hs0 : forall p, In p L ->
            store_get s0 (keyv (stored p)) = Some (primal (pd p)) /\
            (has_dot (fst (arg_entry p)) = true -> store_get s0 (keyv (DotOf (stored p))) = Some (tangent (pd p)))).
  { intros p Hp; unfold s0, keyv, stored; simpl; rewrite !store_get_app.
    split; [rewrite prim_lookup; auto; apply in_rev; rewrite rev_involutive; exact Hp |].
    intros Hd; rewrite prim_lookup_dot, dot_lookup; auto; apply in_rev; rewrite rev_involutive; exact Hp. }
  assert (Hsok : forall p, In p L -> store_ok s0 p).
  { intros p Hp; destruct (Hs0 p Hp) as [S1 S2]; split; [exact S1 | intros Ht; apply S2, Hdot; auto]. }
  (* the tangent function, opened *)
  change (open_pairs (dfbody (Tangent.tangent (annotate false (normalize f))) W) 0)
    with (open_pairs (open_arguments W (rebuild_definition (tvar W) (afdef (normalize f) (tvar W)) tr) 0
                        (map arg_entry []) (tangent_body W)) 0).
  rewrite Hopen; unfold tangent_body; rewrite open_pairs_sbind, Htr.
  set (wT := match resT with AWrites y => Some y | AReturns _ => None end).
  destruct (open_pairs (tan W wT (rebuild (tvar W) bT (annotate_body_t false Forward n bA))) n)
    as [[sb [ve de]] c'] eqn:Hob.
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
  set (pps := map (tangent_primal W) (rev (map arg_entry L)) ++ concat (map (tangent_dot W) (rev (map arg_entry L)))).
  assert (Hpps : params pps = map stored (rev L) ++
                 concat (map (fun p => if has_dot (fst (arg_entry p)) then [DotOf (stored p)] else []) (rev L))).
  { unfold pps; rewrite params_app, <- map_rev, params_primal, params_dots by exact HAL'; reflexivity. }
  assert (Hpps_ok : forall y, In y (params pps) -> below n y /\ consistent y).
  { intros y Hy; rewrite Hpps in Hy; apply in_app_or in Hy as [Hy | Hy].
    - apply in_map_iff in Hy as [p [<- Hp]]; rewrite in_rev_iff in Hp; pose proof (Hnum p Hp).
      unfold stored; simpl; split; [lia | reflexivity].
    - apply in_dots_inv in Hy as [p [Hp [-> _]]]; rewrite in_rev_iff in Hp.
      pose proof (Hnum p Hp); unfold stored; simpl; split; [lia | reflexivity]. }
  assert (Hreads : forall p, In p L -> In (stored p) (params pps) /\
                                       (tdot (pt p) = true -> In (DotOf (stored p)) (params pps))).
  { intros p Hp; rewrite Hpps; split.
    - apply in_or_app; left; apply in_map; rewrite in_rev_iff; exact Hp.
    - intros Ht; apply in_or_app; right; apply in_dots; [rewrite in_rev_iff; exact Hp |].
      apply Hdot; auto. }
  destruct (wf_result_facts _ _ _ _ Hwf) as [[EW [Hnw HtcB]] | [w [nm [role [EW [Hg [Hwr [H1w [Hraw [HtcB [Hdep Hinout]]]]]]]]]]].
  - (* the function returns a real *)
    subst resW; destruct res as [tR | yP]; simpl in HrW; [subst tR | contradiction].
    destruct resT as [tT | yT]; simpl in HrT; [subst tT | contradiction].
    assert (Hctx : ctx_ok L n n s0 None PTop (live_anf n bW) Real).
    { constructor; auto; try (intros; discriminate); try (simpl; exact I); intros H; destruct H. }
    pose proof ((proj1 simulation) bP L n n s0 None PTop Forward bA bW bT bD Real v HbA HbW HbT HbD Hctx I HtcB Hev)
      as Hsim.
    match type of Hsim with context [open_pairs ?t n] =>
      replace (open_pairs t n) with ((sb, (ve, de)), c') in Hsim by (rewrite <- Hob; reflexivity) end.
    destruct Hsim as [Hcc [Hht [_ [Hrv1 [Hrv2 [s1 [Hrun1 [Hfr1 [Hve Hde]]]]]]]]].
    destruct v as [dv | | | |]; try contradiction.
    (* the scoping discipline *)
    set (rps := [DParam ByRef Real (DotOf ResultVar)] : list (dparam W)).
    set (sc := params (pps ++ rps)).
    assert (Hsc_ok : forall y, In y sc -> below n y /\ consistent y).
    { intros y Hy; unfold sc in Hy; rewrite params_app in Hy; apply in_app_or in Hy as [Hy | [<- | []]];
        [exact (Hpps_ok y Hy) | simpl; auto]. }
    assert (Hscope : scope_ok L n None PTop (live_anf n bW) sc sc).
    { split; [apply Forall_forall; exact Hsc_ok | split; [apply incl_refl | split; [| intros o E; discriminate]]].
      intros p Hp _; destruct (Hreads p Hp) as [R1 R2]; unfold sc; rewrite params_app.
      split; [apply in_or_app; left; exact R1 | intros Hd; apply in_or_app; left; exact (R2 Hd)]. }
    pose proof ((proj1 scoping) bP L n n None PTop Forward bA bW bT Real sc sc HbA HbW HbT
                  (ctx_sctx _ _ _ _ _ _ _ _ Hctx) Hscope I HtcB) as Hgood.
    match type of Hgood with context [open_pairs ?t n] =>
      replace (open_pairs t n) with ((sb, (ve, de)), c') in Hgood by (rewrite <- Hob; reflexivity) end.
    destruct Hgood as [_ [Hnt Hgk]].
    simpl.
    set (tail := [DAssign (DVar (DotOf ResultVar)) de; DReturn ve] : list (dstmt W)).
    (* the run *)
    set (s2 := store_set s1 (keyv (DotOf ResultVar)) (VReal (dsnd dv))).
    set (s3 := store_set s2 Returned (VReal (dfst dv))).
    assert (Hve2 : xev s2 ve = Some (VReal (dfst dv))).
    { unfold s2; rewrite xev_set_other; [exact Hve |].
      intros y Hy E; destruct (Hrv1 y Hy) as [[p [_ [_ [-> | ->]]]] | [Hb Hcy]];
        try (unfold keyv, stored in E; simpl in E; discriminate).
      apply keyv_inj in E; [subst y; apply Hb; exact I | exact Hcy | exact I]. }
    assert (Hrun : run (sb ++ tail) s0 = Some s3).
    { rewrite run_app, Hrun1; unfold tail; rewrite run_assign_var with (v := VReal (dsnd dv)) by exact Hde.
      fold s2; unfold run, xev in *; simpl; rewrite Hve2; reflexivity. }
    assert (Hin : tangent_inputs (decls f) x dx =
                  map (fun p => primal (pd p)) (rev L) ++ concat (map dot_in (rev L)) ++ [VReal 0%R]).
    { rewrite (inputs_eq (decls f) x dx (rev L)); [rewrite Hnw; reflexivity | fold xs; exact Hxs | exact Hds]. }
    assert (Hlenp : length (map (out_dparam nat) (pps ++ rps)) = length (tangent_inputs (decls f) x dx)).
    { assert (Hcl : length (concat (map (tangent_dot W) (map arg_entry (rev L)))) =
                    length (concat (map dot_in (rev L)))).
      { clear - HAL'; induction HAL' as [| p AL Hg HAL IH]; simpl; auto.
        rewrite !length_app, IH, tangent_dot_entry by exact Hg; unfold dot_in;
          destruct (has_dot (fst (arg_entry p))); reflexivity. }
      rewrite Hin, length_map; unfold pps, rps; rewrite <- map_rev, !length_app, !length_map, Hcl; simpl; lia. }
    assert (Hs0eq : map (fun '(DParam _ _ x, a) => (KVar x, a))
                      (combine (map (out_dparam nat) (pps ++ rps)) (tangent_inputs (decls f) x dx)) = s0).
    { rewrite Hin; unfold pps; rewrite <- map_rev, <- app_assoc.
      rewrite (initial_store (rev L) rps [VReal 0%R] HAL eq_refl).
      unfold s0, ext; rewrite Hnw; reflexivity. }
    (* every parameter has a final value *)
    assert (Hfin : forall pw t y, In (DParam pw t y) (map (out_dparam nat) (pps ++ rps)) ->
                   exists w, store_get s3 (KVar y) = Some w).
    { intros pp0 t0 y Hy; apply in_map_iff in Hy as [[pp1 t1 y'] [E Hy']]; injection E as E1 E2 E3; subst.
      assert (Hy2 : In y' sc) by (unfold sc, params; apply in_map_iff; eexists; split; [| exact Hy']; reflexivity).
      unfold s3, s2; rewrite store_get_set_other by discriminate.
      unfold sc in Hy2; rewrite params_app in Hy2; apply in_app_or in Hy2 as [Hy2 | [<- | []]].
      - assert (Hne : y' <> DotOf ResultVar).
        { intros ->; rewrite Hpps in Hy2; apply in_app_or in Hy2 as [Hy2 | Hy2];
            [apply in_map_iff in Hy2 as [? [E _]]; discriminate
            | apply in_dots_inv in Hy2 as [? [_ [E _]]]; discriminate]. }
        rewrite store_get_set_other.
        2: { intros E; apply keyv_inj in E; [apply Hne; symmetry; exact E | exact I | exact (proj2 (Hpps_ok _ Hy2))]. }
        change (KVar (out_dvar nat y')) with (keyv y'); rewrite (Hfr1 y'); try apply Hpps_ok; auto;
          [| intros m E; discriminate].
        rewrite Hpps in Hy2; apply in_app_or in Hy2 as [Hy2 | Hy2].
        + apply in_map_iff in Hy2 as [p [<- Hp]]; rewrite in_rev_iff in Hp; destruct (Hs0 p Hp) as [S1 _]; eauto.
        + apply in_dots_inv in Hy2 as [p [Hp [-> Hd]]]; rewrite in_rev_iff in Hp.
          destruct (Hs0 p Hp) as [_ S2]; eauto.
      - rewrite store_get_set_same; eauto. }
    destruct (finals_some s3 _ Hfin) as [fs [Hfs [Hlfs Hnth]]].
    exists DReturnsReal, (pps ++ rps), (sb ++ tail), c', (fs, [VReal (dfst dv)]).
    split; [unfold pps, rps; rewrite <- app_assoc; reflexivity |].
    split; [apply Forall_forall; intros y Hy; exact (proj2 (Hsc_ok y Hy)) |].
    split; [apply Hgk; intros sc' wr' I1 I2 _ _ [Q1 Q2]; unfold tail;
            apply GoodAssign; [apply I2; unfold sc; rewrite params_app; apply in_or_app; right; left; reflexivity
                              | exact Q2 |];
            apply GoodReturn; [exact Q1 | constructor] |].
    split; [rewrite existsb_app; unfold notape in Hnt; rewrite Hnt; reflexivity |].
    split.
    + rewrite Hlenp, Nat.eqb_refl; simpl negb; cbv iota.
      rewrite Hs0eq; change (exec_stmts reals (map (out_dstmt nat) (sb ++ tail)) s0) with (run (sb ++ tail) s0).
      rewrite Hrun; simpl; rewrite Hfs; unfold s3; rewrite store_get_set_same; reflexivity.
    + simpl; rewrite index_of_written_none by exact Hnw.
      assert (Hlast : nth_error (map (out_dparam nat) (pps ++ rps)) (length fs - 1) =
                      Some (DParam ByRef Real (DotOf ResultVar))).
      { rewrite Hlfs, map_app, length_app, length_map; simpl.
        rewrite nth_error_app2 by (rewrite length_map; lia).
        rewrite length_map; replace (length pps + 1 - 1 - length pps)%nat with 0%nat by lia; reflexivity. }
      rewrite (nth_error_last fs (VInt 0) (VReal (dsnd dv))); [reflexivity |].
      rewrite (Hnth _ _ _ _ Hlast); unfold s3; rewrite store_get_set_other by discriminate.
      unfold s2; rewrite store_get_set_same; reflexivity.
  - (* the function writes an argument *)
    subst resW; destruct res as [tR | yP]; simpl in HrW; [contradiction |].
    destruct yP as [y | | ]; simpl in HrW; try contradiction.
    apply in_gW in HrW as [HyL Ew]; subst w.
    destruct resT as [tT | yT]; simpl in HrT; [contradiction |].
    destruct yT as [yt | | ]; simpl in HrT; try contradiction.
    apply in_gT in HrT as [_ ->].
    destruct (Hargs' y HyL) as [j [nm' [t [r [x0 [Ey [Hxj [Hdj Hj]]]]]]]].
    assert (Hvy : vty (pw y) = t) by (rewrite Ey; reflexivity).
    assert (Hpy : pn y = j) by (rewrite Ey; reflexivity).
    rewrite Ey in Hg; simpl in Hg; injection Hg as <- <-.
    assert (Hdecl_y : fst (arg_entry y) = Decl nm' t r) by (rewrite Ey; reflexivity).
    assert (Hnw : existsb written_decl (decls f) = true).
    { apply existsb_exists; exists (Decl nm' t r); split; [apply nth_error_In with j; exact Hdj | exact Hwr]. }
    assert (Hdy : has_dot (fst (arg_entry y)) = true).
    { rewrite Hdecl_y; rewrite Hvy in Hraw; destruct t; try destruct Hraw; destruct r; simpl in Hwr |- *;
        try discriminate; reflexivity. }
    assert (Hpn_inj : forall p q, In p L -> In q L -> pn p = pn q -> p = q).
    { intros p q Hp Hq E; destruct (Hargs' p Hp) as [i [? [? [? [? [-> [Hx [Hd _]]]]]]]].
      destruct (Hargs' q Hq) as [i' [? [? [? [? [-> [Hx' [Hd' _]]]]]]]]; simpl in E; subst i'.
      rewrite Hx in Hx'; injection Hx' as <-; rewrite Hd in Hd'; injection Hd' as <- <- <-; reflexivity. }
    rewrite Hvy in HtcB.
    assert (Hown_cases : owner (Some (AVar y)) PTop = match t with Array _ => Some y | _ => None end)
      by (simpl; rewrite Hvy; reflexivity).
    assert (Hctx : ctx_ok L n n s0 (Some (AVar y)) PTop (live_anf n bW) t).
    { constructor.
      - exact Hstat.
      - exact Huniq.
      - exact Hnum.
      - intros p Hp _; exact (Hsok p Hp).
      - intros a0 E; injection E as <-; exists y; split; [reflexivity | split; [exact HyL | rewrite Ey; discriminate]].
      - exact I.
      - intros o p Hw0 Hp E; rewrite Hown_cases in Hw0; destruct t; try discriminate; injection Hw0 as <-.
        left; exact (Hpn_inj p y Hp HyL E).
      - intros o p Hw0 Hp Lp E; rewrite Hown_cases in Hw0; destruct t; try discriminate; injection Hw0 as <-.
        rewrite (Hpn_inj p y Hp HyL E); split; [exact (proj1 (Hs0 y HyL)) | exact (proj2 (Hs0 y HyL) Hdy)].
      - intros p o Hp Lp Ha Hg' Hw0; rewrite Hown_cases in Hw0; destruct t; try discriminate; injection Hw0 as <-.
        destruct Hg' as [Hg' | Hg'];
          [destruct (Hargs' p Hp) as [? [? [? [? [? [-> _]]]]]]; discriminate | injection Hg' as ->; reflexivity].
      - intros Ha; rewrite Hown_cases; destruct t; try destruct Ha; discriminate.
      - intros y' _ E Ha; injection E as <-; split; [symmetry; exact Hvy | split].
        + intros Ly; destruct r; simpl in Hwr; try discriminate.
          * unfold live_anf in Ly; rewrite Hdep in Ly by reflexivity; discriminate.
          * rewrite Ey; reflexivity.
        + destruct (static_in _ _ _ Hstat HyL) as [_ [_ [_ [_ [_ [_ [_ [_ [Ht _]]]]]]]]].
          destruct (Hs0 y HyL) as [S1 S2]; specialize (S2 Hdy).
          rewrite Hvy in Ha, Ht |- *; destruct t as [| | | z]; try destruct Ha.
          destruct (pd y) as [| | | l |] eqn:Ep; try contradiction.
          exists (map dfst l), (map dsnd l); rewrite !length_map; auto. }
    assert (Hra' : real_or_array t) by (rewrite <- Hvy; exact Hraw).
    pose proof ((proj1 simulation) bP L n n s0 (Some (AVar y)) PTop Forward bA bW bT bD t v HbA HbW HbT HbD
                  Hctx Hra' HtcB Hev) as Hsim.
    match type of Hsim with context [open_pairs ?t0 n] =>
      replace (open_pairs t0 n) with ((sb, (ve, de)), c') in Hsim by (rewrite <- Hob; reflexivity) end.
    destruct Hsim as [Hcc [Hht [_ [Hrv1 [Hrv2 [s1 [Hrun1 [Hfr1 Hres]]]]]]]].
    (* the scoping discipline *)
    set (sc := params pps).
    assert (Hscope : scope_ok L n (Some (AVar y)) PTop (live_anf n bW) sc sc).
    { split; [apply Forall_forall; exact Hpps_ok | split; [apply incl_refl | split]].
      - intros p Hp _; exact (Hreads p Hp).
      - intros o Hw0; rewrite Hown_cases in Hw0; destruct t; try discriminate; injection Hw0 as <-.
        destruct (Hreads y HyL) as [R1 R2]; split; [exact R1 |].
        unfold sc; rewrite Hpps; apply in_or_app; right; apply in_dots; [rewrite in_rev_iff; exact HyL | exact Hdy]. }
    pose proof ((proj1 scoping) bP L n n (Some (AVar y)) PTop Forward bA bW bT t sc sc HbA HbW HbT
                  (ctx_sctx _ _ _ _ _ _ _ _ Hctx) Hscope Hra' HtcB) as Hgood.
    match type of Hgood with context [open_pairs ?t0 n] =>
      replace (open_pairs t0 n) with ((sb, (ve, de)), c') in Hgood by (rewrite <- Hob; reflexivity) end.
    destruct Hgood as [_ [Hnt Hgk]].
    (* the arguments of the tangent function *)
    assert (Hin : tangent_inputs (decls f) x dx =
                  map (fun p => primal (pd p)) (rev L) ++ concat (map dot_in (rev L)) ++ []).
    { rewrite (inputs_eq (decls f) x dx (rev L)); [rewrite Hnw; reflexivity | fold xs; exact Hxs | exact Hds]. }
    assert (Hlenp : length (map (out_dparam nat) (pps ++ [])) = length (tangent_inputs (decls f) x dx)).
    { assert (Hcl : length (concat (map (tangent_dot W) (map arg_entry (rev L)))) =
                    length (concat (map dot_in (rev L)))).
      { clear - HAL'; induction HAL' as [| p AL Hg HAL IH]; simpl; auto.
        rewrite !length_app, IH, tangent_dot_entry by exact Hg; unfold dot_in;
          destruct (has_dot (fst (arg_entry p))); reflexivity. }
      rewrite Hin, length_map; unfold pps; rewrite <- map_rev, !length_app, !length_map, Hcl; simpl; lia. }
    assert (Hs0eq : map (fun '(DParam _ _ x, a) => (KVar x, a))
                      (combine (map (out_dparam nat) (pps ++ [])) (tangent_inputs (decls f) x dx)) = s0).
    { rewrite Hin; unfold pps; rewrite <- map_rev, <- app_assoc.
      rewrite (initial_store (rev L) [] [] HAL eq_refl).
      unfold s0, ext; rewrite Hnw; reflexivity. }
    assert (Hidx : index_of_written (decls f) 0 = Some j)
      by exact (index_of_written_unique (decls f) j _ 0 Hdj Hwr H1w).
    assert (HLn : length L = n) by (change n with (length xs); rewrite Hxs, length_map, length_rev; reflexivity).
    assert (Hlds : length (decls f) = n).
    { rewrite Hds, length_map, length_rev; change n with (length xs); rewrite Hxs, length_map, length_rev; reflexivity. }
    assert (Hprim_j : nth_error (map (out_dparam nat) pps) j = Some (out_dparam nat (tangent_primal W (arg_entry y)))).
    { unfold pps; rewrite map_app, nth_error_app1 by (rewrite !length_map, length_rev, length_map; lia).
      rewrite <- map_rev, !nth_error_map.
      assert (Hry : nth_error (rev L) j = Some y).
      { destruct (nth_error (rev L) j) as [q |] eqn:Eq.
        - destruct (Hargs j q Eq) as [? [? [? [? [-> Hx']]]]]; rewrite Hxj in Hx'; injection Hx' as <-.
          rewrite Hds, nth_error_map, Eq in Hdj; simpl in Hdj; injection Hdj as -> -> ->; rewrite Ey; reflexivity.
        - apply nth_error_None in Eq; rewrite length_rev in Eq; lia. }
      rewrite Hry; reflexivity. }
    assert (Hdot_j : exists pw0 t0, nth_error (map (out_dparam nat) pps)
                       (length (decls f) + length (filter has_dot (firstn j (decls f)))) =
                     Some (out_dparam nat (DParam pw0 t0 (DotOf (stored y))))).
    { assert (Hry : nth_error (rev L) j = Some y).
      { destruct (nth_error (rev L) j) as [q |] eqn:Eq.
        - destruct (Hargs j q Eq) as [? [? [? [? [-> Hx']]]]]; rewrite Hxj in Hx'; injection Hx' as <-.
          rewrite Hds, nth_error_map, Eq in Hdj; simpl in Hdj; injection Hdj as -> -> ->; rewrite Ey; reflexivity.
        - apply nth_error_None in Eq; rewrite length_rev in Eq; lia. }
      destruct (dot_param_position (rev L) j y HAL' Hry Hdy) as [pw0 [t0 Hpos]].
      exists pw0, t0; unfold pps; rewrite map_app, nth_error_app2 by (rewrite !length_map, length_rev, length_map; lia).
      rewrite !length_map, length_rev, length_map, HLn, Hlds.
      replace (n + length (filter has_dot (firstn j (decls f))) - n)%nat
        with (length (filter has_dot (firstn j (decls f)))) by lia.
      rewrite <- map_rev, nth_error_map, Hds, Hpos; reflexivity. }
    (* the parameters keep a value *)
    assert (Hs0p : forall y0, In y0 (params pps) -> exists w, store_get s0 (keyv y0) = Some w).
    { intros y0 Hy0; rewrite Hpps in Hy0; apply in_app_or in Hy0 as [Hy0 | Hy0].
      - apply in_map_iff in Hy0 as [p [<- Hp]]; rewrite in_rev_iff in Hp; destruct (Hs0 p Hp) as [S1 _]; eauto.
      - apply in_dots_inv in Hy0 as [p [Hp [-> Hd]]]; rewrite in_rev_iff in Hp; destruct (Hs0 p Hp) as [_ S2]; eauto. }
    assert (Hs1p : forall y0, In y0 (params pps) -> exists w, store_get s1 (keyv y0) = Some w).
    { intros y0 Hy0.
      destruct (inplace (Some (AVar y)) PTop) as [m |] eqn:Ein.
      - destruct (dvar_eq_dec y0 m) as [-> | Hn1]; [| destruct (dvar_eq_dec y0 (DotOf m)) as [-> | Hn2]].
        + unfold inplace in Ein; rewrite Hown_cases in Ein; destruct t as [| | | z]; try discriminate.
          injection Ein as <-; destruct Hres as [o [Eo [R1 R2]]]; injection Eo as <-; eauto.
        + unfold inplace in Ein; rewrite Hown_cases in Ein; destruct t as [| | | z]; try discriminate.
          injection Ein as <-; destruct Hres as [o [Eo [R1 R2]]]; injection Eo as <-; eauto.
        + rewrite (Hfr1 y0); [exact (Hs0p y0 Hy0) | exact (proj1 (Hpps_ok y0 Hy0)) | exact (proj2 (Hpps_ok y0 Hy0)) |].
          intros m' E; injection E as <-; auto.
      - rewrite (Hfr1 y0); [exact (Hs0p y0 Hy0) | exact (proj1 (Hpps_ok y0 Hy0)) | exact (proj2 (Hpps_ok y0 Hy0)) |].
        intros m' E; discriminate. }
    assert (Hty_y : tty (pt y) = t) by (rewrite Ey; reflexivity).
    assert (Hst_y : tstored (pt y) = stored y) by (rewrite Ey; reflexivity).
    simpl tangent_result; rewrite Hty_y, Hst_y.
    destruct t as [| | | z]; try destruct Hra'.
    + (* a written real *)
      destruct Hres as [Hve Hde]; destruct v as [dv | | | |]; try contradiction.
      set (tail := [DAssign (DVar (stored y)) ve; DAssign (DVar (DotOf (stored y))) de] : list (dstmt W)).
      set (s2 := store_set s1 (keyv (stored y)) (VReal (dfst dv))).
      set (s3 := store_set s2 (keyv (DotOf (stored y))) (VReal (dsnd dv))).
      assert (Hde2 : xev s2 de = Some (VReal (dsnd dv))).
      { unfold s2; rewrite xev_set_other; [exact Hde |].
        intros y0 Hy0 E; destruct (Hrv2 y0 Hy0) as [[p [_ [_ ->]]] | [Hb Hcy]];
          [unfold keyv, stored in E; simpl in E; discriminate |].
        apply keyv_inj in E; [subst y0; apply Hb; simpl; rewrite Hpy; exact Hj | exact Hcy | reflexivity]. }
      assert (Hrun : run (sb ++ tail) s0 = Some s3).
      { rewrite run_app, Hrun1; unfold tail; rewrite run_assign_var with (v := VReal (dfst dv)) by exact Hve.
        fold s2; rewrite run_assign_var with (v := VReal (dsnd dv)) by exact Hde2; reflexivity. }
      assert (Hfin : forall pw0 t0 y0, In (DParam pw0 t0 y0) (map (out_dparam nat) (pps ++ [])) ->
                     exists w, store_get s3 (KVar y0) = Some w).
      { intros pp0 t0 y0 Hy; rewrite app_nil_r in Hy; apply in_map_iff in Hy as [[pp1 t1 y'] [E Hy']].
        injection E as E1 E2 E3; subst pp0 t0 y0.
        assert (Hy2 : In y' (params pps)) by (unfold params; apply in_map_iff; eexists; split; [| exact Hy']; reflexivity).
        change (KVar (out_dvar nat y')) with (keyv y'); unfold s3, s2; rewrite !store_get_set.
        destruct (key_eqb (keyv (DotOf (stored y))) (keyv y')); [eauto |].
        destruct (key_eqb (keyv (stored y)) (keyv y')); [eauto |].
        exact (Hs1p y' Hy2). }
      destruct (finals_some s3 _ Hfin) as [fs [Hfs [Hlfs Hnth]]].
      exists DVoid, (pps ++ []), (sb ++ tail), c', (fs, []).
      split; [unfold pps; rewrite <- app_assoc; reflexivity |].
      split; [apply Forall_forall; intros y0 Hy0; rewrite app_nil_r in Hy0; exact (proj2 (Hpps_ok y0 Hy0)) |].
      split; [rewrite app_nil_r; apply Hgk; intros sc' wr' I1 I2 _ _ [Q1 Q2]; unfold tail;
              destruct (Hreads y HyL) as [R1 _];
              apply GoodAssign; [apply I2, R1 | exact Q1 |];
              apply GoodAssign; [apply I2; unfold sc; rewrite Hpps; apply in_or_app; right;
                                 apply in_dots; [rewrite in_rev_iff; exact HyL | exact Hdy] | exact Q2 | constructor] |].
      split; [rewrite existsb_app; unfold notape in Hnt; rewrite Hnt; reflexivity |].
      split.
      * cbn [exec_scoped]; rewrite Hlenp, Nat.eqb_refl; simpl negb; cbv iota.
        rewrite Hs0eq; change (exec_stmts reals (map (out_dstmt nat) (sb ++ tail)) s0) with (run (sb ++ tail) s0).
        rewrite Hrun; simpl; rewrite Hfs; reflexivity.
      * simpl; rewrite Hidx.
        destruct Hdot_j as [pw0 [t0 Hdj']].
        rewrite app_nil_r in Hnth.
        assert (Hpj : nth_error (map (out_dparam nat) pps) j = Some (DParam ByRef Real (DBound (pn y)))).
        { rewrite Hprim_j, Ey; destruct r; simpl in Hwr; try discriminate; reflexivity. }
        assert (Hdj2 : nth_error (map (out_dparam nat) pps) (length (decls f) + length (filter has_dot (firstn j (decls f))))
                       = Some (DParam pw0 t0 (DotOf (DBound (pn y))))) by (rewrite Hdj'; reflexivity).
        rewrite (Hnth _ _ _ _ Hpj), (Hnth _ _ _ _ Hdj2).
        change (KVar (DotOf (DBound (pn y)))) with (keyv (DotOf (stored y))).
        change (KVar (DBound (pn y))) with (keyv (stored y)).
        unfold s3, s2; rewrite store_get_set_same, store_get_set_other, store_get_set_same;
          [reflexivity | intros E; inversion E].
    + (* a written array, updated in place *)
      destruct Hres as [o [Eo [R1 R2]]].
      unfold inplace in Eo; rewrite Hown_cases in Eo; injection Eo as <-.
      assert (Hrun : run (sb ++ []) s0 = Some s1) by (rewrite app_nil_r; exact Hrun1).
      assert (Hfin : forall pw0 t0 y0, In (DParam pw0 t0 y0) (map (out_dparam nat) (pps ++ [])) ->
                     exists w, store_get s1 (KVar y0) = Some w).
      { intros pp0 t0 y0 Hy; rewrite app_nil_r in Hy; apply in_map_iff in Hy as [[pp1 t1 y'] [E Hy']].
        injection E as E1 E2 E3; subst pp0 t0 y0.
        assert (Hy2 : In y' (params pps)) by (unfold params; apply in_map_iff; eexists; split; [| exact Hy']; reflexivity).
        exact (Hs1p y' Hy2). }
      destruct (finals_some s1 _ Hfin) as [fs [Hfs [Hlfs Hnth]]].
      exists DVoid, (pps ++ []), (sb ++ []), c', (fs, []).
      split; [unfold pps; rewrite <- app_assoc; reflexivity |].
      split; [apply Forall_forall; intros y0 Hy0; rewrite app_nil_r in Hy0; exact (proj2 (Hpps_ok y0 Hy0)) |].
      split; [rewrite app_nil_r; apply Hgk; intros; constructor |].
      split; [rewrite app_nil_r; exact Hnt |].
      split.
      * cbn [exec_scoped]; rewrite Hlenp, Nat.eqb_refl; simpl negb; cbv iota.
        rewrite Hs0eq; change (exec_stmts reals (map (out_dstmt nat) (sb ++ [])) s0) with (run (sb ++ []) s0).
        rewrite Hrun; simpl; rewrite Hfs; reflexivity.
      * simpl; rewrite Hidx.
        destruct Hdot_j as [pw0 [t0 Hdj']].
        rewrite app_nil_r in Hnth.
        assert (Hpj : nth_error (map (out_dparam nat) pps) j = Some (DParam ByRef (Array z) (DBound (pn y)))).
        { rewrite Hprim_j, Ey; destruct r; simpl in Hwr; try discriminate; reflexivity. }
        assert (Hdj2 : nth_error (map (out_dparam nat) pps) (length (decls f) + length (filter has_dot (firstn j (decls f))))
                       = Some (DParam pw0 t0 (DotOf (DBound (pn y))))) by (rewrite Hdj'; reflexivity).
        rewrite (Hnth _ _ _ _ Hpj), (Hnth _ _ _ _ Hdj2).
        change (KVar (DotOf (DBound (pn y)))) with (keyv (DotOf (stored y))).
        change (KVar (DBound (pn y))) with (keyv (stored y)).
        rewrite R1, R2; reflexivity.
Qed.
