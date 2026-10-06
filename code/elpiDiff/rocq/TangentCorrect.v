(* TangentCorrect.v — theorem 1: the tangent program computes the dual
   numbers.

   Running the program `tangent (annotate false (normalize f))` over the
   reals, from the primal arguments and their tangents, computes what the
   evaluation of the source over the dual numbers computes: the value and the
   tangent of the result. The reals are equal up to ring identities (the
   tangent program and dual_op1/dual_op2 associate differently, and the
   tangent program omits the terms of the operands that are not varied).

   The proof is a simulation, by induction on the program of L1. A program of
   L1 is instantiated by each pass at its own type of variables: annotate at
   avar, well_formed at vinfo, tangent at tvar, the evaluator at the dual
   numbers. We take one more instance, at `pv`, the record of the four, and
   relate it to the four others (AnfEquiv.v); a variable of the simulation is
   a pv: what the analyses say of it, its type, where the tangent program
   stores it, and its dual value. The invariant relates the store of the
   tangent program to the dual values of the variables in scope, for the
   variables the rest of the program reads (`live`): the value in the stored
   variable, the tangent in its dot when the variable has one; a variable
   that is not varied has a tangent 0 (the soundness of the activity
   analysis, proved along).

   The simulation proves at the same time that the generated statements
   follow the discipline `good` of Scoping.v, which simplify relies on. *)

From Stdlib Require Import String ZArith List Bool Reals QArith Qreals Lia Lra DecimalString.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Operations
  Normalize WellFormed Atoms Activity Tbr Annotate Transform Tangent Simplify Scoping
  AnfEquiv Correctness.

Import ListNotations.
Open Scope R_scope.

(* ---------------------------------------------------------------------------
   The store of the tangent program. Its variables are opened with pairs
   (open_pairs, Scoping.v) and executed after out_dvar. *)

Definition keyv (v : dvar W) : key := KVar (out_dvar nat v).
Definition xev (s : store R) (e : dexpr W) : option (val R) := xeval reals s (out_dexpr nat e).
Definition run (ss : list (dstmt W)) (s : store R) : option (store R) :=
  exec_stmts reals (map (out_dstmt nat) ss) s.

Lemma dvar_eqb_eq (a b : dvar nat) : dvar_eqb a b = true <-> a = b.
Proof.
  revert b; induction a as [x | a IH | a IH | a IH |]; intros [y | b | b | b |]; simpl;
    try (split; [discriminate | intros E; discriminate E]).
  - rewrite Nat.eqb_eq; split; [intros ->; reflexivity | intros E; injection E; auto].
  - rewrite IH; split; [intros ->; reflexivity | intros E; injection E; auto].
  - rewrite IH; split; [intros ->; reflexivity | intros E; injection E; auto].
  - rewrite IH; split; [intros ->; reflexivity | intros E; injection E; auto].
  - split; reflexivity.
Qed.

Lemma key_eqb_eq (a b : key) : key_eqb a b = true <-> a = b.
Proof.
  destruct a as [x |], b as [y |]; simpl; try (split; [discriminate | intros E; discriminate E]).
  - rewrite dvar_eqb_eq; split; [intros ->; reflexivity | intros E; injection E; auto].
  - split; reflexivity.
Qed.

Lemma key_eqb_refl (a : key) : key_eqb a a = true.
Proof. apply key_eqb_eq; reflexivity. Qed.

(* Reading a store after a write. *)
Lemma store_get_set (s : store R) k v k' :
  store_get (store_set s k v) k' = if key_eqb k k' then Some v else store_get s k'.
Proof.
  induction s as [| [k0 w] s IH]; simpl; [reflexivity |].
  destruct (key_eqb k0 k) eqn:E0.
  - apply key_eqb_eq in E0; subst k0; simpl; destruct (key_eqb k k'); reflexivity.
  - simpl; destruct (key_eqb k0 k') eqn:E1; rewrite ?IH.
    + apply key_eqb_eq in E1; subst k'; destruct (key_eqb k k0) eqn:E2; [| reflexivity].
      apply key_eqb_eq in E2; subst; rewrite key_eqb_refl in E0; discriminate.
    + reflexivity.
Qed.

(* Executing a block in two parts. *)
Lemma exec_stmts_app (l1 l2 : list (dstmt nat)) s :
  exec_stmts reals (l1 ++ l2) s = match exec_stmts reals l1 s with Some s1 => exec_stmts reals l2 s1 | None => None end.
Proof.
  revert s; induction l1 as [| st l1 IH]; intros s; simpl; [reflexivity |].
  destruct (exec reals st s); [apply IH | reflexivity].
Qed.

Lemma run_app ss1 ss2 s :
  run (ss1 ++ ss2) s = match run ss1 s with Some s1 => run ss2 s1 | None => None end.
Proof. unfold run; rewrite map_app; apply exec_stmts_app. Qed.

Lemma run_cons st ss s :
  run (st :: ss) s = match exec reals (out_dstmt nat st) s with Some s1 => run ss s1 | None => None end.
Proof. reflexivity. Qed.

Lemma run_nil s : run [] s = Some s.
Proof. reflexivity. Qed.

(* The literals the tangent programs use. *)
Lemma lit_0 : real_lit "0" = Some 0.
Proof. unfold real_lit; vm_compute (read_literal _); unfold Q2R; simpl; f_equal; ring. Qed.

Lemma lit_1 : real_lit "1" = Some 1.
Proof. unfold real_lit; vm_compute (read_literal _); unfold Q2R; simpl; f_equal; rewrite Rinv_1; ring. Qed.

Lemma lit_m1 : real_lit "-1" = Some (-1).
Proof. unfold real_lit; vm_compute (read_literal _); unfold Q2R; simpl; f_equal; rewrite Rinv_1; ring. Qed.

(* ---------------------------------------------------------------------------
   Dual values: their primal part and their tangent, as values of the reals. *)

Definition dfst (d : dual R) : R := let 'Dual x _ := d in x.
Definition dsnd (d : dual R) : R := let 'Dual _ y := d in y.

Definition primal (v : val (dual R)) : val R :=
  match v with
  | VReal d => VReal (dfst d)
  | VInt k => VInt k
  | VBool b => VBool b
  | VArray l => VArray (map dfst l)
  | VTape l => VTape (map dfst l)
  end.

Definition tangent (v : val (dual R)) : val R :=
  match v with
  | VReal d => VReal (dsnd d)
  | VInt k => VInt k
  | VBool b => VBool b
  | VArray l => VArray (map dsnd l)
  | VTape l => VTape (map dsnd l)
  end.

(* A dual value whose tangent is zero. *)
Definition zero (v : val (dual R)) : Prop :=
  match v with
  | VReal d => dsnd d = 0
  | VArray l => Forall (fun d => dsnd d = 0) l
  | _ => True
  end.

(* A value of the type t: an array of the declared extent. *)
Definition has_type (t : ty) (v : val (dual R)) : Prop :=
  match t, v with
  | Real, VReal _ | Integer, VInt _ | Boolean, VBool _ => True
  | Array n, VArray l => length l = Z.to_nat n
  | _, _ => False
  end.

Definition real_or_array (t : ty) : Prop := match t with Real | Array _ => True | _ => False end.
Definition is_array (t : ty) : Prop := match t with Array _ => True | _ => False end.

(* ---------------------------------------------------------------------------
   The variables of the simulation: what the analyses know of a variable
   (avar), its type (vinfo), how the tangent program holds it (tvar), its
   dual value, and the number of the variable of the tangent program that
   stores it. *)

Record pv : Type := PV { pa : avar; pw : vinfo; pt : tvar W; pd : val (dual R); pn : nat }.

Definition stored (p : pv) : dvar W := DBound (pn p, pn p).

(* The contexts of the four instances, for the variables in scope. *)
Definition gA (L : list pv) := map (fun p => (p, pa p)) L.
Definition gW (L : list pv) := map (fun p => (p, pw p)) L.
Definition gT (L : list pv) := map (fun p => (p, pt p)) L.
Definition gD (L : list pv) := map (fun p => (p, pd p)) L.

Definition amap {A B : Type} (f : A -> B) (a : atom A) : atom B :=
  match a with AVar x => AVar (f x) | ANum s => ANum s | ANat k => ANat k end.

(* What holds of a variable in scope, whatever the store: the instances agree
   on its identity, its type and its activity; a varied variable is a real or
   an array, and carries a tangent; its dual value has its type, and a zero
   tangent when it is not varied (the soundness of the activity analysis). *)
Definition static_ok (k : nat) (p : pv) : Prop :=
  aid (pa p) = vid (pw p) /\ (vid (pw p) < k)%nat /\
  tstored (pt p) = stored p /\ tty (pt p) = vty (pw p) /\
  tvaried (pt p) = avaried (pa p) /\ tdot (pt p) = avaried (pa p) /\ tid (pt p) <> Some 0%nat /\
  (avaried (pa p) = true -> real_or_array (vty (pw p))) /\
  has_type (vty (pw p)) (pd p) /\ (avaried (pa p) = false -> zero (pd p)).

Definition ids_unique (L : list pv) : Prop :=
  forall p q, In p L -> In q L -> vid (pw p) = vid (pw q) -> p = q.

(* The store holds the primal value of the variable, and its tangent when the
   variable has one. *)
Definition store_ok (s : store R) (p : pv) : Prop :=
  store_get s (keyv (stored p)) = Some (primal (pd p)) /\
  (tdot (pt p) = true -> store_get s (keyv (DotOf (stored p))) = Some (tangent (pd p))).

(* Where a body sits, with the variables of an in-place loop. *)
Inductive pplace : Type :=
| PTop | PBranch | PScalar
| PArray (ix sx : pv).

Definition wplace (pp : pplace) : place :=
  match pp with
  | PTop => Top | PBranch => InBranch | PScalar => ScalarBody
  | PArray ix sx => ArrayBody (AVar (pw ix)) (AVar (pw sx))
  end.

(* The variable whose storage a body may update in place: the written array
   at the top, the state of an in-place loop in its body. *)
Definition owner (wP : option (atom pv)) (pp : pplace) : option pv :=
  match pp, wP with
  | PTop, Some (AVar y) => match vty (pw y) with Array _ => Some y | _ => None end
  | PArray _ sx, _ => Some sx
  | _, _ => None
  end.

Definition inplace (wP : option (atom pv)) (pp : pplace) : option (dvar W) :=
  option_map stored (owner wP pp).

Definition place_ok (L : list pv) (pp : pplace) : Prop :=
  match pp with
  | PArray ix sx =>
      In ix L /\ In sx L /\ vty (pw ix) = Integer /\ is_array (vty (pw sx)) /\
      avaried (pa sx) = true /\ varg (pw ix) = None /\ varg (pw sx) = None
  | _ => True
  end.

(* The store holds the value and the tangent of the variable, even when the
   variable is not varied (the tangent is then the zero of the caller). *)
Definition store_full (s : store R) (p : pv) : Prop :=
  store_get s (keyv (stored p)) = Some (primal (pd p)) /\
  store_get s (keyv (DotOf (stored p))) = Some (tangent (pd p)).

(* The storage of an array and its dot hold arrays of length len. *)
Definition arrays_len (s : store R) (n : dvar W) (len : nat) : Prop :=
  exists l1 l2, store_get s (keyv n) = Some (VArray l1) /\ length l1 = len /\
                store_get s (keyv (DotOf n)) = Some (VArray l2) /\ length l2 = len.

(* The context of a body or a value: the variables in scope L, their binders
   numbered below k and their storage below c, the store s, the written
   argument wP, the place pp, and which variables the rest of the program
   reads (live); ty is the type of the body. *)
Record ctx_ok (L : list pv) (k c : nat) (s : store R) (wP : option (atom pv)) (pp : pplace)
  (live : pv -> Prop) (ty : ty) : Prop := {
  c_static : Forall (static_ok k) L;
  c_unique : ids_unique L;
  c_num : forall p, In p L -> (pn p < c)%nat;
  c_store : forall p, In p L -> live p -> store_ok s p;
  c_written : forall a, wP = Some a ->
      exists y, a = AVar y /\ In y L /\ varg (pw y) <> None;
  c_place : place_ok L pp;
  c_owner : forall o p, owner wP pp = Some o -> In p L -> pn p = pn o -> p = o \/ ~ live p;
  c_inplace : forall o p, owner wP pp = Some o -> In p L -> live p -> pn p = pn o -> store_full s p;
  c_arrays : forall p o, In p L -> live p -> is_array (vty (pw p)) ->
      (varg (pw p) = None \/ wP = Some (AVar p)) -> owner wP pp = Some o -> pn p = pn o;
  c_ty : is_array ty -> owner wP pp <> None;
  c_top : forall y, pp = PTop -> wP = Some (AVar y) -> is_array (vty (pw y)) ->
      ty = vty (pw y) /\ (live y -> avaried (pa y) = true) /\
      arrays_len s (stored y) (match vty (pw y) with Array n => Z.to_nat n | _ => 0%nat end)
}.

(* The keys of the store a run leaves unchanged: those of the variables
   opened before c, except the storage updated in place and its dot. *)
Fixpoint below (c : nat) (v : dvar W) : Prop :=
  match v with
  | DBound (i, _) => (i < c)%nat
  | DotOf v' | BarOf v' | TapeOf v' => below c v'
  | ResultVar => True
  end.

Definition frame (c : nat) (ex : option (dvar W)) (s s' : store R) : Prop :=
  forall v, below c v -> consistent v -> (forall n, ex = Some n -> v <> n /\ v <> DotOf n) ->
  store_get s' (keyv v) = store_get s (keyv v).

(* The result of a body: a real, its value and tangent computed by the two
   expressions; an array, left in the storage updated in place. *)
Definition body_result (t : ty) (ex : option (dvar W)) (s : store R) (ve de : dexpr W)
  (v : val (dual R)) : Prop :=
  match t with
  | Array _ => exists o, ex = Some o /\ store_get s (keyv o) = Some (primal v) /\
                         store_get s (keyv (DotOf o)) = Some (tangent v)
  | _ => xev s ve = Some (primal v) /\ xev s de = Some (tangent v)
  end.


(* ---------------------------------------------------------------------------
   The operations: the tangent the generated code computes, a partial
   derivative times the tangent of the operand, is the tangent of the dual
   operation. *)

(* Unfolds the operations of the domains, but not the reading of literals. *)
Ltac unfold_ops H :=
  cbv beta iota delta [dual_op1 dual_op2 dual_partial1 dom_op1 dom_op2 dom_lit dom_cmp reals
    duals dual_lit real_op1 real_op2 partial1 partial2] in H.

Lemma xev_DOp1 s f e :
  xev s (DOp1 f e) = match xev s e with Some va => eval_op1 reals f va | None => None end.
Proof. reflexivity. Qed.

Lemma xev_DOp2 s f e1 e2 :
  xev s (DOp2 f e1 e2) =
  match xev s e1 with
  | Some va => match xev s e2 with Some vb => eval_op2 reals f va vb | None => None end
  | None => None end.
Proof. reflexivity. Qed.

Lemma xev_DReal s l : xev s (DReal l) = match real_lit l with Some x => Some (VReal x) | None => None end.
Proof. reflexivity. Qed.

Lemma tangent_op1 s f (a : atom (tvar W)) e x dx y dy p :
  xev s (spell a) = Some (VReal x) -> xev s e = Some (VReal dx) ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) -> partial1 f a = Some p ->
  xev s (DOp1 f (spell a)) = Some (VReal y) /\ xev s (scale (spell_partial p) e) = Some (VReal dy).
Proof.
  intros Ha He Hd Hp; rewrite xev_DOp1, Ha.
  destruct f as [| | | | | | k |]; unfold_ops Hd; unfold_ops Hp; try discriminate;
    try (injection Hp as <-); simpl.
  - (* Neg *) rewrite lit_m1 in Hd; injection Hd as <- <-; split; [reflexivity |].
    rewrite xev_DOp1, He; simpl; f_equal; f_equal; ring.
  - (* Sin *) injection Hd as <- <-; split; [reflexivity |].
    rewrite xev_DOp2, xev_DOp1, Ha, He; reflexivity.
  - (* Cos *) injection Hd as <- <-; split; [reflexivity |].
    rewrite xev_DOp2, xev_DOp1, xev_DOp1, Ha, He; reflexivity.
  - (* Exp *) injection Hd as <- <-; split; [reflexivity |].
    rewrite xev_DOp2, xev_DOp1, Ha, He; reflexivity.
  - (* Log *) rewrite lit_1 in Hd; injection Hd as <- <-; split; [reflexivity |].
    rewrite xev_DOp2, xev_DOp2, xev_DReal, lit_1, Ha, He; reflexivity.
  - (* Sqrt *) rewrite lit_1 in Hd; destruct (real_lit "2") as [two |] eqn:E2; [| discriminate].
    injection Hd as <- <-; split; [reflexivity |].
    rewrite xev_DOp2, xev_DOp2, xev_DReal, lit_1, xev_DOp2, xev_DReal, E2, xev_DOp1, Ha, He.
    reflexivity.
  - (* Pow *) destruct k as [| k | k].
    + injection Hp as <-; rewrite lit_0 in Hd; injection Hd as <- <-; split; [reflexivity |]; simpl.
      rewrite xev_DOp2, xev_DReal, lit_0, He; reflexivity.
    + destruct (real_lit (NilZero.string_of_int (Z.to_int (Z.pos k)))) as [kb |] eqn:Ek; [| discriminate].
      injection Hp as <-; injection Hd as <- <-; split; [reflexivity |]; simpl.
      rewrite xev_DOp2, xev_DOp2, xev_DReal; unfold z_to_string; rewrite Ek, xev_DOp1, Ha, He.
      reflexivity.
    + destruct (real_lit (NilZero.string_of_int (Z.to_int (Z.neg k)))) as [kb |] eqn:Ek; [| discriminate].
      injection Hp as <-; injection Hd as <- <-; split; [reflexivity |]; simpl.
      rewrite xev_DOp2, xev_DOp2, xev_DReal; unfold z_to_string; rewrite Ek, xev_DOp1, Ha, He.
      reflexivity.
Qed.

(* scale p e computes the product p * e, omitting a factor 1 or -1. *)
Lemma xev_scale s p e q r :
  xev s p = Some (VReal q) -> xev s e = Some (VReal r) -> xev s (scale p e) = Some (VReal (q * r)).
Proof.
  intros Hp He; destruct p; try (simpl; rewrite xev_DOp2, Hp, He; reflexivity).
  unfold scale; destruct (String.eqb s0 "1") eqn:E1.
  - apply String.eqb_eq in E1; subst; rewrite xev_DReal, lit_1 in Hp; injection Hp as <-.
    rewrite He; f_equal; f_equal; ring.
  - destruct (String.eqb s0 "-1") eqn:E2.
    + apply String.eqb_eq in E2; subst; rewrite xev_DReal, lit_m1 in Hp; injection Hp as <-.
      rewrite xev_DOp1, He; simpl; f_equal; f_equal; ring.
    + rewrite xev_DOp2, Hp, He; reflexivity.
Qed.

Lemma xev_sum2 s e1 e2 :
  xev s (sum [e1; e2]) = xev s (DOp2 Add e1 e2).
Proof. reflexivity. Qed.

(* For a binary arithmetic operation, at least one operand varied: the sum
   of the partial derivatives times the tangents of the varied operands, the
   others having tangent zero. *)
Lemma tangent_op2 s f (a b : atom (tvar W)) x y dx dy z dz pa pb :
  xev s (spell a) = Some (VReal x) -> xev s (spell b) = Some (VReal y) ->
  (tvaried_atom a = true -> xev s (dot a) = Some (VReal dx)) -> (tvaried_atom a = false -> dx = 0) ->
  (tvaried_atom b = true -> xev s (dot b) = Some (VReal dy)) -> (tvaried_atom b = false -> dy = 0) ->
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z dz) -> partial2 f a b = Some (pa, pb) ->
  tvaried_atom a || tvaried_atom b = true ->
  xev s (DOp2 f (spell a) (spell b)) = Some (VReal z) /\
  xev s (sum (tangent_term W a pa ++ tangent_term W b pb)) = Some (VReal dz).
Proof.
  intros Ha Hb Hda Hza Hdb Hzb Hd Hp Hv; rewrite xev_DOp2, Ha, Hb.
  unfold tangent_term.
  destruct f; unfold_ops Hd; unfold_ops Hp; try discriminate; injection Hp as <- <-;
    injection Hd as <- <-; simpl; split; try reflexivity;
    destruct (tvaried_atom a), (tvaried_atom b); try discriminate; simpl;
    rewrite ?xev_DOp2, ?xev_DOp1, ?xev_DReal, ?lit_1, ?lit_m1, ?Ha, ?Hb, ?Hda, ?Hdb by reflexivity;
    rewrite ?Hza, ?Hzb by reflexivity; simpl;
    repeat (first [ rewrite xev_DOp2 | rewrite xev_DOp1 | rewrite xev_DReal | rewrite lit_1
                  | erewrite xev_scale by eauto | rewrite Ha | rewrite Hb | rewrite Hda by reflexivity
                  | rewrite Hdb by reflexivity ]; simpl);
    f_equal; f_equal; unfold Rdiv; rewrite ?Rinv_mult; ring.
Qed.

(* ---------------------------------------------------------------------------
   What the analyses compute does not depend on how the binders are opened,
   as long as the identities agree: two instances related to the same pv
   instance, with contexts that agree on the identities, have the same
   occurrences. (A closed program is parametric: its binders do not look at
   their variables.) *)

(* A pv opened to look into a binder, with identity k. *)
Definition pfresh (k : nat) : pv := PV (AV k false) (anon k) (probe W) (VInt 0) 0.

Definition agree (G1 G2 : list (pv * vinfo)) (k : nat) : Prop :=
  (forall p w1 w2, In (p, w1) G1 -> In (p, w2) G2 -> vid w1 = vid w2) /\
  (forall p w, In (p, w) G1 \/ In (p, w) G2 -> (aid (pa p) < k)%nat).

Lemma agree_open G1 G2 k :
  agree G1 G2 k -> agree ((pfresh k, anon k) :: G1) ((pfresh k, anon k) :: G2) (S k).
Proof.
  intros [H1 H2]; split.
  - intros p w1 w2 [E1 | I1] [E2 | I2].
    + inversion E1; inversion E2; reflexivity.
    + inversion E1; subst; specialize (H2 _ _ (or_intror I2)); simpl in H2; lia.
    + inversion E2; subst; specialize (H2 _ _ (or_introl I1)); simpl in H2; lia.
    + eauto.
  - intros p w [[E | I] | [E | I]]; try (inversion E; subst; simpl; lia);
      specialize (H2 p w); intuition lia.
Qed.

Lemma agree_atom G1 G2 k (a : atom pv) a1 a2 id :
  agree G1 G2 k -> atom_eq G1 a a1 -> atom_eq G2 a a2 -> occurs_atom id a1 = occurs_atom id a2.
Proof.
  intros [H _]; destruct a, a1, a2; simpl; try contradiction; try reflexivity.
  intros I1 I2; rewrite (H _ _ _ I1 I2); reflexivity.
Qed.

Ltac rewrite_atoms Hg :=
  repeat match goal with
  | A1 : atom_eq ?G1 ?x ?y1, A2 : atom_eq ?G2 ?x ?y2 |- context [occurs_atom ?id ?y1] =>
      rewrite (agree_atom G1 G2 _ x y1 y2 id Hg A1 A2)
  end.

Lemma occurs_transfer :
  (forall bP : anf pv bare, forall G1 G2 b1 b2 id k, anf_eq G1 bP b1 -> anf_eq G2 bP b2 ->
     agree G1 G2 k -> occurs_anf id k b1 = occurs_anf id k b2) /\
  (forall eP : value pv bare, forall G1 G2 e1 e2 id k, value_eq G1 eP e1 -> value_eq G2 eP e2 ->
     agree G1 G2 k -> occurs_value id k e1 = occurs_value id k e2).
Proof.
  apply anf_value_ind.
  - (* ALet *) intros [] e IHe b IHb G1 G2 [] [] id k; simpl; try contradiction.
    intros [He1 Hb1] [He2 Hb2] Hg; rewrite (IHe _ _ _ _ id k He1 He2 Hg).
    f_equal; apply (IHb (pfresh k) ((pfresh k, anon k) :: G1) ((pfresh k, anon k) :: G2));
      auto using agree_open.
  - (* ARet *) intros a G1 G2 [] [] id k; simpl; try contradiction; intros; eapply agree_atom; eauto.
  - intros f a G1 G2 [] [] id k; simpl; try contradiction; intros [_ H1] [_ H2] Hg;
      eapply agree_atom; eauto.
  - intros f a b G1 G2 [] [] id k; simpl; try contradiction; intros [_ [A1 B1]] [_ [A2 B2]] Hg;
      rewrite_atoms Hg; reflexivity.
  - intros a i G1 G2 [] [] id k; simpl; try contradiction; intros [A1 B1] [A2 B2] Hg;
      rewrite_atoms Hg; reflexivity.
  - intros a i v G1 G2 [] [] id k; simpl; try contradiction; intros [A1 [B1 C1]] [A2 [B2 C2]] Hg;
      rewrite_atoms Hg; reflexivity.
  - intros c t IHt e IHe G1 G2 [] [] id k; simpl; try contradiction; intros [A1 [B1 C1]] [A2 [B2 C2]] Hg.
    rewrite_atoms Hg; rewrite (IHt _ _ _ _ id k B1 B2 Hg), (IHe _ _ _ _ id k C1 C2 Hg); reflexivity.
  - intros lo hi b IHb G1 G2 [] [] id k; simpl; try contradiction; intros [A1 [B1 C1]] [A2 [B2 C2]] Hg.
    rewrite_atoms Hg; f_equal.
    apply (IHb (pfresh k) ((pfresh k, anon k) :: G1) ((pfresh k, anon k) :: G2)); auto using agree_open.
  - intros [] lo hi init b IHb G1 G2 [] [] id k; simpl; try contradiction;
      intros [A1 [B1 [C1 D1]]] [A2 [B2 [C2 D2]]] Hg.
    rewrite_atoms Hg; f_equal.
    apply (IHb (pfresh k) (pfresh (S k)) ((pfresh (S k), anon (S k)) :: (pfresh k, anon k) :: G1)
                 ((pfresh (S k), anon (S k)) :: (pfresh k, anon k) :: G2)); auto using agree_open.
Qed.

(* ---------------------------------------------------------------------------
   Lists: reading and replacing an element commute with a map. *)

Lemma nth_z_map {A B : Type} (f : A -> B) k l :
  nth_z k (map f l) = option_map f (nth_z k l).
Proof. unfold nth_z; destruct (k <? 0)%Z; [reflexivity |]; apply nth_error_map. Qed.

Lemma replace_nth_map {A B : Type} (f : A -> B) n x l :
  replace_nth n (f x) (map f l) = option_map (map f) (replace_nth n x l).
Proof.
  revert l; induction n as [| n IH]; intros [| y l]; simpl; try reflexivity.
  rewrite IH; destruct (replace_nth n x l); reflexivity.
Qed.

Lemma replace_nth_z_map {A B : Type} (f : A -> B) k x l :
  replace_nth_z k (f x) (map f l) = option_map (map f) (replace_nth_z k x l).
Proof. unfold replace_nth_z; destruct (k <? 0)%Z; [reflexivity | apply replace_nth_map]. Qed.

Lemma replace_nth_length {A : Type} n (x : A) l l' :
  replace_nth n x l = Some l' -> length l' = length l.
Proof.
  revert l l'; induction n as [| n IH]; intros [| y l] l' H; simpl in H; try discriminate.
  - injection H as <-; reflexivity.
  - destruct (replace_nth n x l) eqn:E; [| discriminate]; injection H as <-; simpl; f_equal; eauto.
Qed.

Lemma replace_nth_z_length {A : Type} k (x : A) l l' :
  replace_nth_z k x l = Some l' -> length l' = length l.
Proof. unfold replace_nth_z; destruct (k <? 0)%Z; [discriminate | apply replace_nth_length]. Qed.

Lemma replace_nth_Forall {A : Type} (P : A -> Prop) n x l l' :
  P x -> Forall P l -> replace_nth n x l = Some l' -> Forall P l'.
Proof.
  revert l l'; induction n as [| n IH]; intros [| y l] l' Hx Hl H; simpl in H; try discriminate;
    inversion Hl; subst.
  - injection H as <-; constructor; auto.
  - destruct (replace_nth n x l) eqn:E; [| discriminate]; injection H as <-; constructor; eauto.
Qed.

Lemma replace_nth_z_Forall {A : Type} (P : A -> Prop) k x l l' :
  P x -> Forall P l -> replace_nth_z k x l = Some l' -> Forall P l'.
Proof. unfold replace_nth_z; destruct (k <? 0)%Z; [discriminate | apply replace_nth_Forall]. Qed.

Lemma nth_z_Forall {A : Type} (P : A -> Prop) k l x :
  Forall P l -> nth_z k l = Some x -> P x.
Proof.
  unfold nth_z; destruct (k <? 0)%Z; [discriminate |]; intros Hl H.
  apply nth_error_In in H; rewrite Forall_forall in Hl; auto.
Qed.

Lemma in_gW L p w : In (p, w) (gW L) -> In p L /\ w = pw p.
Proof. unfold gW; rewrite in_map_iff; intros [q [E I]]; inversion E; subst; auto. Qed.
Lemma in_gT L p t : In (p, t) (gT L) -> In p L /\ t = pt p.
Proof. unfold gT; rewrite in_map_iff; intros [q [E I]]; inversion E; subst; auto. Qed.
Lemma in_gA L p a : In (p, a) (gA L) -> In p L /\ a = pa p.
Proof. unfold gA; rewrite in_map_iff; intros [q [E I]]; inversion E; subst; auto. Qed.
Lemma in_gD L p d : In (p, d) (gD L) -> In p L /\ d = pd p.
Proof. unfold gD; rewrite in_map_iff; intros [q [E I]]; inversion E; subst; auto. Qed.

(* A body that only returns the variable it binds, as well_formed sees it
   (opened with anon k), is such for every opening of the pv instance. *)
Lemma is_tail_shape L k (bP : pv -> anf pv bare) (bW : vinfo -> anf vinfo bare) :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (bP x1) (bW x2)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat) ->
  WellFormed.is_tail bW k = true -> forall x, bP x = ARet (AVar x).
Proof.
  intros HW Hk Ht x; specialize (HW x (anon k)); unfold WellFormed.is_tail in Ht.
  destruct (bP x) as [? ? ? | [p | |]], (bW (anon k)) as [? ? ? | [w | |]];
    simpl in HW; try contradiction; try discriminate.
  apply Nat.eqb_eq in Ht; destruct HW as [E | I]; [inversion E; reflexivity |].
  apply in_gW in I as [I ->]; specialize (Hk _ I); lia.
Qed.

(* well_formed and tangent agree on which bodies only return their variable. *)
Lemma is_tail_transfer L k (bP : pv -> anf pv bare) (bW : vinfo -> anf vinfo bare)
  (bT : tvar W -> anf (tvar W) bare) tr :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (bP x1) (bW x2)) ->
  (forall x1 x2, anf_eq ((x1, x2) :: gT L) (bP x1) (bT x2)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat) ->
  WellFormed.is_tail bW k = Transform.is_tail (fun v => rebuild _ (bT v) tr).
Proof.
  intros HW HT Hk; set (x := pfresh k).
  assert (Hx : ~ In x L) by (intros I; destruct (Hk _ I) as [H _]; simpl in H; lia).
  specialize (HW x (anon k)); specialize (HT x (probe W));
    unfold WellFormed.is_tail, Transform.is_tail.
  destruct (bP x) as [? ? ? | [p | |]], (bW (anon k)) as [? ? ? | [w | |]],
    (bT (probe W)) as [? ? ? | [t | |]]; simpl in HW, HT; try contradiction; try reflexivity;
    try (destruct tr; reflexivity); simpl.
  destruct HW as [E | I]; destruct HT as [E' | I'].
  - inversion E; inversion E'; subst; simpl; rewrite Nat.eqb_refl; reflexivity.
  - inversion E; subst; apply in_gT in I' as [I' _]; contradiction.
  - inversion E'; subst; apply in_gW in I as [I _]; contradiction.
  - apply in_gW in I as [I ->]; apply in_gT in I' as [_ ->].
    destruct (Hk _ I) as [H1 H2].
    destruct (Nat.eqb_spec (vid (pw p)) k); [lia |].
    destruct (tid (pt p)) as [[|] |]; congruence.
Qed.

(* ---------------------------------------------------------------------------
   Loops: a loop of the tangent program simulates a fold or a map of the dual
   evaluation, given an invariant kept by one iteration. *)

Lemma fold_loop_sim (ev : val (dual R) -> val (dual R) -> option (val (dual R)))
  (body : store R -> option (store R)) (i : dvar nat)
  (Inv : Z -> store R -> val (dual R) -> Prop) :
  (forall j s st st', Inv j s st -> ev (VInt j) st = Some st' ->
     exists s', body (store_set s (KVar i) (VInt j)) = Some s' /\ Inv (j + 1)%Z s' st') ->
  forall n lo s st v, Inv lo s st -> eval_fold ev lo n st = Some v ->
  exists s', exec_up R body i lo n s = Some s' /\ Inv (lo + Z.of_nat n)%Z s' v.
Proof.
  intros Hstep n; induction n as [| n IH]; intros lo s st v Hinv Hev; simpl in Hev; cbn [exec_up].
  - injection Hev as <-; exists s; split; [reflexivity | rewrite Z.add_0_r; exact Hinv].
  - destruct (ev (VInt lo) st) as [st1 |] eqn:E; [| discriminate].
    destruct (Hstep _ _ _ _ Hinv E) as [s1 [Hb Hi]]; rewrite Hb.
    destruct (IH _ _ _ _ Hi Hev) as [s' [He Hi']]; exists s'; split; [exact He |].
    replace (lo + Z.of_nat (S n))%Z with (lo + 1 + Z.of_nat n)%Z by lia; exact Hi'.
Qed.

Lemma map_loop_sim (ev : val (dual R) -> option (val (dual R)))
  (body : store R -> option (store R)) (i : dvar nat)
  (Inv : Z -> store R -> list (dual R) -> Prop) :
  (forall j s acc x, Inv j s acc -> ev (VInt j) = Some (VReal x) ->
     exists s', body (store_set s (KVar i) (VInt j)) = Some s' /\ Inv (j + 1)%Z s' (acc ++ [x])%list) ->
  forall n lo s acc xs, Inv lo s acc -> eval_map ev lo n = Some xs ->
  exists s', exec_up R body i lo n s = Some s' /\ Inv (lo + Z.of_nat n)%Z s' (acc ++ xs)%list.
Proof.
  intros Hstep n; induction n as [| n IH]; intros lo s acc xs Hinv Hev; simpl in Hev; cbn [exec_up].
  - injection Hev as <-; exists s; rewrite app_nil_r, Z.add_0_r; auto.
  - destruct (ev (VInt lo)) as [[x | | | |] |] eqn:E; try discriminate.
    destruct (eval_map ev (lo + 1) n) as [xs1 |] eqn:E1; [| discriminate]; injection Hev as <-.
    destruct (Hstep _ _ _ _ Hinv E) as [s1 [Hb Hi]]; rewrite Hb.
    destruct (IH _ _ _ _ Hi E1) as [s' [He Hi']]; exists s'; split; [exact He |].
    replace (lo + Z.of_nat (S n))%Z with (lo + 1 + Z.of_nat n)%Z by lia.
    rewrite <- app_assoc in Hi'; exact Hi'.
Qed.

(* ---------------------------------------------------------------------------
   Atoms: the generated code reads the value of an atom in its stored
   variable, and its tangent in the dot of that variable, or 0. *)

Lemma atom_graph {V : Type} (pr : pv -> V) L (aP : atom pv) aX :
  atom_eq (map (fun p => (p, pr p)) L) aP aX ->
  aX = amap pr aP /\ (forall p, aP = AVar p -> In p L).
Proof.
  destruct aP as [p | sP | kP], aX as [x | sX | kX]; simpl; try contradiction.
  - rewrite in_map_iff; intros [q [E I]]; inversion E; subst; split; [reflexivity |].
    intros r E'; inversion E'; subst; exact I.
  - intros ->; split; [reflexivity | discriminate].
  - intros ->; split; [reflexivity | discriminate].
Qed.

Lemma aeval_literal s d : aeval_atom (duals reals) (ANum s) = Some d ->
  exists x, real_lit s = Some x /\ d = VReal (Dual x 0).
Proof.
  cbv beta iota delta [aeval_atom duals dual_lit dom_lit reals]; rewrite lit_0.
  destruct (real_lit s) as [x |]; [| discriminate]; intros H; injection H as <-; eauto.
Qed.

(* The value of an atom. *)
Lemma spell_ok k s (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p /\ store_ok s p) ->
  aeval_atom (duals reals) (amap pd aP) = Some d ->
  xev s (spell (amap pt aP)) = Some (primal d).
Proof.
  intros Hs Hd; destruct aP as [q | str | z].
  - simpl in Hd; injection Hd as <-; destruct (Hs q eq_refl) as [Hst [H _]].
    destruct Hst as [_ [_ [Hstore _]]]; simpl; rewrite Hstore; exact H.
  - apply aeval_literal in Hd as [x [Hx ->]]; simpl; rewrite xev_DReal, Hx; reflexivity.
  - simpl in Hd; injection Hd as <-; reflexivity.
Qed.

(* The tangent of a real atom. *)
Lemma dot_ok k s (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p /\ store_ok s p) ->
  aeval_atom (duals reals) (amap pd aP) = Some (VReal d) ->
  xev s (dot (amap pt aP)) = Some (VReal (dsnd d)).
Proof.
  intros Hs Hd; destruct aP as [q | str | z].
  - simpl in Hd; injection Hd as Hd; destruct (Hs q eq_refl) as [Hst [_ H]].
    destruct Hst as [_ [_ [Hstore [_ [_ [Hdot [_ [_ [_ Hz]]]]]]]]]; simpl.
    rewrite Hdot; destruct (avaried (pa q)) eqn:Ev.
    + rewrite Hstore; specialize (H Hdot); rewrite Hd in H; exact H.
    + specialize (Hz eq_refl); rewrite Hd in Hz; simpl in Hz; rewrite xev_DReal, lit_0, Hz; reflexivity.
  - apply aeval_literal in Hd as [x [Hx E]]; injection E as ->; simpl; rewrite xev_DReal, lit_0; reflexivity.
  - discriminate.
Qed.

(* ---------------------------------------------------------------------------
   The simulation. *)

Fixpoint dvars (e : dexpr W) : list (dvar W) :=
  match e with
  | DVar x => [x]
  | DAt a i => dvars a ++ dvars i
  | DOp1 _ a => dvars a
  | DOp2 _ a b => dvars a ++ dvars b
  | _ => []
  end.

(* The variables an expression of the result reads: in scope, or opened by
   the code (at or after c). *)
Definition res_vars (L : list pv) (live : pv -> Prop) (c : nat) (e : dexpr W) : Prop :=
  forall x, In x (dvars e) ->
  (exists p, In p L /\ live p /\ (x = stored p \/ x = DotOf (stored p))) \/ (~ below c x /\ consistent x).

Definition live_anf (k : nat) (b : anf vinfo bare) (p : pv) : Prop :=
  occurs_anf (vid (pw p)) k b = true.
Definition live_value (k : nat) (e : value vinfo bare) (p : pv) : Prop :=
  occurs_value (vid (pw p)) k e = true.

(* For a body: run from a store related to the dual values of the variables
   the body reads, the statements the tangent pass generates compute the
   value and the tangent of the body, as the dual evaluation does, and leave
   the variables opened before unchanged, except the storage updated in
   place. The activity analysis is sound: a body that is not varied has a
   zero tangent. *)
Definition sim_body (bP : anf pv bare) : Prop :=
  forall L k c s wP pp m bA bW bT bD ty v,
  anf_eq (gA L) bP bA -> anf_eq (gW L) bP bW -> anf_eq (gT L) bP bT -> anf_eq (gD L) bP bD ->
  ctx_ok L k c s wP pp (live_anf k bW) ty -> real_or_array ty ->
  typecheck (option_map (amap pw) wP) (wplace pp) k bW = (ty, Ok) ->
  aeval (duals reals) bD = Some v ->
  let '((ss, (ve, de)), c') :=
    open_pairs (tan W (option_map (amap pt) wP) (rebuild _ bT (annotate_body_t false m k bA))) c in
  (c <= c')%nat /\ has_type ty v /\ (varied_anf k bA = false -> zero v) /\
  res_vars L (fun p => live_anf k bW p \/ owner wP pp = Some p) c ve /\
  res_vars L (fun p => live_anf k bW p \/ owner wP pp = Some p) c de /\
  exists s', run ss s = Some s' /\ frame c (inplace wP pp) s s' /\
             body_result ty (inplace wP pp) s' ve de v.

(* Where the tangent pass stores a value (with_storage): the storage of the
   array it updates in place, or the array written by a final map; None for
   a fresh variable. *)
Definition storage (wP : option (atom pv)) (tail : bool) (eP : value pv bare) : option (dvar W) :=
  match eP with
  | ASet (AVar a) _ _ => Some (stored a)
  | AFold _ _ _ (AVar i) _ => match vty (pw i) with Array _ => Some (stored i) | _ => None end
  | AMap _ _ _ => if tail then match wP with Some (AVar y) => Some (stored y) | _ => None end else None
  | _ => None
  end.

(* For a value, computed into the variable n: the value is stored in n, its
   tangent in the dot of n when it is varied. *)
Definition sim_value (eP : value pv bare) : Prop :=
  forall L k c s wP pp tail eA eW eT eD te n ve ty,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gT L) eP eT -> value_eq (gD L) eP eD ->
  ctx_ok L k c s wP pp (live_value k eW) ty ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  (exists j, n = DBound (j, j) /\ (j < c)%nat) ->
  match storage wP tail eP with
  | Some m => n = m
  | None => forall p, In p L -> stored p <> n /\ DotOf (stored p) <> n
  end ->
  aeval_value (duals reals) eD = Some ve ->
  let vr := varied_value k eA in
  let '(se, c') :=
    open_pairs (tan_value W (option_map (amap pt) wP)
                  (rebuild_value _ eT (annotate_value_t false k eA)) te vr n) c in
  (c <= c')%nat /\ has_type te ve /\ (vr = false -> zero ve) /\ (vr = true -> real_or_array te) /\
  exists s', run se s = Some s' /\ frame c (Some n) s s' /\
             store_get s' (keyv n) = Some (primal ve) /\
             (vr = true \/ storage wP tail eP <> None ->
              store_get s' (keyv (DotOf n)) = Some (tangent ve)).

Ltac graph H := apply atom_graph in H; destruct H as [-> ?].

Lemma static_in L k p : Forall (static_ok k) L -> In p L -> static_ok k p.
Proof. rewrite Forall_forall; auto. Qed.

Lemma unique_written L k c s wP pp live ty p y :
  ctx_ok L k c s wP pp live ty -> In p L -> wP = Some y ->
  (match amap pw y with AVar y0 => (vid (pw p) =? vid y0)%nat | _ => false end) = true ->
  wP = Some (AVar p).
Proof.
  intros Hc Hp Hw Hid; destruct (c_written _ _ _ _ _ _ _ _ Hc _ Hw) as [q [-> [Hq _]]].
  simpl in Hid; apply Nat.eqb_eq in Hid.
  rewrite (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hq Hp (eq_sym Hid)) in Hw; exact Hw.
Qed.

(* A body that returns an atom. *)
Lemma sim_ret (aP : atom pv) : sim_body (ARet aP).
Proof.
  intros L k c s wP pp m bA bW bT bD ty v HA HW HT HD Hc Hty Htc Hev.
  destruct bA as [| aA], bW as [| aW], bT as [| aT], bD as [| aD]; simpl in HA, HW, HT, HD;
    try contradiction.
  graph HA; graph HW; graph HT; graph HD.
  destruct aP as [p | str | z]; simpl in Htc, Hev |- *.
  - injection Hev as <-.
    assert (Hp : In p L) by auto.
    pose proof (static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hp) as Hst.
    assert (Hl : live_anf k (ARet (amap pw (AVar p))) p) by (unfold live_anf; simpl; apply Nat.eqb_refl).
    pose proof (c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl) as Hs.
    assert (Ety : ty = vty (pw p) /\
                  (varg (pw p) = None \/ wP = Some (AVar p) \/ ~ is_array (vty (pw p)))).
    { destruct (varg (pw p)) as [[nx r] |] eqn:Eg; [| injection Htc; auto].
      destruct (ty_is_array (vty (pw p))) eqn:Ea; simpl in Htc.
      - destruct (option_map (amap pw) wP) as [y |] eqn:Ew; simpl in Htc; [| discriminate].
        destruct wP as [y' |]; [| discriminate]; injection Ew as <-.
        destruct (match amap pw y' with AVar y0 => (vid (pw p) =? vid y0)%nat | _ => false end) eqn:Eid;
          simpl in Htc; [| discriminate].
        injection Htc as ->; split; [reflexivity |].
        right; left; eapply unique_written; eauto.
      - injection Htc as <-; split; [reflexivity |]; right; right.
        unfold is_array; destruct (vty (pw p)); simpl in Ea; try discriminate; tauto. }
    destruct Ety as [-> Hcase]. pose proof Hst as Hst0.
    destruct Hst as [_ [_ [Hstore [_ [_ [Hdot [_ [_ [Hht Hz]]]]]]]]].
    split; [lia | split; [exact Hht | split; [exact Hz |]]].
    split; [intros x Hx; left; exists p; simpl in Hx; rewrite Hstore in Hx;
            destruct Hx as [<- | []]; auto |].
    split; [intros x Hx; left; exists p; simpl in Hx; destruct (tdot (pt p)); simpl in Hx;
            [rewrite Hstore in Hx; destruct Hx as [<- | []]; auto | contradiction] |].
    exists s; split; [reflexivity | split; [intros ? ? ? ?; reflexivity |]].
    destruct (vty (pw p)) eqn:Ety; try contradiction.
    + (* a real *) pose proof (proj1 Hs) as Hs1.
      destruct (pd p) as [d | | | |] eqn:Ed; try contradiction; split.
      * simpl; rewrite Hstore; exact Hs1.
      * apply (dot_ok k s (AVar p)); [| simpl; rewrite Ed; reflexivity].
        intros q E; injection E as <-; split; [exact Hst0 | exact Hs].
    + (* an array: the variable updated in place *)
      destruct (owner wP pp) as [o |] eqn:Eo;
        [| destruct (c_ty _ _ _ _ _ _ _ _ Hc I); exact Eo].
      assert (Hpo : pn p = pn o).
      { apply (c_arrays _ _ _ _ _ _ _ _ Hc p o Hp Hl); [rewrite Ety; exact I | | exact Eo].
        destruct Hcase as [Hc1 | [Hc1 | Hc1]]; auto; exfalso; apply Hc1; exact I. }
      destruct (c_inplace _ _ _ _ _ _ _ _ Hc o p Eo Hp Hl Hpo) as [F1 F2].
      exists (stored p); unfold inplace, stored in *; rewrite Eo, Hpo in *; simpl; auto.
  - apply aeval_literal in Hev as [x [Hx ->]]; injection Htc as <-.
    split; [lia | split; [exact I | split; [reflexivity |]]].
    split; [intros x' [] | split; [intros x' [] |]].
    exists s; split; [reflexivity | split; [intros ? ? ? ?; reflexivity |]].
    simpl; rewrite !xev_DReal, Hx, lit_0; auto.
  - injection Htc as <-; destruct Hty.
Qed.

(* ---------------------------------------------------------------------------
   The pieces of a let. *)

Ltac fresh_case := solve [eexists (DBound (_, _)), false, (S _); simpl; auto].

(* with_storage, opened: the value goes to the storage the pv instance says. *)
Lemma open_with_storage {A : Type} L k wP (eP : value pv bare) eT vt
  (bT : tvar W -> anf (tvar W) ann) (K : dvar W -> bool -> scoped W A) c :
  value_eq (gT L) eP eT -> Forall (static_ok k) L ->
  (forall a, wP = Some a -> exists y, a = AVar y /\ In y L) ->
  exists n rec c0,
    open_pairs (with_storage (option_map (amap pt) wP) (rebuild_value _ eT vt) bT K) c =
    open_pairs (K n rec) c0 /\
    match storage wP (Transform.is_tail bT) eP with
    | Some m => n = m /\ c0 = c
    | None => n = DBound (c, c) /\ c0 = S c
    end.
Proof.
  intros HT HL Hw.
  assert (Hst : forall p, In p L -> tstored (pt p) = stored p /\ tty (pt p) = vty (pw p))
    by (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [_ [H1 [H2 _]]]]; auto).
  destruct eP as [f a | f a b | a i | a i x | cnd t e | lo hi b | an lo hi init b], eT;
    simpl in HT; try contradiction; simpl;
    try fresh_case; try (destruct vt; fresh_case).
  - (* ASet *) destruct HT as [Ha _]; destruct a as [p | |]; destruct a0; simpl in Ha; try contradiction;
      try fresh_case.
    apply in_gT in Ha as [Hp ->]; destruct (Hst _ Hp) as [E _].
    exists (stored p), (trecorded (pt p)), c; simpl; rewrite E; auto.
  - (* AMap *) destruct (vt); simpl;
      (destruct (Transform.is_tail bT); [| fresh_case]);
      (destruct wP as [[y | |] |]; simpl;
       [| fresh_case
        | fresh_case
        | fresh_case]);
      (destruct (Hw _ eq_refl) as [y' [E Hy]]; injection E as <-;
       destruct (Hst _ Hy) as [E _]; exists (stored y), (trecorded (pt y)), c; rewrite E; auto).
  - (* AFold *) destruct HT as [_ [_ [Hi _]]]; destruct init as [p | |], init0; simpl in Hi; try contradiction;
      destruct vt; simpl; try fresh_case;
      (apply in_gT in Hi as [Hp ->]; destruct (Hst _ Hp) as [E1 E2]; rewrite E2;
       destruct (vty (pw p)); try fresh_case;
       exists (stored p), (trecorded (pt p)), c; rewrite E1; auto).
Qed.

Lemma tof_amap k L (a : atom pv) :
  Forall (static_ok k) L -> (forall p, a = AVar p -> In p L) -> tof (amap pt a) = of_atom (amap pw a).
Proof.
  intros HL Ha; destruct a as [p | |]; simpl; auto.
  destruct (static_in _ _ _ HL (Ha p eq_refl)) as [_ [_ [_ [E _]]]]; exact E.
Qed.

Lemma ty_eqb_true a b : ty_eqb a b = true -> a = b.
Proof. destruct a, b; simpl; try discriminate; auto. intros E; apply Z.eqb_eq in E; subst; auto. Qed.

Ltac crush_match H :=
  repeat (match type of H with context [match ?x with _ => _ end] => destruct x eqn:? end;
          simpl in H);
  repeat match goal with
         | E : (if ?b then _ else _) = Some _ |- _ => destruct b; [| discriminate]
         | E : ty_eqb _ _ = true |- _ => apply ty_eqb_true in E
         end; try congruence.

(* The type the tangent pass computes for a value is the type well_formed
   gives it. *)
Lemma type_of_ok L k wW pW tail (eP : value pv bare) eW eT vt te :
  value_eq (gW L) eP eW -> value_eq (gT L) eP eT -> Forall (static_ok k) L ->
  typecheck_value wW pW tail k eW = (te, Ok) -> Transform.type_of (rebuild_value _ eT vt) = te.
Proof.
  intros HW HT HL Htc.
  destruct eP, eW, eT; simpl in HW, HT; try contradiction;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
    | H : atom_eq (gT L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
    end; subst; simpl in Htc |- *;
    try (destruct vt; reflexivity);
    rewrite ?(tof_amap k L) by auto.
  - (* AOp1 *) crush_match Htc.
  - (* AOp2 *) crush_match Htc.
  - (* AGet *) crush_match Htc.
  - (* ASet *) destruct (of_atom (amap pw a)) eqn:E; destruct pW; simpl in Htc; crush_match Htc.
  - (* AIte *) destruct vt; simpl; destruct pW; simpl in Htc; crush_match Htc.
  - (* AMap *) destruct vt; simpl; destruct pW; simpl in Htc; try congruence;
      destruct tail; try congruence; destruct lo; simpl in Htc; try congruence;
      destruct hi; simpl in Htc |- *; try congruence; crush_match Htc.
  - (* AFold *) destruct vt; simpl; rewrite (tof_amap k L) by auto; crush_match Htc.
Qed.

(* A value stored in place has an array type. *)
Lemma inplace_array L wP pW tail k (eP : value pv bare) eW te :
  value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) pW tail k eW = (te, Ok) ->
  storage wP tail eP <> None -> is_array te.
Proof.
  intros HW Htc Hs.
  destruct eP, eW; simpl in HW; try contradiction; simpl in Hs; try (destruct Hs; reflexivity);
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
    end; subst; simpl in Htc.
  - destruct pW; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - destruct pW; simpl in Htc; try (crush_match Htc; fail).
    destruct tail; [| crush_match Htc].
    destruct lo, hi; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - destruct init as [i | |]; simpl in Hs; try (destruct Hs; reflexivity); simpl in Htc.
    destruct (vty (pw i)) eqn:Ev; try (destruct Hs; reflexivity).
    crush_match Htc; injection Htc as <-; exact I.
Qed.

Lemma open_pairs_sbind {A B : Type} (sc : scoped W A) (f : A -> scoped W B) c :
  open_pairs (sbind sc f) c = let '(a, c1) := open_pairs sc c in open_pairs (f a) c1.
Proof.
  revert c; induction sc as [n g IH | p g IH | a]; intros c; simpl; auto.
Qed.

Lemma open_pairs_mono {A : Type} (sc : scoped W A) c : (c <= snd (open_pairs sc c))%nat.
Proof. revert c; induction sc as [n g IH | p g IH | a]; intros c; simpl; auto; specialize (IH (c, c) (S c)); lia. Qed.

Lemma static_mono k k' p : static_ok k p -> (k <= k')%nat -> static_ok k' p.
Proof. intros [H1 [H2 H3]] Hk; split; [exact H1 | split; [lia | exact H3]]. Qed.

Lemma owner_in L k c s wP pp live ty o :
  ctx_ok L k c s wP pp live ty -> owner wP pp = Some o -> In o L.
Proof.
  intros Hc Ho; destruct pp as [| | | ix sx]; simpl in Ho; try discriminate.
  - destruct wP as [[y | |] |]; try discriminate; destruct (vty (pw y)); try discriminate.
    injection Ho as <-; destruct (c_written _ _ _ _ _ _ _ _ Hc _ eq_refl) as [y' [E [Hy _]]].
    injection E as <-; exact Hy.
  - injection Ho as <-; apply (c_place _ _ _ _ _ _ _ _ Hc).
Qed.

(* A fresh pv for a binder of identity k is not in scope. *)
Lemma fresh_notin L k x :
  (forall p, In p L -> (aid (pa p) < k)%nat) -> aid (pa x) = k -> ~ In x L.
Proof. intros H Hx I; specialize (H _ I); lia. Qed.

Lemma aids_below L k : Forall (static_ok k) L -> forall p, In p L -> (aid (pa p) < k)%nat.
Proof. intros HL p Hp; destruct (static_in _ _ _ HL Hp) as [E [H _]]; lia. Qed.

(* The body after a binder, opened as the simulation opens it and as
   well_formed's occurs opens it (anon k), has the same occurrences. *)
Lemma live_cont L k (cP : pv -> anf pv bare) (cW : vinfo -> anf vinfo bare) x w id :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (cP x1) (cW x2)) ->
  Forall (static_ok k) L -> aid (pa x) = k -> vid w = k ->
  occurs_anf id (S k) (cW w) = occurs_anf id (S k) (cW (anon k)).
Proof.
  intros HcW HL Hx Hw.
  apply (proj1 occurs_transfer (cP x) ((x, w) :: gW L) ((x, anon k) :: gW L)); auto.
  pose proof (fresh_notin L k x (aids_below L k HL) Hx) as Hn.
  split.
  - intros p w1 w2 [E1 | I1] [E2 | I2].
    + inversion E1; inversion E2; subst; simpl; auto.
    + inversion E1; subst; apply in_gW in I2 as [I2 _]; contradiction.
    + inversion E2; subst; apply in_gW in I1 as [I1 _]; contradiction.
    + apply in_gW in I1 as [_ ->]; apply in_gW in I2 as [_ ->]; reflexivity.
  - intros p w' [[E | I] | [E | I]]; try (inversion E; subst; lia);
      apply in_gW in I as [I _]; specialize (aids_below L k HL p I); lia.
Qed.

(* A body that only returns its variable, opened with w. *)
Lemma tail_cont L k (cP : pv -> anf pv bare) (cW : vinfo -> anf vinfo bare) x w :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (cP x1) (cW x2)) ->
  Forall (static_ok k) L -> aid (pa x) = k ->
  WellFormed.is_tail cW k = true -> cP x = ARet (AVar x) /\ cW w = ARet (AVar w).
Proof.
  intros HcW HL Hx Ht.
  assert (Hk : forall p, In p L -> (vid (pw p) < k)%nat)
    by (intros p Hp; destruct (static_in _ _ _ HL Hp) as [E [H _]]; lia).
  pose proof (is_tail_shape L k cP cW HcW Hk Ht) as Hs.
  split; [apply Hs |].
  specialize (HcW x w); rewrite (Hs x) in HcW.
  destruct (cW w) as [? ? ? | [w' | |]]; simpl in HcW; try contradiction.
  destruct HcW as [E | I]; [inversion E; reflexivity |].
  apply in_gW in I as [I _]; destruct (fresh_notin L k x (aids_below L k HL) Hx I).
Qed.

Lemma same_vid L k c s wP pp live ty p q :
  ctx_ok L k c s wP pp live ty -> In p L -> In q L -> (vid (pw p) =? vid (pw q))%nat = true -> p = q.
Proof. intros Hc Hp Hq E; apply Nat.eqb_eq in E; exact (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E). Qed.

Lemma operation2_typed_scalar f a b t sp : operation2_typed f a b = Some (t, sp) -> ~ is_array t.
Proof.
  unfold operation2_typed; intros H; destruct f, a, b; simpl in H;
    try discriminate; injection H as <- <-; simpl; auto.
Qed.

(* A value that updates an array in place (it has an array type, or the
   tangent pass stores it in place) ends its body, and is stored in the
   storage of the variable updated in place. *)
Lemma inplace_value L k c s wP pp live ty tail (eP : value pv bare) eW te :
  ctx_ok L k c s wP pp live ty -> value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  storage wP tail eP <> None \/ is_array te ->
  tail = true /\ exists o, owner wP pp = Some o /\ storage wP tail eP = Some (stored o).
Proof.
  intros Hc HW Htc Hty Hin.
  destruct eP, eW; simpl in HW; try contradiction;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
    end; subst; simpl in Htc, Hin |- *.
  - destruct Hin as [Hi | Hi]; [congruence |]; destruct f0; simpl in Htc; crush_match Htc;
      injection Htc as <-; destruct Hi.
  - destruct Hin as [Hi | Hi]; [congruence |]; crush_match Htc; injection Htc as <-.
    match goal with H : operation2_typed _ _ _ = Some _ |- _ => apply operation2_typed_scalar in H end.
    contradiction.
  - destruct Hin as [Hi | Hi]; [congruence |]; crush_match Htc; injection Htc as <-; destruct Hi.
  - (* ASet *) destruct pp as [| | | ix sx]; simpl in Htc; try discriminate.
    destruct (of_atom (amap pw a)) eqn:Ea; try discriminate.
    destruct tail; simpl in Htc; [| discriminate]; split; [reflexivity |].
    destruct a as [p | |]; simpl in Htc; try discriminate.
    destruct (vid (pw p) =? vid (pw sx))%nat eqn:E; simpl in Htc; [| discriminate].
    assert (Hp : In p L) by auto.
    pose proof (c_place _ _ _ _ _ _ _ _ Hc) as [_ [Hsx _]].
    rewrite (same_vid _ _ _ _ _ _ _ _ _ _ Hc Hp Hsx E); exists sx; auto.
  - (* AIte *) destruct Hin as [Hi | Hi]; [congruence |]; destruct pp; simpl in Htc; crush_match Htc;
      injection Htc as <-; destruct Hi.
  - (* AMap *) destruct pp; simpl in Htc; try (crush_match Htc; fail).
    destruct tail; [| crush_match Htc]; split; [reflexivity |].
    destruct (owner wP PTop) as [o |] eqn:Eo.
    + destruct wP as [[y | |] |]; simpl in Eo; try discriminate.
      destruct (vty (pw y)); try discriminate; injection Eo as <-; exists y; auto.
    + exfalso; apply (c_ty _ _ _ _ _ _ _ _ Hc); [| exact Eo].
      rewrite <- (Hty eq_refl).
      destruct lo, hi; simpl in Htc; crush_match Htc; injection Htc as <-; exact I.
  - (* AFold *)
    destruct (ty_eqb (of_atom (amap pw lo)) Integer && ty_eqb (of_atom (amap pw hi)) Integer);
      simpl in Htc; [| discriminate].
    destruct init as [i | str | z]; simpl in Htc, Hin |- *.
    + destruct (vty (pw i)) as [| | | n] eqn:Ev; simpl in Htc.
      * destruct Hin as [Hi | Hi]; [congruence |]; destruct pp; simpl in Htc; crush_match Htc;
          injection Htc as <-; destruct Hi.
      * discriminate.
      * discriminate.
      * assert (Hi : In i L) by auto.
        destruct pp as [| | | ix sx]; destruct tail; simpl in Htc; try discriminate.
        -- destruct wP as [y |] eqn:Ew; simpl in Htc; [| discriminate].
           destruct (match amap pw y with AVar y0 => (vid (pw i) =? vid y0)%nat | _ => false end) eqn:E;
             [| discriminate].
           rewrite (unique_written _ _ _ _ _ _ _ _ _ _ Hc Hi eq_refl E).
           split; [reflexivity |]; exists i; simpl; rewrite Ev; auto.
        -- destruct (vid (pw i) =? vid (pw sx))%nat eqn:E; simpl in Htc; [| discriminate].
           pose proof (c_place _ _ _ _ _ _ _ _ Hc) as [_ [Hsx _]].
           pose proof (same_vid _ _ _ _ _ _ _ _ _ _ Hc Hi Hsx E) as ->.
           split; [reflexivity |]; exists sx; simpl; auto.
    + destruct Hin as [Hi | Hi]; [congruence |]; destruct pp; simpl in Htc; crush_match Htc;
        injection Htc as <-; destruct Hi.
    + discriminate.
Qed.

Lemma below_mono c c' v : below c v -> (c <= c')%nat -> below c' v.
Proof. induction v as [[i j] | v IH | v IH | v IH |]; simpl; auto; lia. Qed.

(* The frames of a value and of the rest of its let compose. *)
Lemma frame_let c c0 c1 ex n s s1 s2 :
  (c <= c0)%nat -> (c0 <= c1)%nat -> frame c0 (Some n) s s1 -> frame c1 ex s1 s2 ->
  ~ below c n \/ ex = Some n -> frame c ex s s2.
Proof.
  intros H01 H12 F1 F2 Hn v Hb Hcons Hex.
  rewrite (F2 v (below_mono _ _ _ Hb (Nat.le_trans _ _ _ H01 H12)) Hcons Hex).
  apply F1; [exact (below_mono _ _ _ Hb H01) | exact Hcons |].
  intros m E; injection E as <-; destruct Hn as [Hn | Hn].
  - split; intros ->; [exact (Hn Hb) | exact (Hn Hb)].
  - exact (Hex _ Hn).
Qed.

(* A context stays a context for fewer live variables and a larger counter. *)
Lemma ctx_weaken L k c c' s wP pp (live live' : pv -> Prop) ty :
  ctx_ok L k c s wP pp live ty -> (forall p, live' p -> live p) -> (c <= c')%nat ->
  ctx_ok L k c' s wP pp live' ty.
Proof.
  intros Hc Hl Hcc; destruct Hc; constructor; auto.
  - intros p Hp; specialize (c_num0 p Hp); lia.
  - intros o p Ho Hp E; destruct (c_owner0 o p Ho Hp E) as [H | H]; [left; exact H | right; auto].
  - intros o p Ho Hp Lp; apply c_inplace0; auto.
  - intros y H1 H2 H3; destruct (c_top0 y H1 H2 H3) as [A [B C]]; auto.
Qed.

Lemma arrays_len_value s n v z :
  store_get s (keyv n) = Some (primal v) -> store_get s (keyv (DotOf n)) = Some (tangent v) ->
  has_type (Array z) v -> arrays_len s n (Z.to_nat z).
Proof.
  intros H1 H2 Ht; destruct v as [| | | l |]; try contradiction; simpl in Ht.
  exists (map dfst l), (map dsnd l); rewrite !length_map; auto.
Qed.

Lemma arrays_len_frame c ex s s' p len :
  frame c ex s s' -> (pn p < c)%nat ->
  (forall m, ex = Some m -> stored p <> m /\ stored p <> DotOf m) ->
  (forall m, ex = Some m -> DotOf (stored p) <> m /\ DotOf (stored p) <> DotOf m) ->
  arrays_len s (stored p) len -> arrays_len s' (stored p) len.
Proof.
  intros F Hp H1 H2 [l1 [l2 [A1 [A2 [A3 A4]]]]]; exists l1, l2.
  rewrite (F (stored p)), (F (DotOf (stored p))); unfold stored in *; simpl; auto.
Qed.

Lemma res_vars_let x L (live live' : pv -> Prop) c c1 e :
  res_vars (x :: L) live' c1 e -> (c <= c1)%nat -> (forall p, In p L -> live' p -> live p) ->
  ((~ below c (stored x) /\ consistent (stored x)) \/ exists o, In o L /\ live o /\ stored x = stored o) ->
  res_vars L live c e.
Proof.
  intros H Hc Hl Hx y Hy; destruct (H y Hy) as [[p [[<- | Hp] [Lp E]]] | [Hb Hcy]].
  - destruct Hx as [[Hx Hcx] | [o [Ho [Lo Eo]]]].
    + right; destruct E as [-> | ->]; auto.
    + left; exists o; rewrite <- Eo; auto.
  - left; exists p; auto.
  - right; split; [intros Hb'; apply Hb, (below_mono c); auto | exact Hcy].
Qed.

Lemma tan_let w a e b :
  tan W w (ALet a e b) =
  with_storage w e b (fun n rec =>
    let vr := match a with LetAnn v _ _ => v | _ => false end in
    sbind (tan_value W w e (Transform.type_of e) vr n) (fun se =>
    sbind (tan W w (b (open_let (Transform.type_of e) n vr rec))) (fun '(sb, vd) => Done ((se ++ sb)%list, vd)))).
Proof. reflexivity. Qed.

(* A let: the value, stored, then the rest of the body with one more
   variable in scope. *)
Lemma sim_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  sim_value eP -> (forall x, sim_body (cP x)) -> sim_body (ALet a eP cP).
Proof.
  intros IHe IHb L k c s wP pp m bA bW bT bD ty v HA HW HT HD Hc Hty Htc Hev.
  destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |], bD as [aD eD cD |];
    simpl in HA, HW, HT, HD; try contradiction.
  destruct HA as [HeA HcA], HW as [HeW HcW], HT as [HeT HcT], HD as [HeD HcD].
  simpl in Htc, Hev.
  destruct (typecheck_value (option_map (amap pw) wP) (wplace pp) (WellFormed.is_tail cW k) k eW)
    as [te d0] eqn:Hte.
  destruct d0; simpl in Htc; [| discriminate].
  destruct (aeval_value (duals reals) eD) as [ve |] eqn:Hve; [| discriminate].
  cbn [annotate_body_t]. destruct (needs false m (S k) (cA (let_binder k eA))) as [u l].
  set (vr := varied_value k eA). set (vt := annotate_value_t false k eA).
  set (rest := annotate_body_t false m (S k) (cA (let_binder k eA))).
  cbn [rebuild]. rewrite tan_let. cbv zeta.
  pose proof (c_static _ _ _ _ _ _ _ _ Hc) as HL.
  rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
  destruct (open_with_storage L k wP eP eT vt (fun v0 => rebuild _ (cT v0) rest)
     (fun n rec => sbind (tan_value W (option_map (amap pt) wP) (rebuild_value _ eT vt) te vr n)
       (fun se => sbind (tan W (option_map (amap pt) wP) (rebuild _ (cT (open_let te n vr rec)) rest))
                    (fun '(sb, vd) => Done ((se ++ sb)%list, vd)))) c HeT HL) as [n [rec [c0 [Hopen Hn]]]].
  { intros a0 E; destruct (c_written _ _ _ _ _ _ _ _ Hc _ E) as [y [-> [Hy _]]]; eauto. }
  rewrite Hopen.
  rewrite <- (is_tail_transfer L k cP cW cT rest HcW HcT) in Hn by
    (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]]; auto).
  set (tail := WellFormed.is_tail cW k) in *.
  rewrite open_pairs_sbind.
  destruct (open_pairs (tan_value W (option_map (amap pt) wP) (rebuild_value (tvar W) eT vt) te vr n) c0)
    as [se c1] eqn:Hse.
  assert (Hlive_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p).
  { intros p H; unfold live_value, live_anf in *; simpl; rewrite H; reflexivity. }
  assert (Htail_ty : tail = true -> te = ty).
  { intros Ht; destruct (tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL eq_refl Ht) as [_ E].
    rewrite E in Htc; simpl in Htc; injection Htc; auto. }
  assert (Hnum : exists j, n = DBound (j, j) /\ (j < c0)%nat /\ (c <= c0)%nat /\
                 match storage wP tail eP with Some _ => True | None => j = c end).
  { destruct (storage wP tail eP) as [m0 |] eqn:Es; destruct Hn as [-> ->].
    - assert (Hsn : storage wP tail eP <> None) by (rewrite Es; discriminate).
      destruct (inplace_value _ _ _ _ _ _ _ _ _ _ _ _ Hc HeW Hte Htail_ty (or_introl Hsn))
        as [_ [o [Ho Es']]].
      rewrite Es in Es'; injection Es' as ->; exists (pn o); split; [reflexivity |].
      pose proof (c_num _ _ _ _ _ _ _ _ Hc _ (owner_in _ _ _ _ _ _ _ _ _ Hc Ho)); lia.
    - exists c; repeat split; lia. }
  destruct Hnum as [j [Ej [Hj0 [Hc0 Hjs]]]].
  specialize (IHe L k c0 s wP pp tail eA eW eT eD te n ve ty HeA HeW HeT HeD
                (ctx_weaken _ _ _ _ _ _ _ _ _ _ Hc Hlive_e Hc0) Hte Htail_ty).
  specialize (IHe (ex_intro _ j (conj Ej Hj0))).
  assert (Hst : match storage wP tail eP with
                | Some m0 => n = m0
                | None => forall p, In p L -> stored p <> n /\ DotOf (stored p) <> n
                end).
  { destruct (storage wP tail eP); [apply Hn |]; intros p Hp; subst j; rewrite Ej;
      pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp); unfold stored; split; intros E; inversion E; lia. }
  specialize (IHe Hst Hve); cbv zeta in IHe; fold vr vt in IHe; rewrite Hse in IHe.
  destruct IHe as [Hc01 [Hht [Hz [Hra [s1 [Hrun1 [Hfr1 [Hn1 Hd1]]]]]]]].
  (* the variable of the let *)
  set (x := PV (let_binder k eA) (VInfo k te None) (open_let te n vr rec) ve j).
  assert (Hx : aid (pa x) = k) by reflexivity.
  assert (HxL : ~ In x L) by exact (fresh_notin L k x (aids_below L k HL) Hx).
  assert (Hvid : forall p, In p L -> (vid (pw p) < k)%nat)
    by (intros p Hp; destruct (static_in _ _ _ HL Hp) as [_ [H _]]; exact H).
  destruct (storage wP tail eP) as [m0 |] eqn:Es.
  - (* stored in place: the rest only returns the variable *)
    assert (Hsn : storage wP tail eP <> None) by (rewrite Es; discriminate).
    destruct (inplace_value _ _ _ _ _ _ _ _ _ _ _ _ Hc HeW Hte Htail_ty (or_introl Hsn))
      as [Ht [o [Ho Es']]].
    pose proof (inplace_array _ _ _ _ _ _ _ _ HeW Hte Hsn) as Harr.
    rewrite Es in Es'; injection Es' as Em0; destruct Hn as [Hnd _]; subst m0.
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
    assert (Hva : varied_anf (S k) (cA (pa x)) = vr) by (rewrite EA; reflexivity).
    simpl in ET, ED, EA; rewrite ED in Hev; simpl in Hev; injection Hev as <-.
    rewrite EW in Htc; simpl in Htc; injection Htc as <-.
    unfold rest; rewrite EA; simpl; rewrite ET; simpl.
    rewrite app_nil_r.
    assert (Hno : n = stored o) by congruence.
    assert (HoL : In o L) by exact (owner_in _ _ _ _ _ _ _ _ _ Hc Ho).
    split; [lia | split; [exact Hht | split; [intros H0; apply Hz; rewrite <- Hva; exact H0 |]]].
    split; [intros y Hy; simpl in Hy; destruct Hy as [<- | []]; left; exists o; auto |].
    split; [intros y Hy; simpl in Hy; destruct vr; simpl in Hy; [| contradiction];
            destruct Hy as [<- | []]; left; exists o; rewrite Hno; auto |].
    exists s1; split; [exact Hrun1 |].
    split; [apply (frame_let c c0 c0 _ n s s1 s1); auto; [intros ? ? ? ?; reflexivity |];
            right; unfold inplace; rewrite Ho; simpl; congruence |].
    destruct te as [| | | z]; try destruct Harr.
    exists n; unfold inplace; rewrite Ho; simpl; split; [congruence | split; [exact Hn1 |]].
    destruct vr; simpl; apply Hd1; right; discriminate.
  - (* a fresh variable *)
    destruct Hn as [-> Hc0']; subst j.
    (* the rest reads the variables in scope it read as part of the let *)
    assert (Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p ->
                                live_anf k (ALet aW eW cW) p).
    { unfold live_anf; intros p Hp H; simpl.
      rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx eq_refl) in H.
      rewrite H; apply orb_true_r. }
    (* the value leaves the variables in scope unchanged *)
    assert (Hframe_old : forall p, In p L ->
              store_get s1 (keyv (stored p)) = store_get s (keyv (stored p)) /\
              store_get s1 (keyv (DotOf (stored p))) = store_get s (keyv (DotOf (stored p)))).
    { intros p Hp; pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp) as Hpn.
      split; apply Hfr1; unfold stored; simpl; try lia; try reflexivity;
        intros m0 E; injection E as <-; split; intros E; inversion E; lia. }
    set (cW' := cW (VInfo k te None)).
    assert (Hxs : static_ok (S k) x).
    { repeat split; simpl; auto; try lia; discriminate. }
    assert (Hxstore : store_ok s1 x).
    { split; unfold stored; simpl; [exact Hn1 |]; intros Hv; apply Hd1; left; exact Hv. }
    assert (Hc' : ctx_ok (x :: L) (S k) c1 s1 wP pp (live_anf (S k) cW') ty).
    { constructor.
      - constructor; [exact Hxs |]; apply Forall_impl with (P := static_ok k); auto.
        intros p Hp; apply (static_mono k); auto.
      - intros p q [<- | Hp] [<- | Hq] E; auto.
        + specialize (Hvid _ Hq); simpl in E; lia.
        + specialize (Hvid _ Hp); simpl in E; lia.
        + exact (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
      - intros p [<- | Hp]; simpl; [lia |].
        pose proof (c_num _ _ _ _ _ _ _ _ Hc _ Hp); lia.
      - intros p [<- | Hp] Hl; [exact Hxstore |].
        destruct (c_store _ _ _ _ _ _ _ _ Hc _ Hp (Hlive_c _ Hp Hl)) as [S1 S2].
        destruct (Hframe_old _ Hp) as [F1 F2]; split; [rewrite F1; exact S1 |].
        intros Hd; rewrite F2; exact (S2 Hd).
      - intros a0 E; destruct (c_written _ _ _ _ _ _ _ _ Hc _ E) as [y [-> [Hy Hv]]].
        exists y; split; [reflexivity | split; [right; exact Hy | exact Hv]].
      - pose proof (c_place _ _ _ _ _ _ _ _ Hc) as Hp; destruct pp; simpl in *; auto.
        destruct Hp as [A [B C]]; split; [right; exact A | split; [right; exact B | exact C]].
      - intros o p Ho [<- | Hp] Ep.
        + pose proof (c_num _ _ _ _ _ _ _ _ Hc _ (owner_in _ _ _ _ _ _ _ _ _ Hc Ho)); simpl in Ep; lia.
        + destruct (c_owner _ _ _ _ _ _ _ _ Hc o p Ho Hp Ep) as [H | H]; [left; exact H |].
          right; intros Hl; apply H, Hlive_c; auto.
      - intros o p Ho [<- | Hp] Lp Ep.
        + pose proof (c_num _ _ _ _ _ _ _ _ Hc _ (owner_in _ _ _ _ _ _ _ _ _ Hc Ho)); simpl in Ep; lia.
        + destruct (c_inplace _ _ _ _ _ _ _ _ Hc o p Ho Hp (Hlive_c _ Hp Lp) Ep) as [S1 S2].
          destruct (Hframe_old _ Hp) as [F1 F2]; split; [rewrite F1 | rewrite F2]; assumption.
      - intros p o [<- | Hp] Lp Ha Hg Ho.
        + destruct (inplace_value _ _ _ _ _ _ _ _ _ _ _ _ Hc HeW Hte Htail_ty (or_intror Ha))
            as [_ [o' [Ho' Es']]].
          rewrite Es in Es'; discriminate.
        + exact (c_arrays _ _ _ _ _ _ _ _ Hc p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho).
      - exact (c_ty _ _ _ _ _ _ _ _ Hc).
      - intros y Hpp Hw Ha.
        destruct (c_written _ _ _ _ _ _ _ _ Hc _ Hw) as [y' [E [Hy _]]]; injection E as <-.
        destruct (c_top _ _ _ _ _ _ _ _ Hc y Hpp Hw Ha) as [T1 [T2 [l1 [l2 [A1 [A2 [A3 A4]]]]]]].
        split; [exact T1 | split; [intros Ly; apply T2, Hlive_c; auto |]].
        destruct (Hframe_old _ Hy) as [F1 F2]; exists l1, l2; rewrite F1, F2; auto. }
    (* the rest of the body *)
    specialize (IHb x (x :: L) (S k) c1 s1 wP pp m (cA (pa x)) cW' (cT (pt x)) (cD (pd x)) ty v
                  (HcA x _) (HcW x _) (HcT x _) (HcD x _) Hc' Hty Htc Hev).
    unfold x in IHb; cbn [pt pa pd] in IHb; fold rest in IHb.
    match type of IHb with context [open_pairs ?t c1] =>
      destruct (open_pairs t c1) as [[sb [ve' de']] c2] eqn:Hsb end.
    destruct IHb as [Hc12 [Hht' [Hz' [Hrv1 [Hrv2 [s2 [Hrun2 [Hfr2 Hres2]]]]]]]].
    assert (Hxs' : (~ below c (DBound (c, c)) /\ consistent (DBound (c, c))) \/
                   exists o, In o L /\ (live_anf k (ALet aW eW cW) o \/ owner wP pp = Some o) /\
                             DBound (c, c) = stored o)
      by (left; simpl; split; [lia | reflexivity]).
    rewrite open_pairs_sbind.
    match goal with |- context [open_pairs ?t c1] =>
      replace (open_pairs t c1) with ((sb, (ve', de')), c2) by (rewrite <- Hsb; reflexivity) end.
    simpl.
    split; [lia | split; [exact Hht' | split; [exact Hz' |]]].
    assert (Hlv' : forall p, In p L -> live_anf (S k) cW' p \/ owner wP pp = Some p ->
                             live_anf k (ALet aW eW cW) p \/ owner wP pp = Some p)
      by (intros p Hp [H | H]; [left; apply Hlive_c; auto | right; exact H]).
    split; [exact (res_vars_let _ L _ _ c c1 ve' Hrv1 (Nat.le_trans _ _ _ Hc0 Hc01) Hlv' Hxs') |].
    split; [exact (res_vars_let _ L _ _ c c1 de' Hrv2 (Nat.le_trans _ _ _ Hc0 Hc01) Hlv' Hxs') |].
    exists s2; split; [rewrite run_app, Hrun1; exact Hrun2 | split; [| exact Hres2]].
    apply (frame_let c c0 c1 _ (DBound (c, c)) s s1 s2); auto.
    left; simpl; lia.
Qed.

(* ---------------------------------------------------------------------------
   Expressions read only the variables they mention: a write to another key
   does not change their value. *)


Definition avoid (k : key) (e : dexpr W) : Prop := forall x, In x (dvars e) -> keyv x <> k.

Lemma xev_set_other s k v e : avoid k e -> xev (store_set s k v) e = xev s e.
Proof.
  unfold avoid, xev; induction e as [x | l | z | a IHa i IHi | f a IHa | f a IHa b IHb]; simpl; intros H.
  - rewrite store_get_set; destruct (key_eqb k (KVar (out_dvar nat x))) eqn:E; [| reflexivity].
    apply key_eqb_eq in E; destruct (H x (or_introl eq_refl)); symmetry; exact E.
  - reflexivity.
  - reflexivity.
  - rewrite IHa, IHi; auto; intros y Hy; apply H, in_or_app; auto.
  - rewrite IHa; auto.
  - rewrite IHa, IHb; auto; intros y Hy; apply H, in_or_app; auto.
Qed.

Lemma avoid_op1 k f e : avoid k e -> avoid k (DOp1 f e).
Proof. auto. Qed.
Lemma avoid_op2 k f e1 e2 : avoid k e1 -> avoid k e2 -> avoid k (DOp2 f e1 e2).
Proof. intros H1 H2 x Hx; simpl in Hx; apply in_app_or in Hx as [Hx | Hx]; auto. Qed.
Lemma avoid_at k e1 e2 : avoid k e1 -> avoid k e2 -> avoid k (DAt e1 e2).
Proof. intros H1 H2 x Hx; simpl in Hx; apply in_app_or in Hx as [Hx | Hx]; auto. Qed.
Lemma avoid_lit k l : avoid k (DReal l).
Proof. intros x []. Qed.
Lemma avoid_scale k p e : avoid k p -> avoid k e -> avoid k (scale p e).
Proof.
  intros H1 H2; destruct p; try (apply avoid_op2; auto); unfold scale.
  destruct (String.eqb s "1"); [exact H2 |]; destruct (String.eqb s "-1"); [apply avoid_op1, H2 |].
  apply avoid_op2; auto.
Qed.
Lemma avoid_sum k l : Forall (avoid k) l -> avoid k (sum l).
Proof.
  induction 1 as [| e l He Hl IH]; [apply avoid_lit |]; simpl.
  destruct l; [exact He | apply avoid_op2; auto].
Qed.

(* The keys of a variable in scope, when the stored variable is not n. *)
Lemma avoid_spell k (aP : atom pv) n :
  (forall p, aP = AVar p -> static_ok k p /\ pn p <> n) ->
  avoid (keyv (DBound (n, n))) (spell (amap pt aP)) /\
  avoid (keyv (DBound (n, n))) (dot (amap pt aP)) /\
  avoid (keyv (DotOf (DBound (n, n)))) (spell (amap pt aP)) /\
  avoid (keyv (DotOf (DBound (n, n)))) (dot (amap pt aP)).
Proof.
  intros H; destruct aP as [p | | ]; simpl;
    try (repeat split; intros x []; fail).
  destruct (H p eq_refl) as [[_ [_ [Hs _]]] Hn]; rewrite Hs; unfold stored.
  repeat split; try destruct (tdot (pt p)); simpl; intros x Hx; simpl in Hx;
    try contradiction; destruct Hx as [<- | []]; unfold keyv; simpl;
    intros E; inversion E; auto.
Qed.

Lemma avoid_partial1 k f (a : atom (tvar W)) p :
  avoid k (spell a) -> avoid k (dot a) -> partial1 f a = Some p ->
  avoid k (scale (spell_partial p) (dot a)).
Proof.
  intros Hs Hd Hp; apply avoid_scale; [| exact Hd].
  destruct f as [| | | | | | z |]; simpl in Hp; try discriminate;
    try (destruct z); injection Hp as <-; simpl;
    repeat (apply avoid_op1 || apply avoid_op2 || apply avoid_lit || assumption).
Qed.

Lemma avoid_partial2 k f (a b : atom (tvar W)) pa pb :
  avoid k (spell a) -> avoid k (dot a) -> avoid k (spell b) -> avoid k (dot b) ->
  partial2 f a b = Some (pa, pb) ->
  avoid k (sum (tangent_term W a pa ++ tangent_term W b pb)).
Proof.
  intros Hsa Hda Hsb Hdb Hp; apply avoid_sum; unfold tangent_term.
  destruct f; simpl in Hp; try discriminate; injection Hp as <- <-;
    destruct (tvaried_atom a), (tvaried_atom b); simpl;
    repeat (apply Forall_cons || apply Forall_nil || apply avoid_scale || apply avoid_op1
            || apply avoid_op2 || apply avoid_lit || assumption).
Qed.

Lemma keyv_inj a b : consistent a -> consistent b -> keyv a = keyv b -> a = b.
Proof.
  unfold keyv; intros Ha Hb E; injection E; clear E; revert b Hb.
  induction a as [[i j] | a IH | a IH | a IH |]; intros [[i' j'] | b | b | b |] Hb E; simpl in *;
    try discriminate; try reflexivity.
  - injection E as ->; subst; reflexivity.
  - injection E as E; f_equal; auto.
  - injection E as E; f_equal; auto.
  - injection E as E; f_equal; auto.
Qed.

Lemma frame_refl c ex s : frame c ex s s.
Proof. intros v _ _ _; reflexivity. Qed.

Lemma frame_set c n s s' k v :
  frame c (Some n) s s' -> consistent n -> (k = keyv n \/ k = keyv (DotOf n)) ->
  frame c (Some n) s (store_set s' k v).
Proof.
  intros F Hn Hk w Hb Hc Hex; rewrite store_get_set.
  destruct (key_eqb k (keyv w)) eqn:E; [| apply F; auto].
  apply key_eqb_eq in E; destruct (Hex n eq_refl) as [H1 H2]; exfalso.
  destruct Hk as [-> | ->]; apply keyv_inj in E; auto.
Qed.

Lemma store_get_set_same (s : store R) k v : store_get (store_set s k v) k = Some v.
Proof. rewrite store_get_set, key_eqb_refl; reflexivity. Qed.

Lemma store_get_set_other (s : store R) k k' v : k <> k' -> store_get (store_set s k v) k' = store_get s k'.
Proof.
  intros H; rewrite store_get_set; destruct (key_eqb k k') eqn:E; [| reflexivity].
  apply key_eqb_eq in E; contradiction.
Qed.

Lemma keyv_dot_neq n : keyv n <> keyv (DotOf n).
Proof.
  unfold keyv; intros E; injection E; clear E.
  induction n as [[i j] | n IH | n IH | n IH |]; simpl; intros E; try discriminate; injection E; auto.
Qed.

(* The facts the simulation of an operation needs on an operand that occurs
   in it. *)
Lemma operand_ok L k c s wP pp (live : pv -> Prop) ty (aP : atom pv) n :
  ctx_ok L k c s wP pp live ty -> (forall p, aP = AVar p -> In p L /\ live p) ->
  (forall p, In p L -> stored p <> DBound (n, n) /\ DotOf (stored p) <> DBound (n, n)) ->
  forall p, aP = AVar p -> (static_ok k p /\ store_ok s p) /\ (static_ok k p /\ pn p <> n).
Proof.
  intros Hc Ha Hn p E; destruct (Ha p E) as [Hp Hl].
  pose proof (static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hp) as Hs.
  split; [split; [exact Hs | exact (c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl)] | split; [exact Hs |]].
  intros E'; destruct (Hn p Hp) as [H _]; apply H; unfold stored; rewrite E'; reflexivity.
Qed.

Lemma operand_ok2 L k c s wP pp (live : pv -> Prop) ty (aP : atom pv) n :
  ctx_ok L k c s wP pp live ty -> (forall p, aP = AVar p -> In p L /\ live p) ->
  (forall p, aP = AVar p -> pn p <> n) ->
  forall p, aP = AVar p -> (static_ok k p /\ store_ok s p) /\ (static_ok k p /\ pn p <> n).
Proof.
  intros Hc Ha Hn p E; destruct (Ha p E) as [Hp Hl].
  pose proof (static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hp) as Hs.
  split; [split; [exact Hs | exact (c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl)] | split; [exact Hs | auto]].
Qed.

Lemma tvaried_amap k (aP : atom pv) :
  (forall p, aP = AVar p -> static_ok k p) -> tvaried_atom (amap pt aP) = varied (amap pa aP).
Proof.
  intros H; destruct aP as [p | |]; simpl; auto.
  destruct (H p eq_refl) as [_ [_ [_ [_ [E _]]]]]; exact E.
Qed.

(* A literal or a variable that is not varied has a zero tangent. *)
Lemma atom_zero k (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p) -> varied (amap pa aP) = false ->
  aeval_atom (duals reals) (amap pd aP) = Some d -> zero d.
Proof.
  intros H Hv Hd; destruct aP as [p | str | z].
  - simpl in Hd; injection Hd as <-; destruct (H p eq_refl) as [_ [_ [_ [_ [_ [_ [_ [_ [_ Hz]]]]]]]]].
    exact (Hz Hv).
  - apply aeval_literal in Hd as [x [_ ->]]; reflexivity.
  - simpl in Hd; injection Hd as <-; exact I.
Qed.

Lemma atom_type k (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p) ->
  aeval_atom (duals reals) (amap pd aP) = Some d -> has_type (of_atom (amap pw aP)) d.
Proof.
  intros H Hd; destruct aP as [p | str | z].
  - simpl in Hd; injection Hd as <-; destruct (H p eq_refl) as [_ [_ [_ [_ [_ [_ [_ [_ [Ht _]]]]]]]]].
    exact Ht.
  - apply aeval_literal in Hd as [x [_ ->]]; exact I.
  - simpl in Hd; injection Hd as <-; exact I.
Qed.

Lemma dual_op1_zero f x y dy : dual_op1 R reals f (Dual x 0) = Some (Dual y dy) -> dy = 0.
Proof.
  intros H; unfold dual_op1 in H; destruct (dom_op1 reals f x); [| discriminate].
  destruct (dual_partial1 R reals f x r); [| discriminate]; simpl in H.
  injection H as _ <-; ring.
Qed.

Lemma run_define s so n e v :
  xev s e = Some v -> run [DDefine so n e] s = Some (store_set s (keyv n) v).
Proof. intros H; unfold run, xev in *; simpl; rewrite H; reflexivity. Qed.

Lemma run_define2 s so so' n e e' v v' :
  xev s e = Some v -> xev (store_set s (keyv n) v) e' = Some v' ->
  run [DDefine so n e; DDefine so' (DotOf n) e'] s =
  Some (store_set (store_set s (keyv n) v) (keyv (DotOf n)) v').
Proof. intros H H'; unfold run, xev, keyv in *; simpl; rewrite H; simpl; rewrite H'; reflexivity. Qed.

Ltac value_intro :=
  let L := fresh "L" in let k := fresh "k" in let c := fresh "c" in let s := fresh "s" in
  intros L k c s wP pp tail eA eW eT eD te n ve ty HA HW HT HD Hc Htc Htail [j [Ej Hj]] Hst Hev;
  destruct eA, eW, eT, eD; simpl in HA, HW, HT, HD; try contradiction;
  repeat match goal with
         | H : _ /\ _ |- _ => destruct H
         | H : atom_eq (gA _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gW _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gT _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         | H : atom_eq (gD _) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
         end; subst.

(* A unary operation. *)
Lemma sim_op1 f (aP : atom pv) : sim_value (AOp1 f aP).
Proof.
  value_intro. simpl in Htc, Hev, Hst |- *.
  rename f3 into f.
  assert (Hlv : forall p, aP = AVar p -> In p L /\ live_value k (AOp1 f (amap pw aP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; apply Nat.eqb_refl]).
  assert (Hop := operand_ok _ _ _ _ _ _ _ _ aP j Hc Hlv Hst).
  assert (Hop1 : forall p, aP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hop; auto).
  assert (Hop2 : forall p, aP = AVar p -> static_ok k p /\ pn p <> j) by (intros; apply Hop; auto).
  assert (Hst1 : forall p, aP = AVar p -> static_ok k p) by (intros; apply Hop1; auto).
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  assert (Hty : te = Real /\ of_atom (amap pw aP) = Real).
  { destruct f; simpl in Htc; crush_match Htc; split; congruence. }
  destruct Hty as [-> Hta].
  pose proof (atom_type k aP va Hst1 Ha) as Htv; rewrite Hta in Htv.
  destruct va as [[x dx] | | | |]; try contradiction; cbn [eval_op1 dom_op1 duals] in Hev.
  destruct (dual_op1 R reals f (Dual x dx)) as [[y dy] |] eqn:Hd; [| discriminate].
  injection Hev as <-.
  assert (Hs := spell_ok k s aP _ Hop1 Ha); simpl in Hs.
  assert (Hdt := dot_ok k s aP _ Hop1 Ha); simpl in Hdt.
  destruct (partial1 f (amap pt aP)) as [p |] eqn:Hp;
    [| destruct f as [| | | | | | z |]; simpl in Hp; try discriminate; try (destruct z; discriminate);
       unfold_ops Hd; discriminate].
  destruct (tangent_op1 s f (amap pt aP) _ x dx y dy p Hs Hdt Hd Hp) as [Hv Ht].
  destruct (avoid_spell k aP j Hop2) as [A1 [A2 [A3 A4]]].
  unfold tangent_term; rewrite (tvaried_amap k aP Hst1).
  destruct (varied (amap pa aP)) eqn:Hvr; simpl.
  - split; [lia | split; [exact I | split; [discriminate | split; [intros _; exact I |]]]].
    exists (store_set (store_set s (keyv (DBound (j, j))) (VReal y)) (keyv (DotOf (DBound (j, j)))) (VReal dy)).
    split; [apply run_define2; [exact Hv | rewrite xev_set_other; [exact Ht |]] |].
    { apply avoid_partial1 with (f := f); auto. }
    split; [apply frame_set; [apply frame_set; [apply frame_refl | reflexivity | auto] | reflexivity | auto] |].
    split; [rewrite store_get_set_other, store_get_set_same; [reflexivity | apply not_eq_sym, keyv_dot_neq] |].
    intros _; rewrite store_get_set_same; reflexivity.
  - split; [lia | split; [exact I | split; [| split; [discriminate |]]]].
    + intros _; pose proof (atom_zero k aP _ Hst1 Hvr Ha) as Hz; simpl in Hz; subst dx.
      simpl; exact (dual_op1_zero f x y dy Hd).
    + exists (store_set s (keyv (DBound (j, j))) (VReal y)).
      split; [apply run_define; exact Hv |].
      split; [apply frame_set; [apply frame_refl | reflexivity | auto] |].
      split; [rewrite store_get_set_same; reflexivity |].
      intros [H | H]; [discriminate | contradiction].
Qed.

Lemma dual_op2_zero f x y z dz : dual_op2 R reals f (Dual x 0) (Dual y 0) = Some (Dual z dz) -> dz = 0.
Proof.
  intros H; destruct f; unfold_ops H; try discriminate; injection H as _ <-; unfold Rdiv; ring.
Qed.

Lemma primal_int_op2 f x y : primal (int_op2 f x y) = int_op2 f x y.
Proof. destruct f; reflexivity. Qed.

Lemma has_type_int t z : has_type t (VInt z) -> t = Integer.
Proof. destruct t; simpl; tauto. Qed.

(* An integer atom is not varied. *)
Lemma int_not_varied k (aP : atom pv) z :
  (forall p, aP = AVar p -> static_ok k p) ->
  aeval_atom (duals reals) (amap pd aP) = Some (VInt z) -> varied (amap pa aP) = false.
Proof.
  intros H Ha; destruct aP as [p | str | z']; simpl; auto.
  simpl in Ha; injection Ha as Hd.
  destruct (H p eq_refl) as [_ [_ [_ [_ [_ [_ [_ [Hv [Ht _]]]]]]]]].
  rewrite Hd in Ht; apply has_type_int in Ht.
  destruct (avaried (pa p)); auto; specialize (Hv eq_refl); rewrite Ht in Hv; destruct Hv.
Qed.

Lemma int_op2_type f (x y : Z) t sp :
  operation2_typed f Integer Integer = Some (t, sp) -> has_type t (@int_op2 (dual R) f x y).
Proof. destruct f; simpl; intros H; try discriminate; injection H as <- <-; exact I. Qed.

Lemma op2_real_type f t sp :
  operation2_typed f Real Real = Some (t, sp) -> t = if comparison f then Boolean else Real.
Proof. destruct f; simpl; intros H; try discriminate; injection H as <- <-; reflexivity. Qed.

(* A binary operation. *)
Lemma sim_op2 f (aP bP : atom pv) : sim_value (AOp2 f aP bP).
Proof.
  value_intro. simpl in Htc, Hev, Hst |- *.
  rename f3 into f.
  assert (Hlv : forall p, aP = AVar p -> In p L /\ live_value k (AOp2 f (amap pw aP) (amap pw bP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity]).
  assert (Hlv' : forall p, bP = AVar p -> In p L /\ live_value k (AOp2 f (amap pw aP) (amap pw bP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl, orb_true_r; reflexivity]).
  assert (Hop := operand_ok _ _ _ _ _ _ _ _ aP j Hc Hlv Hst).
  assert (Hop' := operand_ok _ _ _ _ _ _ _ _ bP j Hc Hlv' Hst).
  assert (HaS : forall p, aP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hop; auto).
  assert (HaN : forall p, aP = AVar p -> static_ok k p /\ pn p <> j) by (intros; apply Hop; auto).
  assert (Ha1 : forall p, aP = AVar p -> static_ok k p) by (intros; apply HaS; auto).
  assert (HbS : forall p, bP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hop'; auto).
  assert (HbN : forall p, bP = AVar p -> static_ok k p /\ pn p <> j) by (intros; apply Hop'; auto).
  assert (Hb1 : forall p, bP = AVar p -> static_ok k p) by (intros; apply HbS; auto).
  destruct (aeval_atom (duals reals) (amap pd aP)) as [va |] eqn:Ha; [| discriminate].
  destruct (aeval_atom (duals reals) (amap pd bP)) as [vb |] eqn:Hb; [| discriminate].
  assert (Hsa := spell_ok k s aP _ HaS Ha); assert (Hsb := spell_ok k s bP _ HbS Hb).
  destruct (operation2 f) eqn:Ho2; [| discriminate].
  destruct (operation2_typed f (of_atom (amap pw aP)) (of_atom (amap pw bP))) as [[t0 sp] |] eqn:Ht2;
    [| discriminate].
  injection Htc as <-.
  pose proof (atom_type k aP va Ha1 Ha) as Hta; pose proof (atom_type k bP vb Hb1 Hb) as Htb.
  destruct (avoid_spell k aP j HaN) as [A1 [A2 [A3 A4]]].
  destruct (avoid_spell k bP j HbN) as [B1 [B2 [B3 B4]]].
  destruct va as [[x dx] | za | | |], vb as [[y dy] | zb | | |]; cbn [eval_op2] in Hev; try discriminate.
  - (* two reals *)
    simpl in Hta, Htb; destruct (of_atom (amap pw aP)) eqn:Ea; try contradiction.
    destruct (of_atom (amap pw bP)) eqn:Eb; try contradiction.
    apply op2_real_type in Ht2; subst t0.
    destruct (comparison f) eqn:Hcmp; simpl.
    + (* a comparison: a boolean, not varied *)
      cbn [dom_cmp duals dual_cmp] in Hev.
      destruct (dom_cmp reals f x y) as [bo |] eqn:Hcy; [| discriminate]; injection Hev as <-.
      split; [lia | split; [exact I | split; [intros _; exact I | split; [discriminate |]]]].
      exists (store_set s (keyv (DBound (j, j))) (VBool bo)).
      split; [apply run_define; rewrite xev_DOp2, Hsa, Hsb; simpl; rewrite Hcmp; simpl in Hcy |- *;
              rewrite Hcy; reflexivity |].
      split; [apply frame_set; [apply frame_refl | reflexivity | auto] |].
      split; [rewrite store_get_set_same; reflexivity |].
      intros [H | H]; [discriminate | contradiction].
    + (* an arithmetic operation *)
      cbn [dom_op2 duals] in Hev.
      destruct (dual_op2 R reals f (Dual x dx) (Dual y dy)) as [[z dz] |] eqn:Hd; [| discriminate].
      injection Hev as <-.
      destruct (partial2 f (amap pt aP) (amap pt bP)) as [[qa qb] |] eqn:Hp;
        [| destruct f; simpl in Hp; try discriminate; simpl in Ho2; discriminate].
      assert (Hda := dot_ok k s aP _ HaS Ha); assert (Hdb := dot_ok k s bP _ HbS Hb).
      pose proof (tvaried_amap k aP Ha1) as Hva; pose proof (tvaried_amap k bP Hb1) as Hvb.
      assert (Hza : varied (amap pa aP) = false -> dx = 0)
        by (intros Hz; exact (atom_zero k aP _ Ha1 Hz Ha)).
      assert (Hzb : varied (amap pa bP) = false -> dy = 0)
        by (intros Hz; exact (atom_zero k bP _ Hb1 Hz Hb)).
      destruct (varied (amap pa aP) || varied (amap pa bP)) eqn:Hvr; simpl.
      * assert (Hvr' : tvaried_atom (amap pt aP) || tvaried_atom (amap pt bP) = true)
          by (rewrite Hva, Hvb; exact Hvr).
        destruct (tangent_op2 s f (amap pt aP) (amap pt bP) x y dx dy z dz qa qb Hsa Hsb
                    (fun _ => Hda) (fun H => Hza (eq_trans (eq_sym Hva) H))
                    (fun _ => Hdb) (fun H => Hzb (eq_trans (eq_sym Hvb) H)) Hd Hp Hvr')
          as [Hv Ht].
        split; [lia | split; [exact I | split; [discriminate | split; [intros _; exact I |]]]].
        exists (store_set (store_set s (keyv (DBound (j, j))) (VReal z)) (keyv (DotOf (DBound (j, j)))) (VReal dz)).
        split; [apply run_define2; [exact Hv | rewrite xev_set_other; [exact Ht |]] |].
        { apply avoid_partial2 with (f := f); auto. }
        split; [apply frame_set; [apply frame_set; [apply frame_refl | reflexivity | auto] | reflexivity | auto] |].
        split; [rewrite store_get_set_other, store_get_set_same; [reflexivity | apply not_eq_sym, keyv_dot_neq] |].
        intros _; rewrite store_get_set_same; reflexivity.
      * apply orb_false_iff in Hvr as [Hva0 Hvb0].
        rewrite (Hza Hva0), (Hzb Hvb0) in Hd.
        split; [lia | split; [exact I | split; [intros _; exact (dual_op2_zero f x y z dz Hd) |]]].
        split; [discriminate |].
        assert (Hv : xev s (DOp2 f (spell (amap pt aP)) (spell (amap pt bP))) = Some (VReal z)).
        { rewrite xev_DOp2, Hsa, Hsb; simpl; rewrite Hcmp.
          destruct f; unfold_ops Hd; try discriminate; injection Hd as <- _; reflexivity. }
        exists (store_set s (keyv (DBound (j, j))) (VReal z)).
        split; [apply run_define; exact Hv |].
        split; [apply frame_set; [apply frame_refl | reflexivity | auto] |].
        split; [rewrite store_get_set_same; reflexivity |].
        intros [H | H]; [discriminate | contradiction].
  - (* two integers *)
    rewrite (int_not_varied k aP za Ha1 Ha), (int_not_varied k bP zb Hb1 Hb).
    replace (if comparison f then false else false || false) with false
      by (destruct (comparison f); reflexivity).
    injection Hev as <-; simpl in Hta, Htb; apply has_type_int in Hta, Htb.
    rewrite Hta, Htb in Ht2.
    split; [lia | split; [exact (int_op2_type f za zb t0 sp Ht2) |]].
    split; [intros _; destruct f; exact I | split; [discriminate |]].
    exists (store_set s (keyv (DBound (j, j))) (int_op2 f za zb)).
    split; [apply run_define; rewrite xev_DOp2, Hsa, Hsb; reflexivity |].
    split; [apply frame_set; [apply frame_refl | reflexivity | auto] |].
    split; [rewrite store_get_set_same, primal_int_op2; reflexivity |].
    intros [H | H]; [discriminate | contradiction].
Qed.

Lemma xev_DAt s a i :
  xev s (DAt a i) =
  match xev s a, xev s i with
  | Some (VArray l), Some (VInt z) => match nth_z z l with Some x => Some (VReal x) | None => None end
  | _, _ => None
  end.
Proof. reflexivity. Qed.

(* Reading an element of an array. *)
Lemma sim_get (aP iP : atom pv) : sim_value (AGet aP iP).
Proof.
  value_intro. simpl in Htc, Hev, Hst |- *.
  assert (Hlv : forall p, aP = AVar p -> In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity]).
  assert (Hlv' : forall p, iP = AVar p -> In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p)
    by (intros p E; split; [auto | subst; unfold live_value; simpl; rewrite Nat.eqb_refl, orb_true_r; reflexivity]).
  assert (Hop := operand_ok _ _ _ _ _ _ _ _ aP j Hc Hlv Hst).
  assert (Hop' := operand_ok _ _ _ _ _ _ _ _ iP j Hc Hlv' Hst).
  assert (HaS : forall p, aP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hop; auto).
  assert (HaN : forall p, aP = AVar p -> static_ok k p /\ pn p <> j) by (intros; apply Hop; auto).
  assert (Ha1 : forall p, aP = AVar p -> static_ok k p) by (intros; apply HaS; auto).
  assert (HiS : forall p, iP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hop'; auto).
  assert (HiN : forall p, iP = AVar p -> static_ok k p /\ pn p <> j) by (intros; apply Hop'; auto).
  destruct (aeval_atom (duals reals) (amap pd aP)) as [[| | | l |] |] eqn:Ha; try discriminate;
    destruct (aeval_atom (duals reals) (amap pd iP)) as [[| z | | |] |] eqn:Hi; try discriminate.
  destruct (nth_z z l) as [d |] eqn:Hn; [| discriminate]; injection Hev as <-.
  crush_match Htc; injection Htc as <-.
  destruct (avoid_spell k aP j HaN) as [A1 [A2 [A3 A4]]].
  destruct (avoid_spell k iP j HiN) as [B1 [B2 [B3 B4]]].
  assert (Hsa := spell_ok k s aP _ HaS Ha); assert (Hsi := spell_ok k s iP _ HiS Hi).
  assert (Hv : xev s (DAt (spell (amap pt aP)) (spell (amap pt iP))) = Some (VReal (dfst d))).
  { rewrite xev_DAt, Hsa, Hsi; simpl; rewrite nth_z_map, Hn; reflexivity. }
  rewrite (tvaried_amap k aP Ha1).
  destruct (varied (amap pa aP)) eqn:Hvr; simpl.
  - (* a varied array: a variable, with a tangent *)
    destruct aP as [p | |]; simpl in Ha; try discriminate; injection Ha as Ha.
    destruct (HaS p eq_refl) as [[_ [_ [Hstp [_ [_ [Hdot _]]]]]] [_ Hsd]].
    assert (Hd : xev s (DAt (dot (amap pt (AVar p))) (spell (amap pt iP))) = Some (VReal (dsnd d))).
    { simpl in Hvr |- *; rewrite Hdot, Hvr, xev_DAt, Hsi; simpl; rewrite Hstp.
      change (xev s (DVar (DotOf (stored p)))) with (store_get s (keyv (DotOf (stored p)))).
      rewrite (Hsd (eq_trans Hdot Hvr)), Ha; simpl; rewrite nth_z_map, Hn; reflexivity. }
    split; [lia | split; [exact I | split; [discriminate | split; [intros _; exact I |]]]].
    exists (store_set (store_set s (keyv (DBound (j, j))) (VReal (dfst d))) (keyv (DotOf (DBound (j, j)))) (VReal (dsnd d))).
    split; [apply run_define2; [exact Hv | rewrite xev_set_other; [exact Hd | apply avoid_at; auto]] |].
    split; [apply frame_set; [apply frame_set; [apply frame_refl | reflexivity | auto] | reflexivity | auto] |].
    split; [rewrite store_get_set_other, store_get_set_same; [reflexivity | apply not_eq_sym, keyv_dot_neq] |].
    intros _; rewrite store_get_set_same; reflexivity.
  - split; [lia | split; [exact I | split; [| split; [discriminate |]]]].
    + intros _; pose proof (atom_zero k aP _ Ha1 Hvr Ha) as Hz; simpl in Hz |- *.
      exact (nth_z_Forall _ z l d Hz Hn).
    + exists (store_set s (keyv (DBound (j, j))) (VReal (dfst d))).
      split; [apply run_define; exact Hv |].
      split; [apply frame_set; [apply frame_refl | reflexivity | auto] |].
      split; [rewrite store_get_set_same; reflexivity |].
      intros [Hq | Hq]; [discriminate | contradiction].
Qed.

Lemma run_assign_at s n ei ev l z e l1 :
  store_get s (keyv n) = Some (VArray l) -> xev s ei = Some (VInt z) -> xev s ev = Some (VReal e) ->
  replace_nth_z z e l = Some l1 ->
  run [DAssign (DAt (DVar n) ei) ev] s = Some (store_set s (keyv n) (VArray l1)).
Proof.
  intros Hn Hi Hv Hr; unfold run, xev, keyv in *; simpl; rewrite Hv; simpl.
  rewrite Hn, Hi, Hr; reflexivity.
Qed.

Lemma run_two st1 st2 s s1 s2 : run [st1] s = Some s1 -> run [st2] s1 = Some s2 -> run [st1; st2] s = Some s2.
Proof. intros H1 H2; change [st1; st2] with ([st1] ++ [st2])%list; rewrite run_app, H1; exact H2. Qed.

(* Two live variables with the storage updated in place are the same. *)
Lemma live_owner L k c s wP pp live ty o p :
  ctx_ok L k c s wP pp live ty -> owner wP pp = Some o -> In p L -> live p -> live o ->
  pn p = pn o -> p = o.
Proof.
  intros Hc Ho Hp Lp Lo E.
  destruct (c_owner _ _ _ _ _ _ _ _ Hc o p Ho Hp E); [auto | contradiction].
Qed.

(* An update of an array, at the end of the body of an in-place loop. *)
Lemma sim_set (aP iP vP : atom pv) : sim_value (ASet aP iP vP).
Proof.
  value_intro. simpl in Htc, Hev |- *.
  destruct pp as [| | | ix sx]; simpl in Htc; try discriminate.
  destruct (of_atom (amap pw aP)) as [| | | z] eqn:Eat; try discriminate.
  destruct tail; simpl in Htc; [| discriminate].
  destruct aP as [a | |]; simpl in Htc, Eat; try discriminate.
  destruct ((vid (pw a) =? vid (pw sx))%nat) eqn:Ea; simpl in Htc; [| discriminate].
  destruct (ty_eqb (of_atom (amap pw vP)) Real) eqn:Ev; simpl in Htc; [| discriminate].
  apply ty_eqb_true in Ev; crush_match Htc; injection Htc as <-.
  pose proof (c_place _ _ _ _ _ _ _ _ Hc) as [Hix [Hsx [Hixt [Hsxt [Hsxv [Hixg Hsxg]]]]]].
  assert (Ha : In a L) by auto.
  pose proof (same_vid _ _ _ _ _ _ _ _ _ _ Hc Ha Hsx Ea); subst a.
  simpl in Hst; injection Hst as Hj'; subst j.
  assert (Hlsx : live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) sx)
    by (unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity).
  simpl in Hev; destruct (pd sx) as [| | | l |] eqn:Hsxd; try discriminate.
  destruct (aeval_atom (duals reals) (amap pd iP)) as [[| zi | | |] |] eqn:Hi; try discriminate.
  destruct (aeval_atom (duals reals) (amap pd vP)) as [[d | | | |] |] eqn:Hv; try discriminate.
  destruct (replace_nth_z zi d l) as [l1 |] eqn:Hr; [| discriminate]; injection Hev as <-.
  (* the index and the value are not stored in the array *)
  assert (Hlv : forall p, iP = AVar p \/ vP = AVar p ->
            In p L /\ live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p)
    by (intros p [E | E]; subst; split; auto; unfold live_value; simpl;
        rewrite Nat.eqb_refl, ?orb_true_r; reflexivity).
  assert (Hnot : forall p, iP = AVar p \/ vP = AVar p -> pn p <> pn sx).
  { intros p E Ep; destruct (Hlv p E) as [Hp Lp].
    pose proof (live_owner _ _ _ _ _ _ _ _ sx p Hc eq_refl Hp Lp Hlsx Ep); subst p.
    destruct E as [E | E]; subst; simpl in Hi, Hv; congruence. }
  assert (Hopi := operand_ok2 _ _ _ _ _ _ _ _ iP (pn sx) Hc (fun p E => Hlv p (or_introl E))
                    (fun p E => Hnot p (or_introl E))).
  assert (Hopv := operand_ok2 _ _ _ _ _ _ _ _ vP (pn sx) Hc (fun p E => Hlv p (or_intror E))
                    (fun p E => Hnot p (or_intror E))).
  assert (HiS : forall p, iP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hopi; auto).
  assert (HiN : forall p, iP = AVar p -> static_ok k p /\ pn p <> pn sx) by (intros; apply Hopi; auto).
  assert (HvS : forall p, vP = AVar p -> static_ok k p /\ store_ok s p) by (intros; apply Hopv; auto).
  assert (HvN : forall p, vP = AVar p -> static_ok k p /\ pn p <> pn sx) by (intros; apply Hopv; auto).
  destruct (avoid_spell k iP (pn sx) HiN) as [A1 [A2 [A3 A4]]].
  destruct (avoid_spell k vP (pn sx) HvN) as [B1 [B2 [B3 B4]]].
  assert (Hsi := spell_ok k s iP _ HiS Hi); assert (Hsv := spell_ok k s vP _ HvS Hv).
  assert (Hdv := dot_ok k s vP _ HvS Hv).
  pose proof (static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hsx) as Hsxs.
  destruct Hsxs as [_ [_ [_ [_ [_ [Hdot [_ [_ [Hht _]]]]]]]]].
  destruct (c_store _ _ _ _ _ _ _ _ Hc sx Hsx Hlsx) as [S1 S2].
  rewrite Hsxd in S1, S2, Hht; specialize (S2 (eq_trans Hdot Hsxv)).
  simpl in Hsxv |- *; rewrite Hsxv; simpl.
  set (s1 := store_set s (keyv (stored sx)) (VArray (map dfst l1))).
  assert (Hrun1 : run [DAssign (DAt (DVar (stored sx)) (spell (amap pt iP))) (spell (amap pt vP))] s = Some s1).
  { apply (run_assign_at s _ _ _ (map dfst l) zi (dfst d)); auto.
    rewrite replace_nth_z_map, Hr; reflexivity. }
  assert (Hrun2 : run [DAssign (DAt (DVar (DotOf (stored sx))) (spell (amap pt iP))) (dot (amap pt vP))] s1 =
                  Some (store_set s1 (keyv (DotOf (stored sx))) (VArray (map dsnd l1)))).
  { apply (run_assign_at s1 _ _ _ (map dsnd l) zi (dsnd d)).
    - unfold s1; rewrite store_get_set_other; [exact S2 | apply keyv_dot_neq].
    - unfold s1; rewrite xev_set_other; auto.
    - unfold s1; rewrite xev_set_other; auto.
    - rewrite replace_nth_z_map, Hr; reflexivity. }
  split; [lia | split; [simpl in Hht |- *; rewrite Eat in Hht; rewrite (replace_nth_z_length _ _ _ _ Hr); simpl in Hht; congruence |]].
  split; [discriminate | split; [intros _; exact I |]].
  exists (store_set s1 (keyv (DotOf (stored sx))) (VArray (map dsnd l1))).
  split; [exact (run_two _ _ _ _ _ Hrun1 Hrun2) |].
  split; [apply frame_set; [unfold s1; apply frame_set; [apply frame_refl | reflexivity | auto]
                           | reflexivity | auto] |].
  split; [rewrite store_get_set_other; [unfold s1; rewrite store_get_set_same; reflexivity |
          apply not_eq_sym, keyv_dot_neq] |].
  intros _; rewrite store_get_set_same; reflexivity.
Qed.

Lemma run_realvar x ss s :
  run (DRealVar x :: ss) s = run ss (store_set s (keyv x) (VReal 0)).
Proof.
  unfold run, keyv; cbn [map out_dstmt exec_stmts exec].
  change (dom_lit reals "0") with (real_lit "0"); rewrite lit_0; reflexivity.
Qed.

Lemma run_branch e t f ss s b :
  xev s e = Some (VBool b) ->
  run (DBranch e t f :: ss) s =
  match run (if b then t else f) s with Some s1 => run ss s1 | None => None end.
Proof.
Proof.
  intros H; unfold run; cbn [map out_dstmt exec_stmts exec]; unfold xev in H; rewrite H.
  destruct b; reflexivity.
Qed.

Lemma run_for i lo hi b ss s l h :
  xev s lo = Some (VInt l) -> xev s hi = Some (VInt h) ->
  run (DFor i lo hi b :: ss) s =
  match exec_up R (run b) (out_dvar nat i) l (count l h) s with Some s1 => run ss s1 | None => None end.
Proof.
  intros Hl Hh; unfold run; cbn [map out_dstmt exec_stmts exec]; unfold xev in Hl, Hh; rewrite Hl, Hh.
  reflexivity.
Qed.

Lemma run_assign_var s x e v ss :
  xev s e = Some v -> run (DAssign (DVar x) e :: ss) s = run ss (store_set s (keyv x) v).
Proof. intros H; unfold run, xev, keyv in *; cbn [map out_dstmt exec_stmts exec]; rewrite H; reflexivity. Qed.

(* Writes to the keys of another variable keep a variable related. *)
Lemma store_ok_set s p k v :
  k <> keyv (stored p) -> k <> keyv (DotOf (stored p)) -> store_ok s p -> store_ok (store_set s k v) p.
Proof.
  intros H1 H2 [S1 S2]; split; [rewrite store_get_set_other; auto |].
  intros Hd; rewrite store_get_set_other; auto.
Qed.

Lemma keyv_bound_neq j j' : j <> j' ->
  keyv (DBound (j, j)) <> keyv (DBound (j', j')) /\ keyv (DBound (j, j)) <> keyv (DotOf (DBound (j', j'))) /\
  keyv (DotOf (DBound (j, j))) <> keyv (DBound (j', j')) /\
  keyv (DotOf (DBound (j, j))) <> keyv (DotOf (DBound (j', j'))).
Proof. intros H; unfold keyv; simpl; repeat split; intros E; inversion E; auto. Qed.

(* The context of a branch or of a loop body without storage updated in
   place, from the context of the value. *)
Lemma ctx_sub L k c s s0 wP pp pp' (live live' : pv -> Prop) ty :
  ctx_ok L k c s wP pp live ty -> owner wP pp' = None -> pp' <> PTop -> place_ok L pp' ->
  (forall p, live' p -> live p) ->
  (forall p, In p L -> live p -> store_ok s p -> store_ok s0 p) ->
  ctx_ok L k c s0 wP pp' live' Real.
Proof.
  intros Hc Ho Hpp Hpl Hl Hs; destruct Hc; constructor; auto; intros; congruence.
Qed.

Lemma frame_chain c c' ex s s0 s1 :
  frame c ex s s0 -> frame c' None s0 s1 -> (c <= c')%nat -> frame c ex s s1.
Proof.
  intros F1 F2 Hc v Hb Hcv Hex; rewrite (F2 v (below_mono _ _ _ Hb Hc) Hcv); [apply F1; auto |].
  intros m E; discriminate.
Qed.

(* A result expression avoids a variable below c' that no variable in scope
   is stored in. *)
Lemma res_vars_avoid L live c' e j :
  res_vars L live c' e -> (j < c')%nat -> (forall p, In p L -> pn p <> j) ->
  avoid (keyv (DBound (j, j))) e /\ avoid (keyv (DotOf (DBound (j, j)))) e.
Proof.
  intros H Hj Hn; split; intros x Hx E; destruct (H x Hx) as [[p [Hp [_ [-> | ->]]]] | [Hb Hcx]];
    try (unfold keyv, stored in E; simpl in E; inversion E; apply (Hn p Hp); auto; fail);
    apply keyv_inj in E; simpl; auto; subst x; simpl in Hb; lia.
Qed.

(* The end of a branch: its value and tangent stored in n. *)
Lemma ite_tail L live c' j s0 s1 st vt dt (vr : bool) x dx :
  run st s0 = Some s1 -> xev s1 vt = Some (VReal x) -> xev s1 dt = Some (VReal dx) ->
  res_vars L live c' dt -> (j < c')%nat -> (forall p, In p L -> pn p <> j) ->
  run (st ++ (if vr then [DAssign (DVar (DBound (j, j))) vt; DAssign (DVar (DotOf (DBound (j, j)))) dt]
              else [DAssign (DVar (DBound (j, j))) vt]))%list s0 =
  Some (if vr then store_set (store_set s1 (keyv (DBound (j, j))) (VReal x)) (keyv (DotOf (DBound (j, j)))) (VReal dx)
        else store_set s1 (keyv (DBound (j, j))) (VReal x)).
Proof.
  intros Hr Hv Hd Hres Hj Hn; rewrite run_app, Hr.
  destruct (res_vars_avoid L live c' dt j Hres Hj Hn) as [A1 A2].
  destruct vr; rewrite run_assign_var with (v := VReal x) by exact Hv; [| reflexivity].
  rewrite run_assign_var with (v := VReal dx); [reflexivity |].
  rewrite xev_set_other; auto.
Qed.

(* A branch: the condition is a boolean in the store, the generated code
   runs the statements of the branch taken, then stores its value and
   tangent in n. *)
Lemma sim_ite (cP : atom pv) (tP eP : anf pv bare) :
  sim_body tP -> sim_body eP -> sim_value (AIte cP tP eP).
Proof.
  intros IHt IHe.
  value_intro. simpl in Htc, Hev, Hst |- *.
  rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT, t2 into tD, e2 into eD.
  (* typing *)
  assert (Hnot : forall ix sx, pp <> PArray ix sx) by (intros ix sx ->; simpl in Htc; discriminate).
  assert (Hpp : pp = PTop \/ pp = PBranch \/ pp = PScalar)
    by (destruct pp as [| | | ix sx]; auto; destruct (Hnot ix sx eq_refl)).
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
  assert (Hn : forall p, In p L -> pn p <> j)
    by (intros p Hp E; destruct (Hst p Hp) as [H' _]; apply H'; unfold stored; rewrite E; reflexivity).
  destruct (aeval_atom (duals reals) (amap pd cP)) as [[| | b | |] |] eqn:Hcd; try discriminate.
  assert (Hlc : forall p, cP = AVar p -> static_ok k p /\ store_ok s p).
  { intros p ->; split; [apply (static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc)); auto |].
    apply (c_store _ _ _ _ _ _ _ _ Hc); auto; unfold live_value; simpl; rewrite Nat.eqb_refl; reflexivity. }
  pose proof (spell_ok k s cP _ Hlc Hcd) as Hsc; simpl in Hsc.
  (* the two bodies, opened *)
  rewrite open_pairs_sbind.
  destruct (open_pairs (tan W (option_map (amap pt) wP) (rebuild (tvar W) tT (annotate_body_t false Replay k tA))) c)
    as [[st [vt dt]] c1] eqn:Hot.
  rewrite open_pairs_sbind.
  destruct (open_pairs (tan W (option_map (amap pt) wP) (rebuild (tvar W) eT (annotate_body_t false Replay k eA))) c1)
    as [[se' [ve' de']] c2] eqn:Hoe.
  pose proof (open_pairs_mono (tan W (option_map (amap pt) wP) (rebuild (tvar W) tT (annotate_body_t false Replay k tA))) c) as M1.
  pose proof (open_pairs_mono (tan W (option_map (amap pt) wP) (rebuild (tvar W) eT (annotate_body_t false Replay k eA))) c1) as M2.
  rewrite Hot in M1; rewrite Hoe in M2; simpl in M1, M2.
  cbn zeta; unfold tan_ite.
  set (vr := varied_anf k tA || varied_anf k eA).
  set (n := DBound (j, j)).
  set (s0 := if vr then store_set (store_set s (keyv n) (VReal 0)) (keyv (DotOf n)) (VReal 0)
             else store_set s (keyv n) (VReal 0)).
  assert (Hs0 : forall p, In p L -> store_ok s p -> store_ok s0 p).
  { intros p Hp Hs; pose proof (keyv_bound_neq j (pn p) (fun E => Hn p Hp (eq_sym E))) as [K1 [K2 [K3 K4]]].
    unfold s0; destruct vr; repeat apply store_ok_set; auto. }
  assert (Hfr0 : frame c (Some n) s s0)
    by (unfold s0; destruct vr;
        [apply frame_set; [apply frame_set; [apply frame_refl | reflexivity | auto] | reflexivity | auto]
        | apply frame_set; [apply frame_refl | reflexivity | auto]]).
  assert (Hc0 : forall pp' bW, (pp' = PBranch) ->
                (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
                ctx_ok L k c s0 wP pp' (live_anf k bW) Real).
  { intros pp' bW -> Hl; apply (ctx_sub L k c s s0 wP pp PBranch (live_value k (AIte (amap pw cP) tW eW))
                                 (live_anf k bW) ty Hc); auto; [discriminate | simpl; exact I]. }
  (* the condition, read after the definitions of n *)
  assert (Hcn : forall p, cP = AVar p -> static_ok k p /\ pn p <> j)
    by (intros p E; split; [apply Hlc; auto | apply Hn; subst; auto]).
  destruct (avoid_spell k cP j Hcn) as [C1 [_ [C3 _]]].
  assert (Hsc0 : xev s0 (spell (amap pt cP)) = Some (VBool b))
    by (unfold s0; destruct vr; rewrite ?xev_set_other; auto).
  (* the branch taken *)
  assert (Hbody : exists sb vb db cb s1 x dx,
            run sb s0 = Some s1 /\ frame cb None s0 s1 /\ (c <= cb)%nat /\
            xev s1 vb = Some (VReal x) /\ xev s1 db = Some (VReal dx) /\ (exists lv, res_vars L lv cb db) /\
            ve = VReal (Dual x dx) /\ (vr = false -> dx = 0) /\
            (if b then st else se') = sb /\ (if b then vt else ve') = vb /\ (if b then dt else de') = db).
  { destruct b.
    - assert (Hl : forall p, live_anf k tW p -> live_value k (AIte (amap pw cP) tW eW) p)
        by (unfold live_anf, live_value; intros p H'; simpl; rewrite H', orb_true_r; reflexivity).
      specialize (IHt L k c s0 wP PBranch Replay tA tW tT tD Real ve H9 H6 H3 H0
                    (Hc0 PBranch tW eq_refl Hl) I HtW Hev).
      rewrite Hot in IHt; destruct IHt as [_ [Hht [Hz [_ [Hrv [s1 [Hrun [Hfr [Hv Hd]]]]]]]]].
      destruct ve as [[x dx] | | | |]; try contradiction.
      exists st, vt, dt, c, s1, x, dx; repeat split; eauto.
      intros Hv0; apply orb_false_iff in Hv0 as [Hv0 _]; exact (Hz Hv0).
    - assert (Hl : forall p, live_anf k eW p -> live_value k (AIte (amap pw cP) tW eW) p)
        by (unfold live_anf, live_value; intros p H'; simpl; rewrite H', !orb_true_r; reflexivity).
      assert (Hce : ctx_ok L k c1 s0 wP PBranch (live_anf k eW) Real)
        by (apply (ctx_weaken L k c c1 s0 wP PBranch (live_anf k eW)); auto).
      specialize (IHe L k c1 s0 wP PBranch Replay eA eW eT eD Real ve H10 H7 H4 H1 Hce I HeW Hev).
      rewrite Hoe in IHe; destruct IHe as [_ [Hht [Hz [_ [Hrv [s1 [Hrun [Hfr [Hv Hd]]]]]]]]].
      destruct ve as [[x dx] | | | |]; try contradiction.
      exists se', ve', de', c1, s1, x, dx; repeat split; eauto; try lia.
      intros Hv0; apply orb_false_iff in Hv0 as [_ Hv0]; exact (Hz Hv0). }
  destruct Hbody as [sb [vb [db [cb [s1 [x [dx [Hrun [Hfr [Hcb [Hv [Hd [[lv Hrv] [-> [Hz [Esb [Evb Edb]]]]]]]]]]]]]]]]].
  assert (Hj' : (j < cb)%nat) by lia.
  split; [lia | split; [exact I | split; [intros Hv0; simpl; exact (Hz Hv0) | split; [intros _; exact I |]]]].
  exists (if vr then store_set (store_set s1 (keyv n) (VReal x)) (keyv (DotOf n)) (VReal dx)
          else store_set s1 (keyv n) (VReal x)).
  assert (Hfr1 : frame c (Some n) s s1) by exact (frame_chain c cb _ s s0 s1 Hfr0 Hfr Hcb).
  destruct vr eqn:Hvr; simpl.
  - split.
    + pose proof (ite_tail L lv cb j s0 s1 sb vb db true x dx Hrun Hv Hd Hrv Hj' Hn) as Htail2.
      rewrite !run_realvar, run_branch with (b := b) by exact Hsc0.
      destruct b; subst sb vb db; fold n in Htail2 |- *; unfold s0 in Htail2; simpl in Htail2;
        match goal with |- (match ?r with _ => _ end) = _ => replace r with (Some (store_set (store_set s1 (keyv n) (VReal x)) (keyv (DotOf n)) (VReal dx))) by (symmetry; exact Htail2) end; reflexivity.
    + split; [apply frame_set; [apply frame_set; [exact Hfr1 | reflexivity | auto] | reflexivity | auto] |].
      split; [rewrite store_get_set_other, store_get_set_same; [reflexivity | apply not_eq_sym, keyv_dot_neq] |].
      intros _; rewrite store_get_set_same; reflexivity.
  - split.
    + pose proof (ite_tail L lv cb j s0 s1 sb vb db false x dx Hrun Hv Hd Hrv Hj' Hn) as Htail2.
      rewrite !run_realvar, run_branch with (b := b) by exact Hsc0.
      destruct b; subst sb vb db; fold n in Htail2 |- *; unfold s0 in Htail2; simpl in Htail2;
        match goal with |- (match ?r with _ => _ end) = _ => replace r with (Some (store_set s1 (keyv n) (VReal x))) by (symmetry; exact Htail2) end; reflexivity.
    + split; [apply frame_set; [exact Hfr1 | reflexivity | auto] |].
      split; [rewrite store_get_set_same; reflexivity |].
      intros [Hq | Hq]; [discriminate | contradiction].
Qed.
