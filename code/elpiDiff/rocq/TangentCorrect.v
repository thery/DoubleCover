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

From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

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
elim: a b => [x | a IH | a IH | a IH |] [y | b | b | b |] /=;
  try (split; [discriminate | move=> E; discriminate E]).
- by rewrite Nat.eqb_eq; split=> [-> | [->]].
- by rewrite IH; split=> [-> | [->]].
- by rewrite IH; split=> [-> | [->]].
- by rewrite IH; split=> [-> | [->]].
by [].
Qed.

Lemma key_eqb_eq (a b : key) : key_eqb a b = true <-> a = b.
Proof.
case: a b => [x |] [y |] /=;
  try (split; [discriminate | move=> E; discriminate E]).
  by rewrite dvar_eqb_eq; split=> [-> | [->]].
by [].
Qed.

Lemma key_eqb_refl (a : key) : key_eqb a a = true.
Proof. by apply/key_eqb_eq. Qed.

(* Reading a store after a write. *)
Lemma store_get_set (s : store R) k v k' :
  store_get (store_set s k v) k' = if key_eqb k k' then Some v else store_get s k'.
Proof.
elim: s => [| [k0 w] s IH] //=.
case E0: (key_eqb k0 k).
  move/key_eqb_eq: E0 => E0; subst k0.
  by rewrite /=; case: (key_eqb k k').
rewrite /=; case E1: (key_eqb k0 k'); rewrite ?IH; last by [].
move/key_eqb_eq: E1 => E1; subst k'.
case E2: (key_eqb k k0) => //.
by move/key_eqb_eq: E2 => E2; subst; rewrite key_eqb_refl in E0.
Qed.

(* Executing a block in two parts. *)
Lemma exec_stmts_app (l1 l2 : list (dstmt nat)) s :
  exec_stmts reals (l1 ++ l2) s = match exec_stmts reals l1 s with Some s1 => exec_stmts reals l2 s1 | None => None end.
Proof.
elim: l1 s => [| st l1 IH] s //=.
by case: (exec reals st s) => [s1 |] //; apply: IH.
Qed.

Lemma run_app ss1 ss2 s :
  run (ss1 ++ ss2) s = match run ss1 s with Some s1 => run ss2 s1 | None => None end.
Proof. by rewrite /run map_app; apply: exec_stmts_app. Qed.

Lemma run_cons st ss s :
  run (st :: ss) s = match exec reals (out_dstmt nat st) s with Some s1 => run ss s1 | None => None end.
Proof. by []. Qed.

Lemma run_nil s : run [] s = Some s.
Proof. by []. Qed.

(* The literals the tangent programs use. *)
Lemma lit_0 : real_lit "0" = Some 0.
Proof.
rewrite /real_lit; vm_compute (read_literal _); rewrite /Q2R /=.
by congr Some; ring.
Qed.

Lemma lit_1 : real_lit "1" = Some 1.
Proof.
rewrite /real_lit; vm_compute (read_literal _); rewrite /Q2R /=.
by congr Some; rewrite Rinv_1; ring.
Qed.

Lemma lit_m1 : real_lit "-1" = Some (-1).
Proof.
rewrite /real_lit; vm_compute (read_literal _); rewrite /Q2R /=.
by congr Some; rewrite Rinv_1; ring.
Qed.

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


(* The facts of a context that do not depend on the store. *)
Record sctx (L : list pv) (k c : nat) (wP : option (atom pv)) (pp : pplace)
  (live : pv -> Prop) (ty : ty) : Prop := {
  s_static : Forall (static_ok k) L;
  s_unique : ids_unique L;
  s_num : forall p, In p L -> (pn p < c)%nat;
  s_written : forall a, wP = Some a ->
      exists y, a = AVar y /\ In y L /\ varg (pw y) <> None;
  s_place : place_ok L pp;
  s_owner : forall o p, owner wP pp = Some o -> In p L -> pn p = pn o -> p = o \/ ~ live p;
  s_arrays : forall p o, In p L -> live p -> is_array (vty (pw p)) ->
      (varg (pw p) = None \/ wP = Some (AVar p)) -> owner wP pp = Some o -> pn p = pn o;
  s_ty : is_array ty -> owner wP pp <> None;
  s_top : forall y, pp = PTop -> wP = Some (AVar y) -> is_array (vty (pw y)) ->
      ty = vty (pw y) /\ (live y -> avaried (pa y) = true)
}.

Lemma ctx_sctx L k c s wP pp live ty : ctx_ok L k c s wP pp live ty -> sctx L k c wP pp live ty.
Proof.
move=> [HS HU HN HSt HW HP HO HI HA HT HTop]; constructor=> //.
by move=> y H1 H2 H3; case: (HTop y H1 H2 H3) => [A [B _]].
Qed.

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
Proof. by []. Qed.

Lemma xev_DOp2 s f e1 e2 :
  xev s (DOp2 f e1 e2) =
  match xev s e1 with
  | Some va => match xev s e2 with Some vb => eval_op2 reals f va vb | None => None end
  | None => None end.
Proof. by []. Qed.

Lemma xev_DReal s l : xev s (DReal l) = match real_lit l with Some x => Some (VReal x) | None => None end.
Proof. by []. Qed.

Lemma tangent_op1 s f (a : atom (tvar W)) e x dx y dy p :
  xev s (spell a) = Some (VReal x) -> xev s e = Some (VReal dx) ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) -> partial1 f a = Some p ->
  xev s (DOp1 f (spell a)) = Some (VReal y) /\ xev s (scale (spell_partial p) e) = Some (VReal dy).
Proof.
move=> Ha He Hd Hp; rewrite xev_DOp1 Ha.
destruct f as [| | | | | | k |]; unfold_ops Hd; unfold_ops Hp; try discriminate;
  try (injection Hp as <-); rewrite /=.
- (* Neg *)
  rewrite lit_m1 in Hd; case: Hd => <- <-; split; first by [].
  by rewrite xev_DOp1 He /=; congr (Some (VReal _)); ring.
- (* Sin *)
  case: Hd => <- <-; split; first by [].
  by rewrite xev_DOp2 xev_DOp1 Ha He.
- (* Cos *)
  case: Hd => <- <-; split; first by [].
  by rewrite xev_DOp2 !xev_DOp1 Ha He.
- (* Exp *)
  case: Hd => <- <-; split; first by [].
  by rewrite xev_DOp2 xev_DOp1 Ha He.
- (* Log *)
  rewrite lit_1 in Hd; case: Hd => <- <-; split; first by [].
  by rewrite !xev_DOp2 xev_DReal lit_1 Ha He.
- (* Sqrt *)
  rewrite lit_1 in Hd; move: Hd; case E2: (real_lit "2") => [two |] // Hd.
  case: Hd => <- <-; split; first by [].
  by rewrite !xev_DOp2 !xev_DReal lit_1 E2 xev_DOp1 Ha He.
(* Pow *)
case: k Hp Hd => [| k | k] Hp Hd.
- case: Hp => <-; rewrite lit_0 in Hd; case: Hd => <- <-.
  split; first by [].
  by rewrite /= xev_DOp2 xev_DReal lit_0 He.
- move: Hp Hd.
  case Ek: (real_lit (NilZero.string_of_int (Z.to_int (Z.pos k))))
    => [kb |] // [<-] [<- <-].
  split; first by [].
  by rewrite /= !xev_DOp2 xev_DReal /z_to_string Ek xev_DOp1 Ha He.
move: Hp Hd.
case Ek: (real_lit (NilZero.string_of_int (Z.to_int (Z.neg k))))
  => [kb |] // [<-] [<- <-].
split; first by [].
by rewrite /= !xev_DOp2 xev_DReal /z_to_string Ek xev_DOp1 Ha He.
Qed.

(* scale p e computes the product p * e, omitting a factor 1 or -1. *)
Lemma xev_scale s p e q r :
  xev s p = Some (VReal q) -> xev s e = Some (VReal r) -> xev s (scale p e) = Some (VReal (q * r)).
Proof.
move=> Hp He; case: p Hp => [x | s0 | z | a i | f a | f a b] Hp;
  try by rewrite /= xev_DOp2 Hp He.
rewrite /scale; case E1: (String.eqb s0 "1").
  move/String.eqb_eq: E1 => E1; subst s0.
  rewrite xev_DReal lit_1 in Hp; case: Hp => <-.
  by rewrite He; congr (Some (VReal _)); ring.
case E2: (String.eqb s0 "-1").
  move/String.eqb_eq: E2 => E2; subst s0.
  rewrite xev_DReal lit_m1 in Hp; case: Hp => <-.
  by rewrite xev_DOp1 He /=; congr (Some (VReal _)); ring.
by rewrite xev_DOp2 Hp He.
Qed.

Lemma xev_sum2 s e1 e2 :
  xev s (sum [e1; e2]) = xev s (DOp2 Add e1 e2).
Proof. by []. Qed.

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
move=> Ha Hb Hda Hza Hdb Hzb Hd Hp Hv; rewrite xev_DOp2 Ha Hb /tangent_term.
destruct f; unfold_ops Hd; unfold_ops Hp; try discriminate;
  injection Hp as <- <-; injection Hd as <- <-; simpl; split; try reflexivity;
  destruct (tvaried_atom a), (tvaried_atom b); try discriminate; simpl;
  rewrite ?xev_DOp2 ?xev_DOp1 ?xev_DReal ?lit_1 ?lit_m1 ?Ha ?Hb;
  try rewrite (Hda erefl); try rewrite (Hdb erefl);
  try rewrite (Hza erefl); try rewrite (Hzb erefl); simpl;
  repeat (first [ rewrite xev_DOp2 | rewrite xev_DOp1 | rewrite xev_DReal
                | rewrite lit_1 | erewrite xev_scale by eauto | rewrite Ha
                | rewrite Hb | rewrite (Hda erefl) | rewrite (Hdb erefl) ];
          simpl);
  f_equal; f_equal; rewrite /Rdiv ?Rinv_mult; ring.
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
move=> [H1 H2]; split.
  move=> p w1 w2 [E1 | I1] [E2 | I2].
  - by inversion E1; inversion E2.
  - by inversion E1; subst; have := H2 _ _ (or_intror I2); rewrite /=; lia.
  - by inversion E2; subst; have := H2 _ _ (or_introl I1); rewrite /=; lia.
  by eauto.
move=> p w [[E | I] | [E | I]]; try (inversion E; subst; rewrite /=; lia).
all: by specialize (H2 p w); intuition lia.
Qed.

Lemma agree_atom G1 G2 k (a : atom pv) a1 a2 id :
  agree G1 G2 k -> atom_eq G1 a a1 -> atom_eq G2 a a2 -> occurs_atom id a1 = occurs_atom id a2.
Proof.
case=> H _; case: a a1 a2 => [x | ? | ?] [? | ? | ?] [? | ? | ?] //=.
by move=> I1 I2; rewrite (H _ _ _ I1 I2).
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
apply: anf_value_ind.
- (* ALet *)
  intros [] e IHe b IHb G1 G2 [] [] id k; simpl; try contradiction.
  intros [He1 Hb1] [He2 Hb2] Hg; rewrite (IHe _ _ _ _ id k He1 He2 Hg).
  f_equal; apply (IHb (pfresh k) ((pfresh k, anon k) :: G1)
                    ((pfresh k, anon k) :: G2)); auto using agree_open.
- (* ARet *)
  intros a G1 G2 [] [] id k; simpl; try contradiction; intros.
  by eapply agree_atom; eauto.
- intros f a G1 G2 [] [] id k; simpl; try contradiction;
    intros [_ H1] [_ H2] Hg.
  by eapply agree_atom; eauto.
- intros f a b G1 G2 [] [] id k; simpl; try contradiction;
    intros [_ [A1 B1]] [_ [A2 B2]] Hg.
  by rewrite_atoms Hg.
- intros a i G1 G2 [] [] id k; simpl; try contradiction;
    intros [A1 B1] [A2 B2] Hg.
  by rewrite_atoms Hg.
- intros a i v G1 G2 [] [] id k; simpl; try contradiction;
    intros [A1 [B1 C1]] [A2 [B2 C2]] Hg.
  by rewrite_atoms Hg.
- intros c t IHt e IHe G1 G2 [] [] id k; simpl; try contradiction;
    intros [A1 [B1 C1]] [A2 [B2 C2]] Hg.
  rewrite_atoms Hg.
  by rewrite (IHt _ _ _ _ id k B1 B2 Hg) (IHe _ _ _ _ id k C1 C2 Hg).
- intros lo hi b IHb G1 G2 [] [] id k; simpl; try contradiction;
    intros [A1 [B1 C1]] [A2 [B2 C2]] Hg.
  rewrite_atoms Hg; f_equal.
  by apply (IHb (pfresh k) ((pfresh k, anon k) :: G1)
              ((pfresh k, anon k) :: G2)); auto using agree_open.
intros [] lo hi init b IHb G1 G2 [] [] id k; simpl; try contradiction;
  intros [A1 [B1 [C1 D1]]] [A2 [B2 [C2 D2]]] Hg.
rewrite_atoms Hg; f_equal.
by apply (IHb (pfresh k) (pfresh (S k))
            ((pfresh (S k), anon (S k)) :: (pfresh k, anon k) :: G1)
            ((pfresh (S k), anon (S k)) :: (pfresh k, anon k) :: G2));
  auto using agree_open.
Qed.

(* ---------------------------------------------------------------------------
   Lists: replacing an element keeps the length and the properties of the
   elements (nth_z_map and replace_nth_z_map are in Correctness.v). *)

Lemma replace_nth_length {A : Type} n (x : A) l l' :
  replace_nth n x l = Some l' -> length l' = length l.
Proof.
elim: n l l' => [| n IH] [| y l] l' //= H.
  by case: H => <-.
move: H; case E: (replace_nth n x l) => [l1 |] // [<-] /=.
by congr S; exact: IH E.
Qed.

Lemma replace_nth_z_length {A : Type} k (x : A) l l' :
  replace_nth_z k x l = Some l' -> length l' = length l.
Proof.
by rewrite /replace_nth_z; case: (k <? 0)%Z => //; apply: replace_nth_length.
Qed.

Lemma replace_nth_Forall {A : Type} (P : A -> Prop) n x l l' :
  P x -> Forall P l -> replace_nth n x l = Some l' -> Forall P l'.
Proof.
elim: n l l' => [| n IH] [| y l] l' Hx Hl //= H; inversion Hl; subst.
  by case: H => <-; constructor.
move: H; case E: (replace_nth n x l) => [l1 |] // [<-].
by constructor=> //; apply: (IH l l1 Hx).
Qed.

Lemma replace_nth_z_Forall {A : Type} (P : A -> Prop) k x l l' :
  P x -> Forall P l -> replace_nth_z k x l = Some l' -> Forall P l'.
Proof.
by rewrite /replace_nth_z; case: (k <? 0)%Z => //; apply: replace_nth_Forall.
Qed.

Lemma nth_z_Forall {A : Type} (P : A -> Prop) k l x :
  Forall P l -> nth_z k l = Some x -> P x.
Proof.
rewrite /nth_z; case: (k <? 0)%Z => // Hl H.
by move/Forall_forall: Hl; apply; exact: nth_error_In H.
Qed.

Lemma in_gW L p w : In (p, w) (gW L) -> In p L /\ w = pw p.
Proof. by rewrite /gW in_map_iff => -[q [E I]]; case: E => <- <-. Qed.
Lemma in_gT L p t : In (p, t) (gT L) -> In p L /\ t = pt p.
Proof. by rewrite /gT in_map_iff => -[q [E I]]; case: E => <- <-. Qed.
Lemma in_gA L p a : In (p, a) (gA L) -> In p L /\ a = pa p.
Proof. by rewrite /gA in_map_iff => -[q [E I]]; case: E => <- <-. Qed.
Lemma in_gD L p d : In (p, d) (gD L) -> In p L /\ d = pd p.
Proof. by rewrite /gD in_map_iff => -[q [E I]]; case: E => <- <-. Qed.

(* A body that only returns the variable it binds, as well_formed sees it
   (opened with anon k), is such for every opening of the pv instance. *)
Lemma is_tail_shape L k (bP : pv -> anf pv bare) (bW : vinfo -> anf vinfo bare) :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (bP x1) (bW x2)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat) ->
  WellFormed.is_tail bW k = true -> forall x, bP x = ARet (AVar x).
Proof.
move=> HW Hk Ht x; move: (HW x (anon k)) => {}HW.
rewrite /WellFormed.is_tail in Ht.
destruct (bP x) as [? ? ? | [p | |]], (bW (anon k)) as [? ? ? | [w | |]];
  rewrite /= in HW; try contradiction; try discriminate.
move/Nat.eqb_eq: Ht => Ht; case: HW => [E | I]; first by inversion E.
by case/in_gW: I => I Ew; subst; have := Hk _ I; lia.
Qed.

(* well_formed and tangent agree on which bodies only return their variable. *)
Lemma is_tail_transfer L k (bP : pv -> anf pv bare) (bW : vinfo -> anf vinfo bare)
  (bT : tvar W -> anf (tvar W) bare) tr :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (bP x1) (bW x2)) ->
  (forall x1 x2, anf_eq ((x1, x2) :: gT L) (bP x1) (bT x2)) ->
  (forall p, In p L -> (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat) ->
  WellFormed.is_tail bW k = Transform.is_tail (fun v => rebuild _ (bT v) tr).
Proof.
move=> HW HT Hk; set x := pfresh k.
have Hx : ~ In x L by move=> I; have [H _] := Hk _ I; rewrite /= in H; lia.
move: (HW x (anon k)) (HT x (probe W)) => {}HW {}HT.
rewrite /WellFormed.is_tail /Transform.is_tail.
destruct (bP x) as [? ? ? | [p | |]], (bW (anon k)) as [? ? ? | [w | |]],
  (bT (probe W)) as [? ? ? | [t | |]]; simpl in HW, HT; try contradiction;
  try reflexivity; try (destruct tr; reflexivity); simpl.
case: HW => [E | I]; case: HT => [E' | I'].
- by inversion E; inversion E'; subst; rewrite /= Nat.eqb_refl.
- by inversion E; subst; case/in_gT: I' => I' _.
- by inversion E'; subst; case/in_gW: I => I _.
case/in_gW: I => I Ew; case/in_gT: I' => _ Et; subst w t.
have [H1 H2] := Hk _ I.
case: (Nat.eqb_spec (vid (pw p)) k) => [? | _]; first lia.
by destruct (tid (pt p)) as [[|] |]; congruence.
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
move=> Hstep n; elim: n => [| n IH] lo s st v Hinv Hev; rewrite /= in Hev;
  cbn [exec_up].
  by case: Hev => <-; exists s; rewrite Z.add_0_r.
move: Hev; case E: (ev (VInt lo) st) => [st1 |] // Hev.
have [s1 [Hb Hi]] := Hstep _ _ _ _ Hinv E; rewrite Hb.
have [s' [He Hi']] := IH _ _ _ _ Hi Hev; exists s'; split=> //.
by have -> : (lo + Z.of_nat (S n))%Z = (lo + 1 + Z.of_nat n)%Z by lia.
Qed.

Lemma map_loop_sim (ev : val (dual R) -> option (val (dual R)))
  (body : store R -> option (store R)) (i : dvar nat)
  (Inv : Z -> store R -> list (dual R) -> Prop) :
  (forall j s acc x, Inv j s acc -> ev (VInt j) = Some (VReal x) ->
     exists s', body (store_set s (KVar i) (VInt j)) = Some s' /\ Inv (j + 1)%Z s' (acc ++ [x])%list) ->
  forall n lo s acc xs, Inv lo s acc -> eval_map ev lo n = Some xs ->
  exists s', exec_up R body i lo n s = Some s' /\ Inv (lo + Z.of_nat n)%Z s' (acc ++ xs)%list.
Proof.
move=> Hstep n; elim: n => [| n IH] lo s acc xs Hinv Hev; rewrite /= in Hev;
  cbn [exec_up].
  by case: Hev => <-; exists s; rewrite app_nil_r Z.add_0_r.
move: Hev; case E: (ev (VInt lo)) => [[x | | | |] |] //.
case E1: (eval_map ev (lo + 1) n) => [xs1 |] // [<-].
have [s1 [Hb Hi]] := Hstep _ _ _ _ Hinv E; rewrite Hb.
have [s' [He Hi']] := IH _ _ _ _ Hi E1; exists s'; split=> //.
have -> : (lo + Z.of_nat (S n))%Z = (lo + 1 + Z.of_nat n)%Z by lia.
by rewrite -app_assoc in Hi'.
Qed.

(* ---------------------------------------------------------------------------
   Atoms: the generated code reads the value of an atom in its stored
   variable, and its tangent in the dot of that variable, or 0. *)

Lemma atom_graph {V : Type} (pr : pv -> V) L (aP : atom pv) aX :
  atom_eq (map (fun p => (p, pr p)) L) aP aX ->
  aX = amap pr aP /\ (forall p, aP = AVar p -> In p L).
Proof.
case: aP aX => [p | sP | kP] [x | sX | kX] //=.
- rewrite in_map_iff => -[q [E I]]; case: E => Eq Ex; subst.
  by split=> // r [<-].
- by move=> ->; split.
by move=> ->; split.
Qed.

Lemma aeval_literal s d : aeval_atom (duals reals) (ANum s) = Some d ->
  exists x, real_lit s = Some x /\ d = VReal (Dual x 0).
Proof.
cbv beta iota delta [aeval_atom duals dual_lit dom_lit reals]; rewrite lit_0.
by case: (real_lit s) => [x |] // [<-]; exists x.
Qed.

(* The value of an atom. *)
Lemma spell_ok k s (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p /\ store_ok s p) ->
  aeval_atom (duals reals) (amap pd aP) = Some d ->
  xev s (spell (amap pt aP)) = Some (primal d).
Proof.
move=> Hs Hd; case: aP Hs Hd => [q | str | z] Hs Hd.
- rewrite /= in Hd; case: Hd => <-.
  have [[_ [_ [Hstore _]]] [H _]] := Hs q erefl.
  by rewrite /= Hstore.
- by move/aeval_literal: Hd => [x [Hx ->]]; rewrite /= xev_DReal Hx.
by rewrite /= in Hd; case: Hd => <-.
Qed.

(* The tangent of a real atom. *)
Lemma dot_ok k s (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p /\ store_ok s p) ->
  aeval_atom (duals reals) (amap pd aP) = Some (VReal d) ->
  xev s (dot (amap pt aP)) = Some (VReal (dsnd d)).
Proof.
move=> Hs Hd; case: aP Hs Hd => [q | str | z] Hs Hd.
- rewrite /= in Hd; case: Hd => Hd.
  have [[_ [_ [Hstore [_ [_ [Hdot [_ [_ [_ Hz]]]]]]]]] [_ H]] := Hs q erefl.
  rewrite /= Hdot; case Ev: (avaried (pa q)).
    by rewrite Hstore; have := H (eq_trans Hdot Ev); rewrite Hd.
  by have := Hz Ev; rewrite Hd /= => ->; rewrite xev_DReal lit_0.
- by move/aeval_literal: Hd => [x [Hx [->]]]; rewrite /= xev_DReal lit_0.
by [].
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

(* The variables the expression of a tangent reads: the dots of variables in
   scope, or variables opened by the code. *)
Definition dot_vars (L : list pv) (live : pv -> Prop) (c : nat) (e : dexpr W) : Prop :=
  forall x, In x (dvars e) ->
  (exists p, In p L /\ live p /\ x = DotOf (stored p)) \/ (~ below c x /\ consistent x).

Lemma dot_vars_res L live c e : dot_vars L live c e -> res_vars L live c e.
Proof.
move=> H x Hx; case: (H x Hx) => [[p [Hp [Lp E]]] | Hf]; last by right.
by left; exists p; auto.
Qed.

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
  dot_vars L (fun p => live_anf k bW p \/ owner wP pp = Some p) c de /\
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
Proof. by move/Forall_forall=> H /H. Qed.

Lemma unique_written_s L k c wP pp live ty p y :
  sctx L k c wP pp live ty -> In p L -> wP = Some y ->
  (match amap pw y with AVar y0 => (vid (pw p) =? vid y0)%nat | _ => false end) = true ->
  wP = Some (AVar p).
Proof.
move=> Hc Hp Hw Hid; have [q [Eq [Hq _]]] := s_written _ _ _ _ _ _ _ Hc _ Hw.
subst y; rewrite /= in Hid; move/Nat.eqb_eq: Hid => Hid.
by rewrite (s_unique _ _ _ _ _ _ _ Hc _ _ Hq Hp (eq_sym Hid)) in Hw.
Qed.

Lemma unique_written L k c s wP pp live ty p y :
  ctx_ok L k c s wP pp live ty -> In p L -> wP = Some y ->
  (match amap pw y with AVar y0 => (vid (pw p) =? vid y0)%nat | _ => false end) = true ->
  wP = Some (AVar p).
Proof. by move=> Hc; exact: unique_written_s (ctx_sctx _ _ _ _ _ _ _ _ Hc). Qed.

(* A body that returns an atom. *)
Lemma sim_ret (aP : atom pv) : sim_body (ARet aP).
Proof.
move=> L k c s wP pp m bA bW bT bD ty v HA HW HT HD Hc Hty Htc Hev.
destruct bA as [| aA], bW as [| aW], bT as [| aT], bD as [| aD];
  rewrite /= in HA HW HT HD; try contradiction.
graph HA; graph HW; graph HT; graph HD.
destruct aP as [p | str | z]; rewrite /= in Htc Hev *.
- case: Hev => Ev; subst v.
  have Hp : In p L by auto.
  have Hst := static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hp.
  have Hl : live_anf k (ARet (amap pw (AVar p))) p.
    by rewrite /live_anf /=; apply: Nat.eqb_refl.
  have Hs := c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl.
  have [Ety Hcase] : ty = vty (pw p) /\
      (varg (pw p) = None \/ wP = Some (AVar p) \/ ~ is_array (vty (pw p))).
    move: Htc; case Eg: (varg (pw p)) => [[nx r] |] /=; last by case=> <-; auto.
    case Ea: (ty_is_array (vty (pw p))) => /=.
      case Ew: (option_map (amap pw) wP) => [y |] //=.
      destruct wP as [y' |]; last discriminate.
      case: Ew => Ey; subst y.
      case Eid: (match amap pw y' with
                 | AVar y0 => (vid (pw p) =? vid y0)%nat
                 | _ => false end) => //= -[->]; split=> //.
      right; left.
      exact: (unique_written _ _ _ _ _ _ _ _ _ _ Hc Hp erefl Eid).
    case=> <-; split=> //; right; right.
    rewrite /is_array; destruct (vty (pw p)); rewrite /= in Ea;
      try discriminate; tauto.
  subst ty; have Hst0 := Hst.
  case: Hst => _ [_ [Hstore [_ [_ [Hdot [_ [_ [Hht Hz]]]]]]]].
  split; first lia.
  split; first exact: Hht.
  split; first exact: Hz.
  split.
    move=> x Hx; left; exists p; rewrite /= Hstore in Hx.
    by case: Hx => [<- | []]; auto.
  split.
    move=> x Hx; left; exists p; rewrite /= in Hx.
    case: (tdot (pt p)) Hx => /= Hx; last by [].
    by rewrite Hstore in Hx; case: Hx => [<- | []]; auto.
  exists s; split; first by [].
  split; first by move=> *.
  destruct (vty (pw p)) eqn:Ety; try contradiction.
    (* a real *)
    have Hs1 := proj1 Hs.
    destruct (pd p) as [d | | | |] eqn:Ed; try contradiction; split.
      by rewrite /= Hstore.
    apply: (dot_ok k s (AVar p)); last by rewrite /= Ed.
    by move=> q [<-]; split.
  (* an array: the variable updated in place *)
  case Eo: (owner wP pp) => [o |]; last first.
    by case: (c_ty _ _ _ _ _ _ _ _ Hc I Eo).
  have Hpo : pn p = pn o.
    apply: (c_arrays _ _ _ _ _ _ _ _ Hc p o Hp Hl);
      [by rewrite Ety | | exact: Eo].
    by case: Hcase => [Hc1 | [Hc1 | Hc1]]; auto; exfalso; apply: Hc1.
  have [F1 F2] := c_inplace _ _ _ _ _ _ _ _ Hc o p Eo Hp Hl Hpo.
  have Es : stored p = stored o by rewrite /stored Hpo.
  rewrite /body_result /inplace Eo /=.
  by exists (stored o); rewrite -Es.
- move/aeval_literal: Hev => [x [Hx ->]]; case: Htc => <-.
  split; first lia.
  split; first by [].
  split; first by [].
  split; first by move=> x' [].
  split; first by move=> x' [].
  exists s; split; first by [].
  split; first by move=> *.
  by rewrite /= !xev_DReal Hx lit_0.
by case: Htc => Ety; subst ty; case: Hty.
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
move=> HT HL Hw.
have Hst : forall p, In p L ->
    tstored (pt p) = stored p /\ tty (pt p) = vty (pw p).
  by move=> p Hp; have [_ [_ [H1 [H2 _]]]] := static_in _ _ _ HL Hp.
destruct eP as
  [f a | f a b | a i | a i x | cnd t e | lo hi b | an lo hi init b], eT;
  simpl in HT; try contradiction; simpl;
  try fresh_case; try (destruct vt; fresh_case).
- (* ASet *)
  case: HT => Ha _; destruct a as [p | |]; destruct a0; simpl in Ha;
    try contradiction; try fresh_case.
  case/in_gT: Ha => Hp ->; have [E _] := Hst _ Hp.
  by exists (stored p), (trecorded (pt p)), c; rewrite /= E; auto.
- (* AMap *)
  destruct vt; simpl;
    (destruct (Transform.is_tail bT); [| fresh_case]);
    (destruct wP as [[y | |] |]; simpl;
     [| fresh_case | fresh_case | fresh_case]);
    (destruct (Hw _ eq_refl) as [y' [E Hy]]; injection E as <-;
     destruct (Hst _ Hy) as [E _]; exists (stored y), (trecorded (pt y)), c;
     rewrite E; auto).
(* AFold *)
case: HT => _ [_ [Hi _]]; destruct init as [p | |], init0; simpl in Hi;
  try contradiction; destruct vt; simpl; try fresh_case;
  (apply in_gT in Hi as [Hp ->]; destruct (Hst _ Hp) as [E1 E2]; rewrite E2;
   destruct (vty (pw p)); try fresh_case;
   exists (stored p), (trecorded (pt p)), c; rewrite E1; auto).
Qed.

Lemma tof_amap k L (a : atom pv) :
  Forall (static_ok k) L -> (forall p, a = AVar p -> In p L) -> tof (amap pt a) = of_atom (amap pw a).
Proof.
move=> HL Ha; case: a Ha => [p | |] Ha //=.
by have [_ [_ [_ [E _]]]] := static_in _ _ _ HL (Ha p erefl).
Qed.

Lemma ty_eqb_true a b : ty_eqb a b = true -> a = b.
Proof. by case: a; case: b => //= ? ? /Z.eqb_eq ->. Qed.

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
move=> HW HT HL Htc.
destruct eP, eW, eT; simpl in HW, HT; try contradiction;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
  | H : atom_eq (gT L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
  end; subst; simpl in Htc |- *;
  try (destruct vt; reflexivity);
  rewrite ?(tof_amap k L) //.
- (* AOp1 *) crush_match Htc.
- (* AOp2 *) crush_match Htc.
- (* AGet *) crush_match Htc.
- (* ASet *)
  destruct (of_atom (amap pw a)) eqn:E; destruct pW; simpl in Htc;
    crush_match Htc.
- (* AIte *) destruct vt; simpl; destruct pW; simpl in Htc; crush_match Htc.
- (* AMap *)
  destruct vt; simpl; destruct pW; simpl in Htc; try congruence;
    destruct tail; try congruence; destruct lo; simpl in Htc; try congruence;
    destruct hi; simpl in Htc |- *; try congruence; crush_match Htc.
(* AFold *)
by destruct vt; simpl; rewrite (tof_amap k L) //; crush_match Htc.
Qed.

(* A value stored in place has an array type. *)
Lemma inplace_array L wP pW tail k (eP : value pv bare) eW te :
  value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) pW tail k eW = (te, Ok) ->
  storage wP tail eP <> None -> is_array te.
Proof.
move=> HW Htc Hs.
destruct eP, eW; simpl in HW; try contradiction; simpl in Hs;
  try (destruct Hs; reflexivity);
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
  end; subst; simpl in Htc.
- by destruct pW; simpl in Htc; crush_match Htc; injection Htc as <-.
- destruct pW; simpl in Htc; try (crush_match Htc; fail).
  destruct tail; last crush_match Htc.
  by destruct lo, hi; simpl in Htc; crush_match Htc; injection Htc as <-.
destruct init as [i | |]; simpl in Hs; try (destruct Hs; reflexivity).
simpl in Htc.
destruct (vty (pw i)) eqn:Ev; try (destruct Hs; reflexivity).
by crush_match Htc; injection Htc as <-.
Qed.

Lemma open_pairs_sbind {A B : Type} (sc : scoped W A) (f : A -> scoped W B) c :
  open_pairs (sbind sc f) c = let '(a, c1) := open_pairs sc c in open_pairs (f a) c1.
Proof. by elim: sc c => [n g IH | p g IH | a] c /=; auto. Qed.

Lemma open_pairs_mono {A : Type} (sc : scoped W A) c : (c <= snd (open_pairs sc c))%nat.
Proof.
by elim: sc c => [n g IH | p g IH | a] c /=; auto; have := IH (c, c) (S c); lia.
Qed.

Lemma static_mono k k' p : static_ok k p -> (k <= k')%nat -> static_ok k' p.
Proof. by move=> [H1 [H2 H3]] Hk; split=> //; split=> //; lia. Qed.

Lemma owner_in_s L k c wP pp live ty o :
  sctx L k c wP pp live ty -> owner wP pp = Some o -> In o L.
Proof.
move=> Hc Ho; destruct pp as [| | | ix sx]; rewrite /= in Ho; try discriminate.
  destruct wP as [[y | |] |]; try discriminate.
  destruct (vty (pw y)); try discriminate.
  case: Ho => Ey; subst y.
  have [y' [E [Hy _]]] := s_written _ _ _ _ _ _ _ Hc _ erefl.
  by case: E => Ey'; subst y'.
by case: Ho => <-; have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hc.
Qed.

Lemma owner_in L k c s wP pp live ty o :
  ctx_ok L k c s wP pp live ty -> owner wP pp = Some o -> In o L.
Proof. by move=> Hc; exact: owner_in_s (ctx_sctx _ _ _ _ _ _ _ _ Hc). Qed.

(* A fresh pv for a binder of identity k is not in scope. *)
Lemma fresh_notin L k x :
  (forall p, In p L -> (aid (pa p) < k)%nat) -> aid (pa x) = k -> ~ In x L.
Proof. by move=> H Hx I; have := H _ I; lia. Qed.

Lemma aids_below L k : Forall (static_ok k) L -> forall p, In p L -> (aid (pa p) < k)%nat.
Proof. by move=> HL p Hp; have [E [H _]] := static_in _ _ _ HL Hp; lia. Qed.

(* The body after a binder, opened as the simulation opens it and as
   well_formed's occurs opens it (anon k), has the same occurrences. *)
Lemma live_cont L k (cP : pv -> anf pv bare) (cW : vinfo -> anf vinfo bare) x w id :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (cP x1) (cW x2)) ->
  Forall (static_ok k) L -> aid (pa x) = k -> vid w = k ->
  occurs_anf id (S k) (cW w) = occurs_anf id (S k) (cW (anon k)).
Proof.
move=> HcW HL Hx Hw.
apply: (proj1 occurs_transfer (cP x) ((x, w) :: gW L)
          ((x, anon k) :: gW L)) => //.
have Hn := fresh_notin L k x (aids_below L k HL) Hx.
split.
  move=> p w1 w2 [E1 | I1] [E2 | I2].
  - by inversion E1; inversion E2; subst; rewrite /=.
  - by inversion E1; subst; case/in_gW: I2 => I2 _.
  - by inversion E2; subst; case/in_gW: I1 => I1 _.
  by case/in_gW: I1 => _ ->; case/in_gW: I2 => _ ->.
move=> p w' [[E | I] | [E | I]]; try (inversion E; subst; lia).
all: by case/in_gW: I => I _; have := aids_below L k HL p I; lia.
Qed.

(* A body that only returns its variable, opened with w. *)
Lemma tail_cont L k (cP : pv -> anf pv bare) (cW : vinfo -> anf vinfo bare) x w :
  (forall x1 x2, anf_eq ((x1, x2) :: gW L) (cP x1) (cW x2)) ->
  Forall (static_ok k) L -> aid (pa x) = k ->
  WellFormed.is_tail cW k = true -> cP x = ARet (AVar x) /\ cW w = ARet (AVar w).
Proof.
move=> HcW HL Hx Ht.
have Hk : forall p, In p L -> (vid (pw p) < k)%nat.
  by move=> p Hp; have [E [H _]] := static_in _ _ _ HL Hp; lia.
have Hs := is_tail_shape L k cP cW HcW Hk Ht.
split; first exact: Hs.
move: (HcW x w); rewrite (Hs x).
case: (cW w) => [? ? ? | [w' | |]] //= [E | I]; first by inversion E.
by case/in_gW: I => I _; case: (fresh_notin L k x (aids_below L k HL) Hx I).
Qed.

Lemma same_vid_s L k c wP pp live ty p q :
  sctx L k c wP pp live ty -> In p L -> In q L -> (vid (pw p) =? vid (pw q))%nat = true -> p = q.
Proof.
move=> Hc Hp Hq /Nat.eqb_eq E.
exact: (s_unique _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
Qed.

Lemma same_vid L k c s wP pp live ty p q :
  ctx_ok L k c s wP pp live ty -> In p L -> In q L -> (vid (pw p) =? vid (pw q))%nat = true -> p = q.
Proof. by move=> Hc; exact: same_vid_s (ctx_sctx _ _ _ _ _ _ _ _ Hc). Qed.

Lemma operation2_typed_scalar f a b t sp : operation2_typed f a b = Some (t, sp) -> ~ is_array t.
Proof.
rewrite /operation2_typed => H; destruct f, a, b; rewrite /= in H;
  try discriminate; injection H as <- <-; simpl; auto.
Qed.

(* A value that updates an array in place (it has an array type, or the
   tangent pass stores it in place) ends its body, and is stored in the
   storage of the variable updated in place. *)
Lemma inplace_value_s L k c wP pp live ty tail (eP : value pv bare) eW te :
  sctx L k c wP pp live ty -> value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  storage wP tail eP <> None \/ is_array te ->
  tail = true /\ exists o, owner wP pp = Some o /\ storage wP tail eP = Some (stored o).
Proof.
move=> Hc HW Htc Hty Hin.
destruct eP, eW; simpl in HW; try contradiction;
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : atom_eq (gW L) _ _ |- _ => apply atom_graph in H; destruct H as [-> ?]
  end; subst; simpl in Htc, Hin |- *.
- destruct Hin as [Hi | Hi]; first congruence.
  by destruct f0; simpl in Htc; crush_match Htc; injection Htc as <-;
    destruct Hi.
- destruct Hin as [Hi | Hi]; first congruence.
  crush_match Htc; injection Htc as <-.
  match goal with H : operation2_typed _ _ _ = Some _ |- _ =>
    apply operation2_typed_scalar in H end.
  contradiction.
- destruct Hin as [Hi | Hi]; first congruence.
  by crush_match Htc; injection Htc as <-; destruct Hi.
- (* ASet *)
  destruct pp as [| | | ix sx]; simpl in Htc; try discriminate.
  destruct (of_atom (amap pw a)) eqn:Ea; try discriminate.
  destruct tail; simpl in Htc; last discriminate.
  split; first by [].
  destruct a as [p | |]; simpl in Htc; try discriminate.
  destruct (vid (pw p) =? vid (pw sx))%nat eqn:E; simpl in Htc;
    last discriminate.
  have Hp : In p L by auto.
  have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hc.
  by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hc Hp Hsx E); exists sx.
- (* AIte *)
  destruct Hin as [Hi | Hi]; first congruence.
  by destruct pp; simpl in Htc; crush_match Htc; injection Htc as <-;
    destruct Hi.
- (* AMap *)
  destruct pp; simpl in Htc; try (crush_match Htc; fail).
  destruct tail; last crush_match Htc.
  split; first by [].
  destruct (owner wP PTop) as [o |] eqn:Eo.
    destruct wP as [[y | |] |]; simpl in Eo; try discriminate.
    by destruct (vty (pw y)); try discriminate; injection Eo as <-; exists y.
  exfalso; apply (s_ty _ _ _ _ _ _ _ Hc); last exact Eo.
  rewrite -(Hty erefl).
  by destruct lo, hi; simpl in Htc; crush_match Htc; injection Htc as <-.
(* AFold *)
destruct (ty_eqb (of_atom (amap pw lo)) Integer &&
          ty_eqb (of_atom (amap pw hi)) Integer); simpl in Htc;
  last discriminate.
destruct init as [i | str | z]; simpl in Htc, Hin |- *.
- destruct (vty (pw i)) as [| | | n] eqn:Ev; simpl in Htc.
  + destruct Hin as [Hi | Hi]; first congruence.
    by destruct pp; simpl in Htc; crush_match Htc; injection Htc as <-;
    destruct Hi.
  + discriminate.
  + discriminate.
  have Hi : In i L by auto.
  destruct pp as [| | | ix sx]; destruct tail; simpl in Htc; try discriminate.
    destruct wP as [y |] eqn:Ew; simpl in Htc; last discriminate.
    destruct (match amap pw y with
              | AVar y0 => (vid (pw i) =? vid y0)%nat
              | _ => false end) eqn:E; last discriminate.
    rewrite (unique_written_s _ _ _ _ _ _ _ _ _ Hc Hi erefl E).
    by split; [| exists i; rewrite /= Ev].
  destruct (vid (pw i) =? vid (pw sx))%nat eqn:E; simpl in Htc;
    last discriminate.
  have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hc.
  pose proof (same_vid_s _ _ _ _ _ _ _ _ _ Hc Hi Hsx E) as ->.
  by split; [| exists sx].
- destruct Hin as [Hi | Hi]; first congruence.
  by destruct pp; simpl in Htc; crush_match Htc; injection Htc as <-;
    destruct Hi.
discriminate.
Qed.

Lemma inplace_value L k c s wP pp live ty tail (eP : value pv bare) eW te :
  ctx_ok L k c s wP pp live ty -> value_eq (gW L) eP eW ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  (tail = true -> te = ty) ->
  storage wP tail eP <> None \/ is_array te ->
  tail = true /\ exists o, owner wP pp = Some o /\ storage wP tail eP = Some (stored o).
Proof. by move=> Hc; exact: inplace_value_s (ctx_sctx _ _ _ _ _ _ _ _ Hc). Qed.

Lemma below_mono c c' v : below c v -> (c <= c')%nat -> below c' v.
Proof. by elim: v => [[i j] | v IH | v IH | v IH |] /=; auto; lia. Qed.

(* The frames of a value and of the rest of its let compose. *)
Lemma frame_let c c0 c1 ex n s s1 s2 :
  (c <= c0)%nat -> (c0 <= c1)%nat -> frame c0 (Some n) s s1 -> frame c1 ex s1 s2 ->
  ~ below c n \/ ex = Some n -> frame c ex s s2.
Proof.
move=> H01 H12 F1 F2 Hn v Hb Hcons Hex.
rewrite (F2 v (below_mono _ _ _ Hb (Nat.le_trans _ _ _ H01 H12)) Hcons Hex).
apply: F1; first exact: (below_mono _ _ _ Hb H01); first exact: Hcons.
move=> m [<-]; case: Hn => [Hn | Hn]; last exact: Hex _ Hn.
by split=> E; subst; exact: Hn Hb.
Qed.

(* A context stays a context for fewer live variables and a larger counter. *)
Lemma ctx_weaken L k c c' s wP pp (live live' : pv -> Prop) ty :
  ctx_ok L k c s wP pp live ty -> (forall p, live' p -> live p) -> (c <= c')%nat ->
  ctx_ok L k c' s wP pp live' ty.
Proof.
move=> Hc Hl Hcc; case: Hc => HS HU HN HSt HW HP HO HI HA HT HTop.
constructor; auto.
- by move=> p Hp; have := HN p Hp; lia.
- move=> o p Ho Hp E.
  by case: (HO o p Ho Hp E) => [H | H]; [left | right; auto].
- by move=> o p Ho Hp Lp; apply: HI; auto.
by move=> y H1 H2 H3; case: (HTop y H1 H2 H3) => [A [B C]]; auto.
Qed.

Lemma arrays_len_value s n v z :
  store_get s (keyv n) = Some (primal v) -> store_get s (keyv (DotOf n)) = Some (tangent v) ->
  has_type (Array z) v -> arrays_len s n (Z.to_nat z).
Proof.
move=> H1 H2 Ht; case: v H1 H2 Ht => [d | z0 | b | l | l] H1 H2 Ht;
  try contradiction.
by rewrite /= in Ht; exists (map dfst l), (map dsnd l); rewrite !length_map.
Qed.

Lemma arrays_len_frame c ex s s' p len :
  frame c ex s s' -> (pn p < c)%nat ->
  (forall m, ex = Some m -> stored p <> m /\ stored p <> DotOf m) ->
  (forall m, ex = Some m -> DotOf (stored p) <> m /\ DotOf (stored p) <> DotOf m) ->
  arrays_len s (stored p) len -> arrays_len s' (stored p) len.
Proof.
move=> F Hp H1 H2 [l1 [l2 [A1 [A2 [A3 A4]]]]]; exists l1, l2.
have E1 : store_get s' (keyv (stored p)) = store_get s (keyv (stored p)).
  by apply: F => //=; auto.
have E2 : store_get s' (keyv (DotOf (stored p))) =
          store_get s (keyv (DotOf (stored p))).
  by apply: F => //=; auto.
by rewrite E1 E2.
Qed.

Lemma dot_vars_let x L (live live' : pv -> Prop) c c1 e :
  dot_vars (x :: L) live' c1 e -> (c <= c1)%nat -> (forall p, In p L -> live' p -> live p) ->
  ((~ below c (stored x) /\ consistent (stored x)) \/ exists o, In o L /\ live o /\ stored x = stored o) ->
  dot_vars L live c e.
Proof.
move=> H Hc Hl Hx y Hy.
case: (H y Hy) => [[p [[Ep | Hp] [Lp Ey]]] | [Hb Hcy]].
- subst; case: Hx => [[Hx Hcx] | [o [Ho [Lo Eo]]]]; first by right; auto.
  by left; exists o; rewrite -Eo; auto.
- by left; exists p; auto.
right; split=> // Hb'; apply: Hb; exact: (below_mono _ _ _ Hb' Hc).
Qed.

Lemma res_vars_let x L (live live' : pv -> Prop) c c1 e :
  res_vars (x :: L) live' c1 e -> (c <= c1)%nat -> (forall p, In p L -> live' p -> live p) ->
  ((~ below c (stored x) /\ consistent (stored x)) \/ exists o, In o L /\ live o /\ stored x = stored o) ->
  res_vars L live c e.
Proof.
move=> H Hc Hl Hx y Hy.
case: (H y Hy) => [[p [[Ep | Hp] [Lp E]]] | [Hb Hcy]].
- subst; case: Hx => [[Hx Hcx] | [o [Ho [Lo Eo]]]].
    by right; case: E => ->; auto.
  by left; exists o; rewrite -Eo; auto.
- by left; exists p; auto.
right; split=> // Hb'; apply: Hb; exact: (below_mono _ _ _ Hb' Hc).
Qed.

Lemma tan_let w a e b :
  tan W w (ALet a e b) =
  with_storage w e b (fun n rec =>
    let vr := match a with LetAnn v _ _ => v | _ => false end in
    sbind (tan_value W w e (Transform.type_of e) vr n) (fun se =>
    sbind (tan W w (b (open_let (Transform.type_of e) n vr rec))) (fun '(sb, vd) => Done ((se ++ sb)%list, vd)))).
Proof. by []. Qed.

(* A let: the value, stored, then the rest of the body with one more
   variable in scope. *)
Lemma sim_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  sim_value eP -> (forall x, sim_body (cP x)) -> sim_body (ALet a eP cP).
Proof.
move=> IHe IHb L k c s wP pp m bA bW bT bD ty v HA HW HT HD Hc Hty Htc Hev.
destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |],
  bD as [aD eD cD |]; rewrite /= in HA HW HT HD; try contradiction.
case: HA => HeA HcA; case: HW => HeW HcW; case: HT => HeT HcT.
case: HD => HeD HcD.
rewrite /= in Htc Hev; move: Htc Hev.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
             (WellFormed.is_tail cW k) k eW) => [te d0].
case: d0 Hte => [| msg] Hte /= Htc //.
case Hve: (aeval_value (duals reals) eD) => [ve |] // Hev.
cbn [annotate_body_t].
case: (needs false m (S k) (cA (let_binder k eA))) => u l.
set vr := varied_value k eA; set vt := annotate_value_t false k eA.
set rest := annotate_body_t false m (S k) (cA (let_binder k eA)).
cbn [rebuild]; rewrite tan_let; cbv zeta.
have HL := c_static _ _ _ _ _ _ _ _ Hc.
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
have Hwr : forall a0, wP = Some a0 -> exists y, a0 = AVar y /\ In y L.
  move=> a0 E; have [y [-> [Hy _]]] := c_written _ _ _ _ _ _ _ _ Hc _ E.
  by exists y.
have [n [rec [c0 [Hopen Hn]]]] :=
  open_with_storage L k wP eP eT vt (fun v0 => rebuild _ (cT v0) rest)
    (fun n rec => sbind (tan_value W (option_map (amap pt) wP)
                           (rebuild_value _ eT vt) te vr n)
       (fun se => sbind (tan W (option_map (amap pt) wP)
                           (rebuild _ (cT (open_let te n vr rec)) rest))
                    (fun '(sb, vd) => Done ((se ++ sb)%list, vd))))
    c HeT HL Hwr.
rewrite Hopen.
have Htid : forall p, In p L ->
    (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat.
  by move=> p Hp; have [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]] := static_in _ _ _ HL Hp.
rewrite -(is_tail_transfer L k cP cW cT rest HcW HcT Htid) in Hn.
set tail := WellFormed.is_tail cW k in Hte Hn *.
rewrite open_pairs_sbind.
case Hse: (open_pairs (tan_value W _ (rebuild_value (tvar W) eT vt) te vr n) c0)
  => [se c1].
have Hlive_e : forall p, live_value k eW p -> live_anf k (ALet aW eW cW) p.
  by move=> p H; rewrite /live_value /live_anf /= in H *; rewrite H.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
have Hnum : exists j, n = DBound (j, j) /\ (j < c0)%nat /\ (c <= c0)%nat /\
    match storage wP tail eP return Prop with
    | Some _ => True | None => j = c end.
  case Es: (storage wP tail eP) Hn => [m0 |] [-> ->]; last first.
    by exists c; repeat split; lia.
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [_ [o [Ho Es']]] := inplace_value _ _ _ _ _ _ _ _ _ _ _ _
                             Hc HeW Hte Htail_ty (or_introl Hsn).
  rewrite Es in Es'; case: Es' => Em; subst m0.
  exists (pn o); split=> //.
  have := c_num _ _ _ _ _ _ _ _ Hc _ (owner_in _ _ _ _ _ _ _ _ _ Hc Ho).
  by lia.
have [j [Ej [Hj0 [Hc0 Hjs]]]] := Hnum.
have Hst : match storage wP tail eP return Prop with
           | Some m0 => n = m0
           | None => forall p, In p L -> stored p <> n /\ DotOf (stored p) <> n
           end.
  case: (storage wP tail eP) Hn Hjs => [m0 |] Hn Hjs; first by case: Hn.
  move=> p Hp; subst j; rewrite Ej.
  have Hpn := c_num _ _ _ _ _ _ _ _ Hc _ Hp.
  by rewrite /stored; split=> E; inversion E; lia.
have IH0 := IHe L k c0 s wP pp tail eA eW eT eD te n ve ty HeA HeW HeT HeD
              (ctx_weaken _ _ _ _ _ _ _ _ _ _ Hc Hlive_e Hc0) Hte Htail_ty
              (ex_intro _ j (conj Ej Hj0)) Hst Hve.
cbv zeta in IH0; rewrite -/vr -/vt Hse in IH0.
case: IH0 => Hc01 [Hht [Hz [Hra [s1 [Hrun1 [Hfr1 [Hn1 Hd1]]]]]]].
(* the variable of the let *)
set x := PV (let_binder k eA) (VInfo k te None) (open_let te n vr rec) ve j.
have Hx : aid (pa x) = k by [].
have HxL : ~ In x L := fresh_notin L k x (aids_below L k HL) Hx.
have Hvid : forall p, In p L -> (vid (pw p) < k)%nat.
  by move=> p Hp; have [_ [H _]] := static_in _ _ _ HL Hp.
case Es: (storage wP tail eP) Hn Hst Hjs => [m0 |] Hn Hst Hjs.
  (* stored in place: the rest only returns the variable *)
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [Ht [o [Ho Es']]] := inplace_value _ _ _ _ _ _ _ _ _ _ _ _
                              Hc HeW Hte Htail_ty (or_introl Hsn).
  have Harr := inplace_array _ _ _ _ _ _ _ _ HeW Hte Hsn.
  rewrite Es in Es'; case: Es' => Em0; case: Hn => Hnd _; subst m0.
  have [Hcx EW] := tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht.
  have ET : cT (pt x) = ARet (AVar (pt x)).
    move: (HcT x (pt x)); rewrite Hcx.
    case: (cT (pt x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => ->.
    by case/in_gT: I => I _.
  have ED : cD (pd x) = ARet (AVar (pd x)).
    move: (HcD x (pd x)); rewrite Hcx.
    case: (cD (pd x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => ->.
    by case/in_gD: I => I _.
  have EA : cA (pa x) = ARet (AVar (pa x)).
    move: (HcA x (pa x)); rewrite Hcx.
    case: (cA (pa x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => ->.
    by case/in_gA: I => I _.
  rewrite /= in ET ED EA; rewrite ED /= in Hev; case: Hev => Ev; subst v.
  rewrite EW /= in Htc; case: Htc => Ety; subst ty.
  rewrite /rest EA /= ET /= app_nil_r.
  have Hno : n = stored o by congruence.
  have HoL : In o L := owner_in _ _ _ _ _ _ _ _ _ Hc Ho.
  split; first lia.
  split; first exact: Hht.
  split; first exact: Hz.
  split; first by move=> y /= [<- | []]; left; exists o; auto.
  split.
    move=> y; case: (vr) => //= -[<- | []].
    by left; exists o; rewrite Hno; auto.
  exists s1; split; first exact: Hrun1.
  split.
    have Hrefl : frame c0 (inplace wP pp) s1 s1 by move=> *.
    apply: (frame_let c c0 c0 _ n s s1 s1 Hc0 (le_n c0) Hfr1 Hrefl).
    by right; rewrite /inplace Ho /=; congruence.
  destruct te as [| | | z]; try destruct Harr.
  rewrite /body_result; exists n; rewrite /inplace Ho /=.
  split; first congruence.
  split; first exact: Hn1.
  by destruct vr; rewrite /=; apply: Hd1; right; rewrite Es.
(* a fresh variable *)
case: Hn => En Hc0'; subst n j.
(* the rest reads the variables in scope it read as part of the let *)
have Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p ->
    live_anf k (ALet aW eW cW) p.
  rewrite /live_anf => p Hp H /=.
  rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx erefl) in H.
  by rewrite H orb_true_r.
(* the value leaves the variables in scope unchanged *)
have Hframe_old : forall p, In p L ->
    store_get s1 (keyv (stored p)) = store_get s (keyv (stored p)) /\
    store_get s1 (keyv (DotOf (stored p))) =
    store_get s (keyv (DotOf (stored p))).
  move=> p Hp; have Hpn := c_num _ _ _ _ _ _ _ _ Hc _ Hp.
  by split; apply: Hfr1; rewrite /stored /=; try lia; try done;
    move=> m0 [<-]; split=> E; inversion E; lia.
set cW' := cW (VInfo k te None).
have Hxs : static_ok (S k) x.
  by repeat split; rewrite /=; auto; try lia; discriminate.
have Hxstore : store_ok s1 x.
  by split; rewrite /stored /=; [exact: Hn1 | move=> Hv; apply: Hd1; left].
have Hc' : ctx_ok (x :: L) (S k) c1 s1 wP pp (live_anf (S k) cW') ty.
  constructor.
  - constructor=> //; apply: (Forall_impl _ _ HL) => p Hp.
    by apply: (static_mono k _ p Hp); lia.
  - move=> p q [Ep | Hp] [Eq | Hq] E; try subst p; try subst q; try done.
    + by have := Hvid _ Hq; rewrite /= in E; lia.
    + by have := Hvid _ Hp; rewrite /= in E; lia.
    exact: (c_unique _ _ _ _ _ _ _ _ Hc _ _ Hp Hq E).
  - move=> p [<- /= | Hp]; first lia.
    by have := c_num _ _ _ _ _ _ _ _ Hc _ Hp; lia.
  - move=> p [<- | Hp] Hl; first exact: Hxstore.
    have [S1 S2] := c_store _ _ _ _ _ _ _ _ Hc _ Hp (Hlive_c _ Hp Hl).
    have [F1 F2] := Hframe_old _ Hp.
    by split; [rewrite F1 | move=> Hd; rewrite F2; exact: S2].
  - move=> a0 E; have [y [-> [Hy Hv]]] := c_written _ _ _ _ _ _ _ _ Hc _ E.
    by exists y; split=> //; split; [right |].
  - have Hp := c_place _ _ _ _ _ _ _ _ Hc; destruct pp; simpl in Hp |- *; auto.
    by case: Hp => A [B C]; split; [right | split; [right |]].
  - move=> o p Ho [<- | Hp] Ep.
      have := c_num _ _ _ _ _ _ _ _ Hc _ (owner_in _ _ _ _ _ _ _ _ _ Hc Ho).
      by rewrite /= in Ep; lia.
    case: (c_owner _ _ _ _ _ _ _ _ Hc o p Ho Hp Ep) => [H | H]; first by left.
    by right=> Hl; apply: H; apply: Hlive_c.
  - move=> o p Ho [<- | Hp] Lp Ep.
      have := c_num _ _ _ _ _ _ _ _ Hc _ (owner_in _ _ _ _ _ _ _ _ _ Hc Ho).
      by rewrite /= in Ep; lia.
    have [S1 S2] :=
      c_inplace _ _ _ _ _ _ _ _ Hc o p Ho Hp (Hlive_c _ Hp Lp) Ep.
    by have [F1 F2] := Hframe_old _ Hp; split; [rewrite F1 | rewrite F2].
  - move=> p o [<- | Hp] Lp Ha Hg Ho.
      have [_ [o' [Ho' Es']]] := inplace_value _ _ _ _ _ _ _ _ _ _ _ _
                                   Hc HeW Hte Htail_ty (or_intror Ha).
      by rewrite Es in Es'.
    exact: (c_arrays _ _ _ _ _ _ _ _ Hc p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho).
  - exact: (c_ty _ _ _ _ _ _ _ _ Hc).
  move=> y Hpp Hw Ha.
  have [y' [E [Hy _]]] := c_written _ _ _ _ _ _ _ _ Hc _ Hw.
  case: E => Ey; subst y'.
  have [T1 [T2 [l1 [l2 [A1 [A2 [A3 A4]]]]]]] :=
    c_top _ _ _ _ _ _ _ _ Hc y Hpp Hw Ha.
  split; first exact: T1.
  split; first by move=> Ly; apply: T2; apply: Hlive_c.
  have [F1 F2] := Hframe_old _ Hy.
  by exists l1, l2; rewrite F1 F2.
(* the rest of the body *)
have IH0 := IHb x (x :: L) (S k) c1 s1 wP pp m (cA (pa x)) cW' (cT (pt x))
              (cD (pd x)) ty v (HcA x _) (HcW x _) (HcT x _) (HcD x _) Hc' Hty
              Htc Hev.
rewrite /x in IH0; cbn [pt pa pd] in IH0; rewrite -/rest in IH0.
rewrite open_pairs_sbind.
case Hsb: (open_pairs (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) (cT (open_let te (DBound (c, c)) vr rec)) rest))
             c1) => [[sb [ve' de']] c2].
rewrite Hsb in IH0.
case: IH0 => Hc12 [Hht' [Hz' [Hrv1 [Hrv2 [s2 [Hrun2 [Hfr2 Hres2]]]]]]].
have Hxs' : (~ below c (DBound (c, c)) /\ consistent (DBound (c, c))) \/
    exists o, In o L /\
      (live_anf k (ALet aW eW cW) o \/ owner wP pp = Some o) /\
      DBound (c, c) = stored o.
  by left; rewrite /=; split; [lia |].
rewrite /=.
split; first lia.
split; first exact: Hht'.
split; first exact: Hz'.
have Hlv' : forall p, In p L -> live_anf (S k) cW' p \/ owner wP pp = Some p ->
    live_anf k (ALet aW eW cW) p \/ owner wP pp = Some p.
  by move=> p Hp [H | H]; [left; apply: Hlive_c | right].
split.
  exact: (res_vars_let _ L _ _ c c1 ve' Hrv1 (Nat.le_trans _ _ _ Hc0 Hc01) Hlv'
            Hxs').
split.
  exact: (dot_vars_let _ L _ _ c c1 de' Hrv2 (Nat.le_trans _ _ _ Hc0 Hc01) Hlv'
            Hxs').
exists s2; split; first by rewrite run_app Hrun1.
split; last exact: Hres2.
apply: (frame_let c c0 c1 _ (DBound (c, c)) s s1 s2) => //.
by left; rewrite /=; lia.
Qed.

(* ---------------------------------------------------------------------------
   Expressions read only the variables they mention: a write to another key
   does not change their value. *)


Definition avoid (k : key) (e : dexpr W) : Prop := forall x, In x (dvars e) -> keyv x <> k.

Lemma xev_set_other s k v e : avoid k e -> xev (store_set s k v) e = xev s e.
Proof.
rewrite /avoid /xev.
elim: e => [x | l | z | a IHa i IHi | f a IHa | f a IHa b IHb] /= H.
- rewrite store_get_set; case E: (key_eqb k (KVar (out_dvar nat x))) => //.
  by move/key_eqb_eq: E => E; case: (H x (or_introl erefl)); rewrite E.
- by [].
- by [].
- by rewrite IHa ?IHi // => y Hy; apply: H; apply: in_or_app; auto.
- by rewrite IHa.
by rewrite IHa ?IHb // => y Hy; apply: H; apply: in_or_app; auto.
Qed.

Lemma avoid_op1 k f e : avoid k e -> avoid k (DOp1 f e).
Proof. by move=> H x Hx; apply: H. Qed.
Lemma avoid_op2 k f e1 e2 : avoid k e1 -> avoid k e2 -> avoid k (DOp2 f e1 e2).
Proof. by move=> H1 H2 x Hx; case: (in_app_or _ _ _ Hx); auto. Qed.
Lemma avoid_at k e1 e2 : avoid k e1 -> avoid k e2 -> avoid k (DAt e1 e2).
Proof. by move=> H1 H2 x Hx; case: (in_app_or _ _ _ Hx); auto. Qed.
Lemma avoid_lit k l : avoid k (DReal l).
Proof. by move=> x []. Qed.
Lemma avoid_scale k p e : avoid k p -> avoid k e -> avoid k (scale p e).
Proof.
move=> H1 H2; case: p H1 => [x | s | z | a i | f a | f a b] H1;
  try by apply: avoid_op2.
rewrite /scale; case: (String.eqb s "1") => //.
by case: (String.eqb s "-1"); [apply: avoid_op1 | apply: avoid_op2].
Qed.
Lemma avoid_sum k l : Forall (avoid k) l -> avoid k (sum l).
Proof.
elim=> [| e l' He Hl IH]; first exact: avoid_lit.
by case: l' Hl IH => [| e' l'] //= Hl IH; apply: avoid_op2.
Qed.

(* The keys of a variable in scope, when the stored variable is not n. *)
Lemma avoid_spell k (aP : atom pv) n :
  (forall p, aP = AVar p -> static_ok k p /\ pn p <> n) ->
  avoid (keyv (DBound (n, n))) (spell (amap pt aP)) /\
  avoid (keyv (DBound (n, n))) (dot (amap pt aP)) /\
  avoid (keyv (DotOf (DBound (n, n)))) (spell (amap pt aP)) /\
  avoid (keyv (DotOf (DBound (n, n)))) (dot (amap pt aP)).
Proof.
case: aP => [p | str | z] H /=; last 2 first.
- by repeat split; move=> x [].
- by repeat split; move=> x [].
have [[_ [_ [Hs _]]] Hn] := H p erefl; rewrite Hs /stored.
by repeat split; try case: (tdot (pt p)); rewrite /= => x Hx;
  rewrite /= in Hx; try contradiction; case: Hx => [<- | []];
  rewrite /keyv /= => E; inversion E; auto.
Qed.

Lemma avoid_partial1 k f (a : atom (tvar W)) p :
  avoid k (spell a) -> avoid k (dot a) -> partial1 f a = Some p ->
  avoid k (scale (spell_partial p) (dot a)).
Proof.
move=> Hs Hd Hp; apply: avoid_scale Hd.
case: f Hp => [| | | | | | [| ? | ?] |] //= [<-] /=;
  repeat (apply avoid_op1 || apply avoid_op2 || apply avoid_lit || assumption).
Qed.

Lemma avoid_partial2 k f (a b : atom (tvar W)) pa pb :
  avoid k (spell a) -> avoid k (dot a) -> avoid k (spell b) -> avoid k (dot b) ->
  partial2 f a b = Some (pa, pb) ->
  avoid k (sum (tangent_term W a pa ++ tangent_term W b pb)).
Proof.
move=> Hsa Hda Hsb Hdb Hp; apply: avoid_sum; rewrite /tangent_term.
case: f Hp => //= -[<- <-];
  case: (tvaried_atom a); case: (tvaried_atom b) => /=;
  repeat (apply Forall_cons || apply Forall_nil || apply avoid_scale
          || apply avoid_op1 || apply avoid_op2 || apply avoid_lit
          || assumption).
Qed.

Lemma keyv_inj a b : consistent a -> consistent b -> keyv a = keyv b -> a = b.
Proof.
rewrite /keyv => Ha Hb [] E; elim: a Ha b Hb E
  => [[i j] | a IH | a IH | a IH |] Ha [[i' j'] | b | b | b |] Hb //= E.
- by case: E => E; move: Ha Hb => /= -> ->; rewrite E.
- by case: E => /(IH Ha b Hb) ->.
- by case: E => /(IH Ha b Hb) ->.
by case: E => /(IH Ha b Hb) ->.
Qed.

Lemma frame_refl c ex s : frame c ex s s.
Proof. by move=> *. Qed.

Lemma frame_set c n s s' k v :
  frame c (Some n) s s' -> consistent n -> (k = keyv n \/ k = keyv (DotOf n)) ->
  frame c (Some n) s (store_set s' k v).
Proof.
move=> F Hn Hk w Hb Hc Hex; rewrite store_get_set.
case E: (key_eqb k (keyv w)); last exact: F.
move/key_eqb_eq: E => E; have [H1 H2] := Hex n erefl; exfalso.
by case: Hk => Ek; rewrite Ek in E; apply keyv_inj in E; auto.
Qed.

Lemma store_get_set_same (s : store R) k v : store_get (store_set s k v) k = Some v.
Proof. by rewrite store_get_set key_eqb_refl. Qed.

Lemma store_get_set_other (s : store R) k k' v : k <> k' -> store_get (store_set s k v) k' = store_get s k'.
Proof.
move=> H; rewrite store_get_set; case E: (key_eqb k k') => //.
by move/key_eqb_eq: E.
Qed.

Lemma keyv_dot_neq n : keyv n <> keyv (DotOf n).
Proof.
rewrite /keyv => -[].
by elim: n => [[i j] | n IH | n IH | n IH |] //= -[].
Qed.

(* The facts the simulation of an operation needs on an operand that occurs
   in it. *)
Lemma operand_ok L k c s wP pp (live : pv -> Prop) ty (aP : atom pv) n :
  ctx_ok L k c s wP pp live ty -> (forall p, aP = AVar p -> In p L /\ live p) ->
  (forall p, In p L -> stored p <> DBound (n, n) /\ DotOf (stored p) <> DBound (n, n)) ->
  forall p, aP = AVar p -> (static_ok k p /\ store_ok s p) /\ (static_ok k p /\ pn p <> n).
Proof.
move=> Hc Ha Hn p E; have [Hp Hl] := Ha p E.
have Hs := static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hp.
split; first by split=> //; exact: (c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl).
split=> // E'; have [H _] := Hn p Hp.
by apply: H; rewrite /stored E'.
Qed.

Lemma operand_ok2 L k c s wP pp (live : pv -> Prop) ty (aP : atom pv) n :
  ctx_ok L k c s wP pp live ty -> (forall p, aP = AVar p -> In p L /\ live p) ->
  (forall p, aP = AVar p -> pn p <> n) ->
  forall p, aP = AVar p -> (static_ok k p /\ store_ok s p) /\ (static_ok k p /\ pn p <> n).
Proof.
move=> Hc Ha Hn p E; have [Hp Hl] := Ha p E.
have Hs := static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hp.
split; first by split=> //; exact: (c_store _ _ _ _ _ _ _ _ Hc _ Hp Hl).
by split=> //; apply: Hn.
Qed.

Lemma tvaried_amap k (aP : atom pv) :
  (forall p, aP = AVar p -> static_ok k p) -> tvaried_atom (amap pt aP) = varied (amap pa aP).
Proof.
case: aP => [p | str | z] H //=.
by have [_ [_ [_ [_ [E _]]]]] := H p erefl.
Qed.

(* A literal or a variable that is not varied has a zero tangent. *)
Lemma atom_zero k (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p) -> varied (amap pa aP) = false ->
  aeval_atom (duals reals) (amap pd aP) = Some d -> zero d.
Proof.
case: aP => [p | str | z] H Hv Hd; last 2 first.
- by case/aeval_literal: Hd => x [_ ->].
- by move: Hd => /= [<-].
move: Hd => /= [<-].
have [_ [_ [_ [_ [_ [_ [_ [_ [_ Hz]]]]]]]]] := H p erefl.
exact: Hz Hv.
Qed.

Lemma atom_type k (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p) ->
  aeval_atom (duals reals) (amap pd aP) = Some d -> has_type (of_atom (amap pw aP)) d.
Proof.
case: aP => [p | str | z] H Hd; last 2 first.
- by case/aeval_literal: Hd => x [_ ->].
- by move: Hd => /= [<-].
move: Hd => /= [<-].
by have [_ [_ [_ [_ [_ [_ [_ [_ [Ht _]]]]]]]]] := H p erefl.
Qed.

Lemma dual_op1_zero f x y dy : dual_op1 R reals f (Dual x 0) = Some (Dual y dy) -> dy = 0.
Proof.
rewrite /dual_op1; case: (dom_op1 reals f x) => // r.
by case: (dual_partial1 R reals f x r) => //= d [_ <-]; ring.
Qed.

Lemma run_define s so n e v :
  xev s e = Some v -> run [DDefine so n e] s = Some (store_set s (keyv n) v).
Proof. by rewrite /run /xev /= => ->. Qed.

Lemma run_define2 s so so' n e e' v v' :
  xev s e = Some v -> xev (store_set s (keyv n) v) e' = Some v' ->
  run [DDefine so n e; DDefine so' (DotOf n) e'] s =
  Some (store_set (store_set s (keyv n) v) (keyv (DotOf n)) v').
Proof. by rewrite /run /xev /keyv /= => -> /= ->. Qed.

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
value_intro.
rewrite /= in Htc Hev Hst *.
rename f3 into f.
have Hlv : forall p, aP = AVar p ->
    In p L /\ live_value k (AOp1 f (amap pw aP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl.
have Hop := operand_ok _ _ _ _ _ _ _ _ aP j Hc Hlv Hst.
have Hop1 : forall p, aP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hop p E).
have Hop2 : forall p, aP = AVar p -> static_ok k p /\ pn p <> j.
  by move=> p E; case: (Hop p E).
have Hst1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; case: (Hop1 p E).
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
have [-> Hta] : te = Real /\ of_atom (amap pw aP) = Real.
  by destruct f; rewrite /= in Htc; crush_match Htc; split; congruence.
have Htv := atom_type k aP va Hst1 Ha; rewrite Hta in Htv.
case: va Ha Htv Hev => [[x dx] | | | |] Ha // _ Hev.
cbn [eval_op1 dom_op1 duals] in Hev.
case Hd: (dual_op1 R reals f (Dual x dx)) Hev => [[y dy] |] // [<-].
have Hs := spell_ok k s aP _ Hop1 Ha; rewrite /= in Hs.
have Hdt := dot_ok k s aP _ Hop1 Ha; rewrite /= in Hdt.
case Hp: (partial1 f (amap pt aP)) => [p |]; last first.
  destruct f as [| | | | | | z |]; rewrite /= in Hp; try discriminate.
  by destruct z; try discriminate; unfold_ops Hd.
have [Hv Ht] := tangent_op1 s f (amap pt aP) _ x dx y dy p Hs Hdt Hd Hp.
have [A1 [A2 [A3 A4]]] := avoid_spell k aP j Hop2.
rewrite /tangent_term (tvaried_amap k aP Hst1).
case Hvr: (varied (amap pa aP)) => /=; last first.
  split; first lia.
  split=> //.
  split.
    move=> _; have Hz := atom_zero k aP _ Hst1 Hvr Ha; rewrite /= in Hz.
    by subst dx; rewrite /=; exact: dual_op1_zero f x y dy Hd.
  split=> //.
  exists (store_set s (keyv (DBound (j, j))) (VReal y)).
  split; first exact: run_define Hv.
  split; first by apply: frame_set; [apply: frame_refl | | left].
  split; first by rewrite store_get_set_same.
  by case.
split; first lia.
split=> //; split=> //; split=> //.
exists (store_set (store_set s (keyv (DBound (j, j))) (VReal y))
          (keyv (DotOf (DBound (j, j)))) (VReal dy)).
split.
  apply: run_define2; first exact: Hv.
  rewrite xev_set_other //.
  exact: (avoid_partial1 _ f _ _ A1 A2 Hp).
split.
  apply: frame_set; [| by [] | by right].
  by apply: frame_set; [apply: frame_refl | | left].
split; first by rewrite store_get_set_other ?store_get_set_same.
by move=> _; rewrite store_get_set_same.
Qed.

Lemma dual_op2_zero f x y z dz : dual_op2 R reals f (Dual x 0) (Dual y 0) = Some (Dual z dz) -> dz = 0.
Proof.
move=> H; destruct f; unfold_ops H; try discriminate.
all: by case: H => _ <-; rewrite /Rdiv; ring.
Qed.

Lemma primal_int_op2 f x y : primal (int_op2 f x y) = int_op2 f x y.
Proof. by case: f. Qed.

Lemma has_type_int t z : has_type t (VInt z) -> t = Integer.
Proof. by case: t => /=; tauto. Qed.

(* An integer atom is not varied. *)
Lemma int_not_varied k (aP : atom pv) z :
  (forall p, aP = AVar p -> static_ok k p) ->
  aeval_atom (duals reals) (amap pd aP) = Some (VInt z) -> varied (amap pa aP) = false.
Proof.
case: aP => [p | str | z'] H //= [Hd].
have [_ [_ [_ [_ [_ [_ [_ [Hv [Ht _]]]]]]]]] := H p erefl.
move: Ht; rewrite Hd => /has_type_int Ht.
by case: (avaried (pa p)) Hv => // /(_ erefl); rewrite Ht.
Qed.

Lemma int_op2_type f (x y : Z) t sp :
  operation2_typed f Integer Integer = Some (t, sp) -> has_type t (@int_op2 (dual R) f x y).
Proof. by case: f => //= -[<- _]. Qed.

Lemma op2_real_type f t sp :
  operation2_typed f Real Real = Some (t, sp) -> t = if comparison f then Boolean else Real.
Proof. by case: f => //= -[<- _]. Qed.

(* A binary operation. *)
Lemma sim_op2 f (aP bP : atom pv) : sim_value (AOp2 f aP bP).
Proof.
value_intro.
rewrite /= in Htc Hev Hst *.
rename f3 into f.
have Hlv : forall p, aP = AVar p ->
    In p L /\ live_value k (AOp2 f (amap pw aP) (amap pw bP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl.
have Hlv' : forall p, bP = AVar p ->
    In p L /\ live_value k (AOp2 f (amap pw aP) (amap pw bP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl orb_true_r.
have Hop := operand_ok _ _ _ _ _ _ _ _ aP j Hc Hlv Hst.
have Hop' := operand_ok _ _ _ _ _ _ _ _ bP j Hc Hlv' Hst.
have HaS : forall p, aP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hop p E).
have HaN : forall p, aP = AVar p -> static_ok k p /\ pn p <> j.
  by move=> p E; case: (Hop p E).
have Ha1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; case: (HaS p E).
have HbS : forall p, bP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hop' p E).
have HbN : forall p, bP = AVar p -> static_ok k p /\ pn p <> j.
  by move=> p E; case: (Hop' p E).
have Hb1 : forall p, bP = AVar p -> static_ok k p.
  by move=> p E; case: (HbS p E).
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
case Hb: (aeval_atom (duals reals) (amap pd bP)) Hev => [vb |] // Hev.
have Hsa := spell_ok k s aP _ HaS Ha; have Hsb := spell_ok k s bP _ HbS Hb.
case Ho2: (operation2 f) Htc => [o2 |] // Htc.
case Ht2: (operation2_typed f (of_atom (amap pw aP)) (of_atom (amap pw bP)))
  Htc => [[t0 sp] |] // [<-].
have Hta := atom_type k aP va Ha1 Ha; have Htb := atom_type k bP vb Hb1 Hb.
have [A1 [A2 [A3 A4]]] := avoid_spell k aP j HaN.
have [B1 [B2 [B3 B4]]] := avoid_spell k bP j HbN.
destruct va as [[x dx] | za | | |], vb as [[y dy] | zb | | |];
  cbn [eval_op2] in Hev; try discriminate; last first.
  (* two integers *)
  rewrite (int_not_varied k aP za Ha1 Ha) (int_not_varied k bP zb Hb1 Hb).
  have -> : (if comparison f then false else false || false) = false.
    by case: (comparison f).
  case: Hev => <-; rewrite /= in Hta Htb.
  move/has_type_int: Hta => Hta; move/has_type_int: Htb => Htb.
  rewrite Hta Htb in Ht2.
  split; first lia.
  split; first exact: int_op2_type f za zb t0 sp Ht2.
  split; first by move=> _; destruct f.
  split=> //.
  exists (store_set s (keyv (DBound (j, j))) (int_op2 f za zb)).
  split; first by apply: run_define; rewrite xev_DOp2 Hsa Hsb.
  split; first by apply: frame_set; [apply: frame_refl | | left].
  split; first by rewrite store_get_set_same primal_int_op2.
  by case.
(* two reals *)
rewrite /= in Hta Htb.
case Ea: (of_atom (amap pw aP)) Hta Ht2 => // _ Ht2.
case Eb: (of_atom (amap pw bP)) Htb Ht2 => // _ Ht2.
move/op2_real_type: Ht2 => ->.
case Hcmp: (comparison f) Hev => Hev /=.
  (* a comparison: a boolean, not varied *)
  cbn [dom_cmp duals dual_cmp] in Hev.
  case Hcy: (dom_cmp reals f x y) Hev => [bo |] // [<-].
  split; first lia.
  split=> //; split=> //; split=> //.
  exists (store_set s (keyv (DBound (j, j))) (VBool bo)).
  split.
    apply: run_define; rewrite xev_DOp2 Hsa Hsb /= Hcmp; rewrite /= in Hcy *.
    by rewrite Hcy.
  split; first by apply: frame_set; [apply: frame_refl | | left].
  split; first by rewrite store_get_set_same.
  by case.
(* an arithmetic operation *)
cbn [dom_op2 duals] in Hev.
case Hd: (dual_op2 R reals f (Dual x dx) (Dual y dy)) Hev => [[z dz] |] // [<-].
case Hp: (partial2 f (amap pt aP) (amap pt bP)) => [[qa qb] |]; last first.
  by destruct f; rewrite /= in Hp; try discriminate; rewrite /= in Ho2.
have Hda := dot_ok k s aP _ HaS Ha; have Hdb := dot_ok k s bP _ HbS Hb.
have Hva := tvaried_amap k aP Ha1; have Hvb := tvaried_amap k bP Hb1.
have Hza : varied (amap pa aP) = false -> dx = 0.
  by move=> Hz; exact: atom_zero k aP _ Ha1 Hz Ha.
have Hzb : varied (amap pa bP) = false -> dy = 0.
  by move=> Hz; exact: atom_zero k bP _ Hb1 Hz Hb.
case Hvr: (varied (amap pa aP) || varied (amap pa bP)) => /=; last first.
  move/orb_false_iff: Hvr => [Hva0 Hvb0].
  rewrite (Hza Hva0) (Hzb Hvb0) in Hd.
  split; first lia.
  split=> //.
  split; first by move=> _; exact: dual_op2_zero f x y z dz Hd.
  split=> //.
  have Hv : xev s (DOp2 f (spell (amap pt aP)) (spell (amap pt bP))) =
      Some (VReal z).
    rewrite xev_DOp2 Hsa Hsb /= Hcmp.
    by destruct f; unfold_ops Hd; try discriminate; case: Hd => <-.
  exists (store_set s (keyv (DBound (j, j))) (VReal z)).
  split; first exact: run_define Hv.
  split; first by apply: frame_set; [apply: frame_refl | | left].
  split; first by rewrite store_get_set_same.
  by case.
have Hvr' : tvaried_atom (amap pt aP) || tvaried_atom (amap pt bP) = true.
  by rewrite Hva Hvb.
have Hza' : tvaried_atom (amap pt aP) = false -> dx = 0 by rewrite Hva.
have Hzb' : tvaried_atom (amap pt bP) = false -> dy = 0 by rewrite Hvb.
have [Hv Ht] := tangent_op2 s f (amap pt aP) (amap pt bP) x y dx dy z dz qa qb
                  Hsa Hsb (fun _ => Hda) Hza' (fun _ => Hdb) Hzb' Hd Hp Hvr'.
split; first lia.
split=> //; split=> //; split=> //.
exists (store_set (store_set s (keyv (DBound (j, j))) (VReal z))
          (keyv (DotOf (DBound (j, j)))) (VReal dz)).
split.
  apply: run_define2; first exact: Hv.
  rewrite xev_set_other //.
  exact: (avoid_partial2 _ f _ _ _ _ A1 A2 B1 B2 Hp).
split.
  apply: frame_set; [| by [] | by right].
  by apply: frame_set; [apply: frame_refl | | left].
split; first by rewrite store_get_set_other ?store_get_set_same.
by move=> _; rewrite store_get_set_same.
Qed.

Lemma xev_DAt s a i :
  xev s (DAt a i) =
  match xev s a, xev s i with
  | Some (VArray l), Some (VInt z) => match nth_z z l with Some x => Some (VReal x) | None => None end
  | _, _ => None
  end.
Proof. by []. Qed.

(* Reading an element of an array. *)
Lemma sim_get (aP iP : atom pv) : sim_value (AGet aP iP).
Proof.
value_intro.
rewrite /= in Htc Hev Hst *.
have Hlv : forall p, aP = AVar p ->
    In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl.
have Hlv' : forall p, iP = AVar p ->
    In p L /\ live_value k (AGet (amap pw aP) (amap pw iP)) p.
  move=> p E; split; first by auto.
  by subst; rewrite /live_value /= Nat.eqb_refl orb_true_r.
have Hop := operand_ok _ _ _ _ _ _ _ _ aP j Hc Hlv Hst.
have Hop' := operand_ok _ _ _ _ _ _ _ _ iP j Hc Hlv' Hst.
have HaS : forall p, aP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hop p E).
have HaN : forall p, aP = AVar p -> static_ok k p /\ pn p <> j.
  by move=> p E; case: (Hop p E).
have Ha1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; case: (HaS p E).
have HiS : forall p, iP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hop' p E).
have HiN : forall p, iP = AVar p -> static_ok k p /\ pn p <> j.
  by move=> p E; case: (Hop' p E).
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [[| | | l |] |] // Hev.
case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev => [[| z | | |] |] // Hev.
case Hn: (nth_z z l) Hev => [d |] // [<-].
crush_match Htc; case: Htc => <-.
have [A1 [A2 [A3 A4]]] := avoid_spell k aP j HaN.
have [B1 [B2 [B3 B4]]] := avoid_spell k iP j HiN.
have Hsa := spell_ok k s aP _ HaS Ha; have Hsi := spell_ok k s iP _ HiS Hi.
have Hv : xev s (DAt (spell (amap pt aP)) (spell (amap pt iP))) =
    Some (VReal (dfst d)).
  by rewrite xev_DAt Hsa Hsi /= nth_z_map Hn.
rewrite (tvaried_amap k aP Ha1).
case Hvr: (varied (amap pa aP)) => /=; last first.
  split; first lia.
  split=> //.
  split.
    move=> _; have Hz := atom_zero k aP _ Ha1 Hvr Ha; rewrite /= in Hz *.
    exact: nth_z_Forall _ z l d Hz Hn.
  split=> //.
  exists (store_set s (keyv (DBound (j, j))) (VReal (dfst d))).
  split; first exact: run_define Hv.
  split; first by apply: frame_set; [apply: frame_refl | | left].
  split; first by rewrite store_get_set_same.
  by case.
(* a varied array: a variable, with a tangent *)
destruct aP as [p | |]; rewrite /= in Ha; try discriminate; case: Ha => Ha.
have [[_ [_ [Hstp [_ [_ [Hdot _]]]]]] [_ Hsd]] := HaS p erefl.
have Hd : xev s (DAt (dot (amap pt (AVar p))) (spell (amap pt iP))) =
    Some (VReal (dsnd d)).
  rewrite /= in Hvr *; rewrite Hdot Hvr xev_DAt Hsi /= Hstp.
  change (xev s (DVar (DotOf (stored p)))) with
    (store_get s (keyv (DotOf (stored p)))).
  by rewrite (Hsd (eq_trans Hdot Hvr)) Ha /= nth_z_map Hn.
split; first lia.
split=> //; split=> //; split=> //.
exists (store_set (store_set s (keyv (DBound (j, j))) (VReal (dfst d)))
          (keyv (DotOf (DBound (j, j)))) (VReal (dsnd d))).
split.
  apply: run_define2; first exact: Hv.
  by rewrite xev_set_other //; apply: avoid_at.
split.
  apply: frame_set; [| by [] | by right].
  by apply: frame_set; [apply: frame_refl | | left].
split; first by rewrite store_get_set_other ?store_get_set_same.
by move=> _; rewrite store_get_set_same.
Qed.

Lemma run_assign_at s n ei ev l z e l1 :
  store_get s (keyv n) = Some (VArray l) -> xev s ei = Some (VInt z) -> xev s ev = Some (VReal e) ->
  replace_nth_z z e l = Some l1 ->
  run [DAssign (DAt (DVar n) ei) ev] s = Some (store_set s (keyv n) (VArray l1)).
Proof.
move=> Hn Hi Hv Hr; rewrite /run /xev /keyv in Hn Hi Hv *.
by rewrite /= Hv /= Hn Hi Hr.
Qed.

Lemma run_two st1 st2 s s1 s2 : run [st1] s = Some s1 -> run [st2] s1 = Some s2 -> run [st1; st2] s = Some s2.
Proof.
move=> H1 H2.
by rewrite (_ : [st1; st2] = [st1] ++ [st2])%list // run_app H1.
Qed.

(* Two live variables with the storage updated in place are the same. *)
Lemma live_owner L k c s wP pp live ty o p :
  ctx_ok L k c s wP pp live ty -> owner wP pp = Some o -> In p L -> live p -> live o ->
  pn p = pn o -> p = o.
Proof.
move=> Hc Ho Hp Lp Lo E.
by case: (c_owner _ _ _ _ _ _ _ _ Hc o p Ho Hp E).
Qed.

(* An update of an array, at the end of the body of an in-place loop. *)
Lemma sim_set (aP iP vP : atom pv) : sim_value (ASet aP iP vP).
Proof.
value_intro.
rewrite /= in Htc Hev *.
destruct pp as [| | | ix sx]; rewrite /= in Htc; try discriminate.
case Eat: (of_atom (amap pw aP)) Htc => [| | | z] // Htc.
destruct tail; rewrite /= in Htc; last discriminate.
destruct aP as [a | |]; rewrite /= in Htc Eat; try discriminate.
case Ea: (vid (pw a) =? vid (pw sx))%nat Htc => //= Htc.
case Ev: (ty_eqb (of_atom (amap pw vP)) Real) Htc => //= Htc.
move/ty_eqb_true: Ev => Ev; crush_match Htc; case: Htc => <-.
have [Hix [Hsx [Hixt [Hsxt [Hsxv [Hixg Hsxg]]]]]] := c_place _ _ _ _ _ _ _ _ Hc.
have Ha : In a L by auto.
have Eas := same_vid _ _ _ _ _ _ _ _ _ _ Hc Ha Hsx Ea; subst a.
rewrite /= in Hst; case: Hst => Hj' _; subst j.
have Hlsx :
    live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) sx.
  by rewrite /live_value /= Nat.eqb_refl.
rewrite /= in Hev; case Hsxd: (pd sx) Hev => [| | | l |] // Hev.
case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev => [[| zi | | |] |] // Hev.
case Hv: (aeval_atom (duals reals) (amap pd vP)) Hev => [[d | | | |] |] // Hev.
case Hr: (replace_nth_z zi d l) Hev => [l1 |] // [<-].
(* the index and the value are not stored in the array *)
have Hlv : forall p, iP = AVar p \/ vP = AVar p ->
    In p L /\
    live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p.
  move=> p [E | E]; subst; split; auto.
  - by rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
  by rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
have Hnot : forall p, iP = AVar p \/ vP = AVar p -> pn p <> pn sx.
  move=> p E Ep; have [Hp Lp] := Hlv p E.
  have Epsx := live_owner _ _ _ _ _ _ _ _ sx p Hc erefl Hp Lp Hlsx Ep.
  by subst p; case: E => E; subst; rewrite /= in Hi Hv; congruence.
have Hli : forall p, iP = AVar p ->
    In p L /\
    live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p.
  by move=> p E; apply: Hlv; left.
have Hlv' : forall p, vP = AVar p ->
    In p L /\
    live_value k (ASet (amap pw (AVar sx)) (amap pw iP) (amap pw vP)) p.
  by move=> p E; apply: Hlv; right.
have Hni : forall p, iP = AVar p -> pn p <> pn sx.
  by move=> p E; apply: Hnot; left.
have Hnv : forall p, vP = AVar p -> pn p <> pn sx.
  by move=> p E; apply: Hnot; right.
have Hopi := operand_ok2 _ _ _ _ _ _ _ _ iP (pn sx) Hc Hli Hni.
have Hopv := operand_ok2 _ _ _ _ _ _ _ _ vP (pn sx) Hc Hlv' Hnv.
have HiS : forall p, iP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hopi p E).
have HiN : forall p, iP = AVar p -> static_ok k p /\ pn p <> pn sx.
  by move=> p E; case: (Hopi p E).
have HvS : forall p, vP = AVar p -> static_ok k p /\ store_ok s p.
  by move=> p E; case: (Hopv p E).
have HvN : forall p, vP = AVar p -> static_ok k p /\ pn p <> pn sx.
  by move=> p E; case: (Hopv p E).
have [A1 [A2 [A3 A4]]] := avoid_spell k iP (pn sx) HiN.
have [B1 [B2 [B3 B4]]] := avoid_spell k vP (pn sx) HvN.
have Hsi := spell_ok k s iP _ HiS Hi; have Hsv := spell_ok k s vP _ HvS Hv.
have Hdv := dot_ok k s vP _ HvS Hv.
have [_ [_ [_ [_ [_ [Hdot [_ [_ [Hht _]]]]]]]]] :=
  static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc) Hsx.
have [S1 S2] := c_store _ _ _ _ _ _ _ _ Hc sx Hsx Hlsx.
rewrite Hsxd in S1 S2 Hht; have {}S2 := S2 (eq_trans Hdot Hsxv).
rewrite /= in Hsxv *; rewrite Hsxv /=.
set s1 := store_set s (keyv (stored sx)) (VArray (map dfst l1)).
have Hrun1 : run [DAssign (DAt (DVar (stored sx)) (spell (amap pt iP)))
                    (spell (amap pt vP))] s = Some s1.
  apply: (run_assign_at s _ _ _ (map dfst l) zi (dfst d)); auto.
  by rewrite replace_nth_z_map Hr.
have Hrun2 : run [DAssign (DAt (DVar (DotOf (stored sx))) (spell (amap pt iP)))
                    (dot (amap pt vP))] s1 =
    Some (store_set s1 (keyv (DotOf (stored sx))) (VArray (map dsnd l1))).
  apply: (run_assign_at s1 _ _ _ (map dsnd l) zi (dsnd d)).
  - by rewrite /s1 store_get_set_other //; apply: keyv_dot_neq.
  - by rewrite /s1 xev_set_other.
  - by rewrite /s1 xev_set_other.
  by rewrite replace_nth_z_map Hr.
split; first lia.
split.
  rewrite /= in Hht *; rewrite Eat in Hht.
  by rewrite (replace_nth_z_length _ _ _ _ Hr); rewrite /= in Hht; congruence.
split=> //; split=> //.
exists (store_set s1 (keyv (DotOf (stored sx))) (VArray (map dsnd l1))).
split; first exact: run_two _ _ _ _ _ Hrun1 Hrun2.
split.
  apply: frame_set; [| by [] | by right].
  by rewrite /s1; apply: frame_set; [apply: frame_refl | | left].
split; first by rewrite store_get_set_other /s1 ?store_get_set_same.
by move=> _; rewrite store_get_set_same.
Qed.

Lemma run_realvar x ss s :
  run (DRealVar x :: ss) s = run ss (store_set s (keyv x) (VReal 0)).
Proof.
rewrite /run /keyv; cbn [map out_dstmt exec_stmts exec].
by change (dom_lit reals "0") with (real_lit "0"); rewrite lit_0.
Qed.

Lemma run_branch e t f ss s b :
  xev s e = Some (VBool b) ->
  run (DBranch e t f :: ss) s =
  match run (if b then t else f) s with Some s1 => run ss s1 | None => None end.
Proof.
move=> H; rewrite /run; cbn [map out_dstmt exec_stmts exec].
by move: H; rewrite /xev => ->; case: b.
Qed.

Lemma run_for i lo hi b ss s l h :
  xev s lo = Some (VInt l) -> xev s hi = Some (VInt h) ->
  run (DFor i lo hi b :: ss) s =
  match exec_up R (run b) (out_dvar nat i) l (count l h) s with Some s1 => run ss s1 | None => None end.
Proof.
move=> Hl Hh; rewrite /run; cbn [map out_dstmt exec_stmts exec].
by rewrite /xev in Hl Hh; rewrite Hl Hh.
Qed.

Lemma run_assign_var s x e v ss :
  xev s e = Some v -> run (DAssign (DVar x) e :: ss) s = run ss (store_set s (keyv x) v).
Proof.
by rewrite /run /xev /keyv; cbn [map out_dstmt exec_stmts exec] => ->.
Qed.

(* Writes to the keys of another variable keep a variable related. *)
Lemma store_ok_set s p k v :
  k <> keyv (stored p) -> k <> keyv (DotOf (stored p)) -> store_ok s p -> store_ok (store_set s k v) p.
Proof.
move=> H1 H2 [S1 S2]; split; first by rewrite store_get_set_other.
by move=> Hd; rewrite store_get_set_other //; apply: S2.
Qed.

Lemma keyv_bound_neq j j' : j <> j' ->
  keyv (DBound (j, j)) <> keyv (DBound (j', j')) /\ keyv (DBound (j, j)) <> keyv (DotOf (DBound (j', j'))) /\
  keyv (DotOf (DBound (j, j))) <> keyv (DBound (j', j')) /\
  keyv (DotOf (DBound (j, j))) <> keyv (DotOf (DBound (j', j'))).
Proof.
by move=> H; rewrite /keyv /=; repeat split; move=> E; inversion E; auto.
Qed.

(* The context of a branch or of a loop body without storage updated in
   place, from the context of the value. *)
Lemma ctx_sub L k c s s0 wP pp pp' (live live' : pv -> Prop) ty :
  ctx_ok L k c s wP pp live ty -> owner wP pp' = None -> pp' <> PTop -> place_ok L pp' ->
  (forall p, live' p -> live p) ->
  (forall p, In p L -> live p -> store_ok s p -> store_ok s0 p) ->
  ctx_ok L k c s0 wP pp' live' Real.
Proof.
move=> Hc Ho Hpp Hpl Hl Hs.
by case: Hc; constructor; auto; move=> *; congruence.
Qed.

Lemma frame_chain c c' ex s s0 s1 :
  frame c ex s s0 -> frame c' None s0 s1 -> (c <= c')%nat -> frame c ex s s1.
Proof.
move=> F1 F2 Hc v Hb Hcv Hex.
by rewrite (F2 v (below_mono _ _ _ Hb Hc) Hcv) //; apply: F1.
Qed.

(* A result expression avoids a variable below c' that no variable in scope
   is stored in. *)
Lemma res_vars_avoid L live c' e j :
  res_vars L live c' e -> (j < c')%nat -> (forall p, In p L -> pn p <> j) ->
  avoid (keyv (DBound (j, j))) e /\ avoid (keyv (DotOf (DBound (j, j)))) e.
Proof.
move=> H Hj Hn; split=> x Hx E.
all: case: (H x Hx) E => [[p [Hp [_ [-> | ->]]]] | [Hb Hcx]] E;
  try by rewrite /keyv /stored /= in E; inversion E; apply: (Hn p Hp).
all: by apply keyv_inj in E; rewrite /=; auto; subst x; rewrite /= in Hb; lia.
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
move=> Hr Hv Hd Hres Hj Hn; rewrite run_app Hr.
have [A1 A2] := res_vars_avoid L live c' dt j Hres Hj Hn.
case: vr; rewrite (run_assign_var _ _ _ _ _ Hv) //.
rewrite (run_assign_var _ _ _ (VReal dx)) //.
by rewrite xev_set_other.
Qed.

(* A branch: the condition is a boolean in the store, the generated code
   runs the statements of the branch taken, then stores its value and
   tangent in n. *)
Lemma sim_ite (cP : atom pv) (tP eP : anf pv bare) :
  sim_body tP -> sim_body eP -> sim_value (AIte cP tP eP).
Proof.
move=> IHt IHe.
value_intro.
rewrite /= in Htc Hev Hst *.
rename t into tA, e into eA, t0 into tW, e0 into eW, t1 into tT, e1 into eT,
  t2 into tD, e2 into eD.
rename H9 into EtA, H10 into EeA, H6 into EtW, H7 into EeW, H3 into EtT,
  H4 into EeT, H0 into EtD, H1 into EeD.
(* typing *)
have Hnot : forall ix sx, pp <> PArray ix sx.
  by move=> ix sx E; rewrite E /= in Htc.
have Hpp : pp = PTop \/ pp = PBranch \/ pp = PScalar.
  by destruct pp as [| | | ix sx]; auto; case: (Hnot ix sx).
have Htc' :
    (if ty_eqb (of_atom (amap pw cP)) Boolean
     then let '(t3, d1) := typecheck (option_map (amap pw) wP) InBranch k tW in
          let '(t4, d2) := typecheck (option_map (amap pw) wP) InBranch k eW in
          if is_ok d1 then
            if is_ok d2 then
              if ty_eqb t3 Real && ty_eqb t4 Real then (Real, Ok)
              else (Real, Error "both branches must compute a real")
            else (Real, d2)
          else (Real, d1)
     else (Real, Error "a branch condition must be a comparison")) = (te, Ok).
  by case: Hpp => [E | [E | E]]; rewrite E in Htc.
clear Htc.
case Ecb: (ty_eqb (of_atom (amap pw cP)) Boolean) Htc' => // Htc'.
case HtW: (typecheck (option_map (amap pw) wP) InBranch k tW) Htc'
  => [t3 d1] Htc'.
case HeW: (typecheck (option_map (amap pw) wP) InBranch k eW) Htc'
  => [t4 d2] Htc'.
case: d1 HtW Htc' => [| m1] HtW //= Htc'.
case: d2 HeW Htc' => [| m2] HeW //=.
case E3: (ty_eqb t3 Real); case E4: (ty_eqb t4 Real) => //= -[<-].
move/ty_eqb_true: E3 => E3; move/ty_eqb_true: E4 => E4; subst t3 t4.
(* the condition *)
have Hn : forall p, In p L -> pn p <> j.
  by move=> p Hp E; have [H' _] := Hst p Hp; apply: H'; rewrite /stored E.
case Hcd: (aeval_atom (duals reals) (amap pd cP)) Hev => [[| | b | |] |] // Hev.
have Hlc : forall p, cP = AVar p -> static_ok k p /\ store_ok s p.
  move=> p E; subst cP.
  split; first by apply: (static_in _ _ _ (c_static _ _ _ _ _ _ _ _ Hc)); auto.
  by apply: (c_store _ _ _ _ _ _ _ _ Hc); auto;
    rewrite /live_value /= Nat.eqb_refl.
have Hsc := spell_ok k s cP _ Hlc Hcd; rewrite /= in Hsc.
(* the two bodies, opened *)
rewrite open_pairs_sbind.
case Hot: (open_pairs (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) tT (annotate_body_t false Replay k tA))) c)
  => [[st [vt dt]] c1].
rewrite open_pairs_sbind.
case Hoe: (open_pairs (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) eT (annotate_body_t false Replay k eA))) c1)
  => [[se' [ve' de']] c2].
have M1 := open_pairs_mono (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) tT (annotate_body_t false Replay k tA))) c.
have M2 := open_pairs_mono (tan W (option_map (amap pt) wP)
             (rebuild (tvar W) eT (annotate_body_t false Replay k eA))) c1.
rewrite Hot /= in M1; rewrite Hoe /= in M2.
cbn zeta; rewrite /tan_ite.
set vr := varied_anf k tA || varied_anf k eA.
set n := DBound (j, j).
set s0 := if vr then store_set (store_set s (keyv n) (VReal 0))
                       (keyv (DotOf n)) (VReal 0)
          else store_set s (keyv n) (VReal 0).
have Hs0 : forall p, In p L -> store_ok s p -> store_ok s0 p.
  move=> p Hp Hs.
  have [K1 [K2 [K3 K4]]] :=
    keyv_bound_neq j (pn p) (fun E => Hn p Hp (esym E)).
  by rewrite /s0; case: (vr); repeat apply store_ok_set; auto.
have Hfr0 : frame c (Some n) s s0.
  rewrite /s0; case: (vr).
  - apply: frame_set; [| by [] | by right].
    by apply: frame_set; [apply: frame_refl | | left].
  by apply: frame_set; [apply: frame_refl | | left].
have Hc0 : forall pp' bW, pp' = PBranch ->
    (forall p, live_anf k bW p -> live_value k (AIte (amap pw cP) tW eW) p) ->
    ctx_ok L k c s0 wP pp' (live_anf k bW) Real.
  move=> pp' bW -> Hl.
  by apply: (ctx_sub L k c s s0 wP pp PBranch
               (live_value k (AIte (amap pw cP) tW eW)) (live_anf k bW) ty Hc);
    auto.
(* the condition, read after the definitions of n *)
have Hcn : forall p, cP = AVar p -> static_ok k p /\ pn p <> j.
  by move=> p E; split; [case: (Hlc p E) | apply: Hn; subst; auto].
have [C1 [_ [C3 _]]] := avoid_spell k cP j Hcn.
have Hsc0 : xev s0 (spell (amap pt cP)) = Some (VBool b).
  by rewrite /s0; case: (vr); rewrite ?xev_set_other.
(* the branch taken *)
have Hbody : exists sb vb db cb s1 x dx,
    run sb s0 = Some s1 /\ frame cb None s0 s1 /\ (c <= cb)%nat /\
    xev s1 vb = Some (VReal x) /\ xev s1 db = Some (VReal dx) /\
    (exists lv, res_vars L lv cb db) /\
    ve = VReal (Dual x dx) /\ (vr = false -> dx = 0) /\
    (if b then st else se') = sb /\ (if b then vt else ve') = vb /\
    (if b then dt else de') = db.
  case: b Hcd Hev Hsc Hsc0 => Hcd Hev Hsc Hsc0.
  - have Hl : forall p, live_anf k tW p ->
        live_value k (AIte (amap pw cP) tW eW) p.
      by rewrite /live_anf /live_value => p H' /=; rewrite H' orb_true_r.
    have := IHt L k c s0 wP PBranch Replay tA tW tT tD Real ve EtA EtW EtT EtD
              (Hc0 PBranch tW erefl Hl) I HtW Hev.
    rewrite Hot => -[_ [Hht [Hz [_ [Hrv [s1 [Hrun [Hfr [Hv Hd]]]]]]]]].
    move/dot_vars_res: Hrv => Hrv.
    case: ve Hht Hev Hz Hv Hd => [[x dx] | | | |] // _ Hev Hz Hv Hd.
    exists st, vt, dt, c, s1, x, dx; repeat split; eauto.
    by move/orb_false_iff => [Hv0 _]; exact: Hz Hv0.
  have Hl : forall p, live_anf k eW p ->
      live_value k (AIte (amap pw cP) tW eW) p.
    by rewrite /live_anf /live_value => p H' /=; rewrite H' !orb_true_r.
  have Hce : ctx_ok L k c1 s0 wP PBranch (live_anf k eW) Real.
    by apply: (ctx_weaken L k c c1 s0 wP PBranch (live_anf k eW)); auto.
  have := IHe L k c1 s0 wP PBranch Replay eA eW eT eD Real ve EeA EeW EeT EeD
            Hce I HeW Hev.
  rewrite Hoe => -[_ [Hht [Hz [_ [Hrv [s1 [Hrun [Hfr [Hv Hd]]]]]]]]].
  move/dot_vars_res: Hrv => Hrv.
  case: ve Hht Hev Hz Hv Hd => [[x dx] | | | |] // _ Hev Hz Hv Hd.
  exists se', ve', de', c1, s1, x, dx; repeat split; eauto; try lia.
  by move/orb_false_iff => [_ Hv0]; exact: Hz Hv0.
have [sb [vb [db [cb [s1 [x [dx [Hrun [Hfr [Hcb [Hv [Hd [[lv Hrv]
       [-> [Hz [Esb [Evb Edb]]]]]]]]]]]]]]]]] := Hbody.
have Hj' : (j < cb)%nat by lia.
split; first lia.
split=> //.
split; first by move=> Hv0 /=; exact: Hz Hv0.
split=> //.
exists (if vr then store_set (store_set s1 (keyv n) (VReal x))
                     (keyv (DotOf n)) (VReal dx)
        else store_set s1 (keyv n) (VReal x)).
have Hfr1 : frame c (Some n) s s1 :=
  frame_chain c cb _ s s0 s1 Hfr0 Hfr Hcb.
destruct vr eqn:Hvr; rewrite /=.
- split.
    have Htail2 :=
      ite_tail L lv cb j s0 s1 sb vb db true x dx Hrun Hv Hd Hrv Hj' Hn.
    rewrite !run_realvar (run_branch _ _ _ _ _ b Hsc0).
    destruct b; subst sb vb db; rewrite -/n in Htail2 *;
      rewrite /s0 /= in Htail2;
      match goal with |- (match ?r with _ => _ end) = _ =>
        replace r with (Some (store_set (store_set s1 (keyv n) (VReal x))
                                (keyv (DotOf n)) (VReal dx)))
          by (symmetry; exact Htail2) end; reflexivity.
  split.
    apply: frame_set; [| by [] | by right].
    by apply: frame_set; [exact: Hfr1 | | left].
  split; first by rewrite store_get_set_other ?store_get_set_same.
  by move=> _; rewrite store_get_set_same.
split.
  have Htail2 :=
    ite_tail L lv cb j s0 s1 sb vb db false x dx Hrun Hv Hd Hrv Hj' Hn.
  rewrite !run_realvar (run_branch _ _ _ _ _ b Hsc0).
  destruct b; subst sb vb db; rewrite -/n in Htail2 *;
    rewrite /s0 /= in Htail2;
    match goal with |- (match ?r with _ => _ end) = _ =>
      replace r with (Some (store_set s1 (keyv n) (VReal x)))
        by (symmetry; exact Htail2) end; reflexivity.
split; first by apply: frame_set; [exact: Hfr1 | | left].
split; first by rewrite store_get_set_same.
by case.
Qed.

(* ---------------------------------------------------------------------------
   Loops. *)

Lemma eval_map_length (ev : val (dual R) -> option (val (dual R))) n i xs :
  eval_map ev i n = Some xs -> length xs = n.
Proof.
elim: n i xs => [| n IH] i xs /= H; first by case: H => <-.
case: (ev (VInt i)) H => [[x | | | |] |] // H.
case E: (eval_map ev (i + 1)%Z n) H => [l |] // [<-] /=.
by rewrite (IH _ _ E).
Qed.

Lemma eval_map_Forall (P : dual R -> Prop) (ev : val (dual R) -> option (val (dual R))) n i xs :
  (forall z x, ev (VInt z) = Some (VReal x) -> P x) -> eval_map ev i n = Some xs -> Forall P xs.
Proof.
move=> HP; elim: n i xs => [| n IH] i xs /= H; first by case: H => <-.
case Ex: (ev (VInt i)) H => [[x | | | |] |] // H.
case E: (eval_map ev (i + 1)%Z n) H => [l |] // [<-].
by constructor; [exact: HP Ex | exact: IH E].
Qed.

(* The loop of a map, with the bound of its indices. *)
Lemma map_loop_bounded (ev : val (dual R) -> option (val (dual R)))
  (body : store R -> option (store R)) (i : dvar nat)
  (Inv : Z -> store R -> list (dual R) -> Prop) (B : Z) :
  (forall j s acc x, (j < B)%Z -> Inv j s acc -> ev (VInt j) = Some (VReal x) ->
     exists s', body (store_set s (KVar i) (VInt j)) = Some s' /\ Inv (j + 1)%Z s' (acc ++ [x])%list) ->
  forall n lo s acc xs, (lo + Z.of_nat n <= B)%Z -> Inv lo s acc -> eval_map ev lo n = Some xs ->
  exists s', exec_up R body i lo n s = Some s' /\ Inv (lo + Z.of_nat n)%Z s' (acc ++ xs)%list.
Proof.
move=> Hstep n.
elim: n => [| n IH] lo s acc xs HB Hinv Hev; rewrite /= in Hev; cbn [exec_up].
- by case: Hev => <-; exists s; rewrite app_nil_r Z.add_0_r.
case E: (ev (VInt lo)) Hev => [[x | | | |] |] // Hev.
case E1: (eval_map ev (lo + 1) n) Hev => [xs1 |] // [<-].
have H1 : (lo < B)%Z by lia.
have H2 : (lo + 1 + Z.of_nat n <= B)%Z by lia.
have [s1 [Hb Hi]] := Hstep _ _ _ _ H1 Hinv E; rewrite Hb.
have [s' [He Hi']] := IH _ _ _ _ H2 Hi E1; exists s'; split; first exact: He.
have -> : (lo + Z.of_nat (S n) = lo + 1 + Z.of_nat n)%Z by lia.
by rewrite -app_assoc in Hi'.
Qed.

Lemma replace_nth_app {B : Type} (a : list B) y z rest :
  replace_nth (length a) z (a ++ y :: rest)%list = Some (a ++ z :: rest)%list.
Proof. by elim: a => [| b a IH] //=; rewrite IH. Qed.

(* Writing the next element of an array being filled from its start. *)
Lemma replace_step {A B : Type} (f : A -> B) acc d (l : list B) :
  (length acc < length l)%nat ->
  replace_nth_z (Z.of_nat (length acc)) (f d) (map f acc ++ skipn (length acc) l)%list =
  Some (map f (acc ++ [d]) ++ skipn (length (acc ++ [d])) l)%list.
Proof.
move=> H; rewrite /replace_nth_z.
case E: (Z.of_nat (length acc) <? 0)%Z; first by move/Z.ltb_lt: E; lia.
rewrite Nat2Z.id.
have Hs : skipn (length acc) l =
    nth (length acc) l (f d) :: skipn (S (length acc)) l.
  clear E; elim: acc l H => [| a acc IH] [| b l] /= H; try lia; auto.
  by apply: IH; lia.
rewrite Hs map_app length_app /=.
rewrite -{1}(length_map f acc) replace_nth_app -app_assoc.
by have -> : (length acc + 1)%nat = S (length acc) by lia.
Qed.
