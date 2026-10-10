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
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

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
rewrite /dual_op1 => Hd.
case E1: (dom_op1 reals f x) Hd => [y0 |] //.
case E2: (dual_partial1 R reals f x y0) => [p |] //= [<- <-].
exists p; split=> // d; by exists (p * d).
Qed.

Lemma dual_op2_linear f x dx y dy z dz :
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z dz) ->
  exists A B, dz = A * dx + B * dy /\
    forall d e, exists t, dual_op2 R reals f (Dual x d) (Dual y e) = Some (Dual z t) /\ t = A * d + B * e.
Proof.
move=> Hd; case: f Hd => Hd; unfold_ops Hd; try discriminate; case: Hd => <- <-.
- exists 1, 1; split; first by ring.
  by move=> d e; eexists; split; [reflexivity | rewrite /=; ring].
- exists 1, (-1); split; first by ring.
  by move=> d e; eexists; split; [reflexivity | rewrite /=; ring].
- exists y, x; split; first by ring.
  by move=> d e; eexists; split; [reflexivity | rewrite /=; ring].
exists (/ y), (- (x / y / y)); split; first by rewrite /Rdiv; ring.
by move=> d e; eexists; split; [reflexivity | rewrite /= /Rdiv; ring].
Qed.

(* The contribution of an operand of an operation of one argument, applied to
   the adjoint e of its result: the derivative times e. *)
Lemma adjoint_op1 s f (a : atom (tvar W)) e x dx y dy p be :
  xev s (spell a) = Some (VReal x) -> xev s e = Some (VReal be) ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) -> partial1 f a = Some p ->
  exists A, dy = A * dx /\ xev s (scale (spell_partial p) e) = Some (VReal (A * be)).
Proof.
move=> Ha He Hd Hp.
have [A [-> HA]] := dual_op1_linear _ _ _ _ _ Hd; exists A; split=> //.
have [t [Ht <-]] := HA be.
exact: (proj2 (tangent_op1 s f a e x be y _ p Ha He Ht Hp)).
Qed.

(* The contributions of the two operands of an operation of two arguments. *)
Lemma adjoint_op2 s f (a b : atom (tvar W)) e x dx y dy z dz pa pb be :
  xev s (spell a) = Some (VReal x) -> xev s (spell b) = Some (VReal y) -> xev s e = Some (VReal be) ->
  dual_op2 R reals f (Dual x dx) (Dual y dy) = Some (Dual z dz) -> partial2 f a b = Some (pa, pb) ->
  exists A B, dz = A * dx + B * dy /\
    xev s (scale (spell_partial pa) e) = Some (VReal (A * be)) /\
    xev s (scale (spell_partial pb) e) = Some (VReal (B * be)).
Proof.
move=> Ha Hb He Hd Hp.
case: f Hd Hp => Hd Hp; unfold_ops Hd; unfold_ops Hp; try discriminate.
all: case: Hp => <- <-; case: Hd => _ <-; cbn [spell_partial].
- exists 1, 1; split; first by ring.
  by split; apply: (xev_scale s) => //; rewrite xev_DReal lit_1.
- exists 1, (-1); split; first by ring.
  by split; apply: (xev_scale s) => //; rewrite xev_DReal ?lit_1 ?lit_m1.
- exists y, x; split; first by ring.
  by split; apply: (xev_scale s).
exists (1 / y), (- (x / (y * y))); split.
  by rewrite /Rdiv Rinv_mult; ring.
split; apply: (xev_scale s) => //.
  by rewrite xev_DOp2 xev_DReal lit_1 Hb.
by rewrite xev_DOp1 xev_DOp2 Ha xev_DOp2 Hb.
Qed.

(* A partial derivative that is a constant does not read its operand. *)
Definition pmentions {V : Type} (p : pexpr V) : Prop := match p with PNum _ => False | _ => True end.

Lemma adjoint_op1_gen s f (a : atom (tvar W)) e x dx y dy p be :
  partial1 f a = Some p -> xev s e = Some (VReal be) ->
  dual_op1 R reals f (Dual x dx) = Some (Dual y dy) ->
  (pmentions p -> xev s (spell a) = Some (VReal x)) ->
  exists A, dy = A * dx /\ xev s (scale (spell_partial p) e) = Some (VReal (A * be)).
Proof.
move=> Hp He Hd.
case: p Hp => [q | l | g q | g q r] Hp Ha;
  try by apply: (adjoint_op1 s f a e x dx y dy) => //; apply: Ha.
case: f Hp Hd {Ha} => [| | | | | | z | u] Hp Hd; rewrite /= in Hp;
  try discriminate.
- case: Hp => <-; unfold_ops Hd; rewrite lit_m1 in Hd; case: Hd => _ <-.
  exists (-1); split=> //.
  by rewrite /= xev_DOp1 He /=; congr (Some (VReal _)); ring.
case: z Hp Hd => [| z | z] Hp Hd; rewrite /= in Hp; try discriminate.
case: Hp => <-; unfold_ops Hd.
rewrite lit_0 in Hd; case: Hd => _ <-; exists 0; split=> //.
by rewrite /= xev_DOp2 xev_DReal lit_0 He.
Qed.

(* The reverse sweep of a unary operation reads its operand when the partial
   derivative mentions it. *)
Lemma reads_op1 f (a : tvar W) (b : avar) p :
  partial1 f (AVar a) = Some p -> pmentions p -> avaried b = true ->
  atom_member (AVar b) (read_by (AVar b) (partial1 f (AVar b))) = true.
Proof.
move=> Hp Hm Hb; rewrite /read_by /= Hb.
case: f Hp => [| | | | | | z | u] /= Hp; try discriminate;
  try (case: z Hp => [| z | z] /= Hp);
  try by case: Hp => E; rewrite -E in Hm.
all: by rewrite ?atom_member_union /= ?Nat.eqb_refl /= ?orb_true_r.
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
move=> Hd; case: f Hd => Hd; unfold_ops Hd; try discriminate.
all: by case: Hd => _ <- /=; rewrite /Rdiv ?Rinv_mult; ring.
Qed.

(* The contribution to the first operand reads the second one (Mul, Divide). *)
Lemma contrib_a s f (a b : atom (tvar W)) e x y be pa pb :
  partial2 f a b = Some (pa, pb) -> xev s e = Some (VReal be) ->
  ((f = Mul \/ f = Divide) -> xev s (spell b) = Some (VReal y)) ->
  xev s (scale (spell_partial pa) e) = Some (VReal (coef_a f x y * be)).
Proof.
move=> Hp He Hb; case: f Hp Hb => /= Hp Hb; try discriminate.
all: case: Hp => <- _; cbn [spell_partial coef_a]; apply: xev_scale He.
- by rewrite xev_DReal lit_1.
- by rewrite xev_DReal lit_1.
- by apply: Hb; left.
by rewrite xev_DOp2 xev_DReal lit_1 Hb //; right.
Qed.

(* The contribution to the second operand reads the first one (Mul, Divide)
   and the second one (Divide). *)
Lemma contrib_b s f (a b : atom (tvar W)) e x y be pa pb :
  partial2 f a b = Some (pa, pb) -> xev s e = Some (VReal be) ->
  ((f = Mul \/ f = Divide) -> xev s (spell a) = Some (VReal x)) ->
  (f = Divide -> xev s (spell b) = Some (VReal y)) ->
  xev s (scale (spell_partial pb) e) = Some (VReal (coef_b f x y * be)).
Proof.
move=> Hp He Ha Hb; case: f Hp Ha Hb => /= Hp Ha Hb; try discriminate.
all: case: Hp => _ <-; cbn [spell_partial coef_b]; apply: xev_scale He.
- by rewrite xev_DReal lit_1.
- by rewrite xev_DReal lit_m1.
- by apply: Ha; left.
by rewrite xev_DOp1 xev_DOp2 Ha ?xev_DOp2 ?Hb //; right.
Qed.

(* The primal part of a dual operation is the operation of the reals. *)
Lemma primal_eval_op1 f va ve :
  eval_op1 (duals reals) f va = Some ve -> eval_op1 reals f (primal va) = Some (primal ve).
Proof.
case: va => [[x dx] | | | |] //=.
case E: (real_op1 f x) => [y |] //=.
by case: (dual_partial1 R reals f x y) => [p |] //= [<-].
Qed.

Lemma primal_eval_op2 f va vb ve :
  eval_op2 (duals reals) f va vb = Some ve -> eval_op2 reals f (primal va) (primal vb) = Some (primal ve).
Proof.
case: va => [[x dx] | za | | |]; case: vb => [[y dy] | zb | | |] //=.
- case: (comparison f).
    by rewrite /dual_cmp /=; case: (real_cmp f x y) => //= ? [<-].
  by case: f => //= - [<-].
by move=> [<-]; case: f.
Qed.

(* The value of an atom whose variable holds its value. *)
Lemma aspell_ok k s (aP : atom pv) d :
  (forall p, aP = AVar p -> static_ok k p /\ store_get s (keyv (stored p)) = Some (primal (pd p))) ->
  aeval_atom (duals reals) (amap pd aP) = Some d ->
  xev s (spell (amap pt aP)) = Some (primal d).
Proof.
move=> Hs Hd; case: aP Hs Hd => [q | str | z] Hs /= Hd.
- case: Hd => <-; have [[_ [_ [Hstore _]]] H] := Hs q erefl.
  by rewrite /xev /= Hstore.
- have [x [Hx ->]] := aeval_literal _ _ Hd.
  by rewrite xev_DReal Hx.
by case: Hd => <-.
Qed.

(* Sets of atoms. *)
Lemma same_term_trans a b c : same_term a b = true -> same_term b c = true -> same_term a c = true.
Proof.
case: a => [a | a | a]; case: b => [b | b | b]; case: c => [c | c | c] //=.
by move=> /Nat.eqb_eq -> /Nat.eqb_eq ->; rewrite Nat.eqb_refl.
Qed.

Lemma same_term_sym a b : same_term a b = same_term b a.
Proof. by case: a; case: b => //= *; apply: Nat.eqb_sym. Qed.

Lemma atom_member_union x l l' :
  atom_member x (atom_union l l') = atom_member x l || atom_member x l'.
Proof.
elim: l' l => [| y ys IH] l /=; first by rewrite orb_false_r.
case Ey: (atom_member y l); rewrite IH /=; last first.
  by case: (same_term x y); case: (atom_member x l); case: (atom_member x ys).
case Exy: (same_term x y) => //=.
move: Ey; rewrite /atom_member => /existsb_exists [z [Iz Ez]].
have -> // : existsb (same_term x) l = true.
by apply/existsb_exists; exists z; split=> //; apply: same_term_trans Ez.
Qed.

Lemma atom_member_var q : atom_member (AVar q) [AVar q] = true.
Proof. by rewrite /= Nat.eqb_refl. Qed.

Lemma atom_member_atoms q (a : atom avar) l :
  In a l -> a = AVar q -> atom_member (AVar q) (atoms_of_atoms l) = true.
Proof.
move=> Hi Ea; subst a; elim: l Hi => [| b l IH] //= Hi.
rewrite atom_member_union; case: Hi => [-> | Hi].
  by rewrite /= Nat.eqb_refl.
by rewrite IH // orb_true_r.
Qed.

Lemma atom_member_remove x y l :
  same_term x y = false -> atom_member y (atom_remove x l) = atom_member y l.
Proof.
move=> H; rewrite /atom_member /atom_remove; elim: l => [| z l IH] //=.
case E: (same_term x z) => /=; rewrite IH //.
case E': (same_term y z) => //=.
by rewrite same_term_sym in E'; rewrite (same_term_trans _ _ _ E E') in H.
Qed.

(* ---------------------------------------------------------------------------
   The pairing: for each storage that carries an adjoint, the tangent of the
   variable it holds (a value of the reals: a real, or an array) times its
   adjoint in the store. *)

Definition barv (s : store R) (n : dvar W) : option (val R) := store_get s (keyv (BarOf n)).

Definition dotr (a b : list R) : R := fold_right Rplus 0 (map (fun '(p, q) => p * q) (combine a b)).

Lemma dotr_cons a l b m : dotr (a :: l) (b :: m) = a * b + dotr l m.
Proof. by []. Qed.

(* Changing one element of the second vector. *)
Lemma dotr_replace n l m m' lk mk w :
  nth_error l n = Some lk -> nth_error m n = Some mk -> replace_nth n w m = Some m' ->
  dotr l m' = dotr l m + lk * (w - mk).
Proof.
elim: n l m m' => [| n IH] [| a l] [| b m] m' //= Hl Hm.
  by case: Hl => <-; case: Hm => <- [<-]; rewrite !dotr_cons; ring.
case E: (replace_nth n w m) => [m1 |] // [<-].
by rewrite !dotr_cons (IH l m m1 Hl Hm E); ring.
Qed.

Lemma dotr_sym l m : dotr l m = dotr m l.
Proof.
elim: l m => [| a l IH] [| b m] //.
by rewrite !dotr_cons IH; ring.
Qed.

Lemma replace_nth_nth {A : Type} n (w : A) m m' :
  replace_nth n w m = Some m' -> exists mk, nth_error m n = Some mk /\ nth_error m' n = Some w /\ length m' = length m.
Proof.
elim: n m m' => [| n IH] [| b m] m' //=.
  by case=> <-; exists b.
case E: (replace_nth n w m) => [m1 |] // [<-].
by have [mk [A1 [A2 A3]]] := IH m m1 E; exists mk; rewrite /= A3.
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
move=> Hn Hn' E; rewrite /barv store_get_set_other // => K.
by case: (keyv_inj (BarOf n) (BarOf n') Hn Hn' K).
Qed.

Lemma barv_set_same s n w : barv (store_set s (keyv (BarOf n)) w) n = Some w.
Proof. exact: store_get_set_same. Qed.

Lemma pairing_set_other O s n w :
  owners_ok O -> consistent n -> ~ In n (map snd O) ->
  pairing O (store_set s (keyv (BarOf n)) w) = pairing O s.
Proof.
elim: O => [| [t n'] O IH] Ho Hn Hi //=.
have Hc' : consistent n' by apply: (Ho t); left.
have Hne : n <> n' by move=> E; apply: Hi; left.
have Ho' : owners_ok O by move=> t' m I; apply: (Ho t'); right.
have Hi' : ~ In n (map snd O) by move=> I; apply: Hi; right.
by rewrite (barv_set_other _ _ _ _ Hn Hc' Hne) IH.
Qed.

Lemma pairing_set_in O s t n w :
  owners_ok O -> NoDup (map snd O) -> In (t, n) O ->
  pairing O (store_set s (keyv (BarOf n)) w) = pairing O s - inner t (barv s n) + inner t (Some w).
Proof.
elim: O => [| [t' n'] O IH] Ho //= /NoDup_cons_iff [Hn Hd] Hi.
have Ho' : owners_ok O by move=> t0 m I; apply: (Ho t0); right.
have Hc' : consistent n' by apply: (Ho t'); left.
case: Hi => [[Et En] | Hi].
  by subst t' n'; rewrite barv_set_same pairing_set_other //; ring.
have Hc : consistent n by apply: (Ho t); right.
have Hne : n' <> n.
  by move=> E; apply: Hn; apply/(in_map_iff _ _ _); exists (t, n); rewrite E.
by rewrite (barv_set_other _ _ _ _ Hc Hc' (not_eq_sym Hne)) IH //; ring.
Qed.

Lemma dvar_eq_consistent a b : consistent a -> consistent b -> Simplify.dvar_eq nat a b = true <-> a = b.
Proof.
elim: a b => [[i j] | a IH | a IH | a IH |] [[i' j'] | b | b | b |] //= Ha Hb;
  split=> // E; try discriminate.
- by move/Nat.eqb_eq: E => E; subst.
- by case: E => E1 E2; subst; rewrite Nat.eqb_refl.
all: first [by congr (_ _); apply/IH | by case: E => E; subst; apply/IH].
Qed.

(* Replacing the tangent of a storage that is not an owner. *)
Lemma oset_notin O n t : owners_ok O -> consistent n -> ~ In n (map snd O) -> oset O n t = O.
Proof.
elim: O => [| [t' n'] O IH] Ho Hn Hi //=.
have Hc' : consistent n' by apply: (Ho t'); left.
case E: (Simplify.dvar_eq nat n n').
  by move/(dvar_eq_consistent _ _ Hn Hc'): E => E; subst; case: Hi; left.
congr (_ :: _); apply: IH => //.
  by move=> t0 m I; apply: (Ho t0); right.
by move=> I; apply: Hi; right.
Qed.

(* Replacing the tangent of an owner by the one it has. *)
Lemma oset_same O n t :
  owners_ok O -> NoDup (map snd O) -> In (t, n) O -> oset O n t = O.
Proof.
elim: O => [| [t' n'] O IH] Ho //= /NoDup_cons_iff [Hn Hd] Hi.
have Ho' : owners_ok O by move=> t0 m I; apply: (Ho t0); right.
have Hcn : consistent n by apply: (Ho t).
have Hcn' : consistent n' by apply: (Ho t'); left.
case: Hi => [[Et En] | Hi].
  subst t' n'; rewrite (proj2 (dvar_eq_consistent n n Hcn Hcn) erefl).
  by congr (_ :: _); apply: oset_notin.
case E: (Simplify.dvar_eq nat n n').
  move/(dvar_eq_consistent _ _ Hcn Hcn'): E => E; subst n'.
  by case: Hn; apply/(in_map_iff _ _ _); exists (t, n).
by congr (_ :: _); apply: IH.
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
(* A place outside the body of an in-place loop. *)
Definition not_in_loop (pp : pplace) : Prop := match pp with PArray _ _ => False | _ => True end.

Record actx (L : list pv) (k c : nat) (s : store R) (wP : option (atom pv)) (pp : pplace)
  (live tb : pv -> Prop) (ty : ty) : Prop := {
  a_sctx : sctx L k c wP pp live ty;
  a_bar : forall p, In p L -> tbar (pt p) = avaried (pa p);
  a_store : forall p, In p L -> tb p -> store_get s (keyv (stored p)) = Some (primal (pd p));
  a_tape : forall p, In p L -> trecorded (pt p) = true ->
             exists l, store_get s (keyv (TapeOf (stored p))) = Some (VTape l);
  a_owner : forall o, owner wP pp = Some o -> (not_in_loop pp \/ tb o) ->
             store_get s (keyv (stored o)) = Some (primal (pd o));
  a_tid : forall o, owner wP pp = Some o -> not_in_loop pp -> tid (pt o) <> None
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
Proof. by move=> v l H; exists l. Qed.

Lemma tapes_kept_trans s s1 s2 : tapes_kept s s1 -> tapes_kept s1 s2 -> tapes_kept s s2.
Proof. by move=> H1 H2 v l /H1 [l1 /H2]. Qed.

(* Writing a key that is not a tape. *)
Lemma tapes_kept_set s x w : ~ is_tape x -> consistent x -> tapes_kept s (store_set s (keyv x) w).
Proof.
move=> Ht Hc v l H; exists l; rewrite store_get_set_other // => K.
by case: x Ht Hc K => [[i j] | x | x | x |] //=.
Qed.

Lemma tapes_kept_set_tape s v0 l0 : tapes_kept s (store_set s (keyv (TapeOf v0)) (VTape l0)).
Proof.
move=> v l H; rewrite store_get_set.
by case: (key_eqb (keyv (TapeOf v0)) (keyv (TapeOf v))); [exists l0 | exists l].
Qed.

(* The tapes of the variables opened before c, but the one of the storage
   updated in place, keep their contents. *)
Definition tapes_same (c : nat) (ex : option (dvar W)) (s s' : store R) : Prop :=
  forall v, below c v -> consistent v -> ex <> Some v ->
  store_get s' (keyv (TapeOf v)) = store_get s (keyv (TapeOf v)).

Lemma tapes_same_refl c ex s : tapes_same c ex s s.
Proof. by []. Qed.

Lemma tapes_same_trans c ex s s1 s2 : tapes_same c ex s s1 -> tapes_same c ex s1 s2 -> tapes_same c ex s s2.
Proof. by move=> H1 H2 v Hb Hc He; rewrite (H2 v Hb Hc He) (H1 v Hb Hc He). Qed.

Lemma tapes_same_mono c c' ex s s' : tapes_same c' ex s s' -> (c <= c')%nat -> tapes_same c ex s s'.
Proof. by move=> H Hc v Hb; apply: H; apply: below_mono Hb Hc. Qed.

Lemma tapes_same_none c ex s s' : tapes_same c None s s' -> tapes_same c ex s s'.
Proof. by move=> H v Hb Hc _; apply: H. Qed.

(* Writing a key that is not a tape. *)
Lemma tapes_same_set c ex s x w : ~ is_tape x -> consistent x -> tapes_same c ex s (store_set s (keyv x) w).
Proof.
move=> Ht Hc v _ _ _; rewrite store_get_set_other // => K.
by case: x Ht Hc K => [[i j] | x | x | x |] //=.
Qed.

(* Writing the tape of a variable not opened before c, or of the storage updated in place. *)
Lemma tapes_same_set_tape c ex s x w :
  consistent x -> (~ below c x \/ ex = Some x) -> tapes_same c ex s (store_set s (keyv (TapeOf x)) w).
Proof.
move=> Hcx Hx v Hb Hc He; rewrite store_get_set_other // => K.
case: (keyv_inj (TapeOf x) (TapeOf v) Hcx Hc K) => E; subst v.
by case: Hx.
Qed.

(* The tapes stay tapes, and those opened before c keep their contents but
   the one of the storage updated in place. *)
Definition tkeep (c : nat) (ex : option (dvar W)) (s s' : store R) : Prop :=
  tapes_kept s s' /\ tapes_same c ex s s'.

Lemma tkeep_refl c ex s : tkeep c ex s s.
Proof. by split; [apply: tapes_kept_refl | apply: tapes_same_refl]. Qed.

Lemma tkeep_trans c ex s s1 s2 : tkeep c ex s s1 -> tkeep c ex s1 s2 -> tkeep c ex s s2.
Proof.
move=> [A B] [C D]; split; first exact: tapes_kept_trans A C.
exact: tapes_same_trans B D.
Qed.

Lemma tkeep_mono c c' ex s s' : tkeep c' ex s s' -> (c <= c')%nat -> tkeep c ex s s'.
Proof. by move=> [A B] H; split=> //; apply: tapes_same_mono B H. Qed.

Lemma tkeep_none c ex s s' : tkeep c None s s' -> tkeep c ex s s'.
Proof. by move=> [A B]; split=> //; apply: tapes_same_none. Qed.

(* The tape of a variable opened after c may change. *)
Lemma tkeep_fresh c c' x ex s s' : tkeep c' (Some x) s s' -> ~ below c x -> (c <= c')%nat -> tkeep c ex s s'.
Proof.
move=> [A B] Hx Hc; split=> // v Hb Hcv _; apply: B => //.
  exact: below_mono Hb Hc.
by case=> E; subst v.
Qed.

Lemma tkeep_set c ex s x w : ~ is_tape x -> consistent x -> tkeep c ex s (store_set s (keyv x) w).
Proof.
by move=> Ht Hc; split; [apply: tapes_kept_set | apply: tapes_same_set].
Qed.

Lemma tkeep_set_tape c ex s x l :
  consistent x -> (~ below c x \/ ex = Some x) -> tkeep c ex s (store_set s (keyv (TapeOf x)) (VTape l)).
Proof.
by move=> Hc Hx; split;
  [apply: tapes_kept_set_tape | apply: tapes_same_set_tape].
Qed.

(* The reverse sweep leaves the keys opened before c unchanged, but the
   tapes, the storage updated in place, and the adjoints of the owners. *)
Definition rev_frame (c : nat) (ex : option (dvar W)) (O : owners) (s s' : store R) : Prop :=
  forall v, below c v -> consistent v -> ~ is_tape v -> ex <> Some v ->
  (forall n, v = BarOf n -> ~ In n (map snd O)) ->
  store_get s' (keyv v) = store_get s (keyv v).

(* The reverse sweep of a value may also change the value itself (a fold
   restores its state). *)
Definition rev_frame_x (c : nat) (ex : option (dvar W)) (n : dvar W) (O : owners) (s s' : store R) : Prop :=
  forall v, v <> n -> below c v -> consistent v -> ~ is_tape v -> ex <> Some v ->
  (forall m, v = BarOf m -> ~ In m (map snd O)) ->
  store_get s' (keyv v) = store_get s (keyv v).

(* Between the end of the forward sweep of a body and the start of its
   reverse sweep, the primal keys opened before c' keep their values (the
   reverse sweep of a loop replays the body before transposing it). *)
Definition agree_prim (c' : nat) (ex : option (dvar W)) (s1 s2 : store R) : Prop :=
  (forall v, below c' v -> consistent v -> is_primal v ->
   store_get s2 (keyv v) = store_get s1 (keyv v)) /\
  (forall v, below c' v -> consistent v ->
   store_get s2 (keyv (TapeOf v)) = store_get s1 (keyv (TapeOf v))).

Lemma agree_prim_refl c' ex s : agree_prim c' ex s s.
Proof. by []. Qed.

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
rewrite /keyv => H1 H2 [E]; case: x H1 E => // x _.
by case: v H2 => [[? ?] | | | |] //= H2 _; apply: H2.
Qed.

Lemma assign_bar s l w s1 :
  bar_target l -> assign reals s (Simplify.out_dexpr nat l) w = Some s1 ->
  exists x w', is_bar x /\ s1 = store_set s (keyv x) w'.
Proof.
case: l => [x | | | a i | |] //= Hb Ha.
  by case: Ha => <-; exists x, w.
case: a Hb Ha => [x | | | | |] //= Hb Ha.
repeat match type of Ha with context [match ?e with _ => _ end] =>
  destruct e end; try discriminate.
by case: Ha => <-; eexists x, _.
Qed.

Lemma run_bars ss s s' :
  Forall bar_stmt ss -> run ss s = Some s' -> forall v, ~ is_bar v -> store_get s' (keyv v) = store_get s (keyv v).
Proof.
elim: ss s => [| st ss IH] s; first by move=> _ [<-].
move=> /Forall_cons_iff [Hst Hf] Hr v Hv.
rewrite run_cons in Hr.
case E: (exec reals (Simplify.out_dstmt nat st) s) Hr => [s1 |] // Hr.
rewrite (IH s1 Hf Hr v Hv).
case: st Hst E
  => [d x e | x | x | l e | l e | ? ? ? | ? ? ? ? | ? ? ? ? | ? ? | ? ? | ?]
  //= Hst E.
- case: (xeval _ _ _) E => // w [<-].
  by apply: store_get_set_other; exact: keyv_bar_other Hst Hv.
- case: (xeval _ _ _) E => // w E.
  have [xb [wb [Hx ->]]] := assign_bar _ _ _ _ Hst E.
  by apply: store_get_set_other; exact: keyv_bar_other Hx Hv.
case: (xeval _ _ (Simplify.out_dexpr nat l)) E => // - [] // a.
case: (xeval _ _ _) => // - [] // b E.
have [xb [wb [Hx ->]]] := assign_bar _ _ _ _ Hst E.
by apply: store_get_set_other; exact: keyv_bar_other Hx Hv.
Qed.

Lemma tkeep_bars c ex ss s s' : Forall bar_stmt ss -> run ss s = Some s' -> tkeep c ex s s'.
Proof.
move=> Hf R; have Ht v : ~ is_bar (TapeOf v) by [].
split=> [v l Hv | v _ _ _]; last exact: run_bars Hf R _ (Ht v).
by exists l; rewrite (run_bars ss s s' Hf R _ (Ht v)).
Qed.

Lemma vo_kept_bars vo ss s s' : Forall bar_stmt ss -> run ss s = Some s' -> vo_kept vo s s'.
Proof. by move=> Hf Hr t _ Hb; apply: run_bars Hf Hr t Hb. Qed.

Lemma vo_kept_refl vo s : vo_kept vo s s.
Proof. by []. Qed.

Lemma vo_kept_trans vo s s1 s2 : vo_kept vo s s1 -> vo_kept vo s1 s2 -> vo_kept vo s s2.
Proof. by move=> H1 H2 t E B; rewrite (H2 t E B) (H1 t E B). Qed.

Lemma vo_kept_set_bar vo s x w : is_bar x -> vo_kept vo s (store_set s (keyv x) w).
Proof.
by move=> Hx t _ Hb; apply: store_get_set_other; exact: keyv_bar_other Hx Hb.
Qed.

Lemma bar_some (a : atom (tvar W)) bx : @bar W a = Some bx -> exists x, bx = DVar x /\ is_bar x.
Proof. by case: a => [y | |] //=; case: (tbar y) => // - [<-]; eexists. Qed.

Lemma contribution_bars (a : atom (tvar W)) p x : Forall bar_stmt (contribution W a p x).
Proof.
rewrite /contribution; case E: (@bar W a) => [bx |] //.
by have [y [-> Hy]] := bar_some a bx E; repeat constructor.
Qed.

(* Adds the clause of the value to the reverse sweep of bar-only code. *)
Lemma keep_add (Q : Prop) vo rv s2 (P : store R -> Prop) :
  Forall bar_stmt rv -> (exists s3, run rv s2 = Some s3 /\ P s3) ->
  exists s3, run rv s2 = Some s3 /\ (Q -> vo_kept vo s2 s3) /\ P s3.
Proof.
move=> Hf [s3 [R H]]; exists s3; split=> //; split=> // _.
exact: vo_kept_bars Hf R.
Qed.

(* The states of a fold before each of its steps. *)
Fixpoint fold_trace (ev : val (dual R) -> val (dual R) -> option (val (dual R))) (i : Z) (n : nat)
  (s : val (dual R)) : option (list (val (dual R))) :=
  match n with
  | O => Some []
  | S n' => match ev (VInt i) s with
            | Some s1 => match fold_trace ev (i + 1) n' s1 with Some tr => Some (s :: tr) | None => None end
            | None => None
            end
  end.

Definition real_of (v : val (dual R)) : R := match v with VReal d => dfst d | _ => 0 end.

(* The index of the set that ends a body, as evaluated. *)
Fixpoint set_index (b : anf (val (dual R)) bare) : option Z :=
  match b with
  | ALet _ e b' =>
      match aeval_value (duals reals) e with
      | Some v =>
          match e, b' v with
          | ASet _ i _, ARet _ => match aeval_atom (duals reals) i with Some (VInt z) => Some z | _ => None end
          | _, _ => set_index (b' v)
          end
      | None => None
      end
  | ARet _ => None
  end.

(* The elements one step of an in-place fold pushes on the tape of its
   storage, from the state st before the step: the element its final set
   overwrites, or, when the step ends with an inner in-place fold (whose
   state starts from st), the elements the steps of that fold push. *)
Fixpoint body_pushes (b : anf (val (dual R)) bare) (st : val (dual R))
  {struct b} : list R :=
  match b with
  | ALet _ e b' =>
      match aeval_value (duals reals) e with
      | Some v =>
          match e, b' v with
          | ASet _ i _, ARet _ =>
              match aeval_atom (duals reals) i, st with
              | Some (VInt zi), VArray l =>
                  [match nth_z zi (map dfst l) with Some x => x | None => 0 end]
              | _, _ => []
              end
          | AFold _ lo hi _ bi, ARet _ =>
              match aeval_atom (duals reals) lo, aeval_atom (duals reals) hi with
              | Some (VInt l), Some (VInt h) =>
                  match fold_trace (fun x y => aeval (duals reals) (bi x y))
                          l (count l h) st with
                  | Some tr =>
                      (fix go (z : Z) (tr : list (val (dual R))) : list R :=
                         match tr with
                         | [] => []
                         | s :: tr' =>
                             (body_pushes (bi (VInt z) s) s ++ go (z + 1)%Z tr')%list
                         end) l tr
                  | None => []
                  end
              | _, _ => []
              end
          | _, _ => body_pushes (b' v) st
          end
      | None => []
      end
  | ARet _ => []
  end.

(* The elements the steps of an in-place fold push, from the states before
   each step. *)
Fixpoint fold_pushes (b : val (dual R) -> val (dual R) -> anf (val (dual R)) bare) (z : Z)
  (tr : list (val (dual R))) : list R :=
  match tr with
  | [] => []
  | st :: tr' => (body_pushes (b (VInt z) st) st ++ fold_pushes b (z + 1) tr')%list
  end.

(* Whether the innermost in-place fold of a nest records its states: a step
   that ends with an inner in-place fold does not read its own state, the
   steps of the innermost fold (the one whose step ends with a set) push the
   elements they overwrite when its state is live. *)
Fixpoint tail_fold_live (cv : bool) (k : nat) (b : anf avar bare) {struct b} :
  option bool :=
  match b with
  | ALet _ e b' =>
      match e, b' (let_binder k e) with
      | AFold _ _ _ init bi, ARet _ =>
          let '(i, s) := fold_binders k init bi in
          match tail_fold_live cv (S (S k)) (bi i s) with
          | Some l => Some l
          | None => Some (state_live cv k init bi)
          end
      | _, _ => tail_fold_live cv (S k) (b' (let_binder k e))
      end
  | ARet _ => None
  end.

Definition fold_live (cv : bool) (k : nat) (init : atom avar)
  (b : avar -> avar -> anf avar bare) : bool :=
  let '(i, s) := fold_binders k init b in
  match tail_fold_live cv (S (S k)) (b i s) with
  | Some l => l
  | None => state_live cv k init b
  end.

Lemma tail_fold_live_records cv :
  forall b k l, tail_fold_live cv k b = Some l -> records_in cv k b = false ->
  l = false.
Proof.
fix IH 1 => -[a e b' | x] k l //=.
case: e => [f0 a0 | f0 a0 b0 | a0 i0 | a0 i0 v0 | c0 t0 e0 | lo0 hi0 bm
           | fa lo hi init bi];
  try by move=> Ht /orb_false_iff [_ Hr]; exact: IH _ _ _ Ht Hr.
case Eb: (b' (let_binder k (AFold fa lo hi init bi))) => [aa ee bb | r].
  by rewrite -Eb => Ht /orb_false_iff [_ Hr]; exact: IH _ _ _ Ht Hr.
move=> Ht /orb_false_iff [Hr _]; move: Hr => /= /orb_false_iff [Hs Hri].
case El: (tail_fold_live cv (S (S k)) _) Ht => [l' |] [<-].
  exact: IH _ _ _ El Hri.
exact: Hs.
Qed.

(* A fold whose forward sweep records nothing has no live innermost fold. *)
Lemma fold_live_records cv k fa lo hi init b :
  records cv k (AFold fa lo hi init b) = false -> fold_live cv k init b = false.
Proof.
move=> /= /orb_false_iff [Hs Hri]; rewrite /fold_live /=.
case El: (tail_fold_live cv (S (S k)) _) => [l' |] //.
exact: tail_fold_live_records El Hri.
Qed.

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
rewrite /inplace => Hs; case Eo: (owner wP pp) => [o |] // [<-].
have Ho : In o L.
  destruct pp as [| | | ix sx]; rewrite /= in Eo; try discriminate.
    destruct wP as [[y | |] |]; try discriminate.
    case: (vty (pw y)) Eo => // ? [<-].
    by have [y' [[<-] [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl.
  by case: Eo => <-; exact: (proj1 (proj2 (s_place _ _ _ _ _ _ _ Hs))).
by rewrite /stored /=; split; first exact: (s_num _ _ _ _ _ _ _ Hs o Ho).
Qed.

(* Outside a loop, a live variable stored in place is the owner, a varied array. *)
Lemma same_ex_read L k c wP pp (live : pv -> Prop) ty p o :
  sctx L k c wP pp live ty -> not_in_loop pp -> owner wP pp = Some o -> In p L -> stored p = stored o -> live p ->
  p = o /\ avaried (pa o) = true.
Proof.
move=> Hs Hl Ho Hp E Hlv.
have Epn : pn p = pn o by case: E.
case: (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Epn) => [Epo | //]; subst p.
split=> //.
destruct pp as [| | | ix sx]; rewrite /= in Hl Ho; try discriminate;
  try contradiction.
destruct wP as [[y | |] |]; try discriminate.
case Ey: (vty (pw y)) Ho => // [ny] [Eyo]; subst y.
have Har : is_array (vty (pw o)) by rewrite Ey.
exact: (proj2 (s_top _ _ _ _ _ _ _ Hs o erefl erefl Har) Hlv).
Qed.

(* Bar-only reverse code gives the storage updated in place back. *)
Lemma keep_add2 (Q : Prop) L k c c' wP pp live ty vo rv s s1 s2 (P : store R -> Prop) :
  sctx L k c wP pp live ty -> (c <= c')%nat -> agree_prim c' (inplace wP pp) s1 s2 -> same_ex pp wP s s1 ->
  Forall bar_stmt rv -> (exists s3, run rv s2 = Some s3 /\ P s3) ->
  exists s3, run rv s2 = Some s3 /\ (Q -> vo_kept vo s2 s3) /\ same_ex pp wP s s3 /\
    tkeep c (inplace wP pp) s2 s3 /\ P s3.
Proof.
move=> Hs Hcc Hag Hsx Hf [s3 [R H]]; exists s3; split=> //.
split; first by move=> _; exact: vo_kept_bars Hf R.
split; last by split; first exact: tkeep_bars Hf R.
move=> Hl o Ho Hav.
have He : inplace wP pp = Some (stored o) by rewrite /inplace Ho.
have [Hb [Hc Hp]] := ex_below _ _ _ _ _ _ _ _ Hs He.
have Hnb : ~ is_bar (stored o) by [].
rewrite (run_bars rv s2 s3 Hf R (stored o) Hnb).
rewrite (proj1 Hag (stored o) (below_mono c c' _ Hb Hcc) Hc Hp).
exact: Hsx Hl o Ho Hav.
Qed.

(* The tape of a fold whose state is recorded. For a scalar fold: the states
   before each step, the last first. For an in-place fold: the elements the
   steps overwrite, the last first, the storage holding the final array. *)
Definition fold_tape (k : nat) (eA : value avar bare) (eW : value vinfo bare) (eD : value (val (dual R)) bare)
  (s : store R) (n : dvar W) : Prop :=
  match eA, eW, eD with
  | AFold fa loA hiA initA bA, AFold _ _ _ initW _, AFold _ lo hi init b =>
      match aeval_atom (duals reals) lo, aeval_atom (duals reals) hi, aeval_atom (duals reals) init with
      | Some (VInt l), Some (VInt h), Some s0 =>
          forall tr, fold_trace (fun v w => aeval (duals reals) (b v w)) l (count l h) s0 = Some tr ->
            (ty_eqb (of_atom initW) Real = true -> state_live cv k initA bA = true ->
               store_get s (keyv (TapeOf n)) = Some (VTape (rev (map real_of tr)))) /\
            (is_array (of_atom initW) ->
               (fold_live cv k initA bA = true ->
                  (exists rest, store_get s (keyv (TapeOf n)) = Some (VTape (rev (fold_pushes b l tr) ++ rest))) /\
                  forall ve, eval_fold (fun v w => aeval (duals reals) (b v w)) l (count l h) s0 = Some ve ->
                    store_get s (keyv n) = Some (primal ve)))
      | _, _, _ => True
      end
  | _, _, _ => True
  end.

(* The forward sweep of an in-place fold inside a loop body, when its
   innermost fold is live: the elements its steps overwrite are pushed on the
   tape of its storage, from s to s'. *)
Definition fold_grow (k : nat) (eA : value avar bare)
  (eD : value (val (dual R)) bare) (s s' : store R) (n : dvar W) : Prop :=
  match eA, eD with
  | AFold _ _ _ initA bA, AFold _ lo hi init b =>
      match aeval_atom (duals reals) lo, aeval_atom (duals reals) hi,
        aeval_atom (duals reals) init with
      | Some (VInt l), Some (VInt h), Some s0 =>
          forall tr,
          fold_trace (fun v w => aeval (duals reals) (b v w)) l (count l h) s0
            = Some tr ->
          fold_live cv k initA bA = true ->
          forall l0, store_get s (keyv (TapeOf n)) = Some (VTape l0) ->
          store_get s' (keyv (TapeOf n)) =
            Some (VTape (rev (fold_pushes b l tr) ++ l0))
      | _, _, _ => True
      end
  | _, _ => True
  end.

(* The reverse sweep of an in-place fold inside a loop body, from s to s',
   when its innermost fold is live: it leaves in its storage the state before
   the fold, the value of the owner o, and pops from the tape of the storage
   the elements the steps pushed. *)
Definition fold_back (k : nat) (eA : value avar bare)
  (eD : value (val (dual R)) bare) (s s' : store R) (n : dvar W) (o : pv) :
  Prop :=
  match eA, eD with
  | AFold _ _ _ initA bA, AFold _ lo hi _ b =>
      match aeval_atom (duals reals) lo, aeval_atom (duals reals) hi with
      | Some (VInt l), Some (VInt h) =>
          fold_live cv k initA bA = true ->
          exists tr,
          fold_trace (fun v w => aeval (duals reals) (b v w)) l (count l h)
            (pd o) = Some tr /\
          store_get s' (keyv n) = Some (primal (pd o)) /\
          forall l0,
          store_get s (keyv (TapeOf n)) =
            Some (VTape (rev (fold_pushes b l tr) ++ l0)) ->
          store_get s' (keyv (TapeOf n)) = Some (VTape l0)
      | _, _ => True
      end
  | _, _ => True
  end.

(* Whether a body ends with `let x = fold in ret x`, a varied fold whose
   innermost fold is live. *)
Fixpoint tail_fold_back (k : nat) (b : anf avar bare) : bool :=
  match b with
  | ALet _ e b' =>
      match e, b' (let_binder k e) with
      | AFold _ _ _ initA bA, ARet (AVar y) =>
          (aid y =? k)%nat && varied_value k e && fold_live cv k initA bA
      | _, _ => tail_fold_back (S k) (b' (let_binder k e))
      end
  | ARet _ => false
  end.

(* The reverse sweep of a body computing an array in place inside a loop,
   when it ends with such a fold: it leaves the owner as it was before the
   body. *)
Definition tail_back (k : nat) (bA : anf avar bare)
  (bD : anf (val (dual R)) bare) (wP : option (atom pv)) (pp : pplace)
  (ty : ty) (s s' : store R) : Prop :=
  ~ not_in_loop pp -> is_array ty -> tail_fold_back k bA = true ->
  forall o, owner wP pp = Some o ->
  store_get s' (keyv (stored o)) = Some (primal (pd o)) /\
  forall l0,
  store_get s (keyv (TapeOf (stored o))) =
    Some (VTape (rev (body_pushes bD (pd o)) ++ l0)) ->
  store_get s' (keyv (TapeOf (stored o))) = Some (VTape l0).

Lemma tail_fold_back_ret k a eA cA :
  cA (let_binder k eA) = ARet (AVar (let_binder k eA)) ->
  tail_fold_back k (ALet a eA cA) = true ->
  varied_value k eA = true /\
  match eA with
  | AFold _ _ _ initA bA => fold_live cv k initA bA = true
  | _ => False
  end.
Proof.
move=> E; rewrite /= E.
case: eA E => //= ? ? ? initA bA E.
by rewrite E Nat.eqb_refl /= => /andb_true_iff.
Qed.

Lemma tail_fold_back_let k a eA cA :
  tail_fold_back k (ALet a eA cA) = true ->
  tail_fold_back (S k) (cA (let_binder k eA)) = true \/
  exists y, cA (let_binder k eA) = ARet (AVar y) /\ aid y = k.
Proof.
rewrite /=.
case: eA => [? ? | ? ? ? | ? ? | ? ? ? | ? ? ? | ? ? ? | ? ? ? ? ?] /=;
  try by move=> H; left.
case E: (cA _) => [? ? ? | [y | |]] /=; try by move=> H; left.
move=> /andb_true_iff [/andb_true_iff [/Nat.eqb_eq Ey _] _].
by right; exists y.
Qed.

(* The pushes of a step ending with a fold are those of the fold. *)
Lemma fold_pushes_fix (b : val (dual R) -> val (dual R) -> anf (val (dual R)) bare) :
  forall tr z,
  (fix go (z : Z) (tr : list (val (dual R))) : list R :=
     match tr with
     | [] => []
     | s :: tr' => (body_pushes (b (VInt z) s) s ++ go (z + 1)%Z tr')%list
     end) z tr = fold_pushes b z tr.
Proof. by elim=> [| st tr IH] z //=; rewrite IH. Qed.

(* A tail fold whose reverse sweep restores its storage restores the owner
   and pops the pushes of the step. *)
Lemma fold_back_tail L k (eP : value pv bare) eA eD aD cD ve s s' n o :
  value_eq (gA L) eP eA -> value_eq (gD L) eP eD ->
  aeval_value (duals reals) eD = Some ve -> cD ve = ARet (AVar ve) ->
  match eA with
  | AFold _ _ _ initA bA => fold_live cv k initA bA = true
  | _ => False
  end ->
  fold_back k eA eD s s' n o ->
  store_get s' (keyv n) = Some (primal (pd o)) /\
  forall l0,
  store_get s (keyv (TapeOf n)) =
    Some (VTape (rev (body_pushes (ALet aD eD cD) (pd o)) ++ l0)) ->
  store_get s' (keyv (TapeOf n)) = Some (VTape l0).
Proof.
case: eA => // ? ? ? initA bA; case: eP => // ? ? ? ? ? HA.
case: eD => // ? lo hi ? b HD Ev Ec Hfl.
move: Ev; rewrite /= /fold_back.
case El: (aeval_atom _ lo) => [[| l | | |] |] //.
case Eh: (aeval_atom _ hi) => [[| h | | |] |] // Ev /(_ Hfl) [tr [Htr [Hn Ht]]].
split=> // l0; rewrite Ev Ec Htr fold_pushes_fix.
exact: Ht.
Qed.

(* A step whose let does not end it pushes what its continuation pushes. *)
Lemma body_pushes_let aD eD cD ve st :
  aeval_value (duals reals) eD = Some ve -> (forall r, cD ve <> ARet r) ->
  body_pushes (ALet aD eD cD) st = body_pushes (cD ve) st.
Proof.
move=> Ev Hc; rewrite /= Ev.
case Ec: (cD ve) Hc => [? ? ? | r] Hc; last by case: (Hc r).
by case: eD Ev.
Qed.

(* The continuations of a let return together. *)
Lemma cont_ret_DA L x (cP : pv -> anf pv bare) cA cD :
  anf_eq ((x, pa x) :: gA L) (cP x) (cA (pa x)) ->
  anf_eq ((x, pd x) :: gD L) (cP x) (cD (pd x)) ->
  (exists r, cD (pd x) = ARet r) -> exists r, cA (pa x) = ARet r.
Proof.
case: (cP x) => [? ? ? | aP] HA HD [r Er]; first by rewrite Er in HD.
by case: (cA (pa x)) HA => // r' _; exists r'.
Qed.

(* A continuation that returns its argument: the let it continues is the
   tail of the body. *)
Definition ptail (cP : pv -> anf pv bare) : Prop := forall x, cP x = ARet (AVar x).

(* tail-tape K L B S N: when the tail of the body B is a fold, its tape in S
   (storage N) is the one of fold-tape. A body inside an in-place loop gets it
   from the enclosing loop: it is the inner in-place fold its step ends
   with. *)
Fixpoint tail_tape (k : nat) (L : list pv) (b : anf pv bare) (s : store R) (n : dvar W) : Prop :=
  match b with
  | ALet _ eP cP =>
      (ptail cP -> forall eA eW eD, value_eq (gA L) eP eA -> value_eq (gW L) eP eW ->
         value_eq (gD L) eP eD -> fold_tape k eA eW eD s n) /\
      (forall x, tail_tape (S k) (x :: L) (cP x) s n)
  | ARet _ => True
  end.

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
  (m = Replay -> pp <> PTop) ->
  (m = Forward -> cv = true -> forall o, owner wP pp = Some o -> avaried (pa o) = false) ->
  let '((fw, rv), c') :=
    open_pairs (adj W (option_map (amap pt) wP) vo m (rebuild _ bT (annotate_body_t cv m k bA)) se) c in
  (c <= c')%nat /\ has_type ty v /\
  exists s1, run fw s = Some s1 /\
    fwd_frame c (inplace wP pp) (if sweep_eqb m Forward then vo else None) s s1 /\ tkeep c (inplace wP pp) s s1 /\
    (m = Forward -> vo_result vo v s1) /\
    forall s2 O, agree_prim c' (inplace wP pp) s1 s2 -> rctx L c wP pp O (useful cv m k bA) s2 ->
      seed_ok c ty se s2 -> tapes_ok L s2 ->
      (forall ix sx n0, pp = PArray ix sx -> inplace wP pp = Some n0 -> tail_tape k L bP s2 n0) ->
      exists s3, run rv s2 = Some s3 /\ (m = Forward -> vo_kept vo s2 s3) /\
        same_ex pp wP s s3 /\ tkeep c (inplace wP pp) s2 s3 /\
        rev_frame c (inplace wP pp) O s2 s3 /\
        (forall t n, In (t, n) O -> shaped t (barv s3 n)) /\
        pairing O s3 = result_pairing O ty (inplace wP pp) v se s2 /\
        tail_back k bA bD wP pp ty s2 s3.

Lemma rctx_owners_ok L c wP pp O use s : rctx L c wP pp O use s -> owners_ok O.
Proof. by move=> Hr t n /(r_below _ _ _ _ _ _ _ Hr) [j [-> _]]. Qed.

(* Writing the adjoint of an owner with a value of its shape keeps the shapes. *)
Lemma shaped_set O s t n w :
  owners_ok O -> (forall t' n', In (t', n') O -> shaped t' (barv s n')) -> In (t, n) O ->
  (forall t', In (t', n) O -> shaped t' (Some w)) ->
  forall t' n', In (t', n') O -> shaped t' (barv (store_set s (keyv (BarOf n)) w) n').
Proof.
move=> Ho Hs Hi Hw t' n' Hi'.
case: (dvar_eq_dec_c n n') => [E | E].
  by subst n'; rewrite barv_set_same; apply: Hw.
by rewrite barv_set_other //; [apply: (Ho t) | apply: (Ho t') | apply: Hs].
Qed.

(* The reverse sweep writes only the adjoint of an owner. *)
Lemma rev_frame_set c ex O s n w :
  In n (map snd O) -> consistent n -> rev_frame c ex O s (store_set s (keyv (BarOf n)) w).
Proof.
move=> Hn Hcn v _ Hcv _ _ Hb; apply: store_get_set_other => K.
have E := keyv_inj (BarOf n) v Hcn Hcv K; subst v.
exact: Hb n erefl Hn.
Qed.

(* The type of a body that returns a variable. *)
Lemma ret_type L k c wP pp live ty p :
  sctx L k c wP pp live ty -> In p L ->
  typecheck (option_map (amap pw) wP) (wplace pp) k (ARet (AVar (pw p))) = (ty, Ok) ->
  ty = vty (pw p) /\ (varg (pw p) = None \/ wP = Some (AVar p) \/ ~ is_array (vty (pw p))).
Proof.
move=> Hs Hp /=.
case Eg: (varg (pw p)) => [[nx r] |]; last by case=> <-; split; [|left].
case Ea: (ty_is_array (vty (pw p))) => /=; last first.
  case=> <-; split=> //; right; right.
  by case: (vty (pw p)) Ea => //= *; case.
case Ew: (option_map (amap pw) wP) => [y |] //=.
case: wP Hs Ew => [y' |] // Hs [Ey]; subst y.
case: ifP => // /negbFE Hid [<-]; split=> //.
by right; left; apply: unique_written_s; eauto.
Qed.

Ltac none_case := eexists; split; [reflexivity | split; [intros ? ? ? ? ? ?; reflexivity |
                     split; [intros _ ? Et'; discriminate | split; [apply tkeep_refl | intros _ ? _; reflexivity]]]].

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
    (m = Forward -> vo_result vo v s1) /\ tkeep c (inplace wP pp) s s1 /\ same_ex pp wP s s1.
Proof.
move=> Hc HaL Htc Hty Hev Hvo.
case: m Hc Hvo => Hc Hvo /=; last first.
  exists s; split=> //; split=> //; split=> //; split=> //.
  exact: tkeep_refl.
have [Epp [Hcv [Hy _]]] := Hvo erefl; subst pp.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have Hx : vo <> None -> xev s (spell (amap pt aP)) = Some (primal v).
  move=> Hn; have Ecv : cv = true.
    by case: (cv) Hcv => // - [_ H]; case: Hn; apply: H.
  destruct aP as [p | str | z]; rewrite /= in Hev *.
  - case: Hev => <-.
    have [_ [_ [Hst _]]] :=
      static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (HaL p erefl).
    rewrite /xev /= Hst.
    apply: (a_store _ _ _ _ _ _ _ _ _ Hc _ (HaL p erefl)).
    by rewrite /tbr Ecv /= Nat.eqb_refl.
  - by have [x [Hx ->]] := aeval_literal _ _ Hev; rewrite xev_DReal Hx.
  by case: Hev => <-.
case: vo Hcv Hy Hx {Hvo} => [r |] Hcv Hy Hx; last first.
  exists s; split=> //; split=> //; split=> //; split=> //.
  exact: tkeep_refl.
have {}Hx : xev s (spell (amap pt aP)) = Some (primal v) by apply: Hx.
case: r Hcv Hy => [t | y] Hcv Hy.
  exists (store_set s (keyv ResultVar) (primal v)).
  split; first by rewrite /run /=; rewrite /xev in Hx; rewrite Hx.
  split.
    move=> v' _ Hcv' _ _ Hne; apply: store_get_set_other => K.
    by have E := keyv_inj ResultVar v' I Hcv' K; subst v'; apply: Hne.
  split; first by move=> _ t' [<-]; apply: store_get_set_same.
  split; first by apply: tkeep_set.
  by move=> _ o _ _; apply: store_get_set_other; rewrite /keyv /stored.
have {}Hy := Hy y erefl.
destruct wP as [yP |]; rewrite /= in Hy; last by [].
case: Hy => Ey; subst y.
have [q [Eyq [Hq _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl; subst yP.
have [_ [_ [Hsq [Htq _]]]] :=
  static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq.
rewrite /vo_result /vo_target /role_of /stored_of /= Hsq Htq.
case Eg: (targ (pt q)) => [[nm r] |] /=;
  last by case: (vty (pw q)); none_case.
case: r Eg => Eg /=; try by case: (vty (pw q)); none_case.
case Evq: (vty (pw q)) => [| | | aty]; try by none_case.
  exists (store_set s (keyv (stored q)) (primal v)).
  split; first by rewrite /run /=; rewrite /xev in Hx; rewrite Hx.
  split.
    move=> v' _ Hcv' _ _ Hne; apply: store_get_set_other => K.
    have E := keyv_inj (stored q) v' erefl Hcv' K; subst v'; apply: Hne.
    by rewrite /vo_target /role_of /stored_of /= Eg Hsq Htq Evq.
  split; first by move=> _ t' [<-]; apply: store_get_set_same.
  split; first by apply: tkeep_set.
  by move=> _ o /= Ho _; rewrite Evq in Ho.
(* an array, updated in place: the result is in the written argument *)
exists s; split=> //; split=> //.
split; last by split; [apply: tkeep_refl | move=> _ o _ _].
move=> _ t' [<-].
have Har : is_array (vty (pw q)) by rewrite Evq.
have [Ety _] := s_top _ _ _ _ _ _ _ Hs q erefl erefl Har.
rewrite Evq in Ety; subst ty.
destruct aP as [p | str | z]; rewrite /= in Htc; try discriminate.
have [Ep Hcase] := ret_type _ _ _ _ _ _ _ _ Hs (HaL p erefl) Htc.
have Hl : live_anf k (ARet (amap pw (AVar p))) p.
  by rewrite /live_anf /= Nat.eqb_refl.
have Hpq : pn p = pn q.
  apply: (s_arrays _ _ _ _ _ _ _ Hs p q (HaL p erefl) Hl).
  - by rewrite -Ep.
  - case: Hcase => [H1 | [H1 | H1]]; [by left | by right |].
    by exfalso; apply: H1; rewrite -Ep.
  by rewrite /= Evq.
have [_ [_ [Hsp _]]] :=
  static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (HaL p erefl).
by rewrite /xev /= Hsp /stored in Hx; rewrite /stored -Hpq.
Qed.

Lemma asim_ret (aP : atom pv) : asim_body (ARet aP).
Proof.
move=> L k c s wP pp m bA bW bT bD ty v se vo HA HW HT HD Hc Hty Htc Hev Hvo
  _ _ _ _.
destruct bA as [| aA], bW as [| aW], bT as [| aT], bD as [| aD];
  rewrite /= in HA HW HT HD; try contradiction.
graph HA; graph HW; graph HT; graph HD.
cbn [annotate_body_t rebuild adj open_pairs].
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have Hhty : has_type ty v.
  destruct aP as [p | str | z]; rewrite /= in Htc Hev.
  - case: Hev => <-.
    have [-> _] := ret_type _ _ _ _ _ _ _ _ Hs (H p erefl) Htc.
    have [_ [_ [_ [_ [_ [_ [_ [_ [Hht _]]]]]]]]] :=
      static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) (H p erefl).
    exact: Hht.
  - by have [x' [_ ->]] := aeval_literal _ _ Hev; case: Htc => <-.
  by case: Htc Hty => <-.
split=> //; split=> //.
have [s1 [Hrun1 [Hfr1 [Hvr1 [Htk Hsx]]]]] :=
  ret_forward L k c s wP pp m aP ty v vo Hc H Htc Hty Hev Hvo.
exists s1; do 4!(split=> //).
move=> s2 O Hag Hr Hseed _ _.
have Htb : forall a0 d0 s3, tail_back k (ARet a0) d0 wP pp ty s2 s3.
  by move=> a0 d0 s3 _ _.
apply: (keep_add2 _ L k c c wP pp _ ty vo _ s s1 s2 _ Hs (le_n c) Hag Hsx).
  case: (tof (amap pt aP)); try by constructor.
  case Eb: (@bar W (amap pt aP)) => [bx |]; last by constructor.
  by have [y [-> Hy]] := bar_some _ _ Eb; repeat constructor.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
destruct aP as [p | str | z]; rewrite /= in Htc Hev *; last 2 first.
- have [x [Hx Ev]] := aeval_literal _ _ Hev; subst v; case: Htc => Ety.
  subst ty; exists s2; split=> //; split=> //.
  split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
  by split; [rewrite /result_pairing /=; ring | exact: Htb].
- by case: Htc Hty => <-.
case: Hev => Ev; subst v.
have Hp : In p L by apply: H.
have [Ety Hcase] := ret_type _ _ _ _ _ _ _ _ Hs Hp Htc; subst ty.
have Hl : live_anf k (ARet (amap pw (AVar p))) p.
  by rewrite /live_anf /= Nat.eqb_refl.
have [_ [_ [Hstore [Hsty [_ [_ [_ [_ [Hht Hz]]]]]]]]] :=
  static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hp.
rewrite Hstore Hsty (a_bar _ _ _ _ _ _ _ _ _ Hc _ Hp).
have Hu : useful cv m k (ARet (AVar (pa p))) p.
  by rewrite /useful /=; case: (sweep_eqb m Forward && cv);
    rewrite /= Nat.eqb_refl.
destruct (vty (pw p)) eqn:Ety; try by case: Hty.
  destruct (pd p) as [d | | | |] eqn:Ed; try by [].
  destruct (avaried (pa p)) eqn:Ev; last first.
    exists s2; split=> //; split=> //.
    split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
    split; last exact: Htb.
    by have /= Hz0 := Hz erefl; rewrite /result_pairing Hz0; ring.
  have Hin := r_useful _ _ _ _ _ _ _ Hr p Hp Hu Ev; rewrite Ed /= in Hin.
  have /= Hsh := r_shape _ _ _ _ _ _ _ Hr _ _ Hin.
  case Eb: (barv s2 (stored p)) Hsh => [[b0 | | | |] |] // _.
  have [sg Hsg] := proj2 Hseed erefl.
  exists (store_set s2 (keyv (BarOf (stored p))) (VReal (b0 + sg))).
  split.
    by rewrite /run /=; rewrite /barv /keyv /= in Eb; rewrite Eb;
      rewrite /xev in Hsg; rewrite Hsg.
  split.
    apply: rev_frame_set => //.
    by apply/(in_map_iff _ _ _); exists (VReal (dsnd d), stored p).
  split.
    apply: (shaped_set O s2 (VReal (dsnd d))) => //.
      exact: (r_shape _ _ _ _ _ _ _ Hr).
    by move=> t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr p t' Hp Hu Ht') Ed.
  split; last exact: Htb.
  rewrite (pairing_set_in O s2 (VReal (dsnd d)) (stored p)) //.
    exact: (r_nodup _ _ _ _ _ _ _ Hr).
  by rewrite /result_pairing /seed_value Hsg Eb /=; ring.
exists s2; split=> //; split=> //.
split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
split; last exact: Htb.
case Eo: (owner wP pp) => [o |];
  last by case: (s_ty _ _ _ _ _ _ _ Hs I Eo).
have Hpo : pn p = pn o.
  apply: (s_arrays _ _ _ _ _ _ _ Hs p o Hp Hl) => //; first by rewrite Ety.
  case: Hcase => [Hc1 | [Hc1 | Hc1]]; [by left | by right |].
  by exfalso; apply: Hc1.
have Ht := r_owner _ _ _ _ _ _ _ Hr o Eo.
have Esp : stored p = stored o by rewrite /stored Hpo.
rewrite -Esp in Ht.
have Ev := r_value _ _ _ _ _ _ _ Hr p _ Hp Hu Ht.
rewrite /result_pairing /inplace Eo /= -Esp -Ev.
rewrite oset_same //.
exact: (r_nodup _ _ _ _ _ _ _ Hr).
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

Lemma fold_tape_same k eA eW eD s s' n :
  store_get s' (keyv (TapeOf n)) = store_get s (keyv (TapeOf n)) -> store_get s' (keyv n) = store_get s (keyv n) ->
  fold_tape k eA eW eD s n -> fold_tape k eA eW eD s' n.
Proof. by move=> E E' H; rewrite /fold_tape in H *; rewrite E E'. Qed.

(* The tail tape only reads the tape of the storage and the storage. *)
Lemma tail_tape_same k L b s s' n :
  store_get s' (keyv (TapeOf n)) = store_get s (keyv (TapeOf n)) ->
  store_get s' (keyv n) = store_get s (keyv n) ->
  tail_tape k L b s n -> tail_tape k L b s' n.
Proof.
move=> Et En; elim: b k L => [a e c IH | x] k L //= [Htl Hnext].
split=> [Hpt eA eW eD HA HW HD | y]; last exact: IH.
exact: (fold_tape_same _ _ _ _ s _ _ Et En (Htl Hpt eA eW eD HA HW HD)).
Qed.

(* A fold that is not updated in place carries a real: its tape is the one of
   a scalar fold. *)
Lemma fold_tape_scalar L k wP tail (eP : value pv bare) eA eW eD s s' n :
  value_eq (gW L) eP eW -> storage wP tail eP = None ->
  store_get s' (keyv (TapeOf n)) = store_get s (keyv (TapeOf n)) ->
  fold_tape k eA eW eD s n -> fold_tape k eA eW eD s' n.
Proof.
move=> HW Hst E.
case: eA => // fa loA hiA initA bA.
case: eW HW => // fw loW hiW initW bW HW.
case: eD => // ? ? ? ? ?.
case: eP HW Hst => // fp loP hiP initP bP /= [_ [_ [Hi _]]] Hst.
move/atom_graph: Hi => [Ei _]; subst initW.
have Hna : ~ is_array (of_atom (amap pw initP)).
  case: initP Hst => [i0 | ? | ?] /= Hst; try by move=> [].
  by case: (vty (pw i0)) Hst => //= *; case.
rewrite E.
case: (aeval_atom _ _) => [[| ? | | |] |] //.
case: (aeval_atom _ _) => [[| ? | | |] |] //.
case: (aeval_atom _ _) => // ? H tr Htr.
by split; [exact: (proj1 (H tr Htr)) | move=> Ha; case: (Hna Ha)].
Qed.

(* Inside the body of an in-place loop, a value not stored in place is no
   fold: a scalar recurrence is not typed there. *)
Lemma fold_tape_in_loop L k wP tail ix sx (eP : value pv bare) eA eW eD te s n :
  value_eq (gW L) eP eW -> storage wP tail eP = None ->
  typecheck_value (option_map (amap pw) wP) (wplace (PArray ix sx)) tail k eW = (te, Ok) ->
  fold_tape k eA eW eD s n.
Proof.
move=> HW Hst Htc.
case: eA => // fa loA hiA initA bA.
case: eW HW Htc => // fw loW hiW initW bW HW Htc.
case: eD => // ? ? ? ? ?.
case: eP HW Hst => // fp loP hiP initP bP /= [_ [_ [Hi _]]] Hst.
move/atom_graph: Hi => [Ei _]; subst initW.
have Hnr : ty_eqb (of_atom (amap pw initP)) Real = false.
  case Er: (ty_eqb _ Real) => //; move: Htc => /=; rewrite Er.
  by case: (_ && _).
have Hna : ~ is_array (of_atom (amap pw initP)).
  move: Hst {Htc Hnr}; case: initP => [i0 | ? | ?] /= Hst; try by move=> [].
  by case: (vty (pw i0)) Hst => //= *; case.
case: (aeval_atom _ _) => [[| ? | | |] |] //.
case: (aeval_atom _ _) => [[| ? | | |] |] //.
case: (aeval_atom _ _) => // ? tr _.
by split; [rewrite Hnr | move=> Ha; case: (Hna Ha)].
Qed.

(* A fold whose forward sweep records nothing has no tape to give. *)
Lemma fold_tape_records k eA eW eD s n : records cv k eA = false -> fold_tape k eA eW eD s n.
Proof.
case: eA => // fa loA hiA initA bA.
case: eW => // ? ? ? ? ?; case: eD => // ? ? ? ? ? Hrec.
have Hlive := fold_live_records cv k fa loA hiA initA bA Hrec.
move: Hrec; rewrite /fold_tape /state_live /= => /orb_false_iff [Hr _].
case: (aeval_atom _ _) => [[| ? | | |] |] //.
case: (aeval_atom _ _) => [[| ? | | |] |] //.
case: (aeval_atom _ _) => // ? tr _.
split=> _; last by rewrite Hlive.
by rewrite /state_live /fold_binders /= => E; congruence.
Qed.


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
  (rec = true \/ (m = Forward /\ records cv k eA = true /\ storage wP tail eP <> None /\ ~ not_in_loop pp) ->
     exists l, store_get s (keyv (TapeOf n)) = Some (VTape l)) ->
  aeval_value (duals reals) eD = Some ve ->
  let '(se, c') :=
    open_pairs (fwd_value W (option_map (amap pt) wP) m (rebuild_value _ eT (annotate_value_t cv k eA)) te n rec) c in
  (c <= c')%nat /\
  exists s1, run se s = Some s1 /\ fwd_frame c (Some n) None s s1 /\ tkeep c (Some n) s s1 /\
             store_get s1 (keyv n) = Some (primal ve) /\ (m = Forward /\ not_in_loop pp -> fold_tape k eA eW eD s1 n) /\
             (m = Forward -> ~ not_in_loop pp -> storage wP tail eP <> None ->
              (forall o, owner wP pp = Some o -> tid (pt o) = None) ->
              fold_grow k eA eD s s1 n).

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
    tapes_ok L s2 -> (pp = PTop \/ (exists ix sx, pp = PArray ix sx) -> fold_tape k eA eW eD s2 n) ->
    (not_in_loop pp -> storage wP tail eP <> None -> forall o, owner wP pp = Some o -> avaried (pa o) = true ->
       records cv k eA = false -> store_get s2 (keyv n) = Some (primal (pd o))) ->
    exists s3, run re s2 = Some s3 /\
      (forall v, below c v -> consistent v -> is_primal v -> v <> n -> store_get s3 (keyv v) = store_get s2 (keyv v)) /\
      (not_in_loop pp -> storage wP tail eP <> None -> forall o, owner wP pp = Some o -> avaried (pa o) = false ->
         store_get s3 (keyv n) = store_get s2 (keyv n)) /\
      (not_in_loop pp -> storage wP tail eP <> None -> forall o, owner wP pp = Some o -> avaried (pa o) = true ->
         store_get s3 (keyv n) = Some (primal (pd o))) /\
      tkeep c (Some n) s2 s3 /\
      rev_frame_x c (inplace wP pp) n (oput O n (tangent ve)) s2 s3 /\
      (forall t m, In (t, m) O -> shaped t (barv s3 m)) /\
      pairing O s3 = pairing (oput O n (tangent ve)) s2 /\
      (~ not_in_loop pp -> storage wP tail eP <> None ->
       forall o, owner wP pp = Some o -> fold_back k eA eD s2 s3 n o).

(* A value updated in place outside the body of an in-place loop (a map)
   writes an argument that is not inout, and does not read it. *)
Definition inplace_only (eP : value pv bare) : Prop :=
  forall L k wP pp tail eA eW te, value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> Forall (static_ok k) L ->
  ids_unique L ->
  typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
  storage wP tail eP <> None -> not_in_loop pp ->
  (forall p ny r, In p L -> varg (pw p) = Some (ny, r) -> avaried (pa p) = varied_role r) ->
  (forall y, wP = Some (AVar y) -> exists ny r, varg (pw y) = Some (ny, r) /\ written_role r = true) ->
  forall o, owner wP pp = Some o -> In o L ->
    ~ vreads k eA o /\ (avaried (pa o) = true -> varied_value k eA = true) /\
    (~ live_value k eW o -> avaried (pa o) = false).

Lemma fwd_frame_set c n vo s w :
  consistent n -> fwd_frame c (Some n) vo s (store_set s (keyv n) w).
Proof.
move=> Hn v _ Hcv _ Hex _; apply: store_get_set_other => K.
by have E := keyv_inj n v Hn Hcv K; subst v; apply: Hex.
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
move=> Hc Ha p /Ha [Hp Hv]; split.
  have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
  exact: (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hp).
exact: (a_store _ _ _ _ _ _ _ _ _ Hc _ Hp Hv).
Qed.

Lemma afwd_op1 f (aP : atom pv) : asim_fwd (AOp1 f aP).
Proof.
fwd_intro.
rewrite /= in Htc Hev Hst *; rename f3 into f.
split; first by lia.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
have Va : forall p, aP = AVar p ->
    In p L /\ vatoms k (AOp1 f (amap pa aP)) p.
  by move=> p E; split; [auto | subst; rewrite /vatoms /= Nat.eqb_refl].
have Hs :=
  aspell_ok k s aP va (operand_store _ _ _ _ _ _ _ _ _ aP Hc Va) Ha.
exists (store_set s (keyv (DBound (j, j))) (primal ve)).
split.
  apply: run_define; rewrite xev_DOp1 Hs; exact: primal_eval_op1 Hev.
split; first exact: fwd_frame_set.
by split; [apply: tkeep_set | split=> //; apply: store_get_set_same].
Qed.

Lemma afwd_op2 f (aP bP : atom pv) : asim_fwd (AOp2 f aP bP).
Proof.
fwd_intro.
rewrite /= in Htc Hev Hst *; rename f3 into f.
split; first by lia.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
case Hb: (aeval_atom (duals reals) (amap pd bP)) Hev => [vb |] // Hev.
have Va : forall p, aP = AVar p ->
    In p L /\ vatoms k (AOp2 f (amap pa aP) (amap pa bP)) p.
  move=> p E; split; first by auto.
  by subst; apply: (atom_member_atoms (pa p) (AVar (pa p))) => /=; auto.
have Vb : forall p, bP = AVar p ->
    In p L /\ vatoms k (AOp2 f (amap pa aP) (amap pa bP)) p.
  move=> p E; split; first by auto.
  by subst; apply: (atom_member_atoms (pa p) (AVar (pa p))) => /=; auto.
have Hsa :=
  aspell_ok k s aP va (operand_store _ _ _ _ _ _ _ _ _ aP Hc Va) Ha.
have Hsb :=
  aspell_ok k s bP vb (operand_store _ _ _ _ _ _ _ _ _ bP Hc Vb) Hb.
exists (store_set s (keyv (DBound (j, j))) (primal ve)).
split.
  apply: run_define; rewrite xev_DOp2 Hsa Hsb.
  exact: primal_eval_op2 Hev.
split; first exact: fwd_frame_set.
by split; [apply: tkeep_set | split=> //; apply: store_get_set_same].
Qed.

Lemma afwd_get (aP iP : atom pv) : asim_fwd (AGet aP iP).
Proof.
fwd_intro.
rewrite /= in Htc Hev Hst *.
split; first by lia.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev
  => [[| | | l |] |] // Hev;
  case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev.
case Ez: (nth_z z l) Hev => [d |] // [Eve]; subst ve.
have Va : forall p, aP = AVar p ->
    In p L /\ vatoms k (AGet (amap pa aP) (amap pa iP)) p.
  move=> p E; split; first by auto.
  by subst; apply: (atom_member_atoms (pa p) (AVar (pa p))) => /=; auto.
have Vi : forall p, iP = AVar p ->
    In p L /\ vatoms k (AGet (amap pa aP) (amap pa iP)) p.
  move=> p E; split; first by auto.
  by subst; apply: (atom_member_atoms (pa p) (AVar (pa p))) => /=; auto.
have Hsa :=
  aspell_ok k s aP _ (operand_store _ _ _ _ _ _ _ _ _ aP Hc Va) Ha.
have Hsi :=
  aspell_ok k s iP _ (operand_store _ _ _ _ _ _ _ _ _ iP Hc Vi) Hi.
exists (store_set s (keyv (DBound (j, j))) (VReal (dfst d))).
split.
  apply: run_define; rewrite /xev /= in Hsa Hsi *.
  by rewrite Hsa Hsi /= nth_z_map Ez.
split; first exact: fwd_frame_set.
by split; [apply: tkeep_set | split=> //; apply: store_get_set_same].
Qed.

Lemma replace_nth_z_nth {A : Type} k (x : A) l l1 :
  replace_nth_z k x l = Some l1 -> exists y, nth_z k l = Some y.
Proof.
rewrite /replace_nth_z /nth_z; case: (k <? 0)%Z => //.
elim: (Z.to_nat k) l l1 => [| n IH] [| y l] l1 //=; first by exists y.
by case E: (replace_nth n x l) => [l2 |] // _; apply: IH E.
Qed.

(* An atom reads primal keys only. *)
Lemma avoid_tape_spell k (aP : atom pv) t :
  (forall p, aP = AVar p -> static_ok k p) -> avoid (keyv (TapeOf t)) (spell (amap pt aP)).
Proof.
move=> H x; case: aP H => [p | |] //= H [Ex | []]; subst x.
have [_ [_ [Hs _]]] := H p erefl; rewrite Hs.
by rewrite /keyv /stored.
Qed.

Lemma afwd_set (aP iP vP : atom pv) : asim_fwd (ASet aP iP vP).
Proof.
fwd_intro.
rewrite /= in Htc Hev *.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev
  => [[| | | l |] |] // Hev;
  case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev;
  case Hv: (aeval_atom (duals reals) (amap pd vP)) Hev
  => [[[y dy] | | | |] |] // Hev.
case Er: (replace_nth_z z (Dual y dy) l) Hev => [l1 |] // [Eve]; subst ve.
destruct aP as [q | str | zq]; last 2 first.
- by have [? [_ E]] := aeval_literal _ _ Ha.
- by [].
case: Ha => Eq; rewrite /= in Hst.
have Va : forall p, AVar q = AVar p ->
    In p L /\ vatoms k (ASet (AVar (pa q)) (amap pa iP) (amap pa vP)) p.
  move=> p [<-]; split; first by auto.
  by apply: (atom_member_atoms (pa q) (AVar (pa q))) => /=; auto.
have Vi : forall p, iP = AVar p ->
    In p L /\ vatoms k (ASet (AVar (pa q)) (amap pa iP) (amap pa vP)) p.
  move=> p E; split; first by auto.
  by subst; apply: (atom_member_atoms (pa p) (AVar (pa p))) => /=; auto.
have Vv : forall p, vP = AVar p ->
    In p L /\ vatoms k (ASet (AVar (pa q)) (amap pa iP) (amap pa vP)) p.
  move=> p E; split; first by auto.
  by subst; apply: (atom_member_atoms (pa p) (AVar (pa p))) => /=; auto.
have [Hsq Hq] := operand_store _ _ _ _ _ _ _ _ _ _ Hc Va q erefl.
rewrite Eq in Hq.
have Hsi :=
  aspell_ok k s iP _ (operand_store _ _ _ _ _ _ _ _ _ iP Hc Vi) Hi.
have Hsv :=
  aspell_ok k s vP _ (operand_store _ _ _ _ _ _ _ _ _ vP Hc Vv) Hv.
have Hsti : forall p, iP = AVar p -> static_ok k p.
  by move=> p E; case: (operand_store _ _ _ _ _ _ _ _ _ iP Hc Vi p E).
have Hstv : forall p, vP = AVar p -> static_ok k p.
  by move=> p E; case: (operand_store _ _ _ _ _ _ _ _ _ vP Hc Vv p E).
rewrite -Hst in Hq.
have /= Hm := replace_nth_z_map dfst z (Dual y dy) l.
rewrite Er /= in Hm.
set s1 := fun s0 =>
  store_set s0 (keyv (DBound (j, j))) (VArray (map dfst l1)).
have Hassign : forall s0,
    store_get s0 (keyv (DBound (j, j))) = Some (VArray (map dfst l)) ->
    xev s0 (spell (amap pt iP)) = Some (VInt z) ->
    xev s0 (spell (amap pt vP)) = Some (VReal y) ->
    run [DAssign (DAt (DVar (DBound (j, j))) (spell (amap pt iP)))
           (spell (amap pt vP))] s0 = Some (s1 s0).
  move=> s0 G1 G2 G3; rewrite /run /xev /keyv /= in G1 G2 G3 *.
  by rewrite G3 /= G1 G2 /= Hm.
have Hframe :
    forall s0, fwd_frame c (Some (DBound (j, j))) None s0 (s1 s0).
  by move=> s0; apply: fwd_frame_set.
case Erec: (sweep_eqb m Forward && rec) => /=; split; try lia; last first.
  exists (s1 s); split; first exact: Hassign.
  split; first exact: Hframe.
  by split; [apply: tkeep_set | split=> //; apply: store_get_set_same].
(* the element overwritten is recorded first *)
move/andb_true_iff: Erec => [_ Erec]; have [lt Hlt] := Hrec (or_introl Erec).
have [old Hold] := replace_nth_z_nth _ _ _ _ Er.
set s0 :=
  store_set s (keyv (TapeOf (DBound (j, j)))) (VTape (dfst old :: lt)).
have Hn0 : store_get s0 (keyv (DBound (j, j))) = Some (VArray (map dfst l)).
  by rewrite /s0 store_get_set_other.
exists (s1 s0); split.
  have Happ : forall a b : dstmt W, [a; b] = ([a] ++ [b])%list by [].
  rewrite Happ run_app (_ : run [_] s = Some s0).
    rewrite /run /xev /keyv /= in Hq Hsi *.
    by rewrite Hq Hsi /= nth_z_map Hold /= Hlt.
  apply: Hassign => //.
    by rewrite /s0 xev_set_other //; apply: (avoid_tape_spell k).
  by rewrite /s0 xev_set_other //; apply: (avoid_tape_spell k).
split.
  move=> v Hb Hcv Ht Hex Hvo; rewrite (Hframe s0 v Hb Hcv Ht Hex Hvo).
  rewrite /s0; apply: store_get_set_other => K.
  have E := keyv_inj (TapeOf (DBound (j, j))) v erefl Hcv K; subst v.
  by apply: Ht.
split.
  apply: (tkeep_trans _ _ _ s0); first by apply: tkeep_set_tape; [|right].
  exact: tkeep_set.
by split=> //; rewrite /s1 store_get_set_same.
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
move=> H1 H2; rewrite /run /xev /keyv in H1 H2 *.
by rewrite /= H1 H2.
Qed.

(* What the reverse sweep of a binary operation reads. *)
Lemma reads_op2 f (a b : atom avar) (q : avar) :
  comparison f = false -> (f = Mul \/ f = Divide) ->
  ((varied a = true /\ b = AVar q) \/ (varied b = true /\ a = AVar q)) ->
  atom_member (AVar q) (fst (match partial2 f a b with
                             | Some (pa, pb) => (atom_union (read_by a (Some pa)) (read_by b (Some pb)), atoms_of_atoms [a; b])
                             | None => ([], atoms_of_atoms [a; b]) end)) = true.
Proof.
move=> _ [-> | ->] [[Ha ->] | [Hb ->]];
  rewrite /= atom_member_union /read_by ?Ha ?Hb /=;
  repeat (rewrite ?atom_member_union /=);
  rewrite ?Nat.eqb_refl /= ?orb_true_r //;
  case: (varied a); case: (varied b);
  by rewrite /= ?atom_member_union /= ?Nat.eqb_refl /= ?orb_true_r.
Qed.

Lemma reads_op2_div (a b : atom avar) (q : avar) :
  varied b = true -> b = AVar q ->
  atom_member (AVar q) (fst (match partial2 Divide a b with
                             | Some (pa, pb) => (atom_union (read_by a (Some pa)) (read_by b (Some pb)), atoms_of_atoms [a; b])
                             | None => ([], atoms_of_atoms [a; b]) end)) = true.
Proof.
move=> Hb Eb; subst b; rewrite /= atom_member_union /read_by /=.
rewrite /= in Hb; rewrite Hb; apply/orb_true_iff; right.
rewrite /= !atom_member_union /= Nat.eqb_refl.
by case: (atom_member _ (atoms_of_atom a)); rewrite /= ?Nat.eqb_refl.
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
move=> Hok Hnd Hin Hsub Hsh Huq Hb Hs Eb Ew s'.
rewrite /contribution /= Hb Hs.
split; first exact: run_increment.
split.
  apply: rev_frame_set; last exact: (Hok (VReal t)).
  by apply: Hsub; apply/(in_map_iff _ _ _); exists (VReal t, stored q).
split.
  apply: (shaped_set O s (VReal t)) => // t' Ht'.
  by rewrite (Huq t' Ht').
by rewrite /s' (pairing_set_in O s (VReal t) (stored q)) // Eb /=; ring.
Qed.

Lemma rev_frame_trans c ex O s s1 s2 :
  rev_frame c ex O s s1 -> rev_frame c ex O s1 s2 -> rev_frame c ex O s s2.
Proof.
by move=> F1 F2 v H1 H2 H3 H4 H5; rewrite (F2 v H1 H2 H3 H4 H5); apply: F1.
Qed.

(* An atom reads primal keys only: writing an adjoint keeps its value. *)
Lemma avoid_bar_spell k (aP : atom pv) t :
  (forall p, aP = AVar p -> static_ok k p) -> avoid (keyv (BarOf t)) (spell (amap pt aP)).
Proof.
move=> H x; case: aP H => [p | |] //= H [Ex | []]; subst x.
have [_ [_ [Hs _]]] := H p erefl; rewrite Hs.
by rewrite /keyv /stored.
Qed.

(* An accumulation into an element of an array. *)
Lemma run_increment_at s x ei e bm z bk w bm' :
  store_get s (keyv x) = Some (VArray bm) -> xev s ei = Some (VInt z) -> nth_z z bm = Some bk ->
  xev s e = Some (VReal w) -> replace_nth_z z (bk + w) bm = Some bm' ->
  run [DIncrement (DAt (DVar x) ei) e] s = Some (store_set s (keyv x) (VArray bm')).
Proof.
move=> H1 H2 H3 H4 H5; rewrite /run /xev /keyv in H1 H2 H4 *.
change (map (Simplify.out_dstmt nat) [DIncrement (DAt (DVar x) ei) e])
  with [DIncrement (DAt (DVar (Simplify.out_dvar nat x))
          (Simplify.out_dexpr nat ei)) (Simplify.out_dexpr nat e)].
cbn [exec_stmts exec]; cbn [xeval]; rewrite H1 H2; cbn; rewrite H3; cbn.
by rewrite H4; cbn; rewrite H1 H2 H5.
Qed.

Lemma nth_z_length {A B : Type} z (l : list A) (m : list B) d :
  nth_z z l = Some d -> length l = length m -> exists e, nth_z z m = Some e.
Proof.
rewrite /nth_z; case: (z <? 0)%Z => // H Hl.
case E: (nth_error m (Z.to_nat z)) => [e |]; first by exists e.
move/nth_error_None: E => E.
have : nth_error l (Z.to_nat z) <> None by rewrite H.
by move/nth_error_Some; lia.
Qed.

Lemma replace_exists {A : Type} z (m : list A) e w :
  nth_z z m = Some e -> exists m', replace_nth_z z w m = Some m'.
Proof.
rewrite /nth_z /replace_nth_z; case: (z <? 0)%Z => //.
elim: (Z.to_nat z) m => [| n IH] [| b m] //= H; first by eexists.
by have [m' ->] := IH m H; eexists.
Qed.

(* Replacing the tangent of an owner. *)
Lemma pairing_oset O s t n t' :
  owners_ok O -> NoDup (map snd O) -> In (t, n) O ->
  pairing (oset O n t') s = pairing O s - inner t (barv s n) + inner t' (barv s n).
Proof.
elim: O => [| [t0 n0] O IH] Hok //= /NoDup_cons_iff [Hn Hnd] Hin.
have Hok' : owners_ok O by move=> t1 m I; apply: (Hok t1); right.
have Hcn : consistent n by apply: (Hok t).
have Hcn0 : consistent n0 by apply: (Hok t0); left.
case: Hin => [[Et En] | Hin].
  subst t0 n0; rewrite (proj2 (dvar_eq_consistent n n Hcn Hcn) erefl) /=.
  by rewrite oset_notin //; ring.
case E: (Simplify.dvar_eq nat n n0).
  move/(dvar_eq_consistent _ _ Hcn Hcn0): E => E; subst n0.
  by case: Hn; apply/(in_map_iff _ _ _); exists (t, n).
by rewrite /= IH //; ring.
Qed.

Lemma dotr_zero l m : Forall (fun x => x = 0) m -> dotr l m = 0.
Proof.
move=> H; elim: H l => [| x m' Hx Hm IH] [| a l] //.
by rewrite dotr_cons IH Hx; ring.
Qed.

Lemma oset_snd O n t : map snd (oset O n t) = map snd O.
Proof.
rewrite /oset map_map; apply: map_ext => - [t' n'].
by case: (Simplify.dvar_eq nat n n').
Qed.

Lemma oput_in O n t : In n (map snd (oput O n t)).
Proof.
rewrite /oput; case: (in_dec dvar_eq_dec_c n (map snd O)) => I.
  by rewrite oset_snd.
by left.
Qed.

Lemma oput_sub O n t m : In m (map snd O) -> In m (map snd (oput O n t)).
Proof.
rewrite /oput; case: (in_dec dvar_eq_dec_c n (map snd O)) => I H.
  by rewrite oset_snd.
by right.
Qed.

(* A variable that holds a real or an integer is not an array. *)
Lemma not_array_val k p :
  static_ok k p -> (match pd p with VArray _ => False | _ => True end) -> ~ is_array (vty (pw p)).
Proof.
move=> [_ [_ [_ [_ [_ [_ [_ [_ [Hht _]]]]]]]]] Hv Ha.
by case: (vty (pw p)) Ha Hht => // ? _; case: (pd p) Hv.
Qed.

Lemma oput_notin O n t : ~ In n (map snd O) -> oput O n t = (t, n) :: O.
Proof. by rewrite /oput; case: (in_dec dvar_eq_dec_c n (map snd O)). Qed.

Lemma arev_op1 f (aP : atom pv) : asim_rev0 (AOp1 f aP).
Proof.
rev_intro.
rewrite /= in Htc Hst Hvr *; rename f3 into f.
split; first by lia.
move=> s2 O Hrd Hr Hns.
destruct aP as [q | |]; rewrite /= in Hvr; try discriminate.
have Hq : In q L by auto.
have [_ [_ [Hsq _]]] := static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq.
cbn [amap aeval_atom aeval_value] in Hev.
destruct (pd q) as [[x dx] | | | |] eqn:Eq;
  cbn [eval_op1 dom_op1 duals] in Hev; try discriminate.
case Hd: (dual_op1 R reals f (Dual x dx)) Hev => [[y dy] |] // [Eve].
subst ve.
have [Hn Hsh] := Hns erefl.
rewrite (oput_notin O _ _ Hn); cbn [amap] in *.
rewrite /= in Hsh.
case Ebn: (barv s2 (DBound (j, j))) Hsh => [[be | | | |] |] // _.
have Hfl : vflows k (AOp1 f (AVar (pa q))) q.
  by rewrite /vflows /= Nat.eqb_refl.
have Hin := r_useful _ _ _ _ _ _ _ Hr q Hq Hfl Hvr; rewrite Eq /= in Hin.
have /= Hshq := r_shape _ _ _ _ _ _ _ Hr _ _ Hin.
case Eb: (barv s2 (stored q)) Hshq => [[b0 | | | |] |] // _.
case Hp: (partial1 f (AVar (pt q))) => [p |]; last first.
  case: f Hd Hp {Hrd Hr Hfl Hs Htc} => [| | | | | | z | u] Hd Hp;
    rewrite /= in Hp; try discriminate.
  by case: z Hd Hp => [| z | z] Hd Hp; rewrite /= in Hp; try discriminate;
    unfold_ops Hd.
have He : xev s2 (DVar (BarOf (DBound (j, j)))) = Some (VReal be) by [].
have Hx : pmentions p -> xev s2 (spell (AVar (pt q))) = Some (VReal x).
  move=> Hm.
  have Hrq : store_get s2 (keyv (stored q)) = Some (primal (pd q)).
    apply: (Hrd q Hq).
    - by rewrite /vreads /=; exact: (reads_op1 f (pt q) (pa q) p Hp Hm Hvr).
    - by rewrite /live_value /= Nat.eqb_refl.
    apply: (not_array_val k); last by rewrite Eq.
    exact: (static_in _ _ _ (s_static _ _ _ _ _ _ _ Hs) Hq).
  by rewrite Eq in Hrq; rewrite /xev /= Hsq.
have [A [Edy Hc]] :=
  adjoint_op1_gen s2 f (AVar (pt q)) _ x dx y dy p be Hp He Hd Hx.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
rewrite /contribution /= (Hbar q Hq) Hvr Hsq.
exists (store_set s2 (keyv (BarOf (stored q))) (VReal (b0 + A * be))).
split; first exact: run_increment.
split.
  apply: rev_frame_set => //; right.
  by apply/(in_map_iff _ _ _); exists (VReal dx, stored q).
split.
  apply: (shaped_set O s2 (VReal dx)) => //.
    exact: (r_shape _ _ _ _ _ _ _ Hr).
  by move=> t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr q t' Hq Hfl Ht') Eq.
rewrite (pairing_set_in O s2 (VReal dx) (stored q)) //.
  exact: (r_nodup _ _ _ _ _ _ _ Hr).
by rewrite Eb Ebn Edy /=; ring.
Qed.

Lemma rctx_shapes L c wP pp O use s s' :
  rctx L c wP pp O use s -> (forall t n, In (t, n) O -> shaped t (barv s' n)) -> rctx L c wP pp O use s'.
Proof. by move=> Hr Hs; case: Hr => *; constructor. Qed.

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
move=> HL HaL Hr Hbar Ha Hsub Hw.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
case Ev: (varied (amap pa aP)) Hw => Hw; last first.
  have Hz : dx = 0.
    have Hst : forall q, aP = AVar q -> static_ok k q.
      by move=> q E; apply: (static_in _ _ _ HL); case: (HaL q E).
    exact: (atom_zero k aP _ Hst Ev Ha).
  have Hn : bar (amap pt aP) = None.
    case: aP HaL Ev {Ha} => [q | |] //= HaL Ev.
    by rewrite (Hbar q (proj1 (HaL q erefl))) Ev.
  rewrite /contribution Hn.
  exists s; split=> //; split=> //.
  split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
  by split=> //; rewrite Hz; ring.
destruct aP as [q | |]; rewrite /= in Ev; try discriminate.
have [Hq Hu] := HaL q erefl.
have [_ [_ [Hsq _]]] := static_in _ _ _ HL Hq.
case: Ha => Eq.
have Hin := r_useful _ _ _ _ _ _ _ Hr q Hq Hu Ev; rewrite Eq /= in Hin.
have /= Hsh := r_shape _ _ _ _ _ _ _ Hr _ _ Hin.
case Eb: (barv s (stored q)) Hsh => [[b0 | | | |] |] // _.
have Huq t' (Ht' : In (t', stored q) O) : t' = VReal dx.
  by rewrite (r_value _ _ _ _ _ _ _ Hr q t' Hq Hu Ht') Eq.
have Hbq : tbar (pt q) = true by rewrite (Hbar q Hq).
have [R1 [R2 [R3 R4]]] :=
  contrib_step c ex O O' s q p xv dx b0 w Hok (r_nodup _ _ _ _ _ _ _ Hr) Hin
    Hsub (r_shape _ _ _ _ _ _ _ Hr) Huq Hbq Hsq Eb (Hw erefl).
eexists; split; first exact: R1.
do 3!(split=> //).
move=> e He; apply: xev_set_other => y Hy K.
have [Hcy Hny] := He y Hy.
have E := keyv_inj y (BarOf (stored q)) Hcy (Hok _ _ Hin) K.
apply: (Hny (stored q)) E.
by apply/(in_map_iff _ _ _); exists (VReal dx, stored q).
Qed.

Lemma arev_op2 f (aP bP : atom pv) : asim_rev0 (AOp2 f aP bP).
Proof.
rev_intro.
rewrite /= in Htc Hst Hvr *; rename f3 into f.
split; first by lia.
move=> s2 O Hrd Hr Hns.
case Ecmp: (comparison f) Hvr => // Hvr.
have HL := s_static _ _ _ _ _ _ _ Hs.
have HaL : forall q, aP = AVar q -> In q L by auto.
have HbL : forall q, bP = AVar q -> In q L by auto.
cbn [aeval_value] in Hev.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
case Hb: (aeval_atom (duals reals) (amap pd bP)) Hev => [vb |] // Hev.
have Hnint (rP : atom pv) z : varied (amap pa rP) = true ->
    aeval_atom (duals reals) (amap pd rP) = Some (VInt z) ->
    (forall q, rP = AVar q -> In q L) -> False.
  move=> Hv Hd HrL; case: rP Hv Hd HrL => [q | |] //= Hv [Ed] HrL.
  have [_ [_ [_ [_ [_ [_ [_ [Hra [Hht _]]]]]]]]] :=
    static_in _ _ _ HL (HrL q erefl).
  have {}Hra := Hra Hv; rewrite Ed in Hht.
  by case: (vty (pw q)) Hra Hht.
case: va Ha Hev => [[x dx] | za | | |] Ha Hev;
  case: vb Hb Hev => [[y dy] | zb | | |] Hb Hev; try discriminate.
2: by move/orb_true_iff: Hvr => [Hv | Hv];
  [case: (Hnint _ _ Hv Ha HaL) | case: (Hnint _ _ Hv Hb HbL)].
cbn [eval_op2] in Hev; rewrite Ecmp in Hev; cbn [dom_op2 duals] in Hev.
case Hd: (dual_op2 R reals f (Dual x dx) (Dual y dy)) Hev
  => [[z dz] |] //.
move=> [Eve]; subst ve.
have [Hn' Hsh] := Hns erefl.
rewrite (oput_notin O _ _ Hn').
rewrite /= in Hsh.
case Ebn: (barv s2 (DBound (j, j))) Hsh => [[be | | | |] |] // _.
case Hp: (partial2 f (amap pt aP) (amap pt bP)) => [[p1 p2] |]; last first.
  by case: f Hd Hp {Hrd Hr Ecmp Hs Htc} => Hd Hp; rewrite /= in Hp;
    try discriminate; unfold_ops Hd.
have Edz := dual_op2_coef _ _ _ _ _ _ _ Hd.
have Hrq (rP : atom pv) : (forall q, rP = AVar q -> In q L) ->
    (rP = aP \/ rP = bP) ->
    (forall q, rP = AVar q ->
       vreads k (AOp2 f (amap pa aP) (amap pa bP)) q) ->
    forall x' dx', aeval_atom (duals reals) (amap pd rP) =
      Some (VReal (Dual x' dx')) ->
    xev s2 (spell (amap pt rP)) = Some (VReal x').
  move=> HrL Hab Hrr x' dx' Hdd; apply: (aspell_ok k s2 rP _ _ Hdd).
  move=> q E; split; first exact: (static_in _ _ _ HL (HrL q E)).
  apply: (Hrd q (HrL q E) (Hrr q E)).
    by subst rP; case: Hab => <-; rewrite /live_value /= Nat.eqb_refl
      /= ?orb_true_r.
  apply: (not_array_val k); first exact: (static_in _ _ _ HL (HrL q E)).
  by subst rP; case: Hdd => ->.
have Hxa : (f = Mul \/ f = Divide) -> varied (amap pa bP) = true ->
    xev s2 (spell (amap pt aP)) = Some (VReal x).
  move=> Hf Hv; apply: (Hrq aP HaL (or_introl erefl) _ _ _ Ha).
  move=> q E; rewrite /vreads /= Ecmp; apply: reads_op2 => //.
  by right; subst.
have Hyb : ((f = Mul \/ f = Divide) /\ varied (amap pa aP) = true) \/
    (f = Divide /\ varied (amap pa bP) = true) ->
    xev s2 (spell (amap pt bP)) = Some (VReal y).
  move=> Hc; apply: (Hrq bP HbL (or_intror erefl) _ _ _ Hb).
  move=> q E; rewrite /vreads /= Ecmp.
  case: Hc => [[Hf Hv] | [Ef Hv]].
    by apply: reads_op2 => //; left; subst.
  by subst; apply: reads_op2_div.
have Hfl (rP : atom pv) : (rP = aP \/ rP = bP) -> forall q, rP = AVar q ->
    In q L /\ vflows k (AOp2 f (amap pa aP) (amap pa bP)) q.
  move=> Hr0 q E; split; first by case: Hr0 => E0; subst; auto.
  rewrite /vflows /= Ecmp.
  case: (partial2 f (amap pa aP) (amap pa bP)) => [[] |] /=;
    rewrite atom_member_union;
    by case: Hr0 => E0; rewrite -E0 E /= Nat.eqb_refl /= ?orb_true_r.
set O' := (tangent (VReal (Dual z dz)), DBound (j, j)) :: O.
have Hsub : forall m, In m (map snd O) -> In m (map snd O').
  by move=> m Hm; right.
have Hsp (rP : atom pv) : (forall q, rP = AVar q -> In q L) ->
    forall y0, In y0 (dvars (spell (amap pt rP))) ->
    consistent y0 /\ forall m, In m (map snd O) -> y0 <> BarOf m.
  move=> HrL y0; case: rP HrL => [q | |] //= HrL [Ey | []]; subst y0.
  have [_ [_ [Hsq _]]] := static_in _ _ _ HL (HrL q erefl).
  by rewrite Hsq; split=> // m _; rewrite /stored.
have Hbn : forall y0, In y0 (dvars (DVar (BarOf (DBound (j, j))))) ->
    consistent y0 /\ forall m, In m (map snd O) -> y0 <> BarOf m.
  move=> y0 [Ey | []]; subst y0; split=> // m Hm [Em].
  by subst m; apply: Hn'.
have He : xev s2 (DVar (BarOf (DBound (j, j)))) = Some (VReal be) by [].
have Hwa : varied (amap pa aP) = true ->
    xev s2 (scale (spell_partial p1) (DVar (BarOf (DBound (j, j))))) =
    Some (VReal (coef_a f x y * be)).
  move=> Hv; apply: (contrib_a s2 f _ _ _ x y be p1 p2 Hp He) => Hf.
  by apply: Hyb; left.
have [s' [R1 [F1 [S1 [P1 T1]]]]] :=
  operand_contrib L k c wP pp (inplace wP pp) O O' s2 aP p1
    (BarOf (DBound (j, j))) x dx (coef_a f x y * be) _
    HL (Hfl aP (or_introl erefl)) Hr Hbar Ha Hsub Hwa.
have Hwb : varied (amap pa bP) = true ->
    xev s' (scale (spell_partial p2) (DVar (BarOf (DBound (j, j))))) =
    Some (VReal (coef_b f x y * be)).
  move=> Hv; apply: (contrib_b s' f _ _ _ x y be p1 p2 Hp).
  - by rewrite T1.
  - by move=> Hf; rewrite T1; [exact: (Hsp aP HaL) | exact: (Hxa Hf Hv)].
  by move=> Hf; rewrite T1; [exact: (Hsp bP HbL) | apply: Hyb; right].
have [s3 [R2 [F2 [S2 [P2 _]]]]] :=
  operand_contrib L k c wP pp (inplace wP pp) O O' s' bP p2
    (BarOf (DBound (j, j))) y dy (coef_b f x y * be) _
    HL (Hfl bP (or_intror erefl)) (rctx_shapes _ _ _ _ _ _ _ _ Hr S1)
    Hbar Hb Hsub Hwb.
exists s3; split.
  by rewrite run_app R1.
split; first exact: (rev_frame_trans _ _ _ _ _ _ F1 F2).
split; first exact: S2.
by rewrite P2 P1 /O' /= Ebn Edz; ring.
Qed.

Lemma arev_get (aP iP : atom pv) : asim_rev0 (AGet aP iP).
Proof.
rev_intro.
rewrite /= in Htc Hst Hvr *.
split; first by lia.
move=> s2 O Hrd Hr Hns.
have HL := s_static _ _ _ _ _ _ _ Hs.
destruct aP as [q | |]; rewrite /= in Hvr; try discriminate.
have Hq : In q L by auto.
have HiL : forall p, iP = AVar p -> In p L by auto.
have [_ [_ [Hsq _]]] := static_in _ _ _ HL Hq.
cbn [aeval_value amap aeval_atom] in Hev.
destruct (pd q) as [| | | l |] eqn:Eq; try discriminate.
case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev.
case Ez: (nth_z z l) Hev => [[x dx] |] // [Eve]; subst ve.
have [Hn Hsh] := Hns erefl.
rewrite (oput_notin O _ _ Hn); cbn [amap] in *.
rewrite /= in Hsh.
case Ebn: (barv s2 (DBound (j, j))) Hsh => [[be | | | |] |] // _.
have Hfl : vflows k (AGet (AVar (pa q)) (amap pa iP)) q.
  by rewrite /vflows /= Nat.eqb_refl.
have Hin := r_useful _ _ _ _ _ _ _ Hr q Hq Hfl Hvr; rewrite Eq /= in Hin.
have /= Hshq := r_shape _ _ _ _ _ _ _ Hr _ _ Hin.
case Eb: (barv s2 (stored q)) Hshq => [[| | | bm |] |] // Hshq.
have Hsi : xev s2 (spell (amap pt iP)) = Some (VInt z).
  apply: (aspell_ok k s2 iP _ _ Hi) => p E.
  split; first exact: (static_in _ _ _ HL (HiL p E)).
  apply: (Hrd p (HiL p E)); subst iP.
  - by rewrite /vreads /= Nat.eqb_refl.
  - by rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
  apply: (not_array_val k); first exact: (static_in _ _ _ HL (HiL p erefl)).
  by case: Hi => ->.
have /= Ezt := nth_z_map dsnd z l; rewrite Ez /= in Ezt.
rewrite length_map in Hshq.
have [bk Ebk] := nth_z_length z l bm _ Ez Hshq.
have [bm' Ebm'] := replace_exists z bm bk (bk + be) Ebk.
rewrite /contribution /= (Hbar q Hq) Hvr Hsq.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
exists (store_set s2 (keyv (BarOf (stored q))) (VArray bm')).
split; first exact: (run_increment_at _ _ _ _ bm z bk be).
split.
  apply: rev_frame_set => //; right.
  by apply/(in_map_iff _ _ _); eexists; split; last exact: Hin.
have Hlen : length bm' = length bm.
  move: Ebm'; rewrite /replace_nth_z; case: (z <? 0)%Z => // Ebm'.
  by have [_ [_ [_ E]]] := replace_nth_nth _ _ _ _ Ebm'.
split.
  apply: (shaped_set O s2 (VArray (map dsnd l))) => //.
    exact: (r_shape _ _ _ _ _ _ _ Hr).
  move=> t' Ht'; rewrite (r_value _ _ _ _ _ _ _ Hr q t' Hq Hfl Ht') Eq /=.
  by rewrite length_map; lia.
rewrite (pairing_set_in O s2 (VArray (map dsnd l)) (stored q)) //.
  exact: (r_nodup _ _ _ _ _ _ _ Hr).
rewrite Eb Ebn /=.
move: Ezt Ebk Ebm'; rewrite /nth_z /replace_nth_z.
case: (z <? 0)%Z => // Ezt Ebk Ebm'.
by rewrite (dotr_replace _ _ _ _ _ _ _ Ezt Ebk Ebm'); ring.
Qed.

Lemma arev_set (aP iP vP : atom pv) : asim_rev0 (ASet aP iP vP).
Proof.
rev_intro.
rewrite /= in Htc Hvr *.
split; first by lia.
move=> s2 O Hrd Hr Hns.
have HL := s_static _ _ _ _ _ _ _ Hs.
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
have Hnd := r_nodup _ _ _ _ _ _ _ Hr.
cbn [aeval_value] in Hev.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev
  => [[| | | l |] |] // Hev;
  case Hi: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev;
  case Hv: (aeval_atom (duals reals) (amap pd vP)) Hev
  => [[[y dy] | | | |] |] // Hev.
case Er: (replace_nth_z z (Dual y dy) l) Hev => [l1 |] // [Eve]; subst ve.
destruct aP as [qa | str | zq]; last 2 first.
- by have [? [_ E]] := aeval_literal _ _ Ha.
- by [].
case: Ha => Eqa; rewrite /= in Hst.
have Hqa : In qa L by auto.
have HiL : forall p, iP = AVar p -> In p L by auto.
have HvL : forall p, vP = AVar p -> In p L by auto.
clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
have Hsi : xev s2 (spell (amap pt iP)) = Some (VInt z).
  apply: (aspell_ok k s2 iP _ _ Hi) => p E.
  split; first exact: (static_in _ _ _ HL (HiL p E)).
  apply: (Hrd p (HiL p E)); subst iP.
  - by rewrite /vreads /= Nat.eqb_refl.
  - by rewrite /live_value /= Nat.eqb_refl ?orb_true_r.
  apply: (not_array_val k); first exact: (static_in _ _ _ HL (HiL p erefl)).
  by case: Hi => ->.
have /= Ert := replace_nth_z_map dsnd z (Dual y dy) l.
rewrite Er /= in Ert.
have Hown : owner wP pp = Some qa.
  destruct pp as [| | | ix sx]; rewrite /= in Htc; try discriminate.
  case: (vty (pw qa)) Htc => // aty Htc.
  case E: (vid (pw qa) =? vid (pw sx))%nat Htc; last first.
    by rewrite andb_false_r.
  move=> _; have [_ [Hsx _]] := s_place _ _ _ _ _ _ _ Hs.
  by rewrite (same_vid_s _ _ _ _ _ _ _ _ _ Hs Hqa Hsx E).
have Hsh :=
  r_shape _ _ _ _ _ _ _ Hr _ _ (r_owner _ _ _ _ _ _ _ Hr qa Hown).
rewrite Eqa -Hst /= in Hsh.
case Ebn: (barv s2 (DBound (j, j))) Hsh => [[| | | bn |] |] // Hsh.
rewrite length_map -(replace_nth_z_length _ _ _ _ Er) in Hsh.
rewrite Hst in Ebn Hns *.
move: Er Ert; rewrite /replace_nth_z; case Ez0: (z <? 0)%Z => // Er Ert.
have [ta_z [Etz [_ Elen]]] := replace_nth_nth _ _ _ _ Ert.
have Elen1 := replace_nth_length _ _ _ _ Er.
case Ebk: (nth_error bn (Z.to_nat z)) => [bk |]; last first.
  exfalso; move/nth_error_None: Ebk => Ebk.
  have Hne : nth_error (map dsnd l) (Z.to_nat z) <> None by rewrite Etz.
  by move/nth_error_Some: Hne; rewrite length_map; lia.
have [bn0 Ebn0] : exists bn0, replace_nth_z z 0 bn = Some bn0.
  by apply: (replace_exists z bn bk 0); rewrite /nth_z Ez0.
set ei := spell (amap pt iP) in Hsi *.
set n := stored qa in Hns Ebn Hsh *.
have Hcn : consistent n by rewrite /n -Hst.
have Helem s : barv s n = Some (VArray bn) -> xev s ei = Some (VInt z) ->
    xev s (DAt (DVar (BarOf n)) ei) = Some (VReal bk).
  move=> G1 G2; rewrite /xev /barv /keyv /= in G1 G2 *.
  by rewrite G1 G2 /nth_z Ez0 /= Ebk.
have Hzero s : barv s n = Some (VArray bn) -> xev s ei = Some (VInt z) ->
    run [DAssign (DAt (DVar (BarOf n)) ei) (DReal "0")] s =
    Some (store_set s (keyv (BarOf n)) (VArray bn0)).
  move=> G1 G2; apply: (run_assign_at s (BarOf n) ei (DReal "0") bn z 0 bn0)
    => //.
  by rewrite xev_DReal lit_0.
have Hdot0 :
    dotr (map dsnd l) bn0 = dotr (map dsnd l) bn + ta_z * (0 - bk).
  apply: (dotr_replace _ _ _ _ _ _ _ Etz Ebk).
  by move: Ebn0; rewrite /replace_nth_z Ez0.
have Hdot1 :
    dotr (map dsnd l1) bn = dotr (map dsnd l) bn + bk * (dy - ta_z).
  rewrite (dotr_sym (map dsnd l1)) (dotr_sym (map dsnd l)).
  exact: (dotr_replace _ _ _ _ _ _ _ Ebk Etz Ert).
have Hfla :
    vflows k (ASet (amap pa (AVar qa)) (amap pa iP) (amap pa vP)) qa.
  rewrite /vflows; cbn [value_needs fst snd atoms_of_atoms atoms_of_atom amap].
  by rewrite atom_member_union atom_member_var.
have Hta t : In (t, n) O -> t = VArray (map dsnd l).
  by move=> Ht; rewrite (r_value _ _ _ _ _ _ _ Hr qa t Hqa Hfla Ht) Eqa.
have Hstep : exists s', run (match bar (amap pt vP) with
      | Some bv => [DIncrement bv (DAt (DVar (BarOf n)) ei)]
      | None => [] end) s2 = Some s' /\
    rev_frame c (inplace wP pp) (oput O n (tangent (VArray l1))) s2 s' /\
    (forall t m, In (t, m) O -> shaped t (barv s' m)) /\
    pairing O s' = pairing O s2 + dy * bk /\
    barv s' n = Some (VArray bn) /\ xev s' ei = Some (VInt z).
  case Evv: (varied (amap pa vP)); last first.
    have Hz : dy = 0.
      have Hst' : forall q, vP = AVar q -> static_ok k q.
        by move=> q E; exact: (static_in _ _ _ HL (HvL q E)).
      exact: (atom_zero k vP _ Hst' Evv Hv).
    have Hnb : bar (amap pt vP) = None.
      destruct vP as [q | |] => //=; rewrite /= in Evv.
      by rewrite (Hbar q (HvL q erefl)) Evv.
    rewrite Hnb; exists s2; split=> //; split=> //.
    split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
    by split; first by rewrite Hz; ring.
  destruct vP as [qv | |]; rewrite /= in Evv; try discriminate.
  have Hqv : In qv L by auto.
  have [_ [_ [Hsqv _]]] := static_in _ _ _ HL Hqv.
  have Hflv :
      vflows k (ASet (amap pa (AVar qa)) (amap pa iP) (amap pa (AVar qv))) qv.
    rewrite /vflows.
    cbn [value_needs fst snd atoms_of_atoms atoms_of_atom amap].
    by rewrite !atom_member_union atom_member_var !orb_true_r.
  case: Hv => Eqv.
  have Hin := r_useful _ _ _ _ _ _ _ Hr qv Hqv Hflv Evv.
  rewrite Eqv /= in Hin.
  have /= Hshv := r_shape _ _ _ _ _ _ _ Hr _ _ Hin.
  case Eb: (barv s2 (stored qv)) Hshv => [[bv0 | | | |] |] // _.
  have Hne : stored qv <> n by move=> E; rewrite E Ebn in Eb.
  have Hcv : consistent (stored qv) by apply: (Hok (VReal dy)).
  rewrite /= (Hbar qv Hqv) Evv Hsqv.
  exists (store_set s2 (keyv (BarOf (stored qv))) (VReal (bv0 + bk))).
  split; first by apply: run_increment => //; exact: Helem.
  split.
    apply: rev_frame_set => //; apply: oput_sub.
    by apply/(in_map_iff _ _ _); exists (VReal dy, stored qv).
  split.
    apply: (shaped_set O s2 (VReal dy)) => //.
      exact: (r_shape _ _ _ _ _ _ _ Hr).
    move=> t' Ht'.
    by rewrite (r_value _ _ _ _ _ _ _ Hr qv t' Hqv Hflv Ht') Eqv.
  split.
    by rewrite (pairing_set_in O s2 (VReal dy) (stored qv)) // Eb /=; ring.
  split; first by rewrite barv_set_other.
  rewrite xev_set_other //; apply: (avoid_bar_spell k) => p E.
  exact: (static_in _ _ _ HL (HiL p E)).
have [s' [R1 [F1 [S1 [P1 [B1 X1]]]]]] := Hstep.
exists (store_set s' (keyv (BarOf n)) (VArray bn0)).
split.
  case: (bar (amap pt vP)) R1 => [bv |] R1; last first.
    by case: R1 => E; subst s'; exact: Hzero.
  have Happ : forall a b : dstmt W, [a; b] = ([a] ++ [b])%list by [].
  by rewrite Happ run_app R1; exact: Hzero.
split.
  apply: (rev_frame_trans _ _ _ _ _ _ F1).
  exact: (rev_frame_set _ _ _ _ _ _ (oput_in O n _) Hcn).
have Hlen0 : length bn0 = length bn := replace_nth_z_length _ _ _ _ Ebn0.
split.
  move=> t m Htm; case: (dvar_eq_dec_c n m) => [Enm | Enm].
    by subst m; rewrite barv_set_same (Hta t Htm) /= length_map; lia.
  by rewrite (barv_set_other _ _ _ _ Hcn (Hok t m Htm) Enm); apply: S1.
case: (in_dec dvar_eq_dec_c n (map snd O)) => [Inn | Inn].
  move/(in_map_iff _ _ _): (Inn) => [[t n'] [En Itn]]; rewrite /= in En.
  subst n'; have Et := Hta t Itn; subst t.
  rewrite (pairing_set_in O s' (VArray (map dsnd l)) n) //.
  rewrite /oput.
  case: (in_dec dvar_eq_dec_c n (map snd O)) => [I | /(_ Inn) []].
  rewrite (pairing_oset O s2 (VArray (map dsnd l)) n) //.
  by rewrite B1 Ebn P1 /= Hdot0 Hdot1; ring.
rewrite pairing_set_other //.
rewrite (oput_notin O _ _ Inn) /= Ebn P1 Hdot1.
have Hva : avaried (pa qa) = false.
  case E: (avaried (pa qa)) => //; exfalso; apply: Inn.
  apply/(in_map_iff _ _ _); exists (tangent (pd qa), stored qa); split=> //.
  exact: (r_useful _ _ _ _ _ _ _ Hr qa Hqa Hfla E).
have [_ [_ [_ [_ [_ [_ [_ [_ [_ Hzq]]]]]]]]] := static_in _ _ _ HL Hqa.
have := Hzq Hva; rewrite Eqa /= => {}Hzq.
have Hz0 : Forall (fun x => x = 0) (map dsnd l) by apply/Forall_map.
rewrite dotr_sym (dotr_zero bn _ Hz0).
have -> : ta_z = 0.
  by move/Forall_forall: Hz0; apply; apply: nth_error_In Etz.
by ring.
Qed.

(* ---------------------------------------------------------------------------
   What needs says at a let, of a variable in scope (an identity below k):
   from the rest of the body, and from the value. *)

Lemma same_term_below (q : avar) k vr : (aid q < k)%nat -> same_term (AVar (AV k vr)) (AVar q) = false.
Proof. by move=> H /=; apply/Nat.eqb_neq; lia. Qed.

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
Proof. by []. Qed.

Section NeedsLet.
Variables (m : sweep) (k : nat) (a : bare) (eA : value avar bare) (cA : avar -> anf avar bare) (p : pv).
Hypothesis Hp : (aid (pa p) < k)%nat.
Let x := let_binder k eA.

Ltac needs_let_tac := rewrite needs_let; unfold x in *; destruct (needs cv m (S k) (cA (let_binder k eA))) as [ub lb]; cbv zeta.
Ltac split_reads := destruct (varied_value k eA && _); [destruct (value_needs cv k eA) as [r f] |]; cbn [fst snd].
Ltac below_tac := apply same_term_below; exact Hp.

Lemma useful_let_cont : useful cv m (S k) (cA x) p -> useful cv m k (ALet a eA cA) p.
Proof.
rewrite /useful; needs_let_tac => /= H; split_reads;
  by rewrite atom_member_union atom_member_remove ?H //; below_tac.
Qed.

Lemma tbr_let_cont : tbr cv m (S k) (cA x) p -> tbr cv m k (ALet a eA cA) p.
Proof.
rewrite /tbr; needs_let_tac => /= H; split_reads;
  by rewrite !atom_member_union atom_member_remove ?H //; below_tac.
Qed.

Lemma useful_let_flows :
  varied_value k eA && atom_member (AVar x) (fst (needs cv m (S k) (cA x))) = true ->
  vflows k eA p -> useful cv m k (ALet a eA cA) p.
Proof.
rewrite /useful /vflows; needs_let_tac => /= Ha Hf; rewrite Ha.
case: (value_needs cv k eA) Hf => r f /= Hf.
by rewrite atom_member_union Hf orb_true_r.
Qed.

Lemma tbr_let_reads :
  varied_value k eA && atom_member (AVar x) (fst (needs cv m (S k) (cA x))) = true ->
  vreads k eA p -> tbr cv m k (ALet a eA cA) p.
Proof.
rewrite /tbr /vreads; needs_let_tac => /= Ha Hf; rewrite Ha.
case: (value_needs cv k eA) Hf => r f /= Hf.
by rewrite !atom_member_union Hf orb_true_r.
Qed.

Lemma tbr_let_atoms :
  atom_member (AVar x) (snd (needs cv m (S k) (cA x))) || (sweep_eqb m Forward && records cv k eA) = true ->
  vatoms k eA p -> tbr cv m k (ALet a eA cA) p.
Proof.
rewrite /tbr /vatoms; needs_let_tac => /= Hc Hf; rewrite Hc.
by split_reads; rewrite !atom_member_union Hf orb_true_r.
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
act_intro.
rewrite /= in Htc Hev *; rename f2 into f.
have Ha1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
have [Ete Hta] : te = Real /\ of_atom (amap pw aP) = Real.
  by destruct f; rewrite /= in Htc; crush_match Htc; split; congruence.
subst te.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
have := atom_type k aP va Ha1 Ha; rewrite Hta => Htv.
case: va Htv Ha Hev => [[x dx] | | | |] // _ Ha Hev.
cbn [eval_op1 dom_op1 duals] in Hev.
case Hd: (dual_op1 R reals f (Dual x dx)) Hev => [[y dy] |] // [Eve].
subst ve; split=> //; split=> // Hv.
have /= Hz := atom_zero k aP _ Ha1 Hv Ha; subst dx.
exact: (dual_op1_zero f x y dy Hd).
Qed.

Lemma act_op2 f (aP bP : atom pv) : act_value (AOp2 f aP bP).
Proof.
act_intro.
rewrite /= in Htc Hev *; rename f2 into f.
have Ha1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
have Hb1 : forall p, bP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev => [va |] // Hev.
case Hb: (aeval_atom (duals reals) (amap pd bP)) Hev => [vb |] // Hev.
case Ho2: (operation2 f) Htc => [o2 |] // Htc.
case Ht2: (operation2_typed f (of_atom (amap pw aP)) (of_atom (amap pw bP)))
  Htc => [[t0 sp] |] // [Et0]; subst t0.
have Hta := atom_type k aP va Ha1 Ha; have Htb := atom_type k bP vb Hb1 Hb.
destruct va as [[x dx] | za | | |], vb as [[y dy] | zb | | |];
  cbn [eval_op2] in Hev; try discriminate.
  rewrite /= in Hta Htb.
  case Ea: (of_atom (amap pw aP)) Hta Ht2 => // _ Ht2.
  case Eb: (of_atom (amap pw bP)) Htb Ht2 => // _ Ht2.
  have Ete := op2_real_type _ _ _ Ht2; subst te.
  case Hcmp: (comparison f) Hev => Hev /=.
    cbn [dom_cmp duals dual_cmp] in Hev.
    by case: (dom_cmp reals f x y) Hev => [bo |] // [<-].
  cbn [dom_op2 duals] in Hev.
  case Hd: (dual_op2 R reals f (Dual x dx) (Dual y dy)) Hev
    => [[z dz] |] // [<-].
  split=> //; split=> // /orb_false_iff [Hva Hvb].
  have /= Hza := atom_zero k aP _ Ha1 Hva Ha.
  have /= Hzb := atom_zero k bP _ Hb1 Hvb Hb.
  by subst dx dy; exact: (dual_op2_zero f x y z dz Hd).
case: Hev => <-; rewrite /= in Hta Htb.
move/has_type_int: Hta => Hta; move/has_type_int: Htb => Htb.
rewrite Hta Htb in Ht2.
rewrite (int_not_varied k aP za Ha1 Ha) (int_not_varied k bP zb Hb1 Hb).
split; first exact: (int_op2_type f za zb te sp Ht2).
by split; [move=> _; case: f {Ho2 Ht2} | case: (comparison f)].
Qed.

Lemma act_get (aP iP : atom pv) : act_value (AGet aP iP).
Proof.
act_intro.
rewrite /= in Htc Hev *.
have Ha1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
case: (ty_is_array (of_atom (amap pw aP)) &&
  ty_eqb (of_atom (amap pw iP)) Integer) Htc => // - [Ete]; subst te.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev
  => [[| | | l |] |] // Hev;
  case: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev.
case Ez: (nth_z z l) Hev => [d |] // [<-].
split=> //; split=> // Hv.
have /= Hz := atom_zero k aP _ Ha1 Hv Ha.
exact: (nth_z_Forall _ _ _ _ Hz Ez).
Qed.

Lemma act_set (aP iP vP : atom pv) : act_value (ASet aP iP vP).
Proof.
act_intro.
rewrite /= in Htc Hev *.
have Ha1 : forall p, aP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
have Hv1 : forall p, vP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
case Ha: (aeval_atom (duals reals) (amap pd aP)) Hev
  => [[| | | l |] |] // Hev;
  case: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev;
  case Hv: (aeval_atom (duals reals) (amap pd vP)) Hev
  => [[d | | | |] |] // Hev.
case Er: (replace_nth_z z d l) Hev => [l1 |] // [<-].
have Hta := atom_type k aP _ Ha1 Ha.
have [n [Ete Ea]] :
    exists n, te = Array n /\ of_atom (amap pw aP) = Array n.
  case: (wplace pp) Htc => //= ? ?.
  case: (of_atom (amap pw aP)) => // n.
  by case: (_ && _) => // - [<-]; exists n.
subst te; rewrite Ea /= in Hta.
split; first by rewrite /= (replace_nth_z_length _ _ _ _ Er).
split=> // /orb_false_iff [Hva Hvv].
have /= Hza := atom_zero k aP _ Ha1 Hva Ha.
have /= Hzv := atom_zero k vP _ Hv1 Hvv Hv.
exact: (replace_nth_z_Forall _ _ _ _ _ Hzv Hza Er).
Qed.

Lemma sctx_weaken L k c c' wP pp (live live' : pv -> Prop) ty :
  sctx L k c wP pp live ty -> (forall p, live' p -> live p) -> (c <= c')%nat -> sctx L k c' wP pp live' ty.
Proof.
move=> Hc Hl Hcc; constructor.
- exact: (s_static _ _ _ _ _ _ _ Hc).
- exact: (s_unique _ _ _ _ _ _ _ Hc).
- by move=> p Hp; have := s_num _ _ _ _ _ _ _ Hc p Hp; lia.
- exact: (s_written _ _ _ _ _ _ _ Hc).
- exact: (s_place _ _ _ _ _ _ _ Hc).
- move=> o p Ho Hp E.
  case: (s_owner _ _ _ _ _ _ _ Hc o p Ho Hp E) => [H | H]; first by left.
  by right=> /Hl.
- by move=> p o Hp /Hl; apply: (s_arrays _ _ _ _ _ _ _ Hc p o Hp).
- exact: (s_ty _ _ _ _ _ _ _ Hc).
move=> y H1 H2 H3; have [A B] := s_top _ _ _ _ _ _ _ Hc y H1 H2 H3.
by split=> // /Hl.
Qed.

Lemma actx_weaken L k c c' s wP pp (live live' tb tb' : pv -> Prop) ty :
  actx L k c s wP pp live tb ty -> (forall p, live' p -> live p) -> (forall p, In p L -> tb' p -> tb p) ->
  (c <= c')%nat -> actx L k c' s wP pp live' tb' ty.
Proof.
move=> Hc Hl Ht Hcc; have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc; constructor.
- exact: (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hl Hcc).
- exact: (a_bar _ _ _ _ _ _ _ _ _ Hc).
- by move=> p Hp /(Ht p Hp); apply: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp).
- exact: (a_tape _ _ _ _ _ _ _ _ _ Hc).
- move=> o Ho Hor; apply: (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho).
  case: Hor => [Hnl | Ho']; [by left | right].
  exact: (Ht o (owner_in_s _ _ _ _ _ _ _ _ Hs Ho) Ho').
exact: (a_tid _ _ _ _ _ _ _ _ _ Hc).
Qed.

(* The variable updated in place is an array. *)
Lemma owner_array L k c wP pp live ty o :
  sctx L k c wP pp live ty -> owner wP pp = Some o -> is_array (vty (pw o)).
Proof.
move=> Hs Ho; destruct pp as [| | | ix sx]; rewrite /= in Ho;
  try discriminate.
  destruct wP as [[y | |] |]; try discriminate.
  by case E: (vty (pw y)) Ho => // [?] [<-]; rewrite E.
by case: Ho => <-; have [_ [_ [_ [H _]]]] := s_place _ _ _ _ _ _ _ Hs.
Qed.

(* A scalar that occurs is not stored in the storage updated in place. *)
Lemma scalar_not_inplace L k c wP pp (live : pv -> Prop) ty p :
  sctx L k c wP pp live ty -> In p L -> live p -> ~ is_array (vty (pw p)) -> inplace wP pp <> Some (stored p).
Proof.
move=> Hs Hp Hl Ha; rewrite /inplace.
case Eo: (owner wP pp) => [o |] //= [E _].
case: (s_owner _ _ _ _ _ _ _ Hs o p Eo Hp (esym E)) => [Epo | //]; subst o.
exact: (Ha (owner_array _ _ _ _ _ _ _ _ Hs Eo)).
Qed.

Lemma inner_zero t : inner t (Some (VReal 0)) = 0.
Proof. by case: t => /= *; ring. Qed.

Lemma oset_ok O e t : owners_ok O -> owners_ok (oset O e t).
Proof.
move=> Hok t' n' Hi.
have : In n' (map snd (oset O e t)).
  by apply/(in_map_iff _ _ _); exists (t', n').
rewrite oset_snd => /(in_map_iff _ _ _) [[t0 n0] [/= E Hi0]]; subst n0.
exact: (Hok t0 n' Hi0).
Qed.

(* A fresh owner, whose adjoint is 0, adds nothing to the result pairing. *)
Lemma result_pairing_fresh O ty ex v se s n t :
  owners_ok O -> consistent n -> ~ In n (map snd O) ->
  (forall x, In x (dvars se) -> consistent x /\ x <> BarOf n) ->
  result_pairing ((t, n) :: O) ty ex v se (store_set s (keyv (BarOf n)) (VReal 0)) =
  result_pairing O ty ex v se s.
Proof.
move=> Hok Hn Hni Hse.
have Hp O' : owners_ok O' -> map snd O' = map snd O ->
    pairing O' (store_set s (keyv (BarOf n)) (VReal 0)) = pairing O' s.
  by move=> Hok' E; apply: pairing_set_other => //; rewrite E.
have Hsv : seed_value se (store_set s (keyv (BarOf n)) (VReal 0)) =
    seed_value se s.
  rewrite /seed_value xev_set_other // => x Hx K.
  have [Hcx Hxn] := Hse x Hx.
  exact: Hxn (keyv_inj x (BarOf n) Hcx Hn K).
rewrite /result_pairing.
case: ty; case: ex => [e |]; case: v => [d | | | |] * /=.
all: rewrite ?barv_set_same ?inner_zero.
all: try by rewrite (Hp O Hok erefl) ?Hsv; ring.
all: case: (Simplify.dvar_eq nat e n); cbv beta iota.
all: by rewrite barv_set_same inner_zero
  (Hp _ (oset_ok _ _ _ Hok) (oset_snd _ _ _)); ring.
Qed.

(* A reverse frame for more owners and a larger counter, seen from fewer. *)
Lemma rev_frame_mono c c' ex O O' s s' :
  rev_frame c' ex O' s s' -> (c <= c')%nat ->
  (forall m, In m (map snd O') -> In m (map snd O) \/ ~ below c (BarOf m)) ->
  rev_frame c ex O s s'.
Proof.
move=> F Hc HO v Hb Hcv Ht Hex Hbar; apply: F => //.
  exact: (below_mono _ _ _ Hb Hc).
move=> m Ev Hm; subst v.
by case: (HO m Hm) => [H | H]; [exact: (Hbar m erefl H) | exact: (H Hb)].
Qed.

Lemma rev_frame_x_of c ex n O s s' : rev_frame c ex O s s' -> rev_frame_x c ex n O s s'.
Proof. by move=> F v _; exact: F. Qed.

Lemma rev_frame_x_mono c c' ex n O O' s s' :
  rev_frame_x c' ex n O' s s' -> (c <= c')%nat ->
  (forall m, In m (map snd O') -> In m (map snd O) \/ ~ below c (BarOf m)) ->
  (~ below c n \/ ex = Some n) ->
  rev_frame c ex O s s'.
Proof.
move=> F Hc HO Hn v Hb Hcv Ht Hex Hbar; apply: F => //.
- move=> Ev; subst v.
  by case: Hn => [Hn | Hn]; [exact: (Hn Hb) | exact: (Hex Hn)].
- exact: (below_mono _ _ _ Hb Hc).
move=> m Ev Hm; subst v.
by case: (HO m Hm) => [H | H]; [exact: (Hbar m erefl H) | exact: (H Hb)].
Qed.

(* Writing an adjoint keeps the primal keys. *)
Lemma agree_prim_set_bar c ex s1 s2 n w :
  agree_prim c ex s1 s2 -> consistent n -> agree_prim c ex s1 (store_set s2 (keyv (BarOf n)) w).
Proof.
move=> [A B] Hn; split.
  move=> v Hb Hcv Hp; rewrite -(A v Hb Hcv Hp).
  apply: store_get_set_other => K.
  by have E := keyv_inj (BarOf n) v Hn Hcv K; subst v.
move=> v Hb Hcv; rewrite -(B v Hb Hcv); apply: store_get_set_other => K.
by have := keyv_inj (BarOf n) (TapeOf v) Hn Hcv K.
Qed.

Lemma agree_prim_mono c c' ex s1 s2 : agree_prim c' ex s1 s2 -> (c <= c')%nat -> agree_prim c ex s1 s2.
Proof.
by move=> [A B] Hc; split=> v Hb; [apply: A | apply: B];
  apply: below_mono Hb Hc.
Qed.

(* A value updated in place that is not varied leaves the tangent of the
   storage as it was: zero. *)
Definition act_owner (eP : value pv bare) : Prop :=
  forall L k c wP pp (live : pv -> Prop) ty tail eA eW eD ve o,
  value_eq (gA L) eP eA -> value_eq (gW L) eP eW -> value_eq (gD L) eP eD ->
  sctx L k c wP pp live ty -> (forall p, live_value k eW p -> live p) ->
  storage wP tail eP = Some (stored o) -> owner wP pp = Some o ->
  aeval_value (duals reals) eD = Some ve -> varied_value k eA = false ->
  (forall p ny r, In p L -> varg (pw p) = Some (ny, r) -> avaried (pa p) = varied_role r) ->
  (forall y, wP = Some (AVar y) -> exists ny r, varg (pw y) = Some (ny, r) /\ written_role r = true) ->
  forall te, typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) -> (tail = true -> te = ty) ->
  tangent (pd o) = tangent ve.

Lemma zeros_eq (a b : list R) :
  Forall (fun x => x = 0) a -> Forall (fun x => x = 0) b -> length a = length b -> a = b.
Proof.
move=> Ha; elim: Ha b => [| x a' Hx Ha IH] [| y b] //=
  /Forall_cons_iff [Hy Hb] [E].
by rewrite Hx Hy (IH b Hb E).
Qed.

Lemma owner_op1 f (aP : atom pv) : act_owner (AOp1 f aP).
Proof. by move=> L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es. Qed.
Lemma owner_op2 f (aP bP : atom pv) : act_owner (AOp2 f aP bP).
Proof. by move=> L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es. Qed.
Lemma owner_get (aP iP : atom pv) : act_owner (AGet aP iP).
Proof. by move=> L k c wP pp live ty tail eA eW eD ve o _ _ _ _ _ Es. Qed.

Lemma owner_set (aP iP vP : atom pv) : act_owner (ASet aP iP vP).
Proof.
move=> L k c wP pp live ty tail eA eW eD ve o HA HW HD Hs Hlv Es Ho Hev Hvr
  _ _ _ _ _.
destruct eA, eW, eD; rewrite /= in HA HW HD; try contradiction.
repeat match goal with
       | H : _ /\ _ |- _ => destruct H
       | H : atom_eq (gA _) _ _ |- _ =>
           apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gW _) _ _ |- _ =>
           apply atom_graph in H; destruct H as [-> ?]
       | H : atom_eq (gD _) _ _ |- _ =>
           apply atom_graph in H; destruct H as [-> ?]
       end; subst.
destruct aP as [q | |]; rewrite /= in Es; try discriminate.
case: Es => Eq _.
have Hq : In q L by auto.
have Hqo : q = o.
  have Hl : live q by apply: Hlv; rewrite /live_value /= Nat.eqb_refl.
  by case: (s_owner _ _ _ _ _ _ _ Hs o q Ho Hq Eq) => [-> | Hnl].
subst o; rewrite /= in Hev Hvr *.
move/orb_false_iff: Hvr => [Hva Hvv].
have HL := s_static _ _ _ _ _ _ _ Hs.
have [_ [_ [_ [_ [_ [_ [_ [_ [_ Hzq]]]]]]]]] := static_in _ _ _ HL Hq.
have {}Hzq := Hzq Hva.
destruct (pd q) as [| | | l |] eqn:Eq'; try discriminate.
case: (aeval_atom (duals reals) (amap pd iP)) Hev
  => [[| z | | |] |] // Hev.
case Hv: (aeval_atom (duals reals) (amap pd vP)) Hev
  => [[d | | | |] |] // Hev.
case Er: (replace_nth_z z d l) Hev => [l1 |] // [<-].
have Hv1 : forall p, vP = AVar p -> static_ok k p.
  by move=> p E; apply: (static_in _ _ _ HL); auto.
have /= Hzv := atom_zero k vP _ Hv1 Hvv Hv; rewrite /= in Hzq *.
congr VArray; apply: zeros_eq.
- exact/Forall_map.
- exact/Forall_map/(replace_nth_z_Forall _ _ _ _ _ Hzv Hzq Er).
by rewrite !length_map (replace_nth_z_length _ _ _ _ Er).
Qed.

Lemma adj_let w vo m a e b se :
  adj W w vo m (ALet a e b) se =
  let '(vr, ac, cp) := let_ann a in
  with_storage w e b (fun n rec =>
    sbind (adj W w vo m (b (open_let (Transform.type_of e) n vr rec)) se) (fun '(fb, rb) =>
    sbind (if cp then fwd_value W w m e (Transform.type_of e) n rec else Done []) (fun fe =>
    sbind (if ac then rev_value W w vo e (Transform.type_of e) n else Done []) (fun re =>
    Done (app fe fb, app (if ac then bar_declaration W (Transform.type_of e) n else []) (app rb re)))))).
Proof. by []. Qed.

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
move=> HT HL Hw.
have Hst : forall p, In p L ->
    tstored (pt p) = stored p /\ tty (pt p) = vty (pw p).
  by move=> p Hp; have [_ [_ [H1 [H2 _]]]] := static_in _ _ _ HL Hp.
Local Ltac fresh_case' :=
  solve [eexists (DBound (_, _)), false, (S _); simpl; auto].
destruct eP as
  [f a | f a b | a i | a i x | cnd t e | lo hi b | an lo hi init b], eT;
  simpl in HT; try contradiction; simpl;
  try fresh_case'; try (destruct vt; fresh_case').
- (* ASet *)
  case: HT => Ha _; destruct a as [p | |]; destruct a0; simpl in Ha;
    try contradiction; try fresh_case'.
  case/in_gT: Ha => Hp ->; have [E _] := Hst _ Hp.
  exists (stored p), (trecorded (pt p)), c; rewrite /= E.
  by split=> //; split=> //; split=> //; exists p.
- (* AMap *)
  destruct vt; simpl;
    (destruct (Transform.is_tail bT); [| fresh_case']);
    (destruct wP as [[y | |] |]; simpl;
     [| fresh_case' | fresh_case' | fresh_case']);
    (destruct (Hw _ eq_refl) as [y' [E Hy]]; injection E as <-;
     destruct (Hst _ Hy) as [E _]; exists (stored y), (trecorded (pt y)), c;
     rewrite E; split; [reflexivity | split; [reflexivity |
       split; [reflexivity | exists y; auto]]]).
(* AFold *)
case: HT => _ [_ [Hi _]]; destruct init as [p | |], init0; simpl in Hi;
  try contradiction; destruct vt; simpl; try fresh_case';
  (apply in_gT in Hi as [Hp ->]; destruct (Hst _ Hp) as [E1 E2]; rewrite E2;
   destruct (vty (pw p)); try fresh_case';
   exists (stored p), (trecorded (pt p)), c; rewrite E1;
   split; [reflexivity | split; [reflexivity |
     split; [reflexivity | exists p; auto]]]).
Qed.

Lemma option_dec_ex (o : option (dvar W)) (v : dvar W) : {o = Some v} + {o <> Some v}.
Proof.
case: o => [w |]; last by right.
by case: (dvar_eq_dec_c w v) => [-> | H]; [left | right=> - [E]].
Qed.

Lemma asim_let a (eP : value pv bare) (cP : pv -> anf pv bare) :
  asim_fwd eP -> asim_rev eP -> inplace_only eP -> act_value eP -> act_owner eP -> (forall x, asim_body (cP x)) ->
  asim_body (ALet a eP cP).
Proof.
move=> IHf IHr IHi IHa IHo IHb L k c s wP pp m bA bW bT bD ty v se vo
  HA HW HT HD Hc Hty Htc Hev Hvo Hvt Hvb Hrpl Hvi.
destruct bA as [aA eA cA |], bW as [aW eW cW |], bT as [aT eT cT |],
  bD as [aD eD cD |]; rewrite /= in HA HW HT HD; try contradiction.
case: HA => HeA HcA; case: HW => HeW HcW; case: HT => HeT HcT.
case: HD => HeD HcD.
rewrite /= in Htc Hev.
case Hte: (typecheck_value (option_map (amap pw) wP) (wplace pp)
  (WellFormed.is_tail cW k) k eW) Htc => [te [| ?]] //= Htc.
case Hve: (aeval_value (duals reals) eD) Hev => [ve |] // Hev.
have Hs := a_sctx _ _ _ _ _ _ _ _ _ Hc.
have HL := s_static _ _ _ _ _ _ _ Hs.
cbn [annotate_body_t].
case Hneeds: (needs cv m (S k) (cA (let_binder k eA))) => [u l].
set vr := varied_value k eA; set vt := annotate_value_t cv k eA.
set rest := annotate_body_t cv m (S k) (cA (let_binder k eA)).
set ac := vr && atom_member (AVar (let_binder k eA)) u.
set cp := atom_member (AVar (let_binder k eA)) l ||
  sweep_eqb m Forward && records cv k eA.
cbn [rebuild]; rewrite adj_let; cbv [let_ann].
rewrite (type_of_ok _ _ _ _ _ _ _ _ vt te HeW HeT HL Hte).
match goal with |- context [with_storage _ _ _ ?K] => set Kf := K end.
have Hw : forall a0, wP = Some a0 -> exists y, a0 = AVar y /\ In y L.
  by move=> a0 E; have [y [-> [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ E;
    exists y.
have [n [rec [c0 [Hopen Hn]]]] := open_with_storage' L k wP eP eT vt
  (fun v0 => rebuild _ (cT v0) rest) Kf c HeT HL Hw.
rewrite Hopen.
have Htt p : In p L -> (vid (pw p) < k)%nat /\ tid (pt p) <> Some 0%nat.
  by move=> Hp; have [_ [H1 [_ [_ [_ [_ [H2 _]]]]]]] := static_in _ _ _ HL Hp.
rewrite -(is_tail_transfer L k cP cW cT rest HcW HcT Htt) in Hn.
set tail := WellFormed.is_tail cW k in Hte Hn *.
have Htail_ty : tail = true -> te = ty.
  move=> Ht.
  have [_ E] :=
    tail_cont L k cP cW (pfresh k) (VInfo k te None) HcW HL erefl Ht.
  by rewrite E /= in Htc; case: Htc.
rewrite /Kf open_pairs_sbind.
case Hb: (open_pairs (adj W (option_map (amap pt) wP) vo m
  (rebuild (tvar W) (cT (open_let te n vr rec)) rest) se) c0)
  => [[fb rb] c1].
rewrite open_pairs_sbind.
case Hfe: (open_pairs (if cp then fwd_value W (option_map (amap pt) wP) m
  (rebuild_value (tvar W) eT vt) te n rec else Done []) c1) => [fe c2].
rewrite open_pairs_sbind.
case Hre: (open_pairs (if ac then rev_value W (option_map (amap pt) wP) vo
  (rebuild_value (tvar W) eT vt) te n else Done []) c2) => [re c3].
cbn [open_pairs].
have Hc01 : (c0 <= c1)%nat.
  by rewrite -[c1]/(snd (fb, rb, c1)) -Hb; exact: open_pairs_mono.
have Hc12 : (c1 <= c2)%nat.
  by rewrite -[c2]/(snd (fe, c2)) -Hfe; exact: open_pairs_mono.
have Hc23 : (c2 <= c3)%nat.
  by rewrite -[c3]/(snd (re, c3)) -Hre; exact: open_pairs_mono.
have Haid := aids_below L k HL.
have Hlv_e p : live_value k eW p -> live_anf k (ALet aW eW cW) p.
  by rewrite /live_value /live_anf /= => ->.
case Es: (storage wP tail eP) Hn => [m0 |] Hn.
  (* stored in place: the let ends the body, which returns the variable *)
  case: Hn => En [Ec0 [qr [Hqr [Esr Erec]]]]; subst n c0.
  have Hsn : storage wP tail eP <> None by rewrite Es.
  have [Ht [o [Ho Es']]] :=
    inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte Htail_ty (or_introl Hsn).
  rewrite Es in Es'; case: Es' => Em0.
  move: Esr; rewrite Em0 => Esr; subst m0.
  have Harr := inplace_array _ _ _ _ _ _ _ _ HeW Hte Hsn.
  have Ety := Htail_ty Ht; subst ty.
  set x := PV (let_binder k eA) (VInfo k te None)
    (open_let te (stored o) vr rec) ve (pn o).
  have Hx : aid (pa x) = k by [].
  have HxL : ~ In x L by exact: (fresh_notin L k x Haid Hx).
  have [Hcx EW] := tail_cont L k cP cW x (VInfo k te None) HcW HL Hx Ht.
  have ET : cT (pt x) = ARet (AVar (pt x)).
    have := HcT x (pt x); rewrite Hcx.
    case: (cT (pt x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => <-.
    by case/in_gT: I => I _; case: HxL.
  have ED : cD (pd x) = ARet (AVar (pd x)).
    have := HcD x (pd x); rewrite Hcx.
    case: (cD (pd x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => <-.
    by case/in_gD: I => I _; case: HxL.
  have EA : cA (pa x) = ARet (AVar (pa x)).
    have := HcA x (pa x); rewrite Hcx.
    case: (cA (pa x)) => [? ? ? | [t' | |]] //= [E | I].
      by case: E => <-.
    by case/in_gA: I => I _; case: HxL.
  rewrite /= in ET ED EA; rewrite ED /= in Hev; case: Hev => Ev; subst v.
  rewrite EA /= in Hneeds.
  rewrite /rest EA in Hb; cbn [annotate_body_t rebuild] in Hb; rewrite ET in Hb.
  cbn [rebuild adj] in Hb; rewrite /= in Hb.
  destruct te as [| | | z]; try by case: Harr.
  have Hfb : (if sweep_eqb m Forward then value_output W vo
      (AVar (open_let (Array z) (stored o) vr rec)) else []) = [].
    destruct m => //=.
    have [Epp [_ [Hy Hr0]]] := Hvo erefl; subst pp.
    destruct vo as [[t0 | y] |] => //.
      by have Ew := Hr0 t0 erefl; subst wP.
    have {}Hy := Hy y erefl.
    destruct wP as [[y' | |] |]; rewrite /= in Ho; try discriminate.
    case: Hy => Ey; subst y.
    case Evy: (vty (pw y')) Ho => // [?] [Eo]; subst o.
    have [y'' [[E] [Hy' _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl; subst y''.
    have [_ [_ [_ [Htq _]]]] := static_in _ _ _ HL Hy'.
    by rewrite /value_output /= Htq Evy.
  rewrite Hfb in Hb; case: Hb => Efb Erb Ec1; subst fb rb c1.
  have Hoin : In o L by exact: (owner_in_s _ _ _ _ _ _ _ _ Hs Ho).
  have Hj : exists j, stored o = DBound (j, j) /\ (j < c)%nat.
    by exists (pn o); split=> //; exact: (s_num _ _ _ _ _ _ _ Hs o Hoin).
  have Hst0 : match storage wP tail eP return Prop with
      | Some m0 => stored o = m0
      | None => forall p, In p L -> stored p <> stored o end by rewrite Es.
  have Hrec : rec = true ->
      exists l0, store_get s (keyv (TapeOf (stored o))) = Some (VTape l0).
    move=> Hr0; rewrite -Esr; apply: (a_tape _ _ _ _ _ _ _ _ _ Hc qr Hqr).
    by rewrite -Erec.
  have Hrec' : rec = true \/ (m = Forward /\ records cv k eA = true /\
      storage wP tail eP <> None /\ ~ not_in_loop pp) ->
      exists l0, store_get s (keyv (TapeOf (stored o))) = Some (VTape l0).
    case=> [Er | [Em [_ [_ Hl]]]]; first exact: Hrec Er.
    by exfalso; apply: Hl; rewrite (proj1 (Hvo Em)).
  have Hex : inplace wP pp = Some (stored o) by rewrite /inplace Ho.
  have Hn0 : needs cv m (S k) (cA (let_binder k eA)) = (u, l) by rewrite EA.
  have Hfw : exists se1, run fe s = Some se1 /\
      fwd_frame c (Some (stored o)) None s se1 /\
      tkeep c (Some (stored o)) s se1 /\
      (cp = true -> store_get se1 (keyv (stored o)) = Some (primal ve)) /\
      (cp = true -> m = Forward /\ not_in_loop pp ->
         fold_tape k eA eW eD se1 (stored o)) /\
      (cp = false -> se1 = s).
    case Ecp: (cp) Hfe => Hfe; last first.
      case: Hfe => Efe Ec2; subst fe c2.
      exists s; split=> //; split=> //; split; first exact: tkeep_refl.
      by split.
    have Hc1 : actx L k c s wP pp (live_value k eW) (vatoms k eA) (Array z).
      apply: (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); last by lia.
      move=> p Hp Hv; apply: (tbr_let_atoms m k aA eA cA p) Hv.
      by rewrite Hn0.
    have IH := IHf L k c s wP pp tail eA eW eT eD (Array z) (stored o) ve
      (Array z) m rec HeA HeW HeT HeD Hc1 Hte Htail_ty Hj Hst0 Hrec' Hve.
    cbv zeta in IH; rewrite -/vt Hfe in IH.
    have [_ [se1 [R1 [F1 [T1 [S1 [Ft1 _]]]]]]] := IH.
    by exists se1; split=> //; split=> //; split=> //; split=> //; split.
  have [se1 [R1 [F1 [T1 [S1 [Ft1 Es1]]]]]] := Hfw.
  split; first by lia.
  split; first exact: (proj1 (IHa L k wP pp tail eA eW eD (Array z) ve HeA HeW
    HeD HL Hte Hve)).
  exists se1; split; first by rewrite app_nil_r.
  split.
    move=> v0 Hb0 Hc0 Ht0 He0 _; apply: F1 => //; first by rewrite -Hex.
  split; first by rewrite Hex.
  split.
    move=> Hm t0' Hvt0; have [Epp [Hcv [Hy Hr0]]] := Hvo Hm; subst pp m.
    destruct vo as [[t0 | y] |]; rewrite /= in Hvt0; try discriminate.
    have Ecv : cv = true.
      by case: (cv) Hcv => // - [_ /(_ erefl)].
    have Ecp : cp = true.
      rewrite /cp; rewrite Ecv /= in Hneeds.
      by case: Hneeds => _ <- /=; rewrite Nat.eqb_refl.
    have {}Hy := Hy y erefl.
    destruct wP as [[y' | |] |]; rewrite /= in Ho; try discriminate.
    case Evy: (vty (pw y')) Ho => // [?] [Eo]; subst y'.
    case: Hy => Ey; subst y.
    have [_ [_ [Hso _]]] := static_in _ _ _ HL Hoin.
    rewrite /role_of /stored_of /= Hso in Hvt0.
    case: (targ (pt o)) Hvt0 => [[? []] |] //=.
    by case: (tty (pt o)) => [| | | ?] // [<-]; exact: S1 Ecp.
  move=> s2 O Hag Hr Hseed Htp Htt2.
  have Hbd : (if ac then bar_declaration W (Array z) (stored o) else []) = [].
    by case: (ac).
  rewrite Hbd !app_nil_l.
  have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
  have Hown := r_owner _ _ _ _ _ _ _ Hr o Ho.
  have Hio : not_in_loop pp -> ~ vreads k eA o /\
      (avaried (pa o) = true -> varied_value k eA = true) /\
      (~ live_value k eW o -> avaried (pa o) = false).
    move=> Hl; exact: (IHi L k wP pp tail eA eW _ HeA HeW HL
      (s_unique _ _ _ _ _ _ _ Hs) Hte Hsn Hl
      (r_args _ _ _ _ _ _ _ Hr) (r_written _ _ _ _ _ _ _ Hr) o Ho Hoin).
  have Hres : result_pairing O (Array z) (inplace wP pp) ve se s2 =
      pairing (oset O (stored o) (tangent ve)) s2 by rewrite Hex.
  rewrite Hres.
  have Hu : atom_member (AVar (let_binder k eA)) u = true.
    by case: (sweep_eqb m Forward && cv) Hneeds => -[<- _] /=;
      rewrite Nat.eqb_refl.
  case Eac: (ac) Hre => Hre; last first.
    case: Hre => Ere Ec3; subst re c3.
    have Hvr : vr = false by move: Eac; rewrite /ac Hu andb_true_r.
    exists s2; split=> //.
    split; first by move=> _; exact: vo_kept_refl.
    split.
      move=> Hl o0 Ho0 Hav0; rewrite Ho in Ho0; case: Ho0 => Eo0; subst o0.
      by have := proj1 (proj2 (Hio Hl)) Hav0; rewrite -/vr Hvr.
    split; first exact: tkeep_refl.
    split=> //; split; first exact: (r_shape _ _ _ _ _ _ _ Hr).
    split; last first.
      move=> _ _ /(tail_fold_back_ret _ _ _ _ EA) [Hv _].
      by move: Hv; rewrite -/vr Hvr.
    rewrite -(IHo L k c wP pp _ (Array z) tail eA eW eD ve o HeA HeW HeD Hs
      Hlv_e Es Ho Hve Hvr (r_args _ _ _ _ _ _ _ Hr) (r_written _ _ _ _ _ _ _ Hr)
      _ Hte Htail_ty).
    by rewrite oset_same //; exact: (r_nodup _ _ _ _ _ _ _ Hr).
  have Hcond : varied_value k eA && atom_member (AVar (let_binder k eA))
      (fst (needs cv m (S k) (cA (let_binder k eA)))) = true.
    by rewrite Hn0; exact: Eac.
  have Hvr : vr = true by move/andb_true_iff: Hcond => [].
  have Hj2 : exists j, stored o = DBound (j, j) /\ (j < c2)%nat.
    by case: Hj => [j0 [E Hj0]]; exists j0; split=> //; lia.
  have IHr' := IHr L k c2 wP pp tail eA eW eT eD (Array z) (stored o) ve
    (Array z) vo HeA HeW HeT HeD (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlv_e Hc12)
    (a_bar _ _ _ _ _ _ _ _ _ Hc) Hte Htail_ty Hj2 Hst0 Hve Hvr.
  cbv zeta in IHr'; rewrite -/vt Hre in IHr'.
  have [_ Hrv] := IHr'.
  have Hcc3 : (c <= c3)%nat by lia.
  have Hrd : forall p, In p L -> vreads k eA p -> live_value k eW p ->
      (not_in_loop pp \/ inplace wP pp <> Some (stored p)) ->
      store_get s2 (keyv (stored p)) = Some (primal (pd p)).
    move=> p Hp Hrd0 Hlv Hdj.
    have Hne : inplace wP pp <> Some (stored p).
      case: Hdj => [Hl | //]; rewrite Hex => E.
      have Epn : pn p = pn o by case: E => ->.
      case: (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Epn) => [Epo | Hnl'].
        by subst p; exact: (proj1 (Hio Hl) Hrd0).
      exact: (Hnl' (Hlv_e p Hlv)).
    have Hbp : below c (stored p).
      by rewrite /stored /=; exact: (s_num _ _ _ _ _ _ _ Hs p Hp).
    rewrite (proj1 Hag (stored p) (below_mono c c3 _ Hbp Hcc3) erefl I).
    have Hnt : ~ is_tape (stored p) by [].
    have Hne' : Some (stored o) <> Some (stored p) by rewrite -Hex.
    have Hnv : @None (dvar W) <> Some (stored p) by [].
    rewrite (F1 (stored p) Hbp erefl Hnt Hne' Hnv).
    exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp
      (tbr_let_reads m k aA eA cA p Hcond Hrd0)).
  have Hr2 : rctx L c2 wP pp O (vflows k eA) s2.
    constructor.
    - exact: (r_nodup _ _ _ _ _ _ _ Hr).
    - exact: (r_shape _ _ _ _ _ _ _ Hr).
    - move=> t0 m0 Hin; have [j0 [E Hj0]] := r_below _ _ _ _ _ _ _ Hr _ _ Hin.
      by exists j0; split=> //; lia.
    - move=> p Hp Hf Hv.
      exact: (r_useful _ _ _ _ _ _ _ Hr p Hp
        (useful_let_flows m k aA eA cA p Hcond Hf) Hv).
    - move=> p t0 Hp Hf Hin.
      exact: (r_value _ _ _ _ _ _ _ Hr p t0 Hp
        (useful_let_flows m k aA eA cA p Hcond Hf) Hin).
    - exact: (r_owner _ _ _ _ _ _ _ Hr).
    - exact: (r_args _ _ _ _ _ _ _ Hr).
    exact: (r_written _ _ _ _ _ _ _ Hr).
  have Hns : storage wP tail eP = None ->
      ~ In (stored o) (map snd O) /\ shaped (tangent ve) (barv s2 (stored o)).
    by move=> E; rewrite Es in E.
  have Hbo : below c3 (stored o).
    by case: Hj => [j0 [E Hj0]]; rewrite E /=; lia.
  have Hft : pp = PTop \/ (exists ix sx, pp = PArray ix sx) ->
      fold_tape k eA eW eD s2 (stored o).
    case=> [Hpt | [ix [sx Epp]]]; last first.
      have Hk p : In p L -> (vid (pw p) < k)%nat by case/Htt.
      have Hpt := is_tail_shape L k cP cW HcW Hk Ht.
      exact: (proj1 (Htt2 ix sx (stored o) Epp Hex) Hpt eA eW eD HeA HeW HeD).
    have Hmf : m = Forward.
      by destruct m => //; case: (Hrpl erefl Hpt).
    case Ecp: (cp) Ft1 => Ft1.
      apply: (fold_tape_same _ _ _ _ se1).
      - exact: (proj2 Hag _ Hbo erefl).
      - exact: (proj1 Hag _ Hbo erefl I).
      have Hnl0 : not_in_loop pp by rewrite Hpt.
      exact: (Ft1 erefl (conj Hmf Hnl0)).
    apply: fold_tape_records; move: Ecp; rewrite /cp Hmf /=.
    by move/orb_false_iff => [_].
  have Hinit : not_in_loop pp -> storage wP tail eP <> None ->
      forall o0, owner wP pp = Some o0 -> avaried (pa o0) = true ->
      records cv k eA = false ->
      store_get s2 (keyv (stored o)) = Some (primal (pd o0)).
    move=> Hl _ o0 Ho0 Hav0 Hrc; rewrite Ho in Ho0; case: Ho0 => Eo; subst o0.
    case Ecp: (cp) Es1 => Es1.
      (* the forward sweep ran though the fold records nothing: the value is
         needed, in adjoint-value *)
      exfalso; move: Ecp; rewrite /cp Hrc andb_false_r orb_false_r => Ecp.
      case Emc: (sweep_eqb m Forward && cv) Hneeds => -[_ El];
        rewrite -El /= in Ecp => //.
      move/andb_true_iff: Emc => [Emf Ecv]; destruct m => //.
      by rewrite (Hvi erefl Ecv o Ho) in Hav0.
    rewrite (proj1 Hag _ Hbo erefl I) (Es1 erefl).
    exact: (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho (or_introl Hl)).
  have [s3 [R3 [K3 [Kn3 [Kv3 [T3 [F3 [S3 [P3 B3]]]]]]]]] :=
    Hrv s2 O Hrd Hr2 Hns Htp Hft Hinit.
  have Hoin' : In (stored o) (map snd O).
    by apply/(in_map_iff _ _ _); eexists; split; last exact: Hown.
  have Eput : oput O (stored o) (tangent ve) = oset O (stored o) (tangent ve).
    by rewrite /oput; case: (in_dec dvar_eq_dec_c (stored o) (map snd O)).
  rewrite Eput in F3 P3.
  exists s3; split=> //.
  split.
    move=> Hm t0 Ht0 _; have [Hb0 [Hc0 Hp0]] := Hvb Hm t0 Ht0.
    have Hl : not_in_loop pp by rewrite (proj1 (Hvo Hm)).
    case: (dvar_eq_dec_c t0 (stored o)) => [Et | Hne0]; last first.
      exact: (K3 t0 (below_mono c c2 t0 Hb0 Hc12) Hc0 Hp0 Hne0).
    subst t0.
    case: (Bool.bool_dec (occurs_value (vid (pw o)) k eW) true) => [Elo | Elo].
      by case: (Hvt Hm o Hoin (Hlv_e o Elo) Ht0).
    exact: (Kn3 Hl Hsn o Ho (proj2 (proj2 (Hio Hl)) Elo)).
  split.
    move=> Hl o0 Ho0 Hav0; rewrite Ho in Ho0; case: Ho0 => Eo; subst o0.
    rewrite (Kv3 Hl Hsn o Ho Hav0).
    by rewrite (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho (or_introl Hl)).
  split; first by rewrite Hex; exact: (tkeep_mono _ _ _ _ _ T3 Hc12).
  split.
    apply: (rev_frame_x_mono c c2 _ (stored o) _ _ _ _ F3 Hc12).
      by move=> m0 Hm; left; rewrite oset_snd in Hm.
    by right.
  split=> //; split=> //.
  move=> Hnl _ /(tail_fold_back_ret _ _ _ _ EA) [_ Hf] o0 Ho0.
  rewrite Ho in Ho0; case: Ho0 => <-.
  exact: (fold_back_tail L k eP eA eD aD cD ve s2 s3 _ o HeA HeD Hve ED Hf
    (B3 Hnl Hsn o Ho)).
case: Hn => En [Ec0 Erec]; subst n c0 rec.
have [Hht [Hz Hra]] := IHa L k wP pp tail eA eW eD te ve HeA HeW HeD HL Hte Hve.
have Hnotin : forall p, In p L -> stored p <> DBound (c, c).
  move=> p Hp [E _]; have := s_num _ _ _ _ _ _ _ Hs p Hp; lia.
set x := PV (let_binder k eA) (VInfo k te None)
  (open_let te (DBound (c, c)) vr false) ve c.
have Hx : aid (pa x) = k by [].
have HxL : ~ In x L by exact: (fresh_notin L k x Haid Hx).
(* the forward sweep of the value *)
have Hfw : exists se1, run fe s = Some se1 /\
    fwd_frame c1 (Some (DBound (c, c))) None s se1 /\
    tkeep c1 (Some (DBound (c, c))) s se1 /\
    (cp = true ->
       store_get se1 (keyv (DBound (c, c))) = Some (primal ve) /\
       (m = Forward /\ not_in_loop pp ->
          fold_tape k eA eW eD se1 (DBound (c, c)))).
  case Ecp: (cp) Hfe => Hfe; last first.
    case: Hfe => Efe Ec2; subst fe c2.
    exists s; split=> //; split=> //.
    by split; first exact: tkeep_refl.
  have Hc1 : actx L k c1 s wP pp (live_value k eW) (vatoms k eA) ty.
    apply: (actx_weaken _ _ _ _ _ _ _ _ _ _ _ _ Hc Hlv_e); last by lia.
    move=> p Hp Hv; apply: (tbr_let_atoms m k aA eA cA p) Hv.
    by rewrite Hneeds.
  have Hj1 : exists j, DBound (c, c) = DBound (j, j) /\ (j < c1)%nat.
    by exists c; split=> //; lia.
  have Hst1 : match storage wP tail eP return Prop with
      | Some m0 => DBound (c, c) = m0
      | None => forall p, In p L -> stored p <> DBound (c, c) end.
    by rewrite Es.
  have Hr1 : false = true \/ (m = Forward /\ records cv k eA = true /\
      storage wP tail eP <> None /\ ~ not_in_loop pp) ->
      exists l0, store_get s (keyv (TapeOf (DBound (c, c)))) = Some (VTape l0).
    by case=> [// | [_ [_ [Hs' _]]]]; case: Hs'.
  have IH := IHf L k c1 s wP pp tail eA eW eT eD te (DBound (c, c)) ve ty m
    false HeA HeW HeT HeD Hc1 Hte Htail_ty Hj1 Hst1 Hr1 Hve.
  cbv zeta in IH; rewrite -/vt Hfe in IH.
  have [_ [se1 [R1 [F1 [T1 [S1 [Ft1 _]]]]]]] := IH.
  by exists se1; do 3!split=> //; move=> _; split.
have [se1 [R1 [F1 [T1 S1]]]] := Hfw.
(* the rest of the body, with x in scope *)
have Hlive_c : forall p, In p L -> live_anf (S k) (cW (VInfo k te None)) p ->
    live_anf k (ALet aW eW cW) p.
  rewrite /live_anf => p Hp H /=.
  rewrite (live_cont L k cP cW x (VInfo k te None) _ HcW HL Hx erefl) in H.
  by rewrite H orb_true_r.
have Hold : forall p, In p L ->
    store_get se1 (keyv (stored p)) = store_get s (keyv (stored p)).
  move=> p Hp; apply: F1 => //.
  - by rewrite /stored /=; have := s_num _ _ _ _ _ _ _ Hs p Hp; lia.
  by case=> E _; apply: (Hnotin p Hp); rewrite /stored -E.
have Hxs : static_ok (S k) x.
  by repeat split; simpl; auto; try lia; discriminate.
have Hs' : sctx (x :: L) (S k) (S c) wP pp
    (live_anf (S k) (cW (VInfo k te None))) ty.
  constructor.
  - constructor=> //; apply: Forall_impl HL => p Hp.
    exact: (static_mono k (S k) p Hp (Nat.le_succ_diag_r k)).
  - move=> p q [<- | Hp] [<- | Hq] E //.
    + have := Haid _ Hq; have [E' _] := static_in _ _ _ HL Hq.
      by rewrite /= in E; lia.
    + have := Haid _ Hp; have [E' _] := static_in _ _ _ HL Hp.
      by rewrite /= in E; lia.
    exact: (s_unique _ _ _ _ _ _ _ Hs _ _ Hp Hq E).
  - move=> p [<- | Hp] /=; first by lia.
    by have := s_num _ _ _ _ _ _ _ Hs _ Hp; lia.
  - move=> a0 E; have [y [-> [Hy Hv]]] := s_written _ _ _ _ _ _ _ Hs _ E.
    by exists y; split=> //; split; [right | ].
  - have Hp := s_place _ _ _ _ _ _ _ Hs; destruct pp => //=.
    by case: Hp => [A [B C]]; split; [right | split; [right |]].
  - move=> o p Ho [<- | Hp] Ep.
      have := s_num _ _ _ _ _ _ _ Hs _ (owner_in_s _ _ _ _ _ _ _ _ Hs Ho).
      by rewrite /= in Ep; lia.
    case: (s_owner _ _ _ _ _ _ _ Hs o p Ho Hp Ep) => [H | H]; first by left.
    by right=> Hl; apply/H/Hlive_c.
  - move=> p o [<- | Hp] Lp Ha Hg Ho.
      have [_ [o' [Ho' Es']]] := inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW
        Hte Htail_ty (or_intror Ha).
      by rewrite Es in Es'.
    exact: (s_arrays _ _ _ _ _ _ _ Hs p o Hp (Hlive_c _ Hp Lp) Ha Hg Ho).
  - exact: (s_ty _ _ _ _ _ _ _ Hs).
  move=> y Hpp Hw' Ha.
  have [T1' T2'] := s_top _ _ _ _ _ _ _ Hs y Hpp Hw' Ha.
  have [y' [[E] [Hy _]]] := s_written _ _ _ _ _ _ _ Hs _ Hw'; subst y'.
  by split=> // Ly; apply/T2'/Hlive_c.
have Hc' : actx (x :: L) (S k) (S c) se1 wP pp
    (live_anf (S k) (cW (VInfo k te None)))
    (tbr cv m (S k) (cA (let_binder k eA))) ty.
  constructor=> //.
  - by move=> p [<- | Hp] //; exact: (a_bar _ _ _ _ _ _ _ _ _ Hc p Hp).
  - move=> p [<- | Hp] Ht.
      apply: (fun H => proj1 (S1 H)); rewrite /tbr Hneeds /= in Ht.
      by rewrite /cp Ht.
    rewrite (Hold p Hp); apply: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp).
    exact: (tbr_let_cont m k aA eA cA p (Haid p Hp) Ht).
  - move=> p [<- | Hp] Hr //.
    have [lt Hlt] := a_tape _ _ _ _ _ _ _ _ _ Hc p Hp Hr.
    exact: (proj1 T1 _ _ Hlt).
  - move=> o Ho Hor; have Hoin := owner_in_s _ _ _ _ _ _ _ _ Hs Ho.
    rewrite (Hold o Hoin); apply: (a_owner _ _ _ _ _ _ _ _ _ Hc o Ho).
    case: Hor => [Hl | Ht]; [by left | right].
    exact: (tbr_let_cont m k aA eA cA o (Haid o Hoin) Ht).
  exact: (a_tid _ _ _ _ _ _ _ _ _ Hc).
have Hvt' : m = Forward -> forall p, In p (x :: L) ->
    live_anf (S k) (cW (VInfo k te None)) p -> vo_target vo <> Some (stored p).
  move=> Hm p [<- | Hp] Hl Ht; last exact: (Hvt Hm p Hp (Hlive_c p Hp Hl) Ht).
  exfalso; have [_ [_ [Hy _]]] := Hvo Hm.
  destruct vo as [[t0 | y] |]; rewrite /= in Ht; try discriminate.
  have {}Hy := Hy y erefl.
  destruct wP as [yP |]; rewrite /= in Hy; last by [].
  case: Hy => Ey; subst y.
  have [q [Eq [Hq _]]] := s_written _ _ _ _ _ _ _ Hs _ erefl; subst yP.
  have [_ [_ [Hsq _]]] := static_in _ _ _ HL Hq.
  rewrite /vo_target /stored_of /= Hsq in Ht.
  case: (targ (pt q)) Ht => [[? []] |] //=.
  by case: (tty (pt q)) => [| | | ?] // [E _]; apply: (Hnotin q Hq);
    rewrite /stored E.
have Hvb' : m = Forward -> forall t, vo_target vo = Some t ->
    below (S c) t /\ consistent t /\ is_primal t.
  move=> Hm t0 Ht0; have [H1 H2] := Hvb Hm t0 Ht0.
  by split=> //; exact: (below_mono c (S c) t0 H1 (Nat.le_succ_diag_r c)).
have IH := IHb x (x :: L) (S k) (S c) se1 wP pp m (cA (pa x)) (cW (pw x))
  (cT (pt x)) (cD (pd x)) ty v se vo (HcA x _) (HcW x _) (HcT x _) (HcD x _)
  Hc' Hty Htc Hev Hvo Hvt' Hvb' Hrpl Hvi.
rewrite /x in IH; cbn [pt pa pd pw] in IH; rewrite -/rest Hb in IH.
have [_ [Hhtv [s1 [Rb [Fb [Tb [Vb Hrev]]]]]]] := IH.
split; first by lia.
split=> //.
exists s1; split; first by rewrite run_app R1.
split.
  move=> v0 Hb0 Hc0 Ht0 He0 Hv0.
  have Hc1' : (c <= c1)%nat by lia.
  rewrite (Fb v0 (below_mono c (S c) v0 Hb0 (Nat.le_succ_diag_r c)) Hc0 Ht0
    He0 Hv0).
  apply: F1 => //; first exact: (below_mono c c1 v0 Hb0 Hc1').
  by case=> E; subst v0; rewrite /= in Hb0; lia.
split.
  have Hcc : ~ below c (DBound (c, c)) by rewrite /=; lia.
  apply: (tkeep_trans _ _ _ _ _ (tkeep_fresh c c1 _ (inplace wP pp) _ _ T1 Hcc
    (Nat.le_trans _ _ _ (Nat.le_succ_diag_r c) Hc01))).
  exact: (tkeep_mono _ _ _ _ _ Tb (Nat.le_succ_diag_r c)).
split=> //.
move=> s2 O Hag Hr Hseed Htp Htt2.
have Htt2' : forall ix sx n0, pp = PArray ix sx -> inplace wP pp = Some n0 ->
    tail_tape (S k) (x :: L) (cP x) s2 n0.
  by move=> ix sx n0 E1 E2; exact: (proj2 (Htt2 ix sx n0 E1 E2) x).
have Hok := rctx_owners_ok _ _ _ _ _ _ _ Hr.
have Hn_notin : ~ In (DBound (c, c)) (map snd O).
  move/(in_map_iff _ _ _) => [[t0 m0] [/= E Hin]]; subst m0.
  have [j0 [[E Ej] Hj]] := r_below _ _ _ _ _ _ _ Hr _ _ Hin; lia.
have Hsel : forall y0, In y0 (dvars se) ->
    consistent y0 /\ y0 <> BarOf (DBound (c, c)).
  move=> y0 Hy; have [Hb0 Hc0] := proj1 Hseed y0 Hy; split=> // E.
  by subst y0; rewrite /= in Hb0; lia.
have Hux : useful cv m (S k) (cA (let_binder k eA)) x -> vr = true ->
    ac = true.
  by rewrite /useful Hneeds /= => H1 H2; rewrite /ac H2 H1.
(* the rctx of the rest of the body, for the owners O and possibly x *)
have Hr' : forall O' sa, (O' = O /\ ac = false /\ sa = s2) \/
    (O' = (tangent ve, DBound (c, c)) :: O /\ ac = true /\
     sa = store_set s2 (keyv (BarOf (DBound (c, c)))) (VReal 0) /\
     shaped (tangent ve) (Some (VReal 0))) ->
    rctx (x :: L) (S c) wP pp O' (useful cv m (S k) (cA (let_binder k eA)))
      sa.
  move=> O' sa HO.
  have Hshb : forall t0 m0, In (t0, m0) O -> shaped t0 (barv sa m0).
    move=> t0 m0 Hin.
    case: HO => [[E1 [_ E2]] | [E1 [_ [E2 _]]]]; subst O' sa.
      exact: (r_shape _ _ _ _ _ _ _ Hr _ _ Hin).
    have Hne : DBound (c, c) <> m0.
      move=> E; apply: Hn_notin; rewrite E.
      by apply/(in_map_iff _ _ _); exists (t0, m0).
    rewrite (barv_set_other s2 (DBound (c, c)) m0 (VReal 0) erefl (Hok _ _ Hin)
      Hne).
    exact: (r_shape _ _ _ _ _ _ _ Hr _ _ Hin).
  have HinO : forall t0 m0, In (t0, m0) O -> In (t0, m0) O'.
    by move=> t0 m0 Hin; case: HO => [[-> _] | [-> _]] //; right.
  have HO' : forall t0 m0, In (t0, m0) O' -> In (t0, m0) O \/
      (t0 = tangent ve /\ m0 = DBound (c, c) /\ ac = true).
    move=> t0 m0 Hin; case: HO Hin => [[-> _] | [-> [Ea _]]]; first by left.
    by case=> [[<- <-] | Hin]; [right | left].
  constructor.
  - case: HO => [[-> _] | [-> _]]; first exact: (r_nodup _ _ _ _ _ _ _ Hr).
    by constructor=> //; exact: (r_nodup _ _ _ _ _ _ _ Hr).
  - move=> t0 m0 Hin; case: (HO' t0 m0 Hin) => [Hin0 | [-> [-> Ea]]].
      exact: (Hshb _ _ Hin0).
    case: HO => [[_ [E _]] | [_ [_ [-> Hsh0]]]]; first by rewrite E in Ea.
    by rewrite barv_set_same.
  - move=> t0 m0 Hin; case: (HO' t0 m0 Hin) => [Hin0 | [_ [-> _]]].
      have [j0 [E Hj]] := r_below _ _ _ _ _ _ _ Hr _ _ Hin0.
      by exists j0; split=> //; lia.
    by exists c; split=> //; lia.
  - move=> p [<- | Hp] Hu Hv.
      have Ea : ac = true by exact: (Hux Hu Hv).
      by case: HO => [[_ [E _]] | [-> _]]; [rewrite E in Ea | left].
    apply/HinO/(r_useful _ _ _ _ _ _ _ Hr p Hp) => //.
    exact: (useful_let_cont m k aA eA cA p (Haid p Hp) Hu).
  - move=> p t0 [<- | Hp] Hu Hin.
      case: (HO' _ _ Hin) => [Hin0 | [-> _]] //.
      exfalso; apply/Hn_notin/(in_map_iff _ _ _).
      by exists (t0, DBound (c, c)).
    case: (HO' _ _ Hin) => [Hin0 | [_ [E _]]]; last by case: (Hnotin p Hp E).
    exact: (r_value _ _ _ _ _ _ _ Hr p t0 Hp
      (useful_let_cont m k aA eA cA p (Haid p Hp) Hu) Hin0).
  - by move=> o Ho; apply/HinO/(r_owner _ _ _ _ _ _ _ Hr o Ho).
  - move=> p ny r [<- | Hp] Hv //.
    exact: (r_args _ _ _ _ _ _ _ Hr p ny r Hp Hv).
  exact: (r_written _ _ _ _ _ _ _ Hr).
(* the value is not the array the body returns *)
have Hnret : forall y, cA (let_binder k eA) = ARet (AVar y) -> aid y = k ->
    is_array ty -> False.
  move=> y Ey Eky Harr.
  have HA1 : anf_eq ((x, let_binder k eA) :: gA L) (cP x)
      (cA (let_binder k eA)) by exact: HcA.
  rewrite Ey in HA1.
  case EcP: (cP x) HA1 => [? ? ? | [p' | |]] //= HA1.
  case: HA1 => [[Ex _] | /in_gA [Hp' Epa]]; last first.
    by move: (Haid p' Hp'); rewrite -Epa Eky; lia.
  subst p'.
  have HW1 : anf_eq ((x, pw x) :: gW L) (cP x) (cW (pw x)) by exact: HcW.
  rewrite EcP in HW1.
  case EcW: (cW (pw x)) HW1 => [? ? ? | [w | |]] //= HW1.
  move: EcW; case: HW1 => [[<-] | /in_gW [HxL' _]] EcW; last exact: HxL HxL'.
  rewrite /= in EcW; rewrite EcW /= in Htc; case: Htc => Ety.
  have Harr' : is_array te by rewrite Ety.
  have [_ [o' [_ Es']]] := inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte
    Htail_ty (or_intror Harr').
  by rewrite Es in Es'.
case Eac: (ac) Hre => Hre; last first.
  (* x is not active *)
  case: Hre => Ere Ec3; subst re c3.
  have Hc13 : (c1 <= c2)%nat by lia.
  have Hseed' : seed_ok (S c) ty se s2.
    split; last exact: (proj2 Hseed).
    move=> y0 Hy; have [H1 H2] := proj1 Hseed y0 Hy.
    by split=> //; exact: (below_mono c (S c) y0 H1 (Nat.le_succ_diag_r c)).
  have Htp2 : tapes_ok (x :: L) s2.
    by move=> p [<- | Hp] Hrp //; exact: (Htp p Hp Hrp).
  have [sb [Rrb [Krb [Ksx [Trb [Frb [Srb [Prb Bb]]]]]]]] :=
    Hrev s2 O (agree_prim_mono _ _ _ _ _ Hag Hc13)
      (Hr' O s2 (or_introl (conj erefl (conj Eac erefl)))) Hseed' Htp2 Htt2'.
  exists sb; split; first by rewrite /= app_nil_r.
  split=> //.
  split.
    move=> Hl o Ho Hav; have He : inplace wP pp = Some (stored o).
      by rewrite /inplace Ho.
    have [Hb0 [Hc0 Hp0]] := ex_below _ _ _ _ _ _ _ _ Hs He.
    have Hcc1 : (c <= c1)%nat by lia.
    rewrite (Ksx Hl o Ho Hav).
    apply: (F1 (stored o) (below_mono c c1 _ Hb0 Hcc1) Hc0) => //.
    by case=> E _; rewrite /stored /= -E in Hb0; lia.
  split; first exact: (tkeep_mono _ _ _ _ _ Trb (Nat.le_succ_diag_r c)).
  split=> //.
  apply: (rev_frame_mono c (S c) _ _ _ _ _ Frb (Nat.le_succ_diag_r c)).
  by move=> m0 Hm; left.
  split=> //; split=> //.
  move=> Hnl Harr /tail_fold_back_let [Ht | [y [Ey Eky]]]; last first.
    by case: (Hnret y Ey Eky Harr).
  move=> o Ho; have [Hso Hto] := Bb Hnl Harr Ht o Ho.
  split=> // l0 E; apply: Hto; move: E.
  rewrite (body_pushes_let aD eD cD ve (pd o) Hve) // => r Er.
  have [r' Er'] := cont_ret_DA L x cP cA cD (HcA x _) (HcD x _)
    (ex_intro _ r Er).
  by move: Ht; rewrite /x /= in Er'; rewrite Er'.
(* x is active: its adjoint is declared, then transposed *)
have Hcond : varied_value k eA && atom_member (AVar (let_binder k eA))
    (fst (needs cv m (S k) (cA (let_binder k eA)))) = true.
  by rewrite Hneeds; exact: Eac.
have Hvr : vr = true by move/andb_true_iff: Hcond => [].
have Ete : te = Real.
  destruct te as [| | | z]; try by case: (Hra Hvr).
  have [_ [o' [_ Es']]] := inplace_value_s _ _ _ _ _ _ _ _ _ _ _ Hs HeW Hte
    Htail_ty (or_intror I).
  by rewrite Es in Es'.
subst te; destruct ve as [d | | | |]; try by [].
set s2a := store_set s2 (keyv (BarOf (DBound (c, c)))) (VReal 0).
have Hd : run (bar_declaration W Real (DBound (c, c))) s2 = Some s2a.
  by apply: run_define; rewrite xev_DReal lit_0.
have Hr2 := Hr' ((tangent (VReal d), DBound (c, c)) :: O) s2a
  (or_intror (conj erefl (conj Eac (conj erefl I)))).
have Hc13 : (c1 <= c3)%nat by lia.
have Hag2 : agree_prim c1 (inplace wP pp) s1 s2a.
  exact: (agree_prim_set_bar c1 (inplace wP pp) s1 s2 (DBound (c, c)) (VReal 0)
    (agree_prim_mono _ _ _ _ _ Hag Hc13) (erefl c)).
have Hseed2 : seed_ok (S c) ty se s2a.
  split.
    move=> y0 Hy; have [H1 H2] := proj1 Hseed y0 Hy.
    by split=> //; exact: (below_mono c (S c) y0 H1 (Nat.le_succ_diag_r c)).
  move=> Ety; have [b0 Hb0] := proj2 Hseed Ety; exists b0.
  rewrite /s2a xev_set_other // => y0 Hy K.
  have [Hcy Hny] := Hsel y0 Hy.
  exact: Hny (keyv_inj y0 (BarOf (DBound (c, c))) Hcy erefl K).
have Htp2 : tapes_ok (x :: L) s2a.
  move=> q [Eq | Hq] Hrq; first by rewrite -Eq in Hrq.
  have [lt Hlt] := Htp q Hq Hrq; exists lt.
  by rewrite /s2a store_get_set_other.
have Htt2a : forall ix sx n0, pp = PArray ix sx -> inplace wP pp = Some n0 ->
    tail_tape (S k) (x :: L) (cP x) s2a n0.
  move=> ix sx n0 E1 E2.
  have Hn0 : ~ is_bar n0.
    by move: E2; rewrite /inplace; case: (owner wP pp) => // o [<-].
  apply: (tail_tape_same _ _ _ s2 _ _ _ _ (Htt2' _ _ _ E1 E2)).
    by rewrite /s2a store_get_set_other //; exact: keyv_bar_other.
  by rewrite /s2a store_get_set_other //; exact: keyv_bar_other.
have [sb [Rrb [Krb [Ksx [Trb [Frb [Srb [Prb Bb]]]]]]]] :=
  Hrev s2a _ Hag2 Hr2 Hseed2 Htp2 Htt2a.
have Hj2 : exists j, DBound (c, c) = DBound (j, j) /\ (j < c2)%nat.
  by exists c; split=> //; lia.
have Hst2 : match storage wP tail eP return Prop with
    | Some m0 => DBound (c, c) = m0
    | None => forall p, In p L -> stored p <> DBound (c, c) end by rewrite Es.
have Hcc2 : (c <= c2)%nat by lia.
have IHr' := IHr L k c2 wP pp tail eA eW eT eD Real (DBound (c, c)) (VReal d)
  ty vo HeA HeW HeT HeD (sctx_weaken _ _ _ _ _ _ _ _ _ Hs Hlv_e Hcc2)
  (a_bar _ _ _ _ _ _ _ _ _ Hc) Hte Htail_ty Hj2 Hst2 Hve Hvr.
cbv zeta in IHr'; rewrite -/vt Hre in IHr'.
have [_ Hrv] := IHr'.
have Hrd : forall p, In p L -> vreads k eA p -> live_value k eW p ->
    (not_in_loop pp \/ inplace wP pp <> Some (stored p)) ->
    store_get sb (keyv (stored p)) = Some (primal (pd p)).
  move=> p Hp Hrd0 Hlv Hdj.
  have Hbp : below c (stored p).
    by rewrite /stored /=; exact: (s_num _ _ _ _ _ _ _ Hs p Hp).
  have Hsc : below c (stored p) -> below (S c) (stored p).
    by move=> H; exact: (below_mono c (S c) _ H (Nat.le_succ_diag_r c)).
  have Hnt : ~ is_tape (stored p) by [].
  case: (option_dec_ex (inplace wP pp) (stored p)) => [Hex | Hne].
    case: Hdj => [Hl | //].
    move: Hex; rewrite /inplace; case Ho: (owner wP pp) => [o |] // [Hex _].
    have Esp : stored p = stored o by rewrite /stored Hex.
    have [Epo Hav] := same_ex_read _ _ _ _ _ _ _ p o Hs Hl Ho Hp Esp
      (Hlv_e p Hlv); subst o.
    rewrite (Ksx Hl p Ho Hav) (Hold p Hp).
    exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp
      (tbr_let_reads m k aA eA cA p Hcond Hrd0)).
  have Hnb : forall m0, stored p = BarOf m0 -> ~ In m0 (map snd
      ((tangent (VReal d), DBound (c, c)) :: O)) by [].
  rewrite (Frb (stored p) (Hsc Hbp) erefl Hnt Hne Hnb).
  rewrite /s2a store_get_set_other //.
  have Hcc3 : (c <= c3)%nat by lia.
  rewrite (proj1 Hag (stored p) (below_mono c c3 _ Hbp Hcc3) erefl I).
  have Hvt0 : vo_target (if sweep_eqb m Forward then vo else None) <>
      Some (stored p).
    by destruct m => //=; exact: (Hvt erefl p Hp (Hlv_e p Hlv)).
  rewrite (Fb (stored p) (Hsc Hbp) erefl Hnt Hne Hvt0) (Hold p Hp).
  exact: (a_store _ _ _ _ _ _ _ _ _ Hc p Hp
    (tbr_let_reads m k aA eA cA p Hcond Hrd0)).
have Hr3 : rctx L c2 wP pp O (vflows k eA) sb.
  constructor.
  - exact: (r_nodup _ _ _ _ _ _ _ Hr).
  - by move=> t0 m0 Hin; apply: Srb; right.
  - move=> t0 m0 Hin; have [j0 [E Hj]] := r_below _ _ _ _ _ _ _ Hr _ _ Hin.
    by exists j0; split=> //; lia.
  - move=> p Hp Hf Hv.
    exact: (r_useful _ _ _ _ _ _ _ Hr p Hp
      (useful_let_flows m k aA eA cA p Hcond Hf) Hv).
  - move=> p t0 Hp Hf Hin.
    exact: (r_value _ _ _ _ _ _ _ Hr p t0 Hp
      (useful_let_flows m k aA eA cA p Hcond Hf) Hin).
  - exact: (r_owner _ _ _ _ _ _ _ Hr).
  - exact: (r_args _ _ _ _ _ _ _ Hr).
  exact: (r_written _ _ _ _ _ _ _ Hr).
have Htpb : tapes_ok L sb.
  move=> p Hp Hrp; have [lt Hlt] := Htp2 p (or_intror Hp) Hrp.
  exact: (proj1 Trb _ _ Hlt).
have Hft : pp = PTop \/ (exists ix sx, pp = PArray ix sx) ->
    fold_tape k eA eW eD sb (DBound (c, c)).
  case=> [Hpt | [ix [sx Epp]]]; last first.
    apply: (fold_tape_in_loop L k wP tail ix sx eP eA eW eD Real sb _ HeW
      Es).
    by rewrite -Epp.
  destruct m; last by case: (Hrpl erefl Hpt).
  case Erc: (records cv k eA);
    last exact: (fold_tape_records k eA eW eD sb _ Erc).
  have Ecp : cp = true by rewrite /cp /= Erc orb_true_r.
  have Hnl0 : not_in_loop pp by rewrite Hpt.
  have Ft := proj2 (S1 Ecp) (conj erefl Hnl0).
  apply: (fold_tape_scalar L k wP tail eP eA eW eD se1 sb _ HeW Es _ Ft).
  set nn := DBound (c, c).
  have Hex : inplace wP pp <> Some nn.
    by move=> E; have [Hbe _] := ex_below _ _ _ _ _ _ _ _ Hs E;
      rewrite /nn /= in Hbe; lia.
  have Hb1 : below (S c) nn by rewrite /nn /=; lia.
  have Hb3 : below c3 nn by rewrite /nn /=; lia.
  rewrite (proj2 Trb nn Hb1 erefl Hex) /s2a store_get_set_other //.
  rewrite (proj2 Hag nn Hb3 erefl).
  exact: (proj2 Tb nn Hb1 erefl Hex).
have Hns : storage wP tail eP = None ->
    ~ In (DBound (c, c)) (map snd O) /\
    shaped (tangent (VReal d)) (barv sb (DBound (c, c))).
  by move=> _; split=> //; apply: Srb; left.
have Hin0 : not_in_loop pp -> storage wP tail eP <> None ->
    forall o0, owner wP pp = Some o0 -> avaried (pa o0) = true ->
    records cv k eA = false ->
    store_get sb (keyv (DBound (c, c))) = Some (primal (pd o0)).
  by move=> _ Hs0; case: (Hs0 Es).
have [s3 [R3 [K3 [Kn3 [_ [T3 [F3 [S3 [P3 _]]]]]]]]] :=
  Hrv sb O Hrd Hr3 Hns Htpb Hft Hin0.
exists s3; split; first by rewrite run_app Hd run_app Rrb.
split.
  move=> Hm; apply: (vo_kept_trans _ _ s2a); first exact: vo_kept_set_bar.
  apply: (vo_kept_trans _ _ sb); first exact: (Krb Hm).
  move=> t0 Ht0 _; have [Hb0 [Hc0 Hp0]] := Hvb Hm t0 Ht0.
  apply: K3 => //; first exact: (below_mono c c2 t0 Hb0 Hcc2).
  by move=> E; subst t0; rewrite /= in Hb0; lia.
split.
  move=> Hl o Ho Hav; have He : inplace wP pp = Some (stored o).
    by rewrite /inplace Ho.
  have [Hb0 [Hc0 Hp0]] := ex_below _ _ _ _ _ _ _ _ Hs He.
  have Hne : stored o <> DBound (c, c).
    by move=> E; rewrite E /= in Hb0; lia.
  rewrite (K3 _ (below_mono c c2 _ Hb0 Hcc2) Hc0 Hp0 Hne) (Ksx Hl o Ho Hav).
  have Hcc1 : (c <= c1)%nat by lia.
  apply: (F1 _ (below_mono c c1 _ Hb0 Hcc1) Hc0) => //.
  by case=> E _; rewrite /stored /= -E in Hb0; lia.
split.
  apply: (tkeep_trans _ _ _ s2a); first by apply: tkeep_set.
  have Hnc : ~ below c (DBound (c, c)) by rewrite /=; lia.
  exact: (tkeep_trans _ _ _ _ _ (tkeep_mono _ _ _ _ _ Trb
    (Nat.le_succ_diag_r c)) (tkeep_fresh c c2 _ (inplace wP pp) _ _ T3 Hnc
    Hcc2)).
have HO'b : forall m0,
    In m0 (map snd ((tangent (VReal d), DBound (c, c)) :: O)) ->
    In m0 (map snd O) \/ ~ below c (BarOf m0).
  by move=> m0 [<- | Hm]; [right; rewrite /=; lia | left].
split.
  apply: (rev_frame_trans _ _ _ _ s2a).
    move=> v0 Hb0 Hc0 _ _ _; rewrite /s2a; apply: store_get_set_other => K.
    have E := keyv_inj (BarOf (DBound (c, c))) v0 erefl Hc0 K; subst v0.
    by rewrite /= in Hb0; lia.
  apply: (rev_frame_trans _ _ _ _ sb).
    exact: (rev_frame_mono c (S c) _ _ _ _ _ Frb (Nat.le_succ_diag_r c) HO'b).
  rewrite (oput_notin O _ _ Hn_notin) in F3.
  have Hnb : ~ below c (DBound (c, c)) by rewrite /=; lia.
  exact: (rev_frame_x_mono c c2 _ _ _ _ _ _ F3 Hcc2 HO'b (or_introl Hnb)).
split=> //; split.
  rewrite P3 (oput_notin O _ _ Hn_notin) Prb.
  exact: (result_pairing_fresh O ty _ v se s2 (DBound (c, c)) _ Hok erefl
    Hn_notin Hsel).
move=> Hnl Harr /tail_fold_back_let [Ht | [y [Ey Eky]]]; last first.
  by case: (Hnret y Ey Eky Harr).
move=> o Ho.
have He : inplace wP pp = Some (stored o) by rewrite /inplace Ho.
have [Hb0 [Hc0 Hp0]] := ex_below _ _ _ _ _ _ _ _ Hs He.
have Hne : stored o <> DBound (c, c) by move=> E; rewrite E /= in Hb0; lia.
have [Hso Hto] := Bb Hnl Harr Ht o Ho.
split; first by rewrite (K3 _ (below_mono c c2 _ Hb0 Hcc2) Hc0 Hp0 Hne).
move=> l0 E.
have Hneq : Some (DBound (c, c)) <> Some (stored o).
  by move=> /Some_inj E'; apply: Hne.
rewrite (proj2 T3 _ (below_mono c c2 _ Hb0 Hcc2) Hc0 Hneq); apply: Hto.
rewrite /s2a store_get_set_other; first exact: keyv_bar_other.
move: E; rewrite (body_pushes_let aD eD cD (VReal d) (pd o) Hve) // => r Er.
have [r' Er'] := cont_ret_DA L x cP cA cD (HcA x _) (HcD x _)
  (ex_intro _ r Er).
by move: Ht; rewrite /x /= in Er'; rewrite Er'.
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
move=> Hs L eT tr wt vo te n c HT.
destruct eP, eT; rewrite /= in Hs HT; try contradiction;
  cbn [rebuild_value rev_value open_pairs fst].
- case: (partial1 _ _) => [p |]; [exact: contribution_bars | constructor].
- case: (partial2 _ _ _) => [[pa pb] |]; last by constructor.
  by apply/Forall_app; split; apply: contribution_bars.
- case Eb: (@bar W _) => [bx |]; last by constructor.
  by have [y [-> Hy]] := bar_some _ _ Eb; repeat constructor.
case Eb: (@bar W _) => [bx |]; last by repeat constructor.
by have [y [-> Hy]] := bar_some _ _ Eb; repeat constructor.
Qed.

(* A value whose reverse code writes only adjoints, proved as the operations
   are (asim_rev0), satisfies asim_rev. *)
Lemma asim_rev_bars (eP : value pv bare) :
  asim_rev0 eP ->
  (forall L eT tr wt vo te n c, value_eq (gT L) eP eT ->
     Forall bar_stmt (fst (open_pairs (rev_value W wt vo (rebuild_value _ eT tr) te n) c))) ->
  (forall L k wP pp tail eW te, value_eq (gW L) eP eW ->
     typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
     storage wP tail eP <> None -> not_in_loop pp -> False) ->
  (forall a lo hi init b, eP <> AFold a lo hi init b) ->
  asim_rev eP.
Proof.
move=> H0 Hb Hnt Hnf L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs
  Hbar Htc Htail Hn Hst Hve Hvr.
have Hfb : forall s2 s3 o, fold_back k eA eD s2 s3 n o.
  move=> s2 s3 o; move: HA Hnf; rewrite /fold_back.
  case E: eA => // [? ? ? ? ?].
  by case EP: eP => //= [? ? ? ? ?] _ Hnf; case: (Hnf _ _ _ _ _ erefl).
have {}H0 := H0 L k c wP pp tail eA eW eT eD te n ve ty vo HA HW HT HD Hs
  Hbar Htc Htail Hn Hst Hve Hvr.
have {}Hb := Hb L eT (annotate_value_t cv k eA) (option_map (amap pt) wP)
  vo te n c HT.
case E: (open_pairs (rev_value W (option_map (amap pt) wP) vo
  (rebuild_value (tvar W) eT (annotate_value_t cv k eA)) te n) c) H0 Hb
  => [re c'] H0 /= Hb.
case: H0 => Hc Hrv; split=> // s2 O Hrd Hr Hns _ _.
have Hrd' p Hp Hrd0 Hlv Hsc :=
  Hrd p Hp Hrd0 Hlv
    (or_intror (scalar_not_inplace _ _ _ _ _ _ _ _ Hs Hp Hlv Hsc)).
have [s3 [R3 [F3 [S3 P3]]]] := Hrv s2 O Hrd' Hr Hns.
exists s3; split=> //.
split.
  move=> v Hb0 Hc0 Hp0 _; apply: (run_bars re s2 s3 Hb R3).
  by case: v Hb0 Hc0 Hp0 => //= *; case.
split.
  move=> _ _ o _ _; case: Hn => [jn [En _]]; subst n.
  exact: (run_bars re s2 s3 Hb R3).
split.
  by move=> Hl Hsn o _ _; case: (Hnt L k wP pp tail eW te HW Htc Hsn Hl).
split; first exact: (tkeep_bars _ _ _ _ _ Hb R3).
split; first exact: (rev_frame_x_of _ _ _ _ _ _ F3).
by split=> //; split=> // _ _ o _; exact: Hfb.
Qed.

(* A straight value is updated in place only in the body of an in-place loop. *)
Lemma straight_no_top (eP : value pv bare) : straight_value eP ->
  forall L k wP pp tail eW te, value_eq (gW L) eP eW ->
    typecheck_value (option_map (amap pw) wP) (wplace pp) tail k eW = (te, Ok) ->
    storage wP tail eP <> None -> not_in_loop pp -> False.
Proof.
move=> Hs L k wP pp tail eW te HW Htc Hst Hl.
destruct eP as [| | | aP iP vP | | |]; rewrite /= in Hs; try contradiction;
  rewrite /= in Hst; try by case: Hst.
destruct eW; rewrite /= in HW; try contradiction; rewrite /= in Htc.
destruct pp; rewrite /= in Htc Hl; [| | | by case: Hl];
  repeat match type of Htc with context [match ?e with _ => _ end] =>
    destruct e end; discriminate.
Qed.

Lemma inplace_straight (eP : value pv bare) : straight_value eP -> inplace_only eP.
Proof.
move=> Hs L k wP pp tail eA eW te _ HW _ _ Htc Hst Hl.
by case: (straight_no_top eP Hs L k wP pp tail eW te HW Htc Hst Hl).
Qed.


Theorem asim_straight : forall bP : anf pv bare, straight bP -> asim_body bP.
Proof.
suff H : (forall b : anf pv bare, straight b -> asim_body b) /\
    (forall e : value pv bare, straight_value e ->
       asim_fwd e /\ asim_rev e /\ act_value e /\ act_owner e).
  exact: (proj1 H).
apply: (anf_value_ind pv bare (fun b => straight b -> asim_body b)
  (fun e => straight_value e ->
     asim_fwd e /\ asim_rev e /\ act_value e /\ act_owner e)).
- move=> a e IHe b IHb [He Hb]; have [Hf [Hr [Ha Ho]]] := IHe He.
  apply: asim_let => //; first exact: inplace_straight.
  by move=> x; apply: IHb (Hb x).
- by move=> x _; apply: asim_ret.
- move=> f x Hs; split; first exact: afwd_op1.
  split; last by split; [apply: act_op1 | apply: owner_op1].
  apply: asim_rev_bars; first exact: arev_op1.
    exact: (straight_rev_bars _ Hs).
  exact: (straight_no_top _ Hs).
  by [].
- move=> f x y Hs; split; first exact: afwd_op2.
  split; last by split; [apply: act_op2 | apply: owner_op2].
  apply: asim_rev_bars; first exact: arev_op2.
    exact: (straight_rev_bars _ Hs).
  exact: (straight_no_top _ Hs).
  by [].
- move=> x i Hs; split; first exact: afwd_get.
  split; last by split; [apply: act_get | apply: owner_get].
  apply: asim_rev_bars; first exact: arev_get.
    exact: (straight_rev_bars _ Hs).
  exact: (straight_no_top _ Hs).
  by [].
- move=> x i y Hs; split; first exact: afwd_set.
  split; last by split; [apply: act_set | apply: owner_set].
  apply: asim_rev_bars; first exact: arev_set.
    exact: (straight_rev_bars _ Hs).
  exact: (straight_no_top _ Hs).
  by [].
- by move=> c t _ e _ [].
- by move=> lo hi b _ [].
by move=> a lo hi init b _ [].
Qed.

End Sim.
