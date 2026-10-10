(* SimplifyCorrect.v — the correctness of simplify: from L2 to L2′, it
   preserves what a program computes over the reals.

   `simplify` (Simplify.v) rewrites each expression with real identities
   (x * 0 = 0, 1 * x = x, x + 0 = x, - - x = x, x^1 = x, x^0 = 1, …), drops the
   accumulations of zero, fuses a mutable that starts at zero with its first
   accumulation, propagates the literal constants and removes the dead ones.
   Each rewrite is a real identity, or reorders statements that do not touch
   the same variables, or removes a definition no later statement reads; this
   holds on the programs whose variables follow the discipline `good` of
   Scoping.v (a variable read is in scope, a variable assigned is writable, a
   variable defined is new), and that use no tape: a push or a pop on a
   variable that simplify turns into a constant would escape the discipline
   (`writes` does not see them). The tangent programs use no tape.

   The theorem is a refinement: when the program computes, its simplification
   computes the same parameters and the same returned value. The proof is a
   simulation: two stores are related when they agree on the variables in
   scope (and on the returned value); every rewrite maps related stores to
   related stores, and the variables out of scope are never read again.

   The input of simplify is instantiated at pairs, (k, k) for the k-th
   variable (`open_pairs`, Scoping.v): simplify compares the first numbers, the
   evaluator the second (`out_dvar`), and they agree on such variables. *)

From Stdlib Require Import String ZArith List Bool Reals QArith Qreals Lra.
From ElpiDiff Require Import Syntax Derivative Domain Eval Exec Operations Simplify Scoping.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope R_scope.
Open Scope list_scope.

Local Notation W := Scoping.W.
Local Notation out := (out_dvar nat).
Local Notation oute := (out_dexpr nat).
Local Notation outs := (out_dstmt nat).
Local Notation store := (store R).

(* The execution of a block of the input, through out_dstmt. *)
Definition ex (ss : list (dstmt W)) (s : store) : option store :=
  exec_stmts reals (map outs ss) s.

Lemma ex_cons st ss s :
  ex (st :: ss) s = match exec reals (outs st) s with Some s1 => ex ss s1 | None => None end.
Proof. by []. Qed.

Lemma ex_app a b s :
  ex (a ++ b) s = match ex a s with Some s1 => ex b s1 | None => None end.
Proof.
elim: a s => [| st a IH] s //=.
by rewrite [ex (st :: _) _]ex_cons ex_cons; case: (exec reals (outs st) s).
Qed.

(* ---------------------------------------------------------------------------
   The store. *)

(* The equality of the variables of the evaluator decides equality. *)
Lemma dvar_eqb_eq (a b : dvar nat) : dvar_eqb a b = true <-> a = b.
Proof.
elim: a b => [x | a IH | a IH | a IH |] [y | b | b | b |] //=.
- by split=> [/Nat.eqb_eq -> | [->]] //; exact: Nat.eqb_refl.
- by rewrite IH; split=> [-> | [->]].
- by rewrite IH; split=> [-> | [->]].
by rewrite IH; split=> [-> | [->]].
Qed.

Lemma key_eqb_eq (a b : key) : key_eqb a b = true <-> a = b.
Proof.
case: a b => [x |] [y |] //=.
by rewrite dvar_eqb_eq; split=> [-> | [->]].
Qed.

(* Reading a store just written. *)
Lemma get_set (s : store) x v y :
  store_get (store_set s x v) y = if key_eqb x y then Some v else store_get s y.
Proof.
elim: s => [| [k w] s IH] /=; first by case: (key_eqb x y).
case Ekx: (key_eqb k x) => /=.
  by move/key_eqb_eq: Ekx => ->; case: (key_eqb x y).
case Eky: (key_eqb k y) => //.
move/key_eqb_eq: Eky => Eky; subst k.
case Exy: (key_eqb x y) => //.
move/key_eqb_eq: Exy => Exy; subst y.
by rewrite (proj2 (key_eqb_eq x x) erefl) in Ekx.
Qed.

Lemma get_set_same (s : store) x v : store_get (store_set s x v) x = Some v.
Proof. by rewrite get_set (proj2 (key_eqb_eq x x) erefl). Qed.

Lemma get_set_other (s : store) x v y : x <> y -> store_get (store_set s x v) y = store_get s y.
Proof.
move=> H; rewrite get_set; case E: (key_eqb x y) => //.
by move/key_eqb_eq: E.
Qed.

(* ---------------------------------------------------------------------------
   Consistent variables: the first number of a pair is the second, so
   simplify's comparison (dvar_eq, on the first numbers) is the equality of
   the variables of the evaluator (out_dvar, the second numbers). *)

Lemma out_inj a b : consistent a -> consistent b -> out a = out b -> a = b.
Proof.
elim: a b => [[i j] | a IH | a IH | a IH |] [[i' j'] | b | b | b |] //=.
- by move=> -> -> [->].
- by move=> Ha Hb [/(IH _ Ha Hb) ->].
- by move=> Ha Hb [/(IH _ Ha Hb) ->].
by move=> Ha Hb [/(IH _ Ha Hb) ->].
Qed.

Lemma dvar_eq_refl a : dvar_eq nat a a = true.
Proof. by elim: a => [[i j] | | | |] //=; rewrite Nat.eqb_refl. Qed.

(* dvar_eq says false only of different variables. *)
Lemma dvar_eq_false_neq a b : dvar_eq nat a b = false -> a <> b.
Proof. by move=> H E; rewrite E dvar_eq_refl in H. Qed.

(* On consistent variables, dvar_eq says true only of equal ones. *)
Lemma dvar_eq_true_eq a b : consistent a -> consistent b -> dvar_eq nat a b = true -> a = b.
Proof.
elim: a b => [[i j] | a IH | a IH | a IH |] [[i' j'] | b | b | b |] //=.
- by move=> -> -> /Nat.eqb_eq ->.
- by move=> Ha Hb /(IH _ Ha Hb) ->.
- by move=> Ha Hb /(IH _ Ha Hb) ->.
by move=> Ha Hb /(IH _ Ha Hb) ->.
Qed.

Lemma neq_dvar_eq_false a b : consistent a -> consistent b -> a <> b -> dvar_eq nat a b = false.
Proof.
move=> Ha Hb H; case E: (dvar_eq nat a b) => //.
by case: H; exact: dvar_eq_true_eq E.
Qed.

(* Two different consistent variables are different keys of the store. *)
Lemma key_neq a b : consistent a -> consistent b -> a <> b -> KVar (out a) <> KVar (out b).
Proof. by move=> Ha Hb H [/(out_inj _ _ Ha Hb)]. Qed.

(* ---------------------------------------------------------------------------
   The literals simplify introduces or recognizes, as the reals read them. *)

Lemma lit_0 : real_lit "0" = Some 0.
Proof.
rewrite /real_lit; vm_compute read_literal.
by rewrite /Q2R /=; congr Some; field.
Qed.

Lemma lit_1 : real_lit "1" = Some 1.
Proof.
rewrite /real_lit; vm_compute read_literal.
by rewrite /Q2R /=; congr Some; field.
Qed.

Lemma lit_m1 : real_lit "-1" = Some (-1).
Proof.
rewrite /real_lit; vm_compute read_literal.
by rewrite /Q2R /=; congr Some; field.
Qed.

Lemma is_lit_eq s e : is_lit nat s e = true -> e = DReal s.
Proof. by case: e => //= s' /String.eqb_eq ->. Qed.

(* ---------------------------------------------------------------------------
   Expressions: simplify_expr is a refinement. When an expression evaluates,
   its simplification evaluates to the same value: each rewrite is a real
   identity, and its operands, which the original evaluated, are reals. *)

(* Unfolds an evaluation hypothesis, operand by operand. *)
Ltac inv_eval :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => injection H as H; subst
  | H : None = Some _ |- _ => discriminate H
  | H : match ?e with _ => _ end = Some _ |- _ =>
      let E := fresh "E" in destruct e eqn:E
  end.

(* The value of a unary operation: its operand is a real. *)
Lemma xeval_op1_inv s f a w :
  xeval reals s (DOp1 f a) = Some w ->
  exists x y, xeval reals s a = Some (VReal x) /\ real_op1 f x = Some y /\ w = VReal y.
Proof.
rewrite /=; case: (xeval reals s a) => [[x | | | |] |] //=.
by case E: (real_op1 f x) => [y |] // [<-]; exists x, y.
Qed.

(* The value of an arithmetic binary operation with a real operand: both
   operands are reals. *)
Lemma xeval_op2_inv_l s f a b x w :
  xeval reals s a = Some (VReal x) -> xeval reals s (DOp2 f a b) = Some w ->
  Operations.comparison f = false ->
  exists y z, xeval reals s b = Some (VReal y) /\ real_op2 f x y = Some z /\ w = VReal z.
Proof.
move=> Ha /= H Hf; move: H; rewrite Ha.
case: (xeval reals s b) => [[y | | | |] |] //=; rewrite Hf.
by case E: (real_op2 f x y) => [z |] // [<-]; exists y, z.
Qed.

Lemma xeval_op2_inv_r s f a b y w :
  xeval reals s b = Some (VReal y) -> xeval reals s (DOp2 f a b) = Some w ->
  Operations.comparison f = false ->
  exists x z, xeval reals s a = Some (VReal x) /\ real_op2 f x y = Some z /\ w = VReal z.
Proof.
move=> Hb /= H Hf; move: H; rewrite Hb.
case: (xeval reals s a) => [[x | | | |] |] //=; rewrite Hf.
by case E: (real_op2 f x y) => [z |] // [<-]; exists x, z.
Qed.

(* A real literal operand. *)
Lemma xeval_lit s l x : real_lit l = Some x -> xeval reals s (oute (DReal l)) = Some (VReal x).
Proof. by move=> /= ->. Qed.

Lemma simplify_op1_ok s f a w :
  xeval reals s (oute (DOp1 f a)) = Some w -> xeval reals s (oute (simplify_op1 nat f a)) = Some w.
Proof.
case: f => [| | | | | | k | g] H; try exact: H.
- case: a H => [v | l | n | b i | [| | | | | | k | g] a' | g b c] H;
    try exact: H.
  (* - - x = x *)
  cbn [out_dexpr simplify_op1] in H |- *.
  have [x [y [Hx [[<-] ->]]]] := xeval_op1_inv _ _ _ _ H.
  have [x' [y' [Hx' [[<-] [Ex]]]]] := xeval_op1_inv _ _ _ _ Hx; subst x.
  by rewrite Hx'; congr (Some (VReal _)); ring.
case: k H => [| [p | p |] | p] H; try exact: H;
  cbn [out_dexpr simplify_op1] in H |- *;
  have [x [y [Hx [[<-] ->]]]] := xeval_op1_inv _ _ _ _ H.
  (* x^0 = 1 *)
  exact: (xeval_lit s "1" 1 lit_1).
(* x^1 = x *)
by rewrite Hx /=; congr (Some (VReal _)); ring.
Qed.

Lemma simplify_op2_ok s f a b w :
  xeval reals s (oute (DOp2 f a b)) = Some w -> xeval reals s (oute (simplify_op2 nat f a b)) = Some w.
Proof.
case: f => [| | | | | | | | g] H; try exact: H; rewrite /simplify_op2;
  cbn [out_dexpr] in H.
- (* 0 + y = y, x + 0 = x *)
  case A: (is_lit nat "0" a).
    move/is_lit_eq: A => A; subst a.
    have [y [z [Hy [[<-] ->]]]] :=
      xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H erefl.
    by rewrite Hy; congr (Some (VReal _)); ring.
  case B: (is_lit nat "0" b); last exact: H.
  move/is_lit_eq: B => B; subst b.
  have [x [z [Hx [[<-] ->]]]] :=
    xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H erefl.
  by rewrite Hx; congr (Some (VReal _)); ring.
- (* x - 0 = x *)
  case B: (is_lit nat "0" b); last exact: H.
  move/is_lit_eq: B => B; subst b.
  have [x [z [Hx [[<-] ->]]]] :=
    xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H erefl.
  by rewrite Hx; congr (Some (VReal _)); ring.
(* products by 0, 1 and -1 *)
case A: (is_lit nat "0" a).
  move/is_lit_eq: A => A; subst a.
  have [y [z [Hy [[<-] ->]]]] :=
    xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H erefl.
  by rewrite (xeval_lit s "0" 0 lit_0); congr (Some (VReal _)); ring.
case B: (is_lit nat "0" b).
  move/is_lit_eq: B => B; subst b.
  have [x [z [Hx [[<-] ->]]]] :=
    xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H erefl.
  by rewrite (xeval_lit s "0" 0 lit_0); congr (Some (VReal _)); ring.
case A1: (is_lit nat "1" a).
  move/is_lit_eq: A1 => A1; subst a.
  have [y [z [Hy [[<-] ->]]]] :=
    xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_1) H erefl.
  by rewrite Hy; congr (Some (VReal _)); ring.
case B1: (is_lit nat "1" b).
  move/is_lit_eq: B1 => B1; subst b.
  have [x [z [Hx [[<-] ->]]]] :=
    xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_1) H erefl.
  by rewrite Hx; congr (Some (VReal _)); ring.
case A2: (is_lit nat "-1" a).
  move/is_lit_eq: A2 => A2; subst a.
  have [y [z [Hy [[<-] ->]]]] :=
    xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_m1) H erefl.
  by rewrite /= Hy /=; congr (Some (VReal _)); ring.
case B2: (is_lit nat "-1" b); last exact: H.
move/is_lit_eq: B2 => B2; subst b.
have [x [z [Hx [[<-] ->]]]] :=
  xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_m1) H erefl.
by rewrite /= Hx /=; congr (Some (VReal _)); ring.
Qed.

Lemma xeval_simplify s e w :
  xeval reals s (oute e) = Some w -> xeval reals s (oute (simplify_expr nat e)) = Some w.
Proof.
elim: e w => [v | l | k | a IHa i IHi | f a IHa | f a IHa b IHb] w H;
  try exact: H.
- cbn [out_dexpr simplify_expr xeval] in H |- *.
  case Ea: (xeval reals s (oute a)) H => [[| | | xs |] |] // H.
  case Ei: (xeval reals s (oute i)) H => [[| k | | |] |] // H.
  by rewrite (IHa _ Ea) (IHi _ Ei).
- apply: simplify_op1_ok.
  change (xeval reals s (DOp1 f (oute (simplify_expr nat a))) = Some w).
  cbn [out_dexpr xeval] in H |- *.
  case Ea: (xeval reals s (oute a)) H => [va |] // H.
  by rewrite (IHa _ Ea).
apply: simplify_op2_ok.
change (xeval reals s (DOp2 f (oute (simplify_expr nat a))
  (oute (simplify_expr nat b))) = Some w).
cbn [out_dexpr xeval] in H |- *.
case Ea: (xeval reals s (oute a)) H => [va |] // H.
case Eb: (xeval reals s (oute b)) H => [vb |] // H.
by rewrite (IHa _ Ea) (IHb _ Eb).
Qed.

(* ---------------------------------------------------------------------------
   The discipline of the variables, without tapes. `gd` is `good` (Scoping.v)
   for a block that pushes and pops nothing: the tangent programs. *)

Inductive gd : list (dvar W) -> list (dvar W) -> list (dstmt W) -> Prop :=
| GdNil sc wr : gd sc wr []
| GdConstant sc wr t v e r :
    expr_ok sc e -> ~ In v sc -> consistent v ->
    gd (v :: sc) wr r -> gd sc wr (DDefine (DConstant t) v e :: r)
| GdMutable sc wr v e r :
    expr_ok sc e -> ~ In v sc -> consistent v ->
    gd (v :: sc) (v :: wr) r -> gd sc wr (DDefine DMutable v e :: r)
| GdRealVar sc wr v r :
    ~ In v sc -> consistent v -> gd (v :: sc) (v :: wr) r -> gd sc wr (DRealVar v :: r)
| GdTape sc wr v r :
    ~ In v sc -> consistent v -> gd (v :: sc) (v :: wr) r -> gd sc wr (DTape v :: r)
| GdAssign sc wr l e r :
    lhs_ok sc wr l -> expr_ok sc e -> gd sc wr r -> gd sc wr (DAssign l e :: r)
| GdIncrement sc wr l e r :
    lhs_ok sc wr l -> expr_ok sc e -> gd sc wr r -> gd sc wr (DIncrement l e :: r)
| GdBranch sc wr c t e r :
    expr_ok sc c -> gd sc wr t -> gd sc wr e -> gd sc wr r -> gd sc wr (DBranch c t e :: r)
| GdFor sc wr i lo hi b r :
    ~ In i sc -> consistent i -> expr_ok sc lo -> expr_ok sc hi ->
    gd (i :: sc) wr b -> gd sc wr r -> gd sc wr (DFor i lo hi b :: r)
| GdForBack sc wr i lo hi b r :
    ~ In i sc -> consistent i -> expr_ok sc lo -> expr_ok sc hi ->
    gd (i :: sc) wr b -> gd sc wr r -> gd sc wr (DForBack i lo hi b :: r)
| GdReturn sc wr e r :
    expr_ok sc e -> gd sc wr r -> gd sc wr (DReturn e :: r).

(* A statement pushes or pops a tape, itself or in a block it contains. *)
Fixpoint has_tape_op (s : dstmt W) : bool :=
  match s with
  | DPush _ _ | DPop _ _ => true
  | DBranch _ t e => existsb has_tape_op t || existsb has_tape_op e
  | DFor _ _ _ b | DForBack _ _ _ b => existsb has_tape_op b
  | _ => false
  end.

(* A good block without tape operations follows gd. *)
Lemma good_gd sc wr ss : good sc wr ss -> existsb has_tape_op ss = false -> gd sc wr ss.
Proof.
elim=> /= *; repeat match goal with H : _ || _ = false |- _ =>
  case/orb_false_iff: H => ? ? end; try discriminate; econstructor; intuition.
Qed.

(* The variables a block defines, and those it defines writable, in order. *)
Fixpoint after_scope (sc : list (dvar W)) (ss : list (dstmt W)) : list (dvar W) :=
  match ss with
  | [] => sc
  | DDefine _ v _ :: r | DRealVar v :: r | DTape v :: r => after_scope (v :: sc) r
  | _ :: r => after_scope sc r
  end.

Fixpoint after_wr (wr : list (dvar W)) (ss : list (dstmt W)) : list (dvar W) :=
  match ss with
  | [] => wr
  | DDefine (DConstant _) _ _ :: r => after_wr wr r
  | DDefine DMutable v _ :: r | DRealVar v :: r | DTape v :: r => after_wr (v :: wr) r
  | _ :: r => after_wr wr r
  end.

Fixpoint defs (ss : list (dstmt W)) : list (dvar W) :=
  match ss with
  | [] => []
  | DDefine _ v _ :: r | DRealVar v :: r | DTape v :: r => v :: defs r
  | _ :: r => defs r
  end.

Lemma in_after_scope y sc ss : In y (after_scope sc ss) <-> In y (defs ss) \/ In y sc.
Proof.
elim: ss sc => [| st r IH] sc /=; first by tauto.
by case: st => *; rewrite /= ?IH /=; tauto.
Qed.

Lemma in_after_wr y wr ss : In y (after_wr wr ss) -> In y (defs ss) \/ In y wr.
Proof.
elim: ss wr => [| st r IH] wr /=; first by tauto.
by case: st => [[t |] v e | v | v | l e | l e | c t e | i lo hi b | i lo hi b
  | t e | t l | e] /= /IH /=; tauto.
Qed.

Lemma incl_both {A : Type} (v : A) wr sc : incl wr sc -> incl (v :: wr) (v :: sc).
Proof. by move=> H y [<- | Hy]; [left | right; apply: H]. Qed.

Lemma after_scope_incl sc ss : incl sc (after_scope sc ss).
Proof. by move=> y Hy; apply/in_after_scope; right. Qed.

Lemma after_incl wr sc ss : incl wr sc -> incl (after_wr wr ss) (after_scope sc ss).
Proof.
move=> H y Hy; apply/in_after_scope.
by case: (in_after_wr _ _ _ Hy) => [| /H]; [left | right].
Qed.

(* The variables defined by a good block are consistent. *)
Lemma after_consistent sc wr ss : gd sc wr ss -> Forall consistent sc -> Forall consistent (after_scope sc ss).
Proof. by elim=> //= *; auto. Qed.

(* A good block splits into good blocks, the second in the scope the first ends with. *)
Lemma gd_app_inv sc wr a b :
  gd sc wr (a ++ b) -> gd sc wr a /\ gd (after_scope sc a) (after_wr wr a) b.
Proof.
elim: a sc wr => [| st a IH] sc wr /= H; first by split; first constructor.
inversion H; subst; edestruct IH as [Ha Hb]; try eassumption;
  by split; first econstructor; eassumption.
Qed.

Lemma gd_app sc wr a b :
  gd sc wr a -> gd (after_scope sc a) (after_wr wr a) b -> gd sc wr (a ++ b).
Proof.
elim: a sc wr => [| st a IH] sc wr Ha Hb //=.
by inversion Ha; subst; econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------------
   Agreement of two stores on the variables in scope, and on the returned
   value. *)

Definition agree (sc : list (dvar W)) (s s' : store) : Prop :=
  (forall x, In x sc -> store_get s (KVar (out x)) = store_get s' (KVar (out x))) /\
  store_get s Returned = store_get s' Returned.

Lemma agree_refl sc s : agree sc s s.
Proof. by []. Qed.

Lemma agree_trans sc s1 s2 s3 : agree sc s1 s2 -> agree sc s2 s3 -> agree sc s1 s3.
Proof.
move=> [H1 R1] [H2 R2]; split; last by rewrite R1 R2.
by move=> x Hx; rewrite H1 ?H2.
Qed.

Lemma agree_incl sc1 sc2 s s' : incl sc1 sc2 -> agree sc2 s s' -> agree sc1 s s'.
Proof. by move=> Hi [H R]; split=> // x /Hi /H. Qed.

(* Writing the same value at the same key keeps the agreement. *)
Lemma agree_set sc s s' k w : agree sc s s' -> agree sc (store_set s k w) (store_set s' k w).
Proof.
move=> [H R]; split=> [x Hx |]; rewrite !get_set.
  by case: (key_eqb k _); auto.
by case: (key_eqb k _).
Qed.

(* Defining a variable extends the scope of the agreement. *)
Lemma agree_set_cons sc s s' v w :
  agree sc s s' -> agree (v :: sc) (store_set s (KVar (out v)) w) (store_set s' (KVar (out v)) w).
Proof.
move=> Hag; have [H R] := agree_set _ _ _ (KVar (out v)) w Hag; split=> //.
by move=> x [<- | Hx]; [rewrite !get_set_same | auto].
Qed.

(* Writing a variable out of scope, on one side, keeps the agreement. *)
Lemma agree_set_out sc s s' v w :
  Forall consistent sc -> consistent v -> ~ In v sc ->
  agree sc s s' -> agree sc (store_set s (KVar (out v)) w) s'.
Proof.
move=> Hc Hv Hn [H R]; split; last by rewrite get_set_other.
move=> x Hx; rewrite get_set_other; last by auto.
apply: key_neq => //; first by move/Forall_forall: Hc; apply.
by move=> E; subst x.
Qed.

(* ---------------------------------------------------------------------------
   Expressions and locations in scope. *)

(* An expression in scope reads the same in two agreeing stores. *)
Lemma xeval_agree sc s s' e :
  expr_ok sc e -> agree sc s s' -> xeval reals s (oute e) = xeval reals s' (oute e).
Proof.
move=> He Hag; elim: e He => [v | l | k | a IHa i IHi | f a IHa | f a IHa b IHb]
  //= He.
- exact: (proj1 Hag _ He).
- by case: He => Ha Hi; rewrite IHa ?IHi.
- by rewrite IHa.
by case: He => Ha Hb; rewrite IHa ?IHb.
Qed.

Lemma expr_ok_incl sc1 sc2 e : incl sc1 sc2 -> expr_ok sc1 e -> expr_ok sc2 e.
Proof. by move=> Hi; elim: e => //= *; intuition. Qed.

Lemma lhs_ok_incl sc1 sc2 wr1 wr2 l :
  incl sc1 sc2 -> incl wr1 wr2 -> lhs_ok sc1 wr1 l -> lhs_ok sc2 wr2 l.
Proof.
move=> Hs Hw; case: l => [| | | [] i | |] //=; intuition.
by apply: expr_ok_incl; eauto.
Qed.

Lemma lhs_expr_ok sc wr l : incl wr sc -> lhs_ok sc wr l -> expr_ok sc l.
Proof. by move=> Hi; case: l => [| | | [] i | |] //=; intuition. Qed.

Lemma expr_ok_simplify sc e : expr_ok sc e -> expr_ok sc (simplify_expr nat e).
Proof.
elim: e => [| | | a IHa i IHi | f a IHa | f a IHa b IHb] //= H.
- by case: H => /IHa ? /IHi.
- move/IHa: H; rewrite /simplify_op1.
  case: f => [| | | | | | k | g] //= H.
    by case: (simplify_expr nat a) H => [| | | | [] a' |].
  by case: k => [| [] |].
case: H => /IHa Ha /IHb Hb; rewrite /simplify_op2.
by case: f => //=; repeat match goal with |- context [if ?c then _ else _] =>
  case: (c) end.
Qed.

Lemma lhs_ok_simplify sc wr l : lhs_ok sc wr l -> lhs_ok sc wr (simplify_expr nat l).
Proof.
by case: l => [| | | [] i | |] //=; intuition; apply: expr_ok_simplify.
Qed.

(* An assignment in scope, from agreeing stores, leaves agreeing stores. *)
Lemma assign_agree sc wr l w s s' t :
  incl wr sc -> lhs_ok sc wr l -> agree sc s s' -> assign reals s (oute l) w = Some t ->
  exists t', assign reals s' (oute l) w = Some t' /\ agree sc t t'.
Proof.
move=> Hi Hl Hag; case: l Hl => [x | | | [x | | | | |] i | |] //= Hl.
  move=> [<-]; exists (store_set s' (KVar (out x)) w); split=> //.
  exact: agree_set.
case: Hl => Hx Hie; case: w => [e | | | |] //=.
rewrite -(proj1 Hag x (Hi _ Hx)) -(xeval_agree _ _ _ _ Hie Hag).
case: (store_get s (KVar (out x))) => [[| | | l |] |] //.
case: (xeval reals s (oute i)) => [[| k | | |] |] //.
case: (replace_nth_z k e l) => // l1 [<-].
exists (store_set s' (KVar (out x)) (VArray l1)); split=> //.
exact: agree_set.
Qed.

(* The simplified location is assigned as the original. *)
Lemma assign_simplify sc wr s l w t :
  lhs_ok sc wr l -> assign reals s (oute l) w = Some t ->
  assign reals s (oute (simplify_expr nat l)) w = Some t.
Proof.
case: l => [x | | | [x | | | | |] i | |] //= Hl.
case: w => [e | | | |] //=.
case: (store_get s (KVar (out x))) => [[| | | l |] |] //.
case Ei: (xeval reals s (oute i)) => [v |] //.
by rewrite (xeval_simplify _ _ _ Ei).
Qed.

(* ---------------------------------------------------------------------------
   The execution of each statement, unfolded. *)

Lemma exec_define s so v e :
  exec reals (outs (DDefine so v e)) s =
  match xeval reals s (oute e) with Some w => Some (store_set s (KVar (out v)) w) | None => None end.
Proof. by []. Qed.

Lemma exec_realvar s v : exec reals (outs (DRealVar v)) s = Some (store_set s (KVar (out v)) (VReal 0)).
Proof.
change (dom_lit reals "0") with (real_lit "0"); cbn -[real_lit].
by rewrite lit_0.
Qed.

Lemma exec_tape s v : exec reals (outs (DTape v)) s = Some (store_set s (KVar (out v)) (VTape [])).
Proof. by []. Qed.

Lemma exec_assign s l e :
  exec reals (outs (DAssign l e)) s =
  match xeval reals s (oute e) with Some w => assign reals s (oute l) w | None => None end.
Proof. by []. Qed.

Lemma exec_increment s l e :
  exec reals (outs (DIncrement l e)) s =
  match xeval reals s (oute l), xeval reals s (oute e) with
  | Some (VReal a), Some (VReal b) => assign reals s (oute l) (VReal (a + b))
  | _, _ => None
  end.
Proof. by []. Qed.

Lemma exec_branch s c t e :
  exec reals (outs (DBranch c t e)) s =
  match xeval reals s (oute c) with
  | Some (VBool true) => ex t s
  | Some (VBool false) => ex e s
  | _ => None
  end.
Proof. by []. Qed.

Lemma exec_for s i lo hi b :
  exec reals (outs (DFor i lo hi b)) s =
  match xeval reals s (oute lo), xeval reals s (oute hi) with
  | Some (VInt l), Some (VInt h) => exec_up R (ex b) (out i) l (count l h) s
  | _, _ => None
  end.
Proof. by []. Qed.

Lemma exec_forback s i lo hi b :
  exec reals (outs (DForBack i lo hi b)) s =
  match xeval reals s (oute lo), xeval reals s (oute hi) with
  | Some (VInt l), Some (VInt h) => exec_down R (ex b) (out i) (h - 1) (count l h) s
  | _, _ => None
  end.
Proof. by []. Qed.

Lemma exec_return s e :
  exec reals (outs (DReturn e)) s =
  match xeval reals s (oute e) with Some w => Some (store_set s Returned w) | None => None end.
Proof. by []. Qed.

(* ---------------------------------------------------------------------------
   Loops: a relation between two stores, kept by the body when the index is
   set to the same value on both sides, is kept by the loop. *)

Lemma exec_up_sim (Rin Rb : store -> store -> Prop) (b1 b2 : store -> option store) i :
  (forall s s' w, Rin s s' -> Rb (store_set s (KVar i) w) (store_set s' (KVar i) w)) ->
  (forall s s' t, Rb s s' -> b1 s = Some t -> exists t', b2 s' = Some t' /\ Rin t t') ->
  forall n lo s s' t, Rin s s' -> exec_up R b1 i lo n s = Some t ->
  exists t', exec_up R b2 i lo n s' = Some t' /\ Rin t t'.
Proof.
move=> Hset Hbody; elim=> [| n IH] lo s s' t Hr /=.
  by move=> [<-]; exists s'.
case E: (b1 (store_set s (KVar i) (VInt lo))) => [s1 |] // H.
have [s1' [-> Hr1]] := Hbody _ _ _ (Hset _ _ (VInt lo) Hr) E.
exact: IH Hr1 H.
Qed.

Lemma exec_down_sim (Rin Rb : store -> store -> Prop) (b1 b2 : store -> option store) i :
  (forall s s' w, Rin s s' -> Rb (store_set s (KVar i) w) (store_set s' (KVar i) w)) ->
  (forall s s' t, Rb s s' -> b1 s = Some t -> exists t', b2 s' = Some t' /\ Rin t t') ->
  forall n hi s s' t, Rin s s' -> exec_down R b1 i hi n s = Some t ->
  exists t', exec_down R b2 i hi n s' = Some t' /\ Rin t t'.
Proof.
move=> Hset Hbody; elim=> [| n IH] hi s s' t Hr /=.
  by move=> [<-]; exists s'.
case E: (b1 (store_set s (KVar i) (VInt hi))) => [s1 |] // H.
have [s1' [-> Hr1]] := Hbody _ _ _ (Hset _ _ (VInt hi) Hr) E.
exact: IH Hr1 H.
Qed.

(* The agreement on the scope, extended by the index, is kept by setting the index. *)
Lemma agree_index sc i : forall s s' w, agree sc s s' ->
  agree (i :: sc) (store_set s (KVar (out i)) w) (store_set s' (KVar (out i)) w).
Proof. by move=> s s' w; apply: agree_set_cons. Qed.

(* ---------------------------------------------------------------------------
   The frame: a good block, run from two stores that agree on its scope, ends
   in stores that agree on its scope and on the variables it defines. It
   reads only variables in scope, and writes the same values on both sides. *)

Lemma frame sc wr ss :
  gd sc wr ss -> incl wr sc ->
  forall s s' t, agree sc s s' -> ex ss s = Some t ->
  exists t', ex ss s' = Some t' /\ agree (after_scope sc ss) t t'.
Proof.
elim=> {sc wr ss} [sc wr | sc wr ty v e r He Hv Hcv Hr IH
       | sc wr v e r He Hv Hcv Hr IH | sc wr v r Hv Hcv Hr IH
       | sc wr v r Hv Hcv Hr IH | sc wr l e r Hl He Hr IH
       | sc wr l e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] Hwr s s' t0 Hag Hex;
  rewrite ?ex_cons in Hex *; rewrite [after_scope _ _]/=.
- by case: Hex => <-; exists s'.
- rewrite !exec_define in Hex *; rewrite -(xeval_agree _ _ _ _ He Hag).
  case: (xeval reals s (oute e)) Hex => // w Hex.
  exact: IH (incl_tl _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex.
- rewrite !exec_define in Hex *; rewrite -(xeval_agree _ _ _ _ He Hag).
  case: (xeval reals s (oute e)) Hex => // w Hex.
  exact: IH (incl_both _ _ _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex.
- rewrite !exec_realvar in Hex *.
  exact: IH (incl_both _ _ _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex.
- rewrite !exec_tape in Hex *.
  exact: IH (incl_both _ _ _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex.
- rewrite !exec_assign in Hex *; rewrite -(xeval_agree _ _ _ _ He Hag).
  case: (xeval reals s (oute e)) Hex => // w.
  case E: (assign reals s (oute l) w) => [s1 |] // Hex.
  have [s1' [-> Hag1]] := assign_agree _ _ _ _ _ _ _ Hwr Hl Hag E.
  exact: IH Hwr _ _ _ Hag1 Hex.
- rewrite !exec_increment in Hex *.
  rewrite -(xeval_agree _ _ _ _ He Hag).
  rewrite -(xeval_agree _ _ _ _ (lhs_expr_ok _ _ _ Hwr Hl) Hag).
  case: (xeval reals s (oute l)) Hex => [[a | | | |] |] //.
  case: (xeval reals s (oute e)) => [[b | | | |] |] //.
  case E: (assign reals s (oute l) _) => [s1 |] // Hex.
  have [s1' [-> Hag1]] := assign_agree _ _ _ _ _ _ _ Hwr Hl Hag E.
  exact: IH Hwr _ _ _ Hag1 Hex.
- rewrite !exec_branch in Hex *; rewrite -(xeval_agree _ _ _ _ Hc Hag).
  case: (xeval reals s (oute c)) Hex => [[| | [] | |] |] //.
    case E: (ex t s) => [s1 |] // Hex.
    have [s1' [-> Hag1]] := IHt Hwr _ _ _ Hag E.
    exact: IH Hwr _ _ _ (agree_incl _ _ _ _ (after_scope_incl _ _) Hag1) Hex.
  case E: (ex e s) => [s1 |] // Hex.
  have [s1' [-> Hag1]] := IHe Hwr _ _ _ Hag E.
  exact: IH Hwr _ _ _ (agree_incl _ _ _ _ (after_scope_incl _ _) Hag1) Hex.
- rewrite !exec_for in Hex *.
  rewrite -(xeval_agree _ _ _ _ Hlo Hag) -(xeval_agree _ _ _ _ Hhi Hag).
  case: (xeval reals s (oute lo)) Hex => [[| l | | |] |] //.
  case: (xeval reals s (oute hi)) => [[| h | | |] |] //.
  case E: (exec_up R (ex b) (out i) l (count l h) s) => [s1 |] // Hex.
  have Hbody : forall u u' v, agree (i :: sc) u u' -> ex b u = Some v ->
      exists v', ex b u' = Some v' /\ agree sc v v'.
    move=> u u' v Hu Hv.
    have [v' [-> Hv']] := IHb (incl_tl _ Hwr) _ _ _ Hu Hv.
    exists v'; split=> //.
    exact: (agree_incl _ _ _ _
      (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hv').
  have [s1' [-> Hag1]] := exec_up_sim (agree sc) (agree (i :: sc)) (ex b)
    (ex b) (out i) (agree_index sc i) Hbody _ _ _ _ _ Hag E.
  exact: IH Hwr _ _ _ Hag1 Hex.
- rewrite !exec_forback in Hex *.
  rewrite -(xeval_agree _ _ _ _ Hlo Hag) -(xeval_agree _ _ _ _ Hhi Hag).
  case: (xeval reals s (oute lo)) Hex => [[| l | | |] |] //.
  case: (xeval reals s (oute hi)) => [[| h | | |] |] //.
  case E: (exec_down R (ex b) (out i) (h - 1) (count l h) s)
    => [s1 |] // Hex.
  have Hbody : forall u u' v, agree (i :: sc) u u' -> ex b u = Some v ->
      exists v', ex b u' = Some v' /\ agree sc v v'.
    move=> u u' v Hu Hv.
    have [v' [-> Hv']] := IHb (incl_tl _ Hwr) _ _ _ Hu Hv.
    exists v'; split=> //.
    exact: (agree_incl _ _ _ _
      (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hv').
  have [s1' [-> Hag1]] := exec_down_sim (agree sc) (agree (i :: sc)) (ex b)
    (ex b) (out i) (agree_index sc i) Hbody _ _ _ _ _ Hag E.
  exact: IH Hwr _ _ _ Hag1 Hex.
rewrite !exec_return in Hex *; rewrite -(xeval_agree _ _ _ _ He Hag).
case: (xeval reals s (oute e)) Hex => // w Hex.
exact: IH Hwr _ _ _ (agree_set _ _ _ _ _ Hag) Hex.
Qed.

(* ---------------------------------------------------------------------------
   The simulation: ss2 refines ss1 in scope sc when, from stores agreeing on
   sc, every run of ss1 is matched by a run of ss2 ending in stores agreeing
   on sc. *)

Definition sim (sc : list (dvar W)) (ss1 ss2 : list (dstmt W)) : Prop :=
  forall s s' t, agree sc s s' -> ex ss1 s = Some t ->
  exists t', ex ss2 s' = Some t' /\ agree sc t t'.

Lemma sim_trans sc a b c : sim sc a b -> sim sc b c -> sim sc a c.
Proof.
move=> Hab Hbc s s' t Hag H.
have [t1 [H1 Ha1]] := Hab _ _ _ (agree_refl sc s) H.
have [t2 [H2 Ha2]] := Hbc _ _ _ Hag H1.
by exists t2; split=> //; exact: agree_trans Ha1 Ha2.
Qed.

(* A good block refines itself. *)
Lemma frame_sim sc wr ss : gd sc wr ss -> incl wr sc -> sim sc ss ss.
Proof.
move=> Hg Hwr s s' t Hag H.
have [t' [H' Ha']] := frame _ _ _ Hg Hwr _ _ _ Hag H.
exists t'; split=> //.
exact: (agree_incl _ _ _ _ (after_scope_incl _ _) Ha').
Qed.

Lemma ex_single h s : ex [h] s = exec reals (outs h) s.
Proof. by rewrite ex_cons; case: (exec reals (outs h) s). Qed.

(* Two blocks refine each other statement by statement. *)
Lemma sim_cons sc sc' h1 h2 r1 r2 :
  incl sc sc' ->
  (forall s s' t, agree sc s s' -> exec reals (outs h1) s = Some t ->
     exists t', exec reals (outs h2) s' = Some t' /\ agree sc' t t') ->
  sim sc' r1 r2 -> sim sc (h1 :: r1) (h2 :: r2).
Proof.
move=> Hi Hh Hr s s' t Hag; rewrite !ex_cons.
case E: (exec reals (outs h1) s) => [s1 |] // H.
have [s1' [-> Hag1]] := Hh _ _ _ Hag E.
have [t' [H' Ha']] := Hr _ _ _ Hag1 H.
by exists t'; split=> //; exact: agree_incl Hi Ha'.
Qed.

(* A statement kept in front of a refined block. *)
Lemma sim_keep sc wr h r r' :
  gd sc wr (h :: r) -> incl wr sc -> sim (after_scope sc [h]) r r' -> sim sc (h :: r) (h :: r').
Proof.
move=> Hg Hwr Hr; apply: (sim_cons _ (after_scope sc [h])) Hr.
  exact: after_scope_incl.
have [Hh _] := gd_app_inv sc wr [h] r Hg.
move=> s s' t Hag; rewrite -!ex_single => H.
exact: frame _ _ _ Hh Hwr _ _ _ Hag H.
Qed.

(* ---------------------------------------------------------------------------
   Changing the scope of a good block. *)

(* With the same variables in scope, and more writable ones. *)
Lemma gd_mono sc1 wr1 ss :
  gd sc1 wr1 ss -> forall sc2 wr2, incl sc1 sc2 -> incl sc2 sc1 -> incl wr1 wr2 -> gd sc2 wr2 ss.
Proof.
induction 1; move=> sc2 wr2 H12 H21 Hw; econstructor;
  try (eapply expr_ok_incl; eassumption);
  try (eapply lhs_ok_incl; eassumption);
  try (move=> Hin; apply H21 in Hin; contradiction);
  try eassumption;
  try (apply IHgd || apply IHgd1 || apply IHgd2 || apply IHgd3);
  try (apply incl_both; assumption); try assumption.
Qed.

Lemma expr_ok_remove sc1 sc2 v e :
  expr_ok sc1 e -> mentions_expr nat v e = false -> (forall y, y <> v -> In y sc1 -> In y sc2) ->
  expr_ok sc2 e.
Proof.
move=> He Hm Hs.
elim: e He Hm => [x | l | k | a IHa i IHi | f a IHa | f a IHa b IHb] //= He.
- by move/dvar_eq_false_neq => Hx; apply: Hs.
- case: He => Ha Hi /orb_false_iff [Ha' Hi'].
  by split; [apply: IHa | apply: IHi].
case: He => Ha Hb /orb_false_iff [Ha' Hb'].
by split; [apply: IHa | apply: IHb].
Qed.

Lemma lhs_ok_remove sc1 sc2 wr1 wr2 v l :
  lhs_ok sc1 wr1 l -> mentions_expr nat v l = false ->
  (forall y, y <> v -> In y sc1 -> In y sc2) -> (forall y, y <> v -> In y wr1 -> In y wr2) ->
  lhs_ok sc2 wr2 l.
Proof.
move=> Hl Hm Hs Hw; case: l Hl Hm => [x | | | [x | | | | |] i | |] //= Hl.
  by move/dvar_eq_false_neq => Hx; apply: Hw.
move=> /orb_false_iff [/dvar_eq_false_neq Hx Hi]; case: Hl => Hl Hie.
by split; [apply: Hw | exact: expr_ok_remove Hie Hi Hs].
Qed.

(* Without a variable the block does not mention. *)
Lemma gd_remove sc1 wr1 ss v :
  gd sc1 wr1 ss -> existsb (mentions nat v) ss = false ->
  forall sc2 wr2, (forall y, y <> v -> In y sc1 -> In y sc2) ->
  (forall y, y <> v -> In y wr1 -> In y wr2) -> incl sc2 sc1 -> gd sc2 wr2 ss.
Proof.
have Hext : forall (x : dvar W) l1 l2,
    (forall y, y <> v -> In y l1 -> In y l2) ->
    forall y, y <> v -> In y (x :: l1) -> In y (x :: l2).
  by move=> x l1 l2 H y Hy [<- | Hin]; [left | right; apply: H].
have Hfresh : forall (x : dvar W) l1 l2, ~ In x l1 -> incl l2 l1 -> ~ In x l2.
  by move=> x l1 l2 H Hi /Hi.
elim=> {sc1 wr1 ss} [sc wr | sc wr ty x e r He Hx Hcx Hr IH
       | sc wr x e r He Hx Hcx Hr IH | sc wr x r Hx Hcx Hr IH
       | sc wr x r Hx Hcx Hr IH | sc wr l e r Hl He Hr IH
       | sc wr l e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] /= Hm sc2 wr2 Hs Hw Hsub.
- exact: GdNil.
- move: Hm => /orb_false_iff [/orb_false_iff [_ He'] Hr'].
  apply: GdConstant => //.
  - exact: expr_ok_remove He He' Hs.
  - exact: Hfresh Hx Hsub.
  exact: IH Hr' _ _ (Hext _ _ _ Hs) Hw (incl_both _ _ _ Hsub).
- move: Hm => /orb_false_iff [/orb_false_iff [_ He'] Hr'].
  apply: GdMutable => //.
  - exact: expr_ok_remove He He' Hs.
  - exact: Hfresh Hx Hsub.
  exact: IH Hr' _ _ (Hext _ _ _ Hs) (Hext _ _ _ Hw) (incl_both _ _ _ Hsub).
- move: Hm => /orb_false_iff [_ Hr'].
  apply: GdRealVar => //; first exact: Hfresh Hx Hsub.
  exact: IH Hr' _ _ (Hext _ _ _ Hs) (Hext _ _ _ Hw) (incl_both _ _ _ Hsub).
- move: Hm => /orb_false_iff [_ Hr'].
  apply: GdTape => //; first exact: Hfresh Hx Hsub.
  exact: IH Hr' _ _ (Hext _ _ _ Hs) (Hext _ _ _ Hw) (incl_both _ _ _ Hsub).
- move: Hm => /orb_false_iff [/orb_false_iff [Hl' He'] Hr'].
  apply: GdAssign; last exact: IH.
    exact: lhs_ok_remove Hl Hl' Hs Hw.
  exact: expr_ok_remove He He' Hs.
- move: Hm => /orb_false_iff [/orb_false_iff [Hl' He'] Hr'].
  apply: GdIncrement; last exact: IH.
    exact: lhs_ok_remove Hl Hl' Hs Hw.
  exact: expr_ok_remove He He' Hs.
- move: Hm => /orb_false_iff
    [/orb_false_iff [/orb_false_iff [Hc' Ht'] He'] Hr'].
  apply: GdBranch; [exact: expr_ok_remove Hc Hc' Hs | exact: IHt | exact: IHe
                   | exact: IH].
- move: Hm => /orb_false_iff [/orb_false_iff [/orb_false_iff
    [/orb_false_iff [_ Hlo'] Hhi'] Hb'] Hr'].
  apply: GdFor => //.
  - exact: Hfresh Hi Hsub.
  - exact: expr_ok_remove Hlo Hlo' Hs.
  - exact: expr_ok_remove Hhi Hhi' Hs.
  - exact: IHb Hb' _ _ (Hext _ _ _ Hs) Hw (incl_both _ _ _ Hsub).
  exact: IH.
- move: Hm => /orb_false_iff [/orb_false_iff [/orb_false_iff
    [/orb_false_iff [_ Hlo'] Hhi'] Hb'] Hr'].
  apply: GdForBack => //.
  - exact: Hfresh Hi Hsub.
  - exact: expr_ok_remove Hlo Hlo' Hs.
  - exact: expr_ok_remove Hhi Hhi' Hs.
  - exact: IHb Hb' _ _ (Hext _ _ _ Hs) Hw (incl_both _ _ _ Hsub).
  exact: IH.
move: Hm => /orb_false_iff [He' Hr'].
apply: GdReturn; last exact: IH.
exact: expr_ok_remove He He' Hs.
Qed.

(* Without a writable variable the block never assigns. *)
Lemma lhs_ok_drop_wr sc wr1 wr2 v l :
  lhs_ok sc wr1 l -> target nat v l = false -> (forall y, y <> v -> In y wr1 -> In y wr2) ->
  lhs_ok sc wr2 l.
Proof.
move=> Hl Ht Hw; case: l Hl Ht => [x | | | [x | | | | |] i | |] //= Hl.
  by move/dvar_eq_false_neq => Hx; apply: Hw.
by move/dvar_eq_false_neq => Hx; case: Hl => Hl Hie; split=> //; apply: Hw.
Qed.

Lemma gd_drop_wr sc wr1 ss v :
  gd sc wr1 ss -> existsb (writes nat v) ss = false ->
  forall wr2, (forall y, y <> v -> In y wr1 -> In y wr2) -> gd sc wr2 ss.
Proof.
have Hext : forall (x : dvar W) l1 l2,
    (forall y, y <> v -> In y l1 -> In y l2) ->
    forall y, y <> v -> In y (x :: l1) -> In y (x :: l2).
  by move=> x l1 l2 H y Hy [<- | Hin]; [left | right; apply: H].
elim=> {sc wr1 ss} [sc wr | sc wr ty x e r He Hx Hcx Hr IH
       | sc wr x e r He Hx Hcx Hr IH | sc wr x r Hx Hcx Hr IH
       | sc wr x r Hx Hcx Hr IH | sc wr l e r Hl He Hr IH
       | sc wr l e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] /= Hm wr2 Hw.
- exact: GdNil.
- by apply: GdConstant => //; exact: IH.
- by apply: GdMutable => //; apply: IH Hm _ (Hext _ _ _ Hw).
- by apply: GdRealVar => //; apply: IH Hm _ (Hext _ _ _ Hw).
- by apply: GdTape => //; apply: IH Hm _ (Hext _ _ _ Hw).
- move: Hm => /orb_false_iff [Hl' Hm].
  by apply: GdAssign => //; [exact: lhs_ok_drop_wr Hl Hl' Hw | exact: IH].
- move: Hm => /orb_false_iff [Hl' Hm].
  by apply: GdIncrement => //; [exact: lhs_ok_drop_wr Hl Hl' Hw | exact: IH].
- move: Hm => /orb_false_iff [/orb_false_iff [Ht' He'] Hm].
  by apply: GdBranch => //; [exact: IHt | exact: IHe | exact: IH].
- move: Hm => /orb_false_iff [Hb' Hm].
  by apply: GdFor => //; [exact: IHb | exact: IH].
- move: Hm => /orb_false_iff [Hb' Hm].
  by apply: GdForBack => //; [exact: IHb | exact: IH].
by apply: GdReturn => //; exact: IH.
Qed.

(* ---------------------------------------------------------------------------
   A block that does not mention a variable leaves its value as it is. *)

Definition lhs_var (l : dexpr nat) : option (dvar nat) :=
  match l with DVar x => Some x | DAt (DVar x) _ => Some x | _ => None end.

(* An assignment writes its variable only. *)
Lemma assign_set s l w t :
  assign reals s l w = Some t -> exists x w', lhs_var l = Some x /\ t = store_set s (KVar x) w'.
Proof.
case: l => [x | | | [x | | | | |] i | |] //=.
  by move=> [<-]; exists x, w.
case: w => [e | | | |] //.
case: (store_get s (KVar x)) => [[| | | l |] |] //.
case: (xeval reals s i) => [[| k | | |] |] //.
by case: (replace_nth_z k e l) => // l1 [<-]; exists x, (VArray l1).
Qed.

Lemma lhs_var_out sc wr l :
  lhs_ok sc wr l -> exists x, In x wr /\ lhs_var (oute l) = Some (out x) /\
                              forall v, mentions_expr nat v l = false -> dvar_eq nat x v = false.
Proof.
case: l => [x | | | [x | | | | |] i | |] //= H; first by exists x.
exists x; split; first by case: H.
by split=> // v /orb_false_iff [].
Qed.

Lemma exec_up_inv (Q : store -> Prop) (b : store -> option store) i :
  (forall s w, Q s -> Q (store_set s (KVar i) w)) -> (forall s t, Q s -> b s = Some t -> Q t) ->
  forall n lo s t, Q s -> exec_up R b i lo n s = Some t -> Q t.
Proof.
move=> Hset Hb; elim=> [| n IH] lo s t Hq /=; first by move=> [<-].
case E: (b (store_set s (KVar i) (VInt lo))) => [s1 |] //.
by apply: IH; apply: Hb E; apply: Hset.
Qed.

Lemma exec_down_inv (Q : store -> Prop) (b : store -> option store) i :
  (forall s w, Q s -> Q (store_set s (KVar i) w)) -> (forall s t, Q s -> b s = Some t -> Q t) ->
  forall n hi s t, Q s -> exec_down R b i hi n s = Some t -> Q t.
Proof.
move=> Hset Hb; elim=> [| n IH] hi s t Hq /=; first by move=> [<-].
case E: (b (store_set s (KVar i) (VInt hi))) => [s1 |] //.
by apply: IH; apply: Hb E; apply: Hset.
Qed.

Lemma preserve_unmentioned sc wr ss v :
  gd sc wr ss -> incl wr sc -> Forall consistent sc -> consistent v ->
  existsb (mentions nat v) ss = false ->
  forall s t, ex ss s = Some t -> store_get t (KVar (out v)) = store_get s (KVar (out v)).
Proof.
elim=> {sc wr ss} [sc wr | sc wr ty x e r He Hx Hcx Hr IH
       | sc wr x e r He Hx Hcx Hr IH | sc wr x r Hx Hcx Hr IH
       | sc wr x r Hx Hcx Hr IH | sc wr l e r Hl He Hr IH
       | sc wr l e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] Hwr Hcs Hv /= Hm s t0;
  rewrite ?ex_cons.
- by move=> [<-].
(* a definition writes a variable other than v *)
- move: Hm => /orb_false_iff [/orb_false_iff [Hxv _] Hm].
  rewrite exec_define; case: (xeval reals s (oute e)) => // w Hex.
  rewrite (IH (incl_tl _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
  by apply: get_set_other; apply: key_neq => //; exact: dvar_eq_false_neq.
- move: Hm => /orb_false_iff [/orb_false_iff [Hxv _] Hm].
  rewrite exec_define; case: (xeval reals s (oute e)) => // w Hex.
  rewrite (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
  by apply: get_set_other; apply: key_neq => //; exact: dvar_eq_false_neq.
- move: Hm => /orb_false_iff [Hxv Hm]; rewrite exec_realvar => Hex.
  rewrite (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
  by apply: get_set_other; apply: key_neq => //; exact: dvar_eq_false_neq.
- move: Hm => /orb_false_iff [Hxv Hm]; rewrite exec_tape => Hex.
  rewrite (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
  by apply: get_set_other; apply: key_neq => //; exact: dvar_eq_false_neq.
(* an assignment writes its variable, other than v *)
- move: Hm => /orb_false_iff [/orb_false_iff [Hlv _] Hm].
  rewrite exec_assign; case: (xeval reals s (oute e)) => // w.
  case E: (assign reals s (oute l) w) => [s1 |] // Hex.
  rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
  have [y [w' [Hy ->]]] := assign_set _ _ _ _ E.
  have [x [Hx [Hy' Hxv]]] := lhs_var_out _ _ _ Hl.
  rewrite Hy in Hy'; case: Hy' => Exy; subst y.
  apply: get_set_other; apply: key_neq => //.
    by move/Forall_forall: Hcs; apply; exact: Hwr.
  exact: dvar_eq_false_neq (Hxv _ Hlv).
- move: Hm => /orb_false_iff [/orb_false_iff [Hlv _] Hm].
  rewrite exec_increment.
  case: (xeval reals s (oute l)) => [[a | | | |] |] //.
  case: (xeval reals s (oute e)) => [[b | | | |] |] //.
  case E: (assign reals s (oute l) _) => [s1 |] // Hex.
  rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
  have [y [w' [Hy ->]]] := assign_set _ _ _ _ E.
  have [x [Hx [Hy' Hxv]]] := lhs_var_out _ _ _ Hl.
  rewrite Hy in Hy'; case: Hy' => Exy; subst y.
  apply: get_set_other; apply: key_neq => //.
    by move/Forall_forall: Hcs; apply; exact: Hwr.
  exact: dvar_eq_false_neq (Hxv _ Hlv).
- move: Hm => /orb_false_iff [/orb_false_iff [/orb_false_iff [_ Htm] Hem] Hm].
  rewrite exec_branch.
  case: (xeval reals s (oute c)) => [[| | [] | |] |] //.
    case E: (ex t s) => [s1 |] // Hex.
    by rewrite (IH Hwr Hcs Hv Hm _ _ Hex); exact: IHt Hwr Hcs Hv Htm _ _ E.
  case E: (ex e s) => [s1 |] // Hex.
  by rewrite (IH Hwr Hcs Hv Hm _ _ Hex); exact: IHe Hwr Hcs Hv Hem _ _ E.
- move: Hm => /orb_false_iff [/orb_false_iff [/orb_false_iff
    [/orb_false_iff [Hiv _] _] Hbm] Hm].
  rewrite exec_for.
  case: (xeval reals s (oute lo)) => [[| l | | |] |] //.
  case: (xeval reals s (oute hi)) => [[| h | | |] |] //.
  case E: (exec_up R (ex b) (out i) l (count l h) s) => [s1 |] // Hex.
  rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
  pose P u := store_get u (KVar (out v)) = store_get s (KVar (out v)).
  have Hset : forall u w, P u -> P (store_set u (KVar (out i)) w).
    move=> u w Hu; rewrite /P get_set_other //.
    by apply: key_neq => //; exact: dvar_eq_false_neq.
  have Hbody : forall u u', P u -> ex b u = Some u' -> P u'.
    move=> u u' Hu Hb'; rewrite /P -Hu.
    exact: IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs) Hv Hbm _ _ Hb'.
  exact: (exec_up_inv P (ex b) (out i) Hset Hbody _ _ _ _ erefl E).
- move: Hm => /orb_false_iff [/orb_false_iff [/orb_false_iff
    [/orb_false_iff [Hiv _] _] Hbm] Hm].
  rewrite exec_forback.
  case: (xeval reals s (oute lo)) => [[| l | | |] |] //.
  case: (xeval reals s (oute hi)) => [[| h | | |] |] //.
  case E: (exec_down R (ex b) (out i) (h - 1) (count l h) s)
    => [s1 |] // Hex.
  rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
  pose P u := store_get u (KVar (out v)) = store_get s (KVar (out v)).
  have Hset : forall u w, P u -> P (store_set u (KVar (out i)) w).
    move=> u w Hu; rewrite /P get_set_other //.
    by apply: key_neq => //; exact: dvar_eq_false_neq.
  have Hbody : forall u u', P u -> ex b u = Some u' -> P u'.
    move=> u u' Hu Hb'; rewrite /P -Hu.
    exact: IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs) Hv Hbm _ _ Hb'.
  exact: (exec_down_inv P (ex b) (out i) Hset Hbody _ _ _ _ erefl E).
move: Hm => /orb_false_iff [_ Hm].
rewrite exec_return; case: (xeval reals s (oute e)) => // w Hex.
by rewrite (IH Hwr Hcs Hv Hm _ _ Hex) get_set_other.
Qed.

(* ---------------------------------------------------------------------------
   Adding zero to a location leaves the store as it is. *)

Lemma replace_nth_same {A : Type} k (x : A) l l1 :
  nth_error l k = Some x -> replace_nth k x l = Some l1 -> l1 = l.
Proof.
elim: k l l1 => [| k IH] [| y l] l1 //=.
  by move=> [->] [<-].
case E: (replace_nth k x l) => [l2 |] // Hn [<-].
by rewrite (IH _ _ Hn E).
Qed.

Lemma assign_same sc wr s l a t :
  lhs_ok sc wr l -> xeval reals s (oute l) = Some (VReal a) ->
  assign reals s (oute l) (VReal a) = Some t -> forall k, store_get t k = store_get s k.
Proof.
move=> Hl Hx H k; case: l Hl Hx H => [x | | | [x | | | | |] i | |] //= Hl.
  move=> Hx [<-]; rewrite get_set.
  case E: (key_eqb (KVar (out x)) k) => //.
  by move/key_eqb_eq: E => <-.
case Ex: (store_get s (KVar (out x))) => [[| | | l |] |] //.
case: (xeval reals s (oute i)) => [[| j | | |] |] //.
case En: (nth_z j l) => [a' |] // [Ea]; subst a'.
move: En; rewrite /nth_z /replace_nth_z; case: (j <? 0)%Z => // En.
case Er: (replace_nth (Z.to_nat j) a l) => [l1 |] //.
rewrite (replace_nth_same _ _ _ _ En Er) => -[<-]; rewrite get_set.
case E: (key_eqb (KVar (out x)) k) => //.
by move/key_eqb_eq: E => <-.
Qed.

(* ---------------------------------------------------------------------------
   A transformation of blocks is correct when it keeps the discipline and
   refines every good block. *)

Definition correct (f : list (dstmt W) -> list (dstmt W)) : Prop :=
  forall sc wr ss, gd sc wr ss -> incl wr sc -> Forall consistent sc ->
  gd sc wr (f ss) /\ sim sc ss (f ss).

(* The identity is correct. *)
Lemma id_correct : correct (fun ss => ss).
Proof. by move=> sc wr ss Hg Hwr Hc; split=> //; exact: frame_sim Hg Hwr. Qed.

(* The head of a definition, with its expression simplified. *)
Lemma head_define sc so v e :
  expr_ok sc e ->
  forall s s' t, agree sc s s' -> exec reals (outs (DDefine so v e)) s = Some t ->
  exists t', exec reals (outs (DDefine so v (simplify_expr nat e))) s' = Some t' /\ agree (v :: sc) t t'.
Proof.
move=> He s s' t Hag; rewrite !exec_define.
case E: (xeval reals s (oute e)) => [w |] // [<-].
rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag).
rewrite (xeval_simplify _ _ _ E).
by exists (store_set s' (KVar (out v)) w); split=> //; exact: agree_set_cons.
Qed.

(* Simplifying each statement of a block, its expressions and the blocks it
   contains, is correct when simplifying the contained blocks is. *)
Lemma simplify_stmt_correct n : correct (simplify_stmts nat n) -> correct (map (simplify_stmt nat (S n))).
Proof.
move=> HA sc wr ss.
elim=> {sc wr ss} [sc wr | sc wr ty v e r He Hv Hcv Hr IH
       | sc wr v e r He Hv Hcv Hr IH | sc wr v r Hv Hcv Hr IH
       | sc wr v r Hv Hcv Hr IH | sc wr l e r Hl He Hr IH
       | sc wr l e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] Hwr Hcs; cbn [map].
- by split=> [| s s' t Hag [<-]]; [exact: GdNil | exists s'].
- have [Hg' Hs'] := IH (incl_tl _ Hwr) (Forall_cons _ Hcv Hcs).
  split; first by apply: GdConstant => //; exact: expr_ok_simplify.
  apply: (sim_cons _ (v :: sc)) Hs'; first exact/incl_tl/incl_refl.
  exact: head_define.
- have [Hg' Hs'] := IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcv Hcs).
  split; first by apply: GdMutable => //; exact: expr_ok_simplify.
  apply: (sim_cons _ (v :: sc)) Hs'; first exact/incl_tl/incl_refl.
  exact: head_define.
- have [Hg' Hs'] := IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcv Hcs).
  split; first exact: GdRealVar.
  apply: (sim_cons _ (v :: sc)) Hs'; first exact/incl_tl/incl_refl.
  move=> s s' t Hag; cbn [simplify_stmt]; rewrite !exec_realvar => -[<-].
  exists (store_set s' (KVar (out v)) (VReal 0)); split=> //.
  exact: agree_set_cons.
- have [Hg' Hs'] := IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcv Hcs).
  split; first exact: GdTape.
  apply: (sim_cons _ (v :: sc)) Hs'; first exact/incl_tl/incl_refl.
  move=> s s' t Hag; cbn [simplify_stmt]; rewrite !exec_tape => -[<-].
  exists (store_set s' (KVar (out v)) (VTape [])); split=> //.
  exact: agree_set_cons.
- have [Hg' Hs'] := IH Hwr Hcs.
  split.
    apply: GdAssign => //; first exact: lhs_ok_simplify.
    exact: expr_ok_simplify.
  apply: (sim_cons _ sc) Hs'; first exact: incl_refl.
  move=> s s' t Hag; cbn [simplify_stmt]; rewrite !exec_assign.
  case E: (xeval reals s (oute e)) => [w |] // H.
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag).
  rewrite (xeval_simplify _ _ _ E).
  exact: assign_agree Hwr (lhs_ok_simplify _ _ _ Hl) Hag
    (assign_simplify _ _ _ _ _ _ Hl H).
- have [Hg' Hs'] := IH Hwr Hcs.
  split.
    apply: GdIncrement => //; first exact: lhs_ok_simplify.
    exact: expr_ok_simplify.
  apply: (sim_cons _ sc) Hs'; first exact: incl_refl.
  move=> s s' t Hag; cbn [simplify_stmt]; rewrite !exec_increment.
  case El: (xeval reals s (oute l)) => [[a | | | |] |] //.
  case E: (xeval reals s (oute e)) => [[b | | | |] |] // H.
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag).
  rewrite (xeval_simplify _ _ _ E).
  rewrite -(xeval_agree _ _ _ _
    (lhs_expr_ok _ _ _ Hwr (lhs_ok_simplify _ _ _ Hl)) Hag).
  rewrite (xeval_simplify _ _ _ El).
  exact: assign_agree Hwr (lhs_ok_simplify _ _ _ Hl) Hag
    (assign_simplify _ _ _ _ _ _ Hl H).
- have [Hg' Hs'] := IH Hwr Hcs.
  have [Ht' Hst] := HA _ _ _ Ht Hwr Hcs.
  have [He' Hse] := HA _ _ _ He Hwr Hcs.
  split; first by apply: GdBranch => //; exact: expr_ok_simplify.
  apply: (sim_cons _ sc) Hs'; first exact: incl_refl.
  move=> s s' t0 Hag; cbn [simplify_stmt]; rewrite !exec_branch.
  case E: (xeval reals s (oute c)) => [w |] // H.
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hc) Hag).
  rewrite (xeval_simplify _ _ _ E).
  case: w E H => [? | ? | [] | ? | ?] _ H //.
    exact: Hst H.
  exact: Hse H.
- have [Hg' Hs'] := IH Hwr Hcs.
  have [Hb' Hsb] := HA _ _ _ Hb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs).
  split; first by apply: GdFor => //; exact: expr_ok_simplify.
  apply: (sim_cons _ sc) Hs'; first exact: incl_refl.
  move=> s s' t0 Hag; cbn [simplify_stmt]; rewrite !exec_for.
  case El: (xeval reals s (oute lo)) => [[| l | | |] |] //.
  case Eh: (xeval reals s (oute hi)) => [[| h | | |] |] // H.
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hlo) Hag).
  rewrite (xeval_simplify _ _ _ El).
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hhi) Hag).
  rewrite (xeval_simplify _ _ _ Eh).
  apply: (exec_up_sim (agree sc) (agree (i :: sc)) _ _ _ (agree_index sc i))
    Hag H.
  move=> u u' v Hu Hv; have [v' [Hv' Ha']] := Hsb _ _ _ Hu Hv.
  exists v'; split=> //.
  exact: (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Ha').
- have [Hg' Hs'] := IH Hwr Hcs.
  have [Hb' Hsb] := HA _ _ _ Hb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs).
  split; first by apply: GdForBack => //; exact: expr_ok_simplify.
  apply: (sim_cons _ sc) Hs'; first exact: incl_refl.
  move=> s s' t0 Hag; cbn [simplify_stmt]; rewrite !exec_forback.
  case El: (xeval reals s (oute lo)) => [[| l | | |] |] //.
  case Eh: (xeval reals s (oute hi)) => [[| h | | |] |] // H.
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hlo) Hag).
  rewrite (xeval_simplify _ _ _ El).
  rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hhi) Hag).
  rewrite (xeval_simplify _ _ _ Eh).
  apply: (exec_down_sim (agree sc) (agree (i :: sc)) _ _ _ (agree_index sc i))
    Hag H.
  move=> u u' v Hu Hv; have [v' [Hv' Ha']] := Hsb _ _ _ Hu Hv.
  exists v'; split=> //.
  exact: (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Ha').
have [Hg' Hs'] := IH Hwr Hcs.
split; first by apply: GdReturn => //; exact: expr_ok_simplify.
apply: (sim_cons _ sc) Hs'; first exact: incl_refl.
move=> s s' t Hag; cbn [simplify_stmt]; rewrite !exec_return.
case E: (xeval reals s (oute e)) => [w |] // [<-].
rewrite -(xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag).
rewrite (xeval_simplify _ _ _ E).
by exists (store_set s' Returned w); split=> //; exact: agree_set.
Qed.

(* ---------------------------------------------------------------------------
   The rewrites of fuse, one by one. *)

(* Two stores equal on every key agree with what the first agrees with. *)
(* A real literal, read by the evaluator. *)
Lemma xeval_real s l x : real_lit l = Some x -> xeval reals s (DReal l) = Some (VReal x).
Proof. by move=> /= ->. Qed.

Lemma agree_same sc s1 s s' :
  (forall k, store_get s1 k = store_get s k) -> agree sc s s' -> agree sc s1 s'.
Proof. by move=> He [H R]; split=> [x Hx |]; rewrite He ?H. Qed.

(* An accumulation of zero is dropped: it rewrites the location with its own value. *)
Lemma sim_zero_increment sc wr l r r' :
  gd sc wr (DIncrement l (DReal "0") :: r) -> sim sc r r' ->
  sim sc (DIncrement l (DReal "0") :: r) r'.
Proof.
move=> Hg Hr s s' t Hag.
inversion Hg as [| | | | | | ? ? ? ? ? Hl | | | |]; subst.
rewrite ex_cons exec_increment; cbn [out_dexpr].
rewrite (xeval_real s "0" 0 lit_0).
case El: (xeval reals s (oute l)) => [[a | | | |] |] //.
rewrite Rplus_0_r.
case E: (assign reals s (oute l) (VReal a)) => [s1 |] // Hex.
exact: Hr _ _ _ (agree_same _ _ _ _ (assign_same _ _ _ _ _ _ Hl El E) Hag) Hex.
Qed.

(* A definition no later statement reads is dropped. *)
Lemma sim_drop_define sc so v e r r' :
  ~ In v sc -> consistent v -> Forall consistent sc -> sim sc r r' -> sim sc (DDefine so v e :: r) r'.
Proof.
move=> Hv Hcv Hcs Hr s s' t Hag; rewrite ex_cons exec_define.
case: (xeval reals s (oute e)) => // w H.
exact: Hr _ _ _ (agree_set_out _ _ _ _ _ Hcs Hcv Hv Hag) H.
Qed.

(* A definition the simplified rest no longer reads is dropped. *)
Lemma sim_drop_define_after sc wr so v e r r' :
  ~ In v sc -> consistent v -> Forall consistent sc -> incl wr sc ->
  sim (v :: sc) r r' -> gd sc wr r' -> sim sc (DDefine so v e :: r) r'.
Proof.
move=> Hv Hcv Hcs Hwr Hr Hg' s s' t Hag; rewrite ex_cons exec_define.
case: (xeval reals s (oute e)) => [w |] // H.
have [t1 [H1 Ha1]] := Hr _ _ _ (agree_refl _ _) H.
have [t' [H' Ha']] :=
  frame _ _ _ Hg' Hwr _ _ _ (agree_set_out _ _ _ _ w Hcs Hcv Hv Hag) H1.
exists t'; split=> //.
apply: (agree_trans _ _ t1).
  exact: (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Ha1).
exact: (agree_incl _ _ _ _ (after_scope_incl _ _) Ha').
Qed.

(* first_mention splits a block before the first statement that mentions v. *)
Lemma first_mention_spec v ss b m a :
  first_mention nat v ss = Some (b, m, a) -> ss = b ++ m :: a /\ existsb (mentions nat v) b = false.
Proof.
elim: ss b => [| st ss IH] b //=.
case Em: (mentions nat v st).
  by move=> [<- <- <-].
case E: (first_mention nat v ss) => [[[b' m'] a'] |] // [Eb Hm Ha].
subst b m a; have [-> Hb] := IH _ E.
by rewrite /= Em Hb.
Qed.

Fixpoint wdefs (ss : list (dstmt W)) : list (dvar W) :=
  match ss with
  | [] => []
  | DDefine (DConstant _) _ _ :: r => wdefs r
  | DDefine DMutable v _ :: r | DRealVar v :: r | DTape v :: r => v :: wdefs r
  | _ :: r => wdefs r
  end.

Lemma in_after_wr_iff y wr ss : In y (after_wr wr ss) <-> In y (wdefs ss) \/ In y wr.
Proof.
elim: ss wr => [| st r IH] wr /=; first by tauto.
by case: st => [[t |] v e | v | v | l e | l e | c t e | i lo hi b | i lo hi b
  | t e | t l | e] /=; rewrite IH /=; tauto.
Qed.

(* A block that does not mention v does not define it. *)
Lemma defs_unmentioned v ss : existsb (mentions nat v) ss = false -> ~ In v (defs ss).
Proof.
elim: ss => [| st r IH] /=; first by move=> _ [].
move/orb_false_iff => [Hs /IH Hr].
case: st Hs => [s x e | x | x | l e | l e | c t e | i lo hi b | i lo hi b
  | t e | t l | e] //= Hs; case=> // E; subst x;
  by rewrite dvar_eq_refl in Hs.
Qed.

(* A mutable that starts at zero, accumulated once before any other use, is
   defined at that accumulation: 0 + e = e, and the statements before it do
   not mention it. *)
Lemma fuse_fused sc wr v before x e after so :
  gd sc wr (DDefine DMutable v (DReal "0") :: before ++ DIncrement (DVar x) e :: after) ->
  incl wr sc -> Forall consistent sc ->
  existsb (mentions nat v) before = false -> dvar_eq nat x v = true -> mentions_expr nat v e = false ->
  so = DMutable \/ (so = DConstant Real /\ existsb (writes nat v) after = false) ->
  gd sc wr (before ++ DDefine so v e :: after) /\
  sim sc (DDefine DMutable v (DReal "0") :: before ++ DIncrement (DVar x) e :: after)
         (before ++ DDefine so v e :: after).
Proof.
move=> Hg Hwr Hcs Hb Hx He Hso.
inversion Hg as [| | ? ? ? ? ? He0 Hv Hcv Hrest | | | | | | | |]; subst.
have [Hbefore Hi] := gd_app_inv _ _ _ _ Hrest.
inversion Hi as [| | | | | | ? ? ? ? ? Hlx Hee Hafter | | | |]; subst.
set SB := after_scope sc before; set WB := after_wr wr before.
have Hcs' : Forall consistent (v :: sc) by constructor.
have Hc_after : Forall consistent (after_scope (v :: sc) before).
  exact: after_consistent Hbefore Hcs'.
(* the accumulated variable is v *)
have Hxv : x = v.
  apply: dvar_eq_true_eq => //; move/Forall_forall: Hc_after; apply.
  exact: (after_incl (v :: wr) (v :: sc) before (incl_both _ _ _ Hwr)).
subst x.
have HvSB : ~ In v SB.
  rewrite /SB in_after_scope => -[Hin | Hin] //.
  exact: defs_unmentioned Hb Hin.
have Hscope : forall y,
    In y (after_scope (v :: sc) before) <-> In y (v :: SB).
  by move=> y; rewrite /SB in_after_scope /= in_after_scope; tauto.
have Hwscope : forall y, In y (after_wr (v :: wr) before) <-> In y (v :: WB).
  by move=> y; rewrite /WB in_after_wr_iff /= in_after_wr_iff; tauto.
(* the new block is good *)
have Hbefore' : gd sc wr before.
  apply: (gd_remove _ _ _ v Hbefore Hb).
  - by move=> y Hy [Eyv | Hin] //; case: Hy.
  - by move=> y Hy [Eyv | Hin] //; case: Hy.
  exact/incl_tl/incl_refl.
have HeSB : expr_ok SB e.
  apply: (expr_ok_remove _ _ _ _ Hee He) => y Hy /Hscope [E | Hin] //.
  by case: Hy.
have Hafter' : gd (v :: SB) (v :: WB) after.
  by apply: (gd_mono _ _ _ Hafter) => y Hin; [apply/Hscope | apply/Hscope
    | apply/Hwscope].
have HWB : incl WB SB by apply: after_incl.
have [wr' [Hafter_new [Hwr' Hdef]]] : exists wr', gd (v :: SB) wr' after /\
    incl wr' (v :: SB) /\ gd SB WB (DDefine so v e :: after).
  case: Hso => [-> | [-> Hw]].
    exists (v :: WB); split=> //; split; first exact: incl_both.
    exact: GdMutable.
  have Hafter'' : gd (v :: SB) WB after.
    apply: (gd_drop_wr _ _ _ v Hafter' Hw) => y Hy [Eyv | Hin] //.
    by case: Hy.
  exists WB; split=> //; split; first exact: incl_tl.
  exact: GdConstant.
split; first exact: gd_app.
(* the simulation *)
move=> s s' t Hag.
rewrite ex_cons exec_define; cbn [out_dexpr].
rewrite (xeval_real s "0" 0 lit_0) ex_app.
set s1 := store_set s (KVar (out v)) (VReal 0).
case E2: (ex before s1) => [s2 |] // H.
have Hv2 : store_get s2 (KVar (out v)) = Some (VReal 0).
  rewrite (preserve_unmentioned _ _ _ v Hbefore (incl_both _ _ _ Hwr) Hcs' Hcv
    Hb _ _ E2).
  exact: get_set_same.
have [s2' [E2' Hag2]] := frame _ _ _ Hbefore' Hwr _ _ _
  (agree_set_out _ _ _ _ _ Hcs Hcv Hv Hag) E2.
move: H; rewrite ex_cons exec_increment; cbn [out_dexpr xeval]; rewrite Hv2.
case Eb: (xeval reals s2 (oute e)) => [[b | | | |] |] //.
cbn [assign out_dexpr]; rewrite Rplus_0_l => H.
rewrite ex_app E2' ex_cons exec_define -(xeval_agree _ _ _ _ HeSB Hag2) Eb.
have [t' [H' Ha']] := frame _ _ _ Hafter_new Hwr' _ _ _
  (agree_set_cons _ _ _ v (VReal b) Hag2) H.
exists t'; split=> //.
apply: (agree_incl sc (after_scope (v :: SB) after)) Ha' => y Hy.
by apply: after_scope_incl; right; apply: after_scope_incl.
Qed.

(* ---------------------------------------------------------------------------
   Propagating a literal constant: replacing the constant by its literal in
   the rest of the block, where it is never assigned, reads the same values. *)

(* Agreement on the scope but one variable. *)
Definition agree_ex (v : dvar W) (sc : list (dvar W)) (s s' : store) : Prop :=
  (forall y, In y sc -> y <> v -> store_get s (KVar (out y)) = store_get s' (KVar (out y))) /\
  store_get s Returned = store_get s' Returned.

Lemma agree_ex_set_cons v sc s s' y w :
  agree_ex v sc s s' -> agree_ex v (y :: sc) (store_set s (KVar (out y)) w) (store_set s' (KVar (out y)) w).
Proof.
move=> [H R]; split; last by rewrite !get_set; case: (key_eqb _ _).
move=> z [<- | Hz] Hzv; rewrite !get_set.
  by rewrite (proj2 (key_eqb_eq _ _) erefl).
by case: (key_eqb _ _); auto.
Qed.

Lemma agree_ex_set v sc s s' k w : agree_ex v sc s s' -> agree_ex v sc (store_set s k w) (store_set s' k w).
Proof.
move=> [H R]; split=> [z Hz Hzv |]; rewrite !get_set; case: (key_eqb _ _) => //.
exact: H.
Qed.

Lemma agree_ex_incl v sc1 sc2 s s' : incl sc1 sc2 -> agree_ex v sc2 s s' -> agree_ex v sc1 s s'.
Proof. by move=> Hi [H R]; split=> // y /Hi /H. Qed.

Section Replace.
Variables (v : dvar W) (l : string) (x : R).
Hypothesis Hcv : consistent v.
Hypothesis Hlit : real_lit l = Some x.

Local Notation re := (replace_expr nat v (DReal l)).
Local Notation rs := (replace_stmt nat v (DReal l)).

Lemma xeval_replace sc s s' e :
  expr_ok sc e -> Forall consistent sc -> agree_ex v sc s s' ->
  store_get s (KVar (out v)) = Some (VReal x) ->
  xeval reals s (oute e) = xeval reals s' (oute (re e)).
Proof.
move=> He Hcs Hag Hv.
elim: e He => [y | | | a IHa i IHi | f a IHa | f a IHa b IHb] //= He.
- case E: (dvar_eq nat y v).
    have Hcy : consistent y by move/Forall_forall: Hcs; apply.
    by rewrite (dvar_eq_true_eq _ _ Hcy Hcv E) Hv /= Hlit.
  exact: (proj1 Hag _ He (dvar_eq_false_neq _ _ E)).
- by case: He => Ha Hi; rewrite IHa ?IHi.
- by rewrite IHa.
by case: He => Ha Hb; rewrite IHa ?IHb.
Qed.

Lemma expr_ok_replace sc1 sc2 e :
  expr_ok sc1 e -> (forall y, y <> v -> In y sc1 -> In y sc2) -> expr_ok sc2 (re e).
Proof.
move=> He Hs; elim: e He => [y | | | | |] /=; try intuition.
by case E: (dvar_eq nat y v) => //=; apply: Hs => //; exact: dvar_eq_false_neq.
Qed.

(* A location assigned is writable, hence not the constant: unchanged by the replacement. *)
Lemma lhs_replace sc wr lh :
  lhs_ok sc wr lh -> incl wr sc -> Forall consistent sc -> ~ In v wr ->
  exists y i, In y wr /\ y <> v /\ (lh = DVar y /\ re lh = DVar y \/ lh = DAt (DVar y) i /\ re lh = DAt (DVar y) (re i)).
Proof.
move=> Hl Hwr Hcs Hv; case: lh Hl => [y | | | [y | | | | |] i | |] //= Hl.
  have Hyv : y <> v by move=> E; subst y.
  have Hcy : consistent y by move/Forall_forall: Hcs; apply; exact: Hwr.
  exists y, (DInt 0%Z); do 2!split=> //; left; split=> //=.
  by rewrite (neq_dvar_eq_false _ _ Hcy Hcv Hyv).
case: Hl => Hl Hi; have Hyv : y <> v by move=> E; subst y.
have Hcy : consistent y by move/Forall_forall: Hcs; apply; exact: Hwr.
exists y, i; do 2!split=> //; right; split=> //=.
by rewrite (neq_dvar_eq_false _ _ Hcy Hcv Hyv).
Qed.

Lemma lhs_ok_replace sc1 sc2 wr lh :
  lhs_ok sc1 wr lh -> incl wr sc1 -> Forall consistent sc1 -> ~ In v wr ->
  (forall y, y <> v -> In y sc1 -> In y sc2) -> lhs_ok sc2 wr (re lh).
Proof.
move=> Hl Hwr Hcs Hv Hs.
have [y [i [Hy [Hyv [[E ->] | [E ->]]]]]] := lhs_replace _ _ _ Hl Hwr Hcs Hv;
  subst lh => //=.
split=> //; case: Hl => _ Hi; exact: expr_ok_replace Hi Hs.
Qed.

(* The replaced block keeps the discipline, without the constant in scope. *)
Lemma gd_replace sc0 wr0 ss0 :
  gd sc0 wr0 ss0 -> Forall consistent sc0 -> In v sc0 -> ~ In v wr0 -> incl wr0 sc0 ->
  forall sc2, (forall y, y <> v -> In y sc0 -> In y sc2) -> incl sc2 sc0 -> gd sc2 wr0 (map rs ss0).
Proof.
have Hext : forall (z : dvar W) l1 l2,
    (forall y, y <> v -> In y l1 -> In y l2) ->
    forall y, y <> v -> In y (z :: l1) -> In y (z :: l2).
  by move=> z l1 l2 H y Hy [<- | Hin]; [left | right; apply: H].
have Hnew : forall (y : dvar W) sc wr,
    In v sc -> ~ In y sc -> ~ In v wr -> ~ In v (y :: wr).
  by move=> y sc wr Hvs Hy Hv [E | Hin] //; subst y.
elim=> {sc0 wr0 ss0} [sc wr | sc wr ty y e r He Hy Hcy Hr IH
       | sc wr y e r He Hy Hcy Hr IH | sc wr y r Hy Hcy Hr IH
       | sc wr y r Hy Hcy Hr IH | sc wr lh e r Hl He Hr IH
       | sc wr lh e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] Hcs Hvs Hv Hwr sc2 Hs Hb21; cbn [map].
- exact: GdNil.
- apply: GdConstant => //; first exact: expr_ok_replace He Hs.
    by move/Hb21.
  apply: (IH _ _ Hv (incl_tl _ Hwr) _ (Hext _ _ _ Hs) (incl_both _ _ _ Hb21)).
    by constructor.
  by right.
- apply: GdMutable => //; first exact: expr_ok_replace He Hs.
    by move/Hb21.
  apply: (IH _ _ (Hnew _ _ _ Hvs Hy Hv) (incl_both _ _ _ Hwr) _ (Hext _ _ _ Hs)
    (incl_both _ _ _ Hb21)).
    by constructor.
  by right.
- apply: GdRealVar => //; first by move/Hb21.
  apply: (IH _ _ (Hnew _ _ _ Hvs Hy Hv) (incl_both _ _ _ Hwr) _ (Hext _ _ _ Hs)
    (incl_both _ _ _ Hb21)).
    by constructor.
  by right.
- apply: GdTape => //; first by move/Hb21.
  apply: (IH _ _ (Hnew _ _ _ Hvs Hy Hv) (incl_both _ _ _ Hwr) _ (Hext _ _ _ Hs)
    (incl_both _ _ _ Hb21)).
    by constructor.
  by right.
- apply: GdAssign; last exact: IH.
    exact: lhs_ok_replace Hl Hwr Hcs Hv Hs.
  exact: expr_ok_replace He Hs.
- apply: GdIncrement; last exact: IH.
    exact: lhs_ok_replace Hl Hwr Hcs Hv Hs.
  exact: expr_ok_replace He Hs.
- apply: GdBranch; [exact: expr_ok_replace Hc Hs | exact: IHt | exact: IHe
                   | exact: IH].
- apply: GdFor => //; first by move/Hb21.
  - exact: expr_ok_replace Hlo Hs.
  - exact: expr_ok_replace Hhi Hs.
  - apply: (IHb _ _ Hv (incl_tl _ Hwr) _ (Hext _ _ _ Hs)
      (incl_both _ _ _ Hb21)).
      by constructor.
    by right.
  exact: IH.
- apply: GdForBack => //; first by move/Hb21.
  - exact: expr_ok_replace Hlo Hs.
  - exact: expr_ok_replace Hhi Hs.
  - apply: (IHb _ _ Hv (incl_tl _ Hwr) _ (Hext _ _ _ Hs)
      (incl_both _ _ _ Hb21)).
      by constructor.
    by right.
  exact: IH.
apply: GdReturn; last exact: IH.
exact: expr_ok_replace He Hs.
Qed.

(* An assignment to a writable location, from stores agreeing but on the
   constant, keeps the agreement and the constant. *)
Lemma assign_replace sc wr lh w s s' t :
  lhs_ok sc wr lh -> incl wr sc -> Forall consistent sc -> ~ In v wr ->
  agree_ex v sc s s' -> store_get s (KVar (out v)) = Some (VReal x) ->
  assign reals s (oute lh) w = Some t ->
  exists t', assign reals s' (oute (re lh)) w = Some t' /\ agree_ex v sc t t' /\
             store_get t (KVar (out v)) = Some (VReal x).
Proof.
move=> Hl Hwr Hcs Hv Hag Hx.
have [y [i [Hy [Hyv [[E Er] | [E Er]]]]]] := lhs_replace _ _ _ Hl Hwr Hcs Hv;
  rewrite Er; subst lh.
  have Hcy : consistent y by move/Forall_forall: Hcs; apply; exact: Hwr.
  move=> /= [<-]; exists (store_set s' (KVar (out y)) w).
  split=> //; split; first exact: agree_ex_set.
  by rewrite get_set_other //; apply: key_neq.
case: Hl => _ Hi; case: w => [e | | | |] //=.
rewrite -(proj1 Hag y (Hwr _ Hy) Hyv) -(xeval_replace sc s s' i Hi Hcs Hag Hx).
case: (store_get s (KVar (out y))) => [[| | | l0 |] |] //.
case: (xeval reals s (oute i)) => [[| k | | |] |] //.
case: (replace_nth_z k e l0) => [l1 |] // [<-].
exists (store_set s' (KVar (out y)) (VArray l1)).
split=> //; split; first exact: agree_ex_set.
have Hcy : consistent y by move/Forall_forall: Hcs; apply; exact: Hwr.
by rewrite get_set_other //; apply: key_neq.
Qed.

(* The replaced block, from stores agreeing but on the constant, which holds
   its literal, runs as the original: the constant is never assigned, and
   every read of it is replaced by its literal. *)
Lemma replace_sim sc0 wr0 ss0 :
  gd sc0 wr0 ss0 -> incl wr0 sc0 -> Forall consistent sc0 -> In v sc0 -> ~ In v wr0 ->
  forall s s' t, agree_ex v sc0 s s' -> store_get s (KVar (out v)) = Some (VReal x) -> ex ss0 s = Some t ->
  exists t', ex (map rs ss0) s' = Some t' /\ agree_ex v (after_scope sc0 ss0) t t' /\
             store_get t (KVar (out v)) = Some (VReal x).
Proof.
have Hnew : forall (y : dvar W) sc wr,
    In v sc -> ~ In y sc -> ~ In v wr -> ~ In v (y :: wr).
  by move=> y sc wr Hvs Hy Hv [E | Hin] //; subst y.
have Hdef : forall (y : dvar W) sc s w, Forall consistent sc -> consistent y ->
    In v sc -> ~ In y sc -> store_get s (KVar (out v)) = Some (VReal x) ->
    store_get (store_set s (KVar (out y)) w) (KVar (out v)) = Some (VReal x).
  move=> y sc s w Hcs Hcy Hvs Hy Hx; rewrite get_set_other //.
  by apply: key_neq => // E; subst y.
elim=> {sc0 wr0 ss0} [sc wr | sc wr ty y e r He Hy Hcy Hr IH
       | sc wr y e r He Hy Hcy Hr IH | sc wr y r Hy Hcy Hr IH
       | sc wr y r Hy Hcy Hr IH | sc wr lh e r Hl He Hr IH
       | sc wr lh e r Hl He Hr IH | sc wr c t e r Hc Ht IHt He IHe Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
       | sc wr e r He Hr IH] Hwr Hcs Hvs Hv s s' t0 Hag Hx H;
  cbn [map after_scope]; rewrite ?ex_cons in H *; cbn [replace_stmt].
- by case: H => <-; exists s'.
- rewrite !exec_define in H *; rewrite -(xeval_replace _ _ _ _ He Hcs Hag Hx).
  case: (xeval reals s (oute e)) H => [w |] // H.
  exact: (IH (incl_tl _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs) Hv _ _ _
    (agree_ex_set_cons _ _ _ _ _ _ Hag) (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
- rewrite !exec_define in H *; rewrite -(xeval_replace _ _ _ _ He Hcs Hag Hx).
  case: (xeval reals s (oute e)) H => [w |] // H.
  exact: (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs)
    (Hnew _ _ _ Hvs Hy Hv) _ _ _ (agree_ex_set_cons _ _ _ _ _ _ Hag)
    (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
- rewrite !exec_realvar in H *.
  exact: (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs)
    (Hnew _ _ _ Hvs Hy Hv) _ _ _ (agree_ex_set_cons _ _ _ _ _ _ Hag)
    (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
- rewrite !exec_tape in H *.
  exact: (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs)
    (Hnew _ _ _ Hvs Hy Hv) _ _ _ (agree_ex_set_cons _ _ _ _ _ _ Hag)
    (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
- rewrite !exec_assign in H *; rewrite -(xeval_replace _ _ _ _ He Hcs Hag Hx).
  case: (xeval reals s (oute e)) H => [w |] //.
  case E: (assign reals s (oute lh) w) => [s1 |] // H.
  have [s1' [-> [Hag1 Hx1]]] :=
    assign_replace _ _ _ _ _ _ _ Hl Hwr Hcs Hv Hag Hx E.
  exact: (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H).
- rewrite !exec_increment in H *.
  rewrite -(xeval_replace _ _ _ _ He Hcs Hag Hx).
  rewrite -(xeval_replace _ _ _ _ (lhs_expr_ok _ _ _ Hwr Hl) Hcs Hag Hx).
  case: (xeval reals s (oute lh)) H => [[a | | | |] |] //.
  case: (xeval reals s (oute e)) => [[b | | | |] |] //.
  case E: (assign reals s (oute lh) _) => [s1 |] // H.
  have [s1' [-> [Hag1 Hx1]]] :=
    assign_replace _ _ _ _ _ _ _ Hl Hwr Hcs Hv Hag Hx E.
  exact: (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H).
- rewrite !exec_branch in H *; rewrite -(xeval_replace _ _ _ _ Hc Hcs Hag Hx).
  case: (xeval reals s (oute c)) H => [[| | [] | |] |] //.
    case E: (ex t s) => [s1 |] // H.
    have [s1' [-> [Hag1 Hx1]]] := IHt Hwr Hcs Hvs Hv _ _ _ Hag Hx E.
    exact: (IH Hwr Hcs Hvs Hv _ _ _
      (agree_ex_incl _ _ _ _ _ (after_scope_incl _ _) Hag1) Hx1 H).
  case E: (ex e s) => [s1 |] // H.
  have [s1' [-> [Hag1 Hx1]]] := IHe Hwr Hcs Hvs Hv _ _ _ Hag Hx E.
  exact: (IH Hwr Hcs Hvs Hv _ _ _
    (agree_ex_incl _ _ _ _ _ (after_scope_incl _ _) Hag1) Hx1 H).
- rewrite !exec_for in H *.
  rewrite -(xeval_replace _ _ _ _ Hlo Hcs Hag Hx).
  rewrite -(xeval_replace _ _ _ _ Hhi Hcs Hag Hx).
  case: (xeval reals s (oute lo)) H => [[| l0 | | |] |] //.
  case: (xeval reals s (oute hi)) => [[| h | | |] |] //.
  case E: (exec_up R (ex b) (out i) l0 (count l0 h) s) => [s1 |] // H.
  pose Rin u u' := agree_ex v sc u u' /\
    store_get u (KVar (out v)) = Some (VReal x).
  pose Rb u u' := agree_ex v (i :: sc) u u' /\
    store_get u (KVar (out v)) = Some (VReal x).
  have Hset : forall u u' w, Rin u u' ->
      Rb (store_set u (KVar (out i)) w) (store_set u' (KVar (out i)) w).
    move=> u u' w [Hu Hxu]; split; first exact: agree_ex_set_cons.
    exact: (Hdef _ _ _ _ Hcs Hci Hvs Hi Hxu).
  have Hbody : forall u u' w, Rb u u' -> ex b u = Some w ->
      exists w', ex (map rs b) u' = Some w' /\ Rin w w'.
    move=> u u' w [Hu Hxu] Hw.
    have [w' [Hw' [Hag' Hx']]] := IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs)
      (or_intror Hvs) Hv _ _ _ Hu Hxu Hw.
    exists w'; split=> //; split=> //.
    exact: (agree_ex_incl _ _ _ _ _
      (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hag').
  have [s1' [-> [Hag1 Hx1]]] := exec_up_sim Rin Rb (ex b) (ex (map rs b))
    (out i) Hset Hbody _ _ _ _ _ (conj Hag Hx) E.
  exact: (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H).
- rewrite !exec_forback in H *.
  rewrite -(xeval_replace _ _ _ _ Hlo Hcs Hag Hx).
  rewrite -(xeval_replace _ _ _ _ Hhi Hcs Hag Hx).
  case: (xeval reals s (oute lo)) H => [[| l0 | | |] |] //.
  case: (xeval reals s (oute hi)) => [[| h | | |] |] //.
  case E: (exec_down R (ex b) (out i) (h - 1) (count l0 h) s)
    => [s1 |] // H.
  pose Rin u u' := agree_ex v sc u u' /\
    store_get u (KVar (out v)) = Some (VReal x).
  pose Rb u u' := agree_ex v (i :: sc) u u' /\
    store_get u (KVar (out v)) = Some (VReal x).
  have Hset : forall u u' w, Rin u u' ->
      Rb (store_set u (KVar (out i)) w) (store_set u' (KVar (out i)) w).
    move=> u u' w [Hu Hxu]; split; first exact: agree_ex_set_cons.
    exact: (Hdef _ _ _ _ Hcs Hci Hvs Hi Hxu).
  have Hbody : forall u u' w, Rb u u' -> ex b u = Some w ->
      exists w', ex (map rs b) u' = Some w' /\ Rin w w'.
    move=> u u' w [Hu Hxu] Hw.
    have [w' [Hw' [Hag' Hx']]] := IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs)
      (or_intror Hvs) Hv _ _ _ Hu Hxu Hw.
    exists w'; split=> //; split=> //.
    exact: (agree_ex_incl _ _ _ _ _
      (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hag').
  have [s1' [-> [Hag1 Hx1]]] := exec_down_sim Rin Rb (ex b) (ex (map rs b))
    (out i) Hset Hbody _ _ _ _ _ (conj Hag Hx) E.
  exact: (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H).
rewrite !exec_return in H *; rewrite -(xeval_replace _ _ _ _ He Hcs Hag Hx).
case: (xeval reals s (oute e)) H => [w |] // H.
apply: (IH Hwr Hcs Hvs Hv _ _ _ (agree_ex_set _ _ _ _ _ _ Hag) _ H).
by rewrite get_set_other.
Qed.

End Replace.

Lemma xeval_real_inv s l w : xeval reals s (DReal l) = Some w -> exists x, real_lit l = Some x /\ w = VReal x.
Proof.
change (xeval reals s (DReal l))
  with (match real_lit l with Some x => Some (VReal x) | None => None end).
by case: (real_lit l) => [x |] // [<-]; exists x.
Qed.

(* A constant defined by a literal is replaced by the literal in the rest of
   the block, and its definition dropped. *)
Lemma fuse_literal sc wr t v l r :
  gd sc wr (DDefine (DConstant t) v (DReal l) :: r) -> incl wr sc -> Forall consistent sc ->
  gd sc wr (map (replace_stmt nat v (DReal l)) r) /\
  sim sc (DDefine (DConstant t) v (DReal l) :: r) (map (replace_stmt nat v (DReal l)) r).
Proof.
move=> Hg Hwr Hcs.
inversion Hg as [| ? ? ? ? ? ? He Hv Hcv Hr | | | | | | | | |]; subst.
have Hvw : ~ In v wr by move/Hwr.
split.
  apply: (gd_replace v l Hcv (v :: sc) wr r Hr (Forall_cons _ Hcv Hcs)
    (or_introl erefl) Hvw (incl_tl _ Hwr) sc); last exact/incl_tl/incl_refl.
  by move=> y Hy [Eyv | Hin] //; case: Hy.
move=> s s' t0 Hag; rewrite ex_cons exec_define; cbn [out_dexpr].
case Ew: (xeval reals s (DReal l)) => [w |] // H.
have [x [Hlit Ew']] := xeval_real_inv _ _ _ Ew; subst w.
set s1 := store_set s (KVar (out v)) (VReal x) in H.
have Hag1 : agree_ex v (v :: sc) s1 s'.
  split; last by rewrite /s1 get_set_other //; exact: (proj2 Hag).
  move=> y [Eyv | Hy] Hyv; first by case: Hyv.
  have Hneq : KVar (out v) <> KVar (out y).
    apply: key_neq; [exact: Hcv | by move/Forall_forall: Hcs; apply |].
    by move=> E; apply: Hyv; rewrite E.
  by rewrite /s1 (get_set_other _ _ _ _ Hneq); exact: (proj1 Hag _ Hy).
have [t' [H' [Ha' _]]] := replace_sim v l x Hcv Hlit (v :: sc) wr r Hr
  (incl_tl _ Hwr) (Forall_cons _ Hcv Hcs) (or_introl erefl) Hvw s1 s' t0 Hag1
  (get_set_same _ _ _) H.
exists t'; split=> //; split; last exact: (proj2 Ha').
move=> y Hy; apply: (proj1 Ha'); first by apply: after_scope_incl; right.
by move=> E; subst y.
Qed.

(* ---------------------------------------------------------------------------
   fuse and simplify are correct, by induction on the fuel. *)

(* A statement kept in front of the fused rest. *)
Lemma fuse_keep n sc wr st r :
  correct (fuse nat n) -> gd sc wr (st :: r) -> incl wr sc -> Forall consistent sc ->
  gd sc wr (st :: fuse nat n r) /\ sim sc (st :: r) (st :: fuse nat n r).
Proof.
move=> HC Hg Hwr Hcs; have [Hst Hr] := gd_app_inv sc wr [st] r Hg.
have [Hg' Hs'] :=
  HC _ _ _ Hr (after_incl _ _ _ Hwr) (after_consistent _ _ _ Hst Hcs).
split; first exact: (gd_app sc wr [st] _ Hst Hg').
exact: (sim_keep _ _ _ _ _ Hg Hwr Hs').
Qed.

Lemma correct_compose f g : correct f -> correct g -> correct (fun ss => g (f ss)).
Proof.
move=> Hf Hg sc wr ss Hss Hwr Hcs; have [Hf1 Hf2] := Hf _ _ _ Hss Hwr Hcs.
have [Hg1 Hg2] := Hg _ _ _ Hf1 Hwr Hcs.
by split=> //; exact: sim_trans Hf2 Hg2.
Qed.

(* The mutable case of fuse, when no accumulation is fused: the definition is
   kept, or dropped when the rest does not mention it. *)
Lemma fuse_mutable_fallback n sc wr v e r :
  correct (fuse nat n) -> gd sc wr (DDefine DMutable v e :: r) -> incl wr sc -> Forall consistent sc ->
  let r' := if negb (existsb (mentions nat v) r) then fuse nat n r else DDefine DMutable v e :: fuse nat n r in
  gd sc wr r' /\ sim sc (DDefine DMutable v e :: r) r'.
Proof.
move=> HC Hg Hwr Hcs r'; rewrite /r'.
case Em: (existsb (mentions nat v) r) => /=.
  exact: (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs).
inversion Hg as [| | ? ? ? ? ? He Hv Hcv Hr | | | | | | | |]; subst.
have Hr' : gd sc wr r.
  apply: (gd_remove _ _ _ v Hr Em).
  - by move=> y Hy [Eyv | Hin] //; case: Hy.
  - by move=> y Hy [Eyv | Hin] //; case: Hy.
  exact/incl_tl/incl_refl.
have [Hg' Hs'] := HC _ _ _ Hr' Hwr Hcs.
by split=> //; exact: (sim_drop_define _ _ _ _ _ _ Hv Hcv Hcs Hs').
Qed.

(* The constant case of fuse, for an expression that is not a literal: the
   definition is kept, or dropped when the fused rest does not mention it. *)
Lemma fuse_constant_other n sc wr t v e r :
  correct (fuse nat n) -> gd sc wr (DDefine (DConstant t) v e :: r) -> incl wr sc -> Forall consistent sc ->
  let r' := fuse nat n r in
  let res := if existsb (mentions nat v) r' then DDefine (DConstant t) v e :: r' else r' in
  gd sc wr res /\ sim sc (DDefine (DConstant t) v e :: r) res.
Proof.
move=> HC Hg Hwr Hcs r' res; rewrite /res /r'.
case Em: (existsb (mentions nat v) (fuse nat n r)).
  exact: (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs).
inversion Hg as [| ? ? ? ? ? ? He Hv Hcv Hr | | | | | | | | |]; subst.
have [Hg' Hs'] := HC _ _ _ Hr (incl_tl _ Hwr) (Forall_cons _ Hcv Hcs).
have Hg'' : gd sc wr (fuse nat n r).
  apply: (gd_remove _ _ _ v Hg' Em).
  - by move=> y Hy [Eyv | Hin] //; case: Hy.
  - by [].
  exact/incl_tl/incl_refl.
split=> //.
exact: (sim_drop_define_after _ _ _ _ _ _ _ Hv Hcv Hcs Hwr Hs' Hg'').
Qed.

(* One more unit of fuel for fuse. *)
Lemma fuse_correct_step n :
  correct (fuse nat n) -> correct (simplify_stmts nat n) -> correct (fuse nat (S n)).
Proof.
move=> HC HA sc wr ss Hg Hwr Hcs; case: ss Hg => [| st r] Hg.
  by split=> [| s s' t Hag [<-]]; [exact: GdNil | exists s'].
case: st Hg => [[t |] v e | v | v | l e | l e | c t e | i lo hi b | i lo hi b
  | t e | t l | e] Hg; cbn [fuse];
  try exact: (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs).
- (* a constant *)
  case: e Hg => [y | l | k | a i | f a | f a b] Hg;
    try exact: (fuse_constant_other _ _ _ _ _ _ _ HC Hg Hwr Hcs).
  have [Hg1 Hs1] := fuse_literal _ _ _ _ _ _ Hg Hwr Hcs.
  have [Hg2 Hs2] := HA _ _ _ Hg1 Hwr Hcs.
  by split=> //; exact: sim_trans Hs1 Hs2.
- (* a mutable *)
  case E0: (is_lit nat "0" e); last exact: (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs).
  move/is_lit_eq: E0 => E0; subst e.
  case Fm: (first_mention nat v r) => [[[b m] a] |];
    last exact: (fuse_mutable_fallback _ _ _ _ _ _ HC Hg Hwr Hcs).
  case: m Fm => [? ? ? | ? | ? | ? ? | [x | ? | ? | ? ? | ? ? | ? ? ?] e
    | ? ? ? | ? ? ? ? | ? ? ? ? | ? ? | ? ? | ?] Fm;
    try exact: (fuse_mutable_fallback _ _ _ _ _ _ HC Hg Hwr Hcs).
  case Ec: (dvar_eq nat x v && ~~ mentions_expr nat v e);
    last exact: (fuse_mutable_fallback _ _ _ _ _ _ HC Hg Hwr Hcs).
  move/andP: Ec => [Hx /negbTE He].
  have [Er Hb] := first_mention_spec _ _ _ _ _ Fm; subst r.
  set so := if existsb (writes nat v) a then DMutable else DConstant Real.
  have Hso : so = DMutable \/
      (so = DConstant Real /\ existsb (writes nat v) a = false).
    by rewrite /so; case: (existsb (writes nat v) a); [left | right].
  have [Hg1 Hs1] := fuse_fused _ _ _ _ _ _ _ so Hg Hwr Hcs Hb Hx He Hso.
  have [Hg2 Hs2] := HC _ _ _ Hg1 Hwr Hcs.
  by split=> //; exact: sim_trans Hs1 Hs2.
(* an accumulation *)
case E0: (is_lit nat "0" e); last exact: (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs).
move/is_lit_eq: E0 => E0; subst e.
inversion Hg as [| | | | | | ? ? ? ? ? Hl He Hr | | | |]; subst.
have [Hg' Hs'] := HC _ _ _ Hr Hwr Hcs.
by split=> //; exact: (sim_zero_increment _ _ _ _ _ Hg Hs').
Qed.

Lemma map_simplify_stmt_0 ss : map (simplify_stmt nat 0) ss = ss.
Proof.
elim: ss => [| s ss IH] //.
change (simplify_stmt nat 0 s :: map (simplify_stmt nat 0) ss = s :: ss).
by rewrite IH.
Qed.

(* simplify_stmts, fuse and the simplification of each statement are
   correct at every fuel. *)
Theorem simplify_correct_fuel n :
  correct (simplify_stmts nat n) /\ correct (fuse nat n) /\ correct (map (simplify_stmt nat n)).
Proof.
elim: n => [| n [HA [HC HM]]].
  split; [| split]; rewrite /correct => sc wr ss;
    [exact: (id_correct sc wr ss) | exact: (id_correct sc wr ss) |].
  by rewrite map_simplify_stmt_0; exact: (id_correct sc wr ss).
split; first exact: (correct_compose _ _ HM HC).
split; first exact: (fuse_correct_step _ HC HA).
exact: (simplify_stmt_correct _ HA).
Qed.

(* ---------------------------------------------------------------------------
   The function: simplify opens its variables as open_pairs does, then
   simplifies the body. *)

Lemma exec_simplify_scoped (sc : scoped W (dbody W)) k args :
  exec_scoped reals (simplify_scoped nat sc k) k args =
  match fst (open_pairs sc k) with
  | DBody r ps ss =>
      exec_scoped reals (Done (DBody r (map (out_dparam nat) ps)
                                      (map outs (simplify_stmts nat (fuel nat ss) ss)))) 0 args
  end.
Proof. by elim: sc k => [n f IH | p f IH | [r ps ss]] k /=. Qed.

(* The variables of the parameters. *)
Definition params (ps : list (dparam W)) : list (dvar W) := map (fun '(DParam _ _ x) => x) ps.

Lemma finals_agree ps s1 s1' :
  agree (params ps) s1 s1' ->
  map (fun '(DParam _ _ x) => store_get s1 (KVar x)) (map (out_dparam nat) ps) =
  map (fun '(DParam _ _ x) => store_get s1' (KVar x)) (map (out_dparam nat) ps).
Proof.
elim: ps => [| [pw t x] ps IH] Hag //=.
rewrite (proj1 Hag x (or_introl erefl)) IH //.
exact: (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Hag).
Qed.

(* A body whose statements are refined, on the variables of the parameters
   and the returned value, returns the same results. *)
Lemma exec_done_sim r ps ss1 ss2 args res :
  (forall s0 s1, ex ss1 s0 = Some s1 -> exists s1', ex ss2 s0 = Some s1' /\ agree (params ps) s1 s1') ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map outs ss1))) 0 args = Some res ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map outs ss2))) 0 args = Some res.
Proof.
move=> Hsim; cbn [exec_scoped].
case: (negb _) => //.
case E: (exec_stmts reals (map outs ss1) _) => [s1 |] // H.
have [s1' [E' Hag]] := Hsim _ _ E; rewrite /ex in E'; rewrite E'.
rewrite -(finals_agree ps s1 s1' Hag).
by case: r H => H; rewrite -?(proj2 Hag).
Qed.

(* The correctness of simplify: it preserves what a function
   computes over the reals. Let the body of g, opened with the pairs (k, k),
   be ps (the parameters) and ss (the statements); when ss follows the
   discipline of the variables (`good`, the parameters in scope and writable)
   and pushes and pops no tape, and the body run on args gives res, the
   simplified function run on args gives res: the same final parameters and
   the same returned value. Each rewrite of simplify is a real identity, a
   reordering of statements on different variables, or the removal of a
   definition that is no longer read (the simulation above). *)
Theorem simplify_correct (g : dfunction) (args : list (val R)) r ps ss k res :
  open_pairs (dfbody g W) 0 = (DBody r ps ss, k) ->
  Forall consistent (params ps) ->
  good (params ps) (params ps) ss ->
  existsb has_tape_op ss = false ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map outs ss))) 0 args = Some res ->
  exec_dfunction reals (simplify g) args = Some res.
Proof.
move=> Hopen Hc Hg Ht H.
rewrite /exec_dfunction /simplify; cbn [dfbody].
rewrite exec_simplify_scoped.
change (open_pairs (dfbody g (nat * nat)) 0)
  with (open_pairs (dfbody g W) 0).
rewrite Hopen; cbn [fst].
apply: (exec_done_sim r ps ss) H => s0 s1 E.
have [_ Hs] := proj1 (simplify_correct_fuel (fuel nat ss)) _ _ _
  (good_gd _ _ _ Hg Ht) (incl_refl _) Hc.
exact: (Hs _ _ _ (agree_refl _ _) E).
Qed.
