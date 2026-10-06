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
Proof. reflexivity. Qed.

Lemma ex_app a b s :
  ex (a ++ b) s = match ex a s with Some s1 => ex b s1 | None => None end.
Proof.
  revert s; induction a as [| st a IH]; intros s; [reflexivity |].
  simpl app; rewrite !ex_cons; destruct (exec reals (outs st) s); auto.
Qed.

(* ---------------------------------------------------------------------------
   The store. *)

(* The equality of the variables of the evaluator decides equality. *)
Lemma dvar_eqb_eq (a b : dvar nat) : dvar_eqb a b = true <-> a = b.
Proof.
  revert b; induction a as [x | a IH | a IH | a IH |]; intros [y | b | b | b |]; simpl;
    split; intros H; try discriminate; try reflexivity.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply Nat.eqb_refl.
  - apply IH in H; subst; reflexivity.
  - injection H as ->; apply IH; reflexivity.
  - apply IH in H; subst; reflexivity.
  - injection H as ->; apply IH; reflexivity.
  - apply IH in H; subst; reflexivity.
  - injection H as ->; apply IH; reflexivity.
Qed.

Lemma key_eqb_eq (a b : key) : key_eqb a b = true <-> a = b.
Proof.
  destruct a as [x |], b as [y |]; simpl; split; intros H; try discriminate; auto.
  - apply dvar_eqb_eq in H; subst; reflexivity.
  - injection H as ->; apply dvar_eqb_eq; reflexivity.
Qed.

(* Reading a store just written. *)
Lemma get_set (s : store) x v y :
  store_get (store_set s x v) y = if key_eqb x y then Some v else store_get s y.
Proof.
  induction s as [| [k w] s IH]; simpl.
  - destruct (key_eqb x y); reflexivity.
  - destruct (key_eqb k x) eqn:Ekx; simpl.
    + apply key_eqb_eq in Ekx; subst k; destruct (key_eqb x y); reflexivity.
    + destruct (key_eqb k y) eqn:Eky.
      * apply key_eqb_eq in Eky; subst k.
        destruct (key_eqb x y) eqn:Exy; [| reflexivity].
        apply key_eqb_eq in Exy; subst; rewrite (proj2 (key_eqb_eq y y) eq_refl) in Ekx; discriminate.
      * exact IH.
Qed.

Lemma get_set_same (s : store) x v : store_get (store_set s x v) x = Some v.
Proof. rewrite get_set, (proj2 (key_eqb_eq x x) eq_refl); reflexivity. Qed.

Lemma get_set_other (s : store) x v y : x <> y -> store_get (store_set s x v) y = store_get s y.
Proof.
  intros H; rewrite get_set; destruct (key_eqb x y) eqn:E; [| reflexivity].
  apply key_eqb_eq in E; contradiction.
Qed.

(* ---------------------------------------------------------------------------
   Consistent variables: the first number of a pair is the second, so
   simplify's comparison (dvar_eq, on the first numbers) is the equality of
   the variables of the evaluator (out_dvar, the second numbers). *)

Lemma out_inj a b : consistent a -> consistent b -> out a = out b -> a = b.
Proof.
  revert b; induction a as [[i j] | a IH | a IH | a IH |]; intros [[i' j'] | b | b | b |];
    simpl; intros Ha Hb H; try discriminate; auto.
  - injection H as ->; subst; reflexivity.
  - injection H as H; f_equal; auto.
  - injection H as H; f_equal; auto.
  - injection H as H; f_equal; auto.
Qed.

Lemma dvar_eq_refl a : dvar_eq nat a a = true.
Proof. induction a as [[i j] | | | |]; simpl; auto; apply Nat.eqb_refl. Qed.

(* dvar_eq says false only of different variables. *)
Lemma dvar_eq_false_neq a b : dvar_eq nat a b = false -> a <> b.
Proof. intros H ->; rewrite dvar_eq_refl in H; discriminate. Qed.

(* On consistent variables, dvar_eq says true only of equal ones. *)
Lemma dvar_eq_true_eq a b : consistent a -> consistent b -> dvar_eq nat a b = true -> a = b.
Proof.
  revert b; induction a as [[i j] | a IH | a IH | a IH |]; intros [[i' j'] | b | b | b |];
    simpl; intros Ha Hb H; try discriminate; auto.
  - apply Nat.eqb_eq in H; subst; reflexivity.
  - f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

Lemma neq_dvar_eq_false a b : consistent a -> consistent b -> a <> b -> dvar_eq nat a b = false.
Proof.
  intros Ha Hb H; destruct (dvar_eq nat a b) eqn:E; [| reflexivity].
  exfalso; exact (H (dvar_eq_true_eq _ _ Ha Hb E)).
Qed.

(* Two different consistent variables are different keys of the store. *)
Lemma key_neq a b : consistent a -> consistent b -> a <> b -> KVar (out a) <> KVar (out b).
Proof. intros Ha Hb H E; injection E as E; exact (H (out_inj _ _ Ha Hb E)). Qed.

(* ---------------------------------------------------------------------------
   The literals simplify introduces or recognizes, as the reals read them. *)

Lemma lit_0 : real_lit "0" = Some 0.
Proof. unfold real_lit; vm_compute read_literal; unfold Q2R; simpl; f_equal; field. Qed.

Lemma lit_1 : real_lit "1" = Some 1.
Proof. unfold real_lit; vm_compute read_literal; unfold Q2R; simpl; f_equal; field. Qed.

Lemma lit_m1 : real_lit "-1" = Some (-1).
Proof. unfold real_lit; vm_compute read_literal; unfold Q2R; simpl; f_equal; field. Qed.

Lemma is_lit_eq s e : is_lit nat s e = true -> e = DReal s.
Proof. destruct e; simpl; intros H; try discriminate; apply String.eqb_eq in H; subst; reflexivity. Qed.

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
  simpl; destruct (xeval reals s a) as [[x | | | |] |]; simpl; intros H; try discriminate.
  destruct (real_op1 f x) as [y |] eqn:E; [| discriminate].
  injection H as <-; eauto.
Qed.

(* The value of an arithmetic binary operation with a real operand: both
   operands are reals. *)
Lemma xeval_op2_inv_l s f a b x w :
  xeval reals s a = Some (VReal x) -> xeval reals s (DOp2 f a b) = Some w ->
  Operations.comparison f = false ->
  exists y z, xeval reals s b = Some (VReal y) /\ real_op2 f x y = Some z /\ w = VReal z.
Proof.
  intros Ha H0 Hf; revert H0; simpl; rewrite Ha.
  destruct (xeval reals s b) as [[y | | | |] |]; simpl; intros H; try discriminate.
  rewrite Hf in H; destruct (real_op2 f x y) as [z |] eqn:E; [| discriminate].
  injection H as <-; eauto.
Qed.

Lemma xeval_op2_inv_r s f a b y w :
  xeval reals s b = Some (VReal y) -> xeval reals s (DOp2 f a b) = Some w ->
  Operations.comparison f = false ->
  exists x z, xeval reals s a = Some (VReal x) /\ real_op2 f x y = Some z /\ w = VReal z.
Proof.
  intros Hb H0 Hf; revert H0; simpl; rewrite Hb.
  destruct (xeval reals s a) as [[x | | | |] |]; simpl; intros H; try discriminate.
  rewrite Hf in H; destruct (real_op2 f x y) as [z |] eqn:E; [| discriminate].
  injection H as <-; eauto.
Qed.

(* A real literal operand. *)
Lemma xeval_lit s l x : real_lit l = Some x -> xeval reals s (oute (DReal l)) = Some (VReal x).
Proof. simpl; intros ->; reflexivity. Qed.

Lemma simplify_op1_ok s f a w :
  xeval reals s (oute (DOp1 f a)) = Some w -> xeval reals s (oute (simplify_op1 nat f a)) = Some w.
Proof.
  intros H.
  destruct f as [| | | | | | k |]; try exact H.
  - (* - - x = x *) destruct a as [| | | | [] a' |]; try exact H.
    cbn [out_dexpr simplify_op1] in H |- *.
    destruct (xeval_op1_inv _ _ _ _ H) as (x & y & Hx & Hy & ->).
    destruct (xeval_op1_inv _ _ _ _ Hx) as (x' & y' & Hx' & Hy' & E).
    injection E as ->; injection Hy as <-; injection Hy' as <-.
    rewrite Hx'; f_equal; f_equal; ring.
  - destruct k as [| [p | p |] | p]; try exact H; cbn [out_dexpr simplify_op1] in H |- *;
      destruct (xeval_op1_inv _ _ _ _ H) as (x & y & Hx & Hy & ->); injection Hy as <-.
    + (* x^0 = 1 *) exact (xeval_lit s "1" 1 lit_1).
    + (* x^1 = x *) rewrite Hx; f_equal; f_equal; simpl; ring.
Qed.

Lemma simplify_op2_ok s f a b w :
  xeval reals s (oute (DOp2 f a b)) = Some w -> xeval reals s (oute (simplify_op2 nat f a b)) = Some w.
Proof.
  intros H; destruct f; try exact H; unfold simplify_op2; cbn [out_dexpr] in H.
  - (* 0 + y = y, x + 0 = x *)
    destruct (is_lit nat "0" a) eqn:A.
    { apply is_lit_eq in A; subst a.
      destruct (xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H eq_refl) as (y & z & Hy & Hz & ->).
      injection Hz as <-; rewrite Hy; f_equal; f_equal; ring. }
    destruct (is_lit nat "0" b) eqn:B; [| exact H].
    apply is_lit_eq in B; subst b.
    destruct (xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H eq_refl) as (x & z & Hx & Hz & ->).
    injection Hz as <-; rewrite Hx; f_equal; f_equal; ring.
  - (* x - 0 = x *)
    destruct (is_lit nat "0" b) eqn:B; [| exact H].
    apply is_lit_eq in B; subst b.
    destruct (xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H eq_refl) as (x & z & Hx & Hz & ->).
    injection Hz as <-; rewrite Hx; f_equal; f_equal; ring.
  - (* products by 0, 1 and -1 *)
    destruct (is_lit nat "0" a) eqn:A.
    { apply is_lit_eq in A; subst a.
      destruct (xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H eq_refl) as (y & z & Hy & Hz & ->).
      injection Hz as <-; rewrite (xeval_lit s "0" 0 lit_0); f_equal; f_equal; ring. }
    destruct (is_lit nat "0" b) eqn:B.
    { apply is_lit_eq in B; subst b.
      destruct (xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_0) H eq_refl) as (x & z & Hx & Hz & ->).
      injection Hz as <-; rewrite (xeval_lit s "0" 0 lit_0); f_equal; f_equal; ring. }
    destruct (is_lit nat "1" a) eqn:A1.
    { apply is_lit_eq in A1; subst a.
      destruct (xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_1) H eq_refl) as (y & z & Hy & Hz & ->).
      injection Hz as <-; rewrite Hy; f_equal; f_equal; ring. }
    destruct (is_lit nat "1" b) eqn:B1.
    { apply is_lit_eq in B1; subst b.
      destruct (xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_1) H eq_refl) as (x & z & Hx & Hz & ->).
      injection Hz as <-; rewrite Hx; f_equal; f_equal; ring. }
    destruct (is_lit nat "-1" a) eqn:A2.
    { apply is_lit_eq in A2; subst a.
      destruct (xeval_op2_inv_l _ _ _ _ _ _ (xeval_lit s _ _ lit_m1) H eq_refl) as (y & z & Hy & Hz & ->).
      injection Hz as <-; simpl; rewrite Hy; simpl; f_equal; f_equal; ring. }
    destruct (is_lit nat "-1" b) eqn:B2; [| exact H].
    apply is_lit_eq in B2; subst b.
    destruct (xeval_op2_inv_r _ _ _ _ _ _ (xeval_lit s _ _ lit_m1) H eq_refl) as (x & z & Hx & Hz & ->).
    injection Hz as <-; simpl; rewrite Hx; simpl; f_equal; f_equal; ring.
Qed.

Lemma xeval_simplify s e w :
  xeval reals s (oute e) = Some w -> xeval reals s (oute (simplify_expr nat e)) = Some w.
Proof.
  revert w; induction e as [v | l | k | a IHa i IHi | f a IHa | f a IHa b IHb]; intros w H;
    try exact H.
  - cbn [out_dexpr simplify_expr xeval] in H |- *.
    destruct (xeval reals s (oute a)) as [[| | | xs |] |] eqn:Ea; try discriminate.
    destruct (xeval reals s (oute i)) as [[| k | | |] |] eqn:Ei; try discriminate.
    rewrite (IHa _ eq_refl), (IHi _ eq_refl); exact H.
  - change (xeval reals s (oute (simplify_op1 nat f (simplify_expr nat a))) = Some w).
    apply simplify_op1_ok.
    change (xeval reals s (DOp1 f (oute (simplify_expr nat a))) = Some w).
    cbn [out_dexpr xeval] in H |- *.
    destruct (xeval reals s (oute a)) eqn:Ea; [| discriminate].
    rewrite (IHa _ eq_refl); exact H.
  - change (xeval reals s (oute (simplify_op2 nat f (simplify_expr nat a) (simplify_expr nat b))) = Some w).
    apply simplify_op2_ok.
    change (xeval reals s (DOp2 f (oute (simplify_expr nat a)) (oute (simplify_expr nat b))) = Some w).
    cbn [out_dexpr xeval] in H |- *.
    destruct (xeval reals s (oute a)) eqn:Ea; [| discriminate].
    destruct (xeval reals s (oute b)) eqn:Eb; [| discriminate].
    rewrite (IHa _ eq_refl), (IHb _ eq_refl); exact H.
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
  induction 1; simpl; intros Ht; repeat rewrite orb_false_iff in Ht;
    try discriminate; econstructor; intuition.
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
  revert sc; induction ss as [| [] r IH]; intros sc; simpl; try rewrite IH; simpl; tauto.
Qed.

Lemma in_after_wr y wr ss : In y (after_wr wr ss) -> In y (defs ss) \/ In y wr.
Proof.
  revert wr; induction ss as [| [[] | | | | | | | | | | ] r IH]; intros wr H; simpl in *;
    try (apply IH in H; simpl in H); tauto.
Qed.

Lemma incl_both {A : Type} (v : A) wr sc : incl wr sc -> incl (v :: wr) (v :: sc).
Proof. intros H y [<- | Hy]; [left | right; apply H]; auto. Qed.

Lemma after_scope_incl sc ss : incl sc (after_scope sc ss).
Proof. intros y Hy; apply in_after_scope; auto. Qed.

Lemma after_incl wr sc ss : incl wr sc -> incl (after_wr wr ss) (after_scope sc ss).
Proof.
  intros H y Hy; apply in_after_scope; destruct (in_after_wr _ _ _ Hy); auto.
Qed.

(* The variables defined by a good block are consistent. *)
Lemma after_consistent sc wr ss : gd sc wr ss -> Forall consistent sc -> Forall consistent (after_scope sc ss).
Proof. induction 1; simpl; intros Hc; auto. Qed.

(* A good block splits into good blocks, the second in the scope the first ends with. *)
Lemma gd_app_inv sc wr a b :
  gd sc wr (a ++ b) -> gd sc wr a /\ gd (after_scope sc a) (after_wr wr a) b.
Proof.
  revert sc wr; induction a as [| st a IH]; intros sc wr H; simpl in *.
  - split; [constructor | exact H].
  - inversion H; subst; edestruct IH as [Ha Hb]; try eassumption;
      (split; [econstructor; eassumption | exact Hb]).
Qed.

Lemma gd_app sc wr a b :
  gd sc wr a -> gd (after_scope sc a) (after_wr wr a) b -> gd sc wr (a ++ b).
Proof.
  revert sc wr; induction a as [| st a IH]; intros sc wr Ha Hb; simpl in *; [exact Hb |].
  inversion Ha; subst; econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------------
   Agreement of two stores on the variables in scope, and on the returned
   value. *)

Definition agree (sc : list (dvar W)) (s s' : store) : Prop :=
  (forall x, In x sc -> store_get s (KVar (out x)) = store_get s' (KVar (out x))) /\
  store_get s Returned = store_get s' Returned.

Lemma agree_refl sc s : agree sc s s.
Proof. split; auto. Qed.

Lemma agree_trans sc s1 s2 s3 : agree sc s1 s2 -> agree sc s2 s3 -> agree sc s1 s3.
Proof. intros [H1 R1] [H2 R2]; split; [intros x Hx; rewrite H1, H2 | rewrite R1, R2]; auto. Qed.

Lemma agree_incl sc1 sc2 s s' : incl sc1 sc2 -> agree sc2 s s' -> agree sc1 s s'.
Proof. intros Hi [H R]; split; auto. Qed.

(* Writing the same value at the same key keeps the agreement. *)
Lemma agree_set sc s s' k w : agree sc s s' -> agree sc (store_set s k w) (store_set s' k w).
Proof.
  intros [H R]; split; [intros x Hx |]; rewrite !get_set; destruct (key_eqb k _); auto.
Qed.

(* Defining a variable extends the scope of the agreement. *)
Lemma agree_set_cons sc s s' v w :
  agree sc s s' -> agree (v :: sc) (store_set s (KVar (out v)) w) (store_set s' (KVar (out v)) w).
Proof.
  intros Hag; destruct (agree_set _ _ _ (KVar (out v)) w Hag) as [H R]; split; auto.
  intros x [<- | Hx]; [rewrite !get_set_same; reflexivity | auto].
Qed.

(* Writing a variable out of scope, on one side, keeps the agreement. *)
Lemma agree_set_out sc s s' v w :
  Forall consistent sc -> consistent v -> ~ In v sc ->
  agree sc s s' -> agree sc (store_set s (KVar (out v)) w) s'.
Proof.
  intros Hc Hv Hn [H R]; split.
  - intros x Hx; rewrite get_set_other; [auto |].
    apply key_neq; auto; [eapply Forall_forall; eauto | intros ->; contradiction].
  - rewrite get_set_other; [exact R | discriminate].
Qed.

(* ---------------------------------------------------------------------------
   Expressions and locations in scope. *)

(* An expression in scope reads the same in two agreeing stores. *)
Lemma xeval_agree sc s s' e :
  expr_ok sc e -> agree sc s s' -> xeval reals s (oute e) = xeval reals s' (oute e).
Proof.
  intros He Hag; induction e; simpl in *; try reflexivity.
  - exact (proj1 Hag _ He).
  - rewrite IHe1, IHe2; tauto.
  - rewrite IHe; tauto.
  - rewrite IHe1, IHe2; tauto.
Qed.

Lemma expr_ok_incl sc1 sc2 e : incl sc1 sc2 -> expr_ok sc1 e -> expr_ok sc2 e.
Proof. intros Hi; induction e; simpl; intuition. Qed.

Lemma lhs_ok_incl sc1 sc2 wr1 wr2 l :
  incl sc1 sc2 -> incl wr1 wr2 -> lhs_ok sc1 wr1 l -> lhs_ok sc2 wr2 l.
Proof.
  intros Hs Hw; destruct l as [| | | [] i | |]; simpl; intuition; eapply expr_ok_incl; eauto.
Qed.

Lemma lhs_expr_ok sc wr l : incl wr sc -> lhs_ok sc wr l -> expr_ok sc l.
Proof. intros Hi; destruct l as [| | | [] i | |]; simpl; intuition. Qed.

Lemma expr_ok_simplify sc e : expr_ok sc e -> expr_ok sc (simplify_expr nat e).
Proof.
  induction e as [| | | a IHa i IHi | f a IHa | f a IHa b IHb]; simpl; intros H; auto.
  - tauto.
  - specialize (IHa H); unfold simplify_op1.
    destruct f as [| | | | | | k |]; simpl; auto.
    + destruct (simplify_expr nat a) as [| | | | [] a' |]; simpl in *; auto.
    + destruct k as [| [] |]; simpl; auto.
  - destruct H as [Ha Hb]; specialize (IHa Ha); specialize (IHb Hb); unfold simplify_op2.
    destruct f; simpl; auto;
      repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl; auto.
Qed.

Lemma lhs_ok_simplify sc wr l : lhs_ok sc wr l -> lhs_ok sc wr (simplify_expr nat l).
Proof.
  destruct l as [| | | [] i | |]; simpl; intuition; apply expr_ok_simplify; auto.
Qed.

(* An assignment in scope, from agreeing stores, leaves agreeing stores. *)
Lemma assign_agree sc wr l w s s' t :
  incl wr sc -> lhs_ok sc wr l -> agree sc s s' -> assign reals s (oute l) w = Some t ->
  exists t', assign reals s' (oute l) w = Some t' /\ agree sc t t'.
Proof.
  intros Hi Hl Hag H; destruct l as [x | | | [x | | | | |] i | |]; simpl in Hl; try contradiction.
  - injection H as <-; eexists; split; [reflexivity | apply agree_set; exact Hag].
  - destruct Hl as [Hx Hie]; destruct w as [e | | | |]; try discriminate; simpl in H |- *.
    rewrite <- (proj1 Hag x (Hi _ Hx)), <- (xeval_agree _ _ _ _ Hie Hag).
    destruct (store_get s (KVar (out x))) as [[| | | l |] |]; try discriminate.
    destruct (xeval reals s (oute i)) as [[| k | | |] |]; try discriminate.
    destruct (replace_nth_z k e l); try discriminate.
    injection H as <-; eexists; split; [reflexivity | apply agree_set; exact Hag].
Qed.

(* The simplified location is assigned as the original. *)
Lemma assign_simplify sc wr s l w t :
  lhs_ok sc wr l -> assign reals s (oute l) w = Some t ->
  assign reals s (oute (simplify_expr nat l)) w = Some t.
Proof.
  intros Hl H; destruct l as [x | | | [x | | | | |] i | |]; simpl in Hl; try contradiction.
  - exact H.
  - destruct w as [e | | | |]; try discriminate; simpl in H |- *.
    destruct (store_get s (KVar (out x))) as [[| | | l |] |]; try discriminate.
    destruct (xeval reals s (oute i)) as [v |] eqn:Ei; [| discriminate].
    rewrite (xeval_simplify _ _ _ Ei); exact H.
Qed.

(* ---------------------------------------------------------------------------
   The execution of each statement, unfolded. *)

Lemma exec_define s so v e :
  exec reals (outs (DDefine so v e)) s =
  match xeval reals s (oute e) with Some w => Some (store_set s (KVar (out v)) w) | None => None end.
Proof. reflexivity. Qed.

Lemma exec_realvar s v : exec reals (outs (DRealVar v)) s = Some (store_set s (KVar (out v)) (VReal 0)).
Proof. change (dom_lit reals "0") with (real_lit "0"); cbn -[real_lit]; rewrite lit_0; reflexivity. Qed.

Lemma exec_tape s v : exec reals (outs (DTape v)) s = Some (store_set s (KVar (out v)) (VTape [])).
Proof. reflexivity. Qed.

Lemma exec_assign s l e :
  exec reals (outs (DAssign l e)) s =
  match xeval reals s (oute e) with Some w => assign reals s (oute l) w | None => None end.
Proof. reflexivity. Qed.

Lemma exec_increment s l e :
  exec reals (outs (DIncrement l e)) s =
  match xeval reals s (oute l), xeval reals s (oute e) with
  | Some (VReal a), Some (VReal b) => assign reals s (oute l) (VReal (a + b))
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma exec_branch s c t e :
  exec reals (outs (DBranch c t e)) s =
  match xeval reals s (oute c) with
  | Some (VBool true) => ex t s
  | Some (VBool false) => ex e s
  | _ => None
  end.
Proof. reflexivity. Qed.

Lemma exec_for s i lo hi b :
  exec reals (outs (DFor i lo hi b)) s =
  match xeval reals s (oute lo), xeval reals s (oute hi) with
  | Some (VInt l), Some (VInt h) => exec_up R (ex b) (out i) l (count l h) s
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma exec_forback s i lo hi b :
  exec reals (outs (DForBack i lo hi b)) s =
  match xeval reals s (oute lo), xeval reals s (oute hi) with
  | Some (VInt l), Some (VInt h) => exec_down R (ex b) (out i) (h - 1) (count l h) s
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma exec_return s e :
  exec reals (outs (DReturn e)) s =
  match xeval reals s (oute e) with Some w => Some (store_set s Returned w) | None => None end.
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------
   Loops: a relation between two stores, kept by the body when the index is
   set to the same value on both sides, is kept by the loop. *)

Lemma exec_up_sim (Rin Rb : store -> store -> Prop) (b1 b2 : store -> option store) i :
  (forall s s' w, Rin s s' -> Rb (store_set s (KVar i) w) (store_set s' (KVar i) w)) ->
  (forall s s' t, Rb s s' -> b1 s = Some t -> exists t', b2 s' = Some t' /\ Rin t t') ->
  forall n lo s s' t, Rin s s' -> exec_up R b1 i lo n s = Some t ->
  exists t', exec_up R b2 i lo n s' = Some t' /\ Rin t t'.
Proof.
  intros Hset Hbody n; induction n as [| n IH]; intros lo s s' t Hr H; simpl in *.
  - injection H as <-; eauto.
  - destruct (b1 (store_set s (KVar i) (VInt lo))) as [s1 |] eqn:E; [| discriminate].
    destruct (Hbody _ _ _ (Hset _ _ (VInt lo) Hr) E) as (s1' & -> & Hr1); eauto.
Qed.

Lemma exec_down_sim (Rin Rb : store -> store -> Prop) (b1 b2 : store -> option store) i :
  (forall s s' w, Rin s s' -> Rb (store_set s (KVar i) w) (store_set s' (KVar i) w)) ->
  (forall s s' t, Rb s s' -> b1 s = Some t -> exists t', b2 s' = Some t' /\ Rin t t') ->
  forall n hi s s' t, Rin s s' -> exec_down R b1 i hi n s = Some t ->
  exists t', exec_down R b2 i hi n s' = Some t' /\ Rin t t'.
Proof.
  intros Hset Hbody n; induction n as [| n IH]; intros hi s s' t Hr H; simpl in *.
  - injection H as <-; eauto.
  - destruct (b1 (store_set s (KVar i) (VInt hi))) as [s1 |] eqn:E; [| discriminate].
    destruct (Hbody _ _ _ (Hset _ _ (VInt hi) Hr) E) as (s1' & -> & Hr1); eauto.
Qed.

(* The agreement on the scope, extended by the index, is kept by setting the index. *)
Lemma agree_index sc i : forall s s' w, agree sc s s' ->
  agree (i :: sc) (store_set s (KVar (out i)) w) (store_set s' (KVar (out i)) w).
Proof. intros; apply agree_set_cons; auto. Qed.

(* ---------------------------------------------------------------------------
   The frame: a good block, run from two stores that agree on its scope, ends
   in stores that agree on its scope and on the variables it defines. It
   reads only variables in scope, and writes the same values on both sides. *)

Lemma frame sc wr ss :
  gd sc wr ss -> incl wr sc ->
  forall s s' t, agree sc s s' -> ex ss s = Some t ->
  exists t', ex ss s' = Some t' /\ agree (after_scope sc ss) t t'.
Proof.
  induction 1 as [sc wr | sc wr ty v e r He Hv Hcv Hr IH | sc wr v e r He Hv Hcv Hr IH
                 | sc wr v r Hv Hcv Hr IH | sc wr v r Hv Hcv Hr IH
                 | sc wr l e r Hl He Hr IH | sc wr l e r Hl He Hr IH
                 | sc wr c t e r Hc Ht IHt He IHe Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr e r He Hr IH];
    intros Hwr s s' t0 Hag Hex; try rewrite ex_cons in Hex |- *; simpl after_scope.
  - injection Hex as <-; exists s'; split; [reflexivity | exact Hag].
  - rewrite exec_define in Hex |- *; rewrite <- (xeval_agree _ _ _ _ He Hag).
    destruct (xeval reals s (oute e)); [| discriminate].
    apply (IH (incl_tl _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex).
  - rewrite exec_define in Hex |- *; rewrite <- (xeval_agree _ _ _ _ He Hag).
    destruct (xeval reals s (oute e)); [| discriminate].
    apply (IH (incl_both _ _ _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex).
  - rewrite exec_realvar in Hex |- *.
    apply (IH (incl_both _ _ _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex).
  - rewrite exec_tape in Hex |- *.
    apply (IH (incl_both _ _ _ Hwr) _ _ _ (agree_set_cons _ _ _ _ _ Hag) Hex).
  - rewrite exec_assign in Hex |- *; rewrite <- (xeval_agree _ _ _ _ He Hag).
    destruct (xeval reals s (oute e)); [| discriminate].
    destruct (assign reals s (oute l) v) as [s1 |] eqn:E; [| discriminate].
    destruct (assign_agree _ _ _ _ _ _ _ Hwr Hl Hag E) as (s1' & -> & Hag1); eauto.
  - rewrite exec_increment in Hex |- *.
    rewrite <- (xeval_agree _ _ _ _ He Hag), <- (xeval_agree _ _ _ _ (lhs_expr_ok _ _ _ Hwr Hl) Hag).
    destruct (xeval reals s (oute l)) as [[a | | | |] |]; try discriminate.
    destruct (xeval reals s (oute e)) as [[b | | | |] |]; try discriminate.
    destruct (assign reals s (oute l) _) as [s1 |] eqn:E; [| discriminate].
    destruct (assign_agree _ _ _ _ _ _ _ Hwr Hl Hag E) as (s1' & -> & Hag1); eauto.
  - rewrite exec_branch in Hex |- *; rewrite <- (xeval_agree _ _ _ _ Hc Hag).
    destruct (xeval reals s (oute c)) as [[| | [] | |] |]; try discriminate.
    + destruct (ex t s) as [s1 |] eqn:E; [| discriminate].
      destruct (IHt Hwr _ _ _ Hag E) as (s1' & -> & Hag1).
      exact (IH Hwr _ _ _ (agree_incl _ _ _ _ (after_scope_incl _ _) Hag1) Hex).
    + destruct (ex e s) as [s1 |] eqn:E; [| discriminate].
      destruct (IHe Hwr _ _ _ Hag E) as (s1' & -> & Hag1).
      exact (IH Hwr _ _ _ (agree_incl _ _ _ _ (after_scope_incl _ _) Hag1) Hex).
  - rewrite exec_for in Hex |- *.
    rewrite <- (xeval_agree _ _ _ _ Hlo Hag), <- (xeval_agree _ _ _ _ Hhi Hag).
    destruct (xeval reals s (oute lo)) as [[| l | | |] |]; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |]; try discriminate.
    destruct (exec_up R (ex b) (out i) l (count l h) s) as [s1 |] eqn:E; [| discriminate].
    edestruct (exec_up_sim (agree sc) (agree (i :: sc)) (ex b) (ex b) (out i) (agree_index sc i))
      as (s1' & -> & Hag1); [| exact Hag | exact E | exact (IH Hwr _ _ _ Hag1 Hex)].
    intros u u' v Hu Hv'; destruct (IHb (incl_tl _ Hwr) _ _ _ Hu Hv') as (v' & -> & Hv'').
    exists v'; split; [reflexivity |].
    apply (agree_incl _ _ _ _ (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hv'').
  - rewrite exec_forback in Hex |- *.
    rewrite <- (xeval_agree _ _ _ _ Hlo Hag), <- (xeval_agree _ _ _ _ Hhi Hag).
    destruct (xeval reals s (oute lo)) as [[| l | | |] |]; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |]; try discriminate.
    destruct (exec_down R (ex b) (out i) (h - 1) (count l h) s) as [s1 |] eqn:E; [| discriminate].
    edestruct (exec_down_sim (agree sc) (agree (i :: sc)) (ex b) (ex b) (out i) (agree_index sc i))
      as (s1' & -> & Hag1); [| exact Hag | exact E | exact (IH Hwr _ _ _ Hag1 Hex)].
    intros u u' v Hu Hv'; destruct (IHb (incl_tl _ Hwr) _ _ _ Hu Hv') as (v' & -> & Hv'').
    exists v'; split; [reflexivity |].
    apply (agree_incl _ _ _ _ (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hv'').
  - rewrite exec_return in Hex |- *; rewrite <- (xeval_agree _ _ _ _ He Hag).
    destruct (xeval reals s (oute e)); [| discriminate].
    exact (IH Hwr _ _ _ (agree_set _ _ _ _ _ Hag) Hex).
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
  intros Hab Hbc s s' t Hag H.
  destruct (Hab _ _ _ (agree_refl sc s) H) as (t1 & H1 & Ha1).
  destruct (Hbc _ _ _ Hag H1) as (t2 & H2 & Ha2).
  exists t2; split; [exact H2 | exact (agree_trans _ _ _ _ Ha1 Ha2)].
Qed.

(* A good block refines itself. *)
Lemma frame_sim sc wr ss : gd sc wr ss -> incl wr sc -> sim sc ss ss.
Proof.
  intros Hg Hwr s s' t Hag H; destruct (frame _ _ _ Hg Hwr _ _ _ Hag H) as (t' & H' & Ha').
  exists t'; split; [exact H' | exact (agree_incl _ _ _ _ (after_scope_incl _ _) Ha')].
Qed.

Lemma ex_single h s : ex [h] s = exec reals (outs h) s.
Proof. rewrite ex_cons; destruct (exec reals (outs h) s); reflexivity. Qed.

(* Two blocks refine each other statement by statement. *)
Lemma sim_cons sc sc' h1 h2 r1 r2 :
  incl sc sc' ->
  (forall s s' t, agree sc s s' -> exec reals (outs h1) s = Some t ->
     exists t', exec reals (outs h2) s' = Some t' /\ agree sc' t t') ->
  sim sc' r1 r2 -> sim sc (h1 :: r1) (h2 :: r2).
Proof.
  intros Hi Hh Hr s s' t Hag H; rewrite ex_cons in H |- *.
  destruct (exec reals (outs h1) s) as [s1 |] eqn:E; [| discriminate].
  destruct (Hh _ _ _ Hag E) as (s1' & -> & Hag1).
  destruct (Hr _ _ _ Hag1 H) as (t' & H' & Ha'); exists t'; split; [exact H' | exact (agree_incl _ _ _ _ Hi Ha')].
Qed.

(* A statement kept in front of a refined block. *)
Lemma sim_keep sc wr h r r' :
  gd sc wr (h :: r) -> incl wr sc -> sim (after_scope sc [h]) r r' -> sim sc (h :: r) (h :: r').
Proof.
  intros Hg Hwr Hr; apply sim_cons with (sc' := after_scope sc [h]); [apply after_scope_incl | | exact Hr].
  destruct (gd_app_inv sc wr [h] r Hg) as [Hh _].
  intros s s' t Hag H; rewrite <- ex_single in H |- *; exact (frame _ _ _ Hh Hwr _ _ _ Hag H).
Qed.

(* ---------------------------------------------------------------------------
   Changing the scope of a good block. *)

(* With the same variables in scope, and more writable ones. *)
Lemma gd_mono sc1 wr1 ss :
  gd sc1 wr1 ss -> forall sc2 wr2, incl sc1 sc2 -> incl sc2 sc1 -> incl wr1 wr2 -> gd sc2 wr2 ss.
Proof.
  induction 1; intros sc2 wr2 H12 H21 Hw; econstructor;
    try (eapply expr_ok_incl; eassumption);
    try (eapply lhs_ok_incl; eassumption);
    try (intros Hin; apply H21 in Hin; contradiction);
    try eassumption;
    try (apply IHgd || apply IHgd1 || apply IHgd2 || apply IHgd3);
    try (apply incl_both; assumption); try assumption.
Qed.

Lemma expr_ok_remove sc1 sc2 v e :
  expr_ok sc1 e -> mentions_expr nat v e = false -> (forall y, y <> v -> In y sc1 -> In y sc2) ->
  expr_ok sc2 e.
Proof.
  intros He Hm Hs; induction e; simpl in *; rewrite ?orb_false_iff in Hm; intuition.
  apply Hs; [apply dvar_eq_false_neq; exact Hm | exact He].
Qed.

Lemma lhs_ok_remove sc1 sc2 wr1 wr2 v l :
  lhs_ok sc1 wr1 l -> mentions_expr nat v l = false ->
  (forall y, y <> v -> In y sc1 -> In y sc2) -> (forall y, y <> v -> In y wr1 -> In y wr2) ->
  lhs_ok sc2 wr2 l.
Proof.
  intros Hl Hm Hs Hw; destruct l as [x | | | [x | | | | |] i | |]; simpl in *; try contradiction.
  - apply Hw; [apply dvar_eq_false_neq; exact Hm | exact Hl].
  - rewrite orb_false_iff in Hm; destruct Hm as [Hx Hi]; destruct Hl as [Hl Hie]; split.
    + apply Hw; [apply dvar_eq_false_neq; exact Hx | exact Hl].
    + exact (expr_ok_remove _ _ _ _ Hie Hi Hs).
Qed.

(* Without a variable the block does not mention. *)
Lemma gd_remove sc1 wr1 ss v :
  gd sc1 wr1 ss -> existsb (mentions nat v) ss = false ->
  forall sc2 wr2, (forall y, y <> v -> In y sc1 -> In y sc2) ->
  (forall y, y <> v -> In y wr1 -> In y wr2) -> incl sc2 sc1 -> gd sc2 wr2 ss.
Proof.
  assert (Hext : forall (x : dvar W) l1 l2, (forall y, y <> v -> In y l1 -> In y l2) ->
                 forall y, y <> v -> In y (x :: l1) -> In y (x :: l2)).
  { intros x l1 l2 H y Hy [<- | Hin]; [left | right]; auto. }
  assert (Hfresh : forall (x : dvar W) l1 l2, ~ In x l1 -> incl l2 l1 -> ~ In x l2).
  { intros x l1 l2 H Hi Hin; apply H, Hi, Hin. }
  induction 1; simpl; intros Hm sc2 wr2 Hs Hw Hb; repeat rewrite orb_false_iff in Hm.
  - apply GdNil.
  - destruct Hm as [[Hx He'] Hr'].
    apply GdConstant; [eapply expr_ok_remove; eauto | eapply Hfresh; eassumption | assumption |].
    apply IHgd; [assumption | apply Hext; assumption | try apply Hext; assumption | apply incl_both; assumption].
  - destruct Hm as [[Hx He'] Hr'].
    apply GdMutable; [eapply expr_ok_remove; eauto | eapply Hfresh; eassumption | assumption |].
    apply IHgd; [assumption | apply Hext; assumption | try apply Hext; assumption | apply incl_both; assumption].
  - destruct Hm as [Hx Hr'].
    apply GdRealVar; [eapply Hfresh; eassumption | assumption |]; apply IHgd; [assumption | apply Hext; assumption | try apply Hext; assumption | apply incl_both; assumption].
  - destruct Hm as [Hx Hr'].
    apply GdTape; [eapply Hfresh; eassumption | assumption |]; apply IHgd; [assumption | apply Hext; assumption | try apply Hext; assumption | apply incl_both; assumption].
  - destruct Hm as [[Hl He'] Hr'].
    apply GdAssign; [eapply lhs_ok_remove | eapply expr_ok_remove | apply IHgd]; eauto.
  - destruct Hm as [[Hl He'] Hr'].
    apply GdIncrement; [eapply lhs_ok_remove | eapply expr_ok_remove | apply IHgd]; eauto.
  - destruct Hm as [[[Hc' Ht'] He'] Hr'].
    apply GdBranch; [eapply expr_ok_remove | apply IHgd1 | apply IHgd2 | apply IHgd3]; eauto.
  - destruct Hm as [[[[Hx Hlo'] Hhi'] Hb'] Hr'].
    apply GdFor; [eapply Hfresh; eassumption | assumption | eapply expr_ok_remove; eauto | eapply expr_ok_remove; eauto
                 | apply IHgd1; [assumption | apply Hext; assumption | assumption | apply incl_both; assumption] | apply IHgd2; auto].
  - destruct Hm as [[[[Hx Hlo'] Hhi'] Hb'] Hr'].
    apply GdForBack; [eapply Hfresh; eassumption | assumption | eapply expr_ok_remove; eauto | eapply expr_ok_remove; eauto
                     | apply IHgd1; [assumption | apply Hext; assumption | assumption | apply incl_both; assumption] | apply IHgd2; auto].
  - destruct Hm as [He' Hr'].
    apply GdReturn; [eapply expr_ok_remove | apply IHgd]; eauto.
Qed.

(* Without a writable variable the block never assigns. *)
Lemma lhs_ok_drop_wr sc wr1 wr2 v l :
  lhs_ok sc wr1 l -> target nat v l = false -> (forall y, y <> v -> In y wr1 -> In y wr2) ->
  lhs_ok sc wr2 l.
Proof.
  intros Hl Ht Hw; destruct l as [x | | | [x | | | | |] i | |]; simpl in *; try contradiction.
  - apply Hw; [apply dvar_eq_false_neq; exact Ht | exact Hl].
  - destruct Hl as [Hl Hie]; split; [apply Hw; [apply dvar_eq_false_neq; exact Ht | exact Hl] | exact Hie].
Qed.

Lemma gd_drop_wr sc wr1 ss v :
  gd sc wr1 ss -> existsb (writes nat v) ss = false ->
  forall wr2, (forall y, y <> v -> In y wr1 -> In y wr2) -> gd sc wr2 ss.
Proof.
  induction 1; simpl; intros Hm wr2 Hw; repeat rewrite orb_false_iff in Hm;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  - constructor.
  - constructor; auto.
  - constructor; auto; apply IHgd; auto; intros y Hy [<- | Hin]; [left | right]; auto.
  - constructor; auto; apply IHgd; auto; intros y Hy [<- | Hin]; [left | right]; auto.
  - constructor; auto; apply IHgd; auto; intros y Hy [<- | Hin]; [left | right]; auto.
  - constructor; auto; eapply lhs_ok_drop_wr; eauto.
  - constructor; auto; eapply lhs_ok_drop_wr; eauto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

(* ---------------------------------------------------------------------------
   A block that does not mention a variable leaves its value as it is. *)

Definition lhs_var (l : dexpr nat) : option (dvar nat) :=
  match l with DVar x => Some x | DAt (DVar x) _ => Some x | _ => None end.

(* An assignment writes its variable only. *)
Lemma assign_set s l w t :
  assign reals s l w = Some t -> exists x w', lhs_var l = Some x /\ t = store_set s (KVar x) w'.
Proof.
  destruct l as [x | | | [x | | | | |] i | |]; simpl; intros H; try discriminate.
  - injection H as <-; eauto.
  - destruct w as [e | | | |]; try discriminate.
    destruct (store_get s (KVar x)) as [[| | | l |] |]; try discriminate.
    destruct (xeval reals s i) as [[| k | | |] |]; try discriminate.
    destruct (replace_nth_z k e l); try discriminate; injection H as <-; eauto.
Qed.

Lemma lhs_var_out sc wr l :
  lhs_ok sc wr l -> exists x, In x wr /\ lhs_var (oute l) = Some (out x) /\
                              forall v, mentions_expr nat v l = false -> dvar_eq nat x v = false.
Proof.
  destruct l as [x | | | [x | | | | |] i | |]; simpl; intros H; try contradiction.
  - exists x; auto.
  - exists x; split; [tauto | split; [reflexivity |]]; intros v Hm; rewrite orb_false_iff in Hm; tauto.
Qed.

Lemma exec_up_inv (Q : store -> Prop) (b : store -> option store) i :
  (forall s w, Q s -> Q (store_set s (KVar i) w)) -> (forall s t, Q s -> b s = Some t -> Q t) ->
  forall n lo s t, Q s -> exec_up R b i lo n s = Some t -> Q t.
Proof.
  intros Hset Hb n; induction n as [| n IH]; intros lo s t Hq H; simpl in H; [injection H as <-; exact Hq |].
  destruct (b (store_set s (KVar i) (VInt lo))) eqn:E; [| discriminate]; eauto.
Qed.

Lemma exec_down_inv (Q : store -> Prop) (b : store -> option store) i :
  (forall s w, Q s -> Q (store_set s (KVar i) w)) -> (forall s t, Q s -> b s = Some t -> Q t) ->
  forall n hi s t, Q s -> exec_down R b i hi n s = Some t -> Q t.
Proof.
  intros Hset Hb n; induction n as [| n IH]; intros hi s t Hq H; simpl in H; [injection H as <-; exact Hq |].
  destruct (b (store_set s (KVar i) (VInt hi))) eqn:E; [| discriminate]; eauto.
Qed.

Lemma preserve_unmentioned sc wr ss v :
  gd sc wr ss -> incl wr sc -> Forall consistent sc -> consistent v ->
  existsb (mentions nat v) ss = false ->
  forall s t, ex ss s = Some t -> store_get t (KVar (out v)) = store_get s (KVar (out v)).
Proof.
  intros Hg; induction Hg as [sc wr | sc wr ty x e r He Hx Hcx Hr IH | sc wr x e r He Hx Hcx Hr IH
                 | sc wr x r Hx Hcx Hr IH | sc wr x r Hx Hcx Hr IH
                 | sc wr l e r Hl He Hr IH | sc wr l e r Hl He Hr IH
                 | sc wr c t e r Hc Ht IHt He IHe Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr e r He Hr IH];
    intros Hwr Hcs Hv Hm s t0 Hex; simpl in Hm; repeat rewrite orb_false_iff in Hm;
    try rewrite ex_cons in Hex.
  - injection Hex as <-; reflexivity.
  (* a definition writes a variable other than v *)
  - destruct Hm as [[Hxv _] Hm]; rewrite exec_define in Hex.
    destruct (xeval reals s (oute e)); [| discriminate].
    rewrite (IH (incl_tl _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
    apply get_set_other, key_neq; auto; exact (dvar_eq_false_neq _ _ Hxv).
  - destruct Hm as [[Hxv _] Hm]; rewrite exec_define in Hex.
    destruct (xeval reals s (oute e)); [| discriminate].
    rewrite (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
    apply get_set_other, key_neq; auto; exact (dvar_eq_false_neq _ _ Hxv).
  - destruct Hm as [Hxv Hm]; rewrite exec_realvar in Hex.
    rewrite (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
    apply get_set_other, key_neq; auto; exact (dvar_eq_false_neq _ _ Hxv).
  - destruct Hm as [Hxv Hm]; rewrite exec_tape in Hex.
    rewrite (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcx Hcs) Hv Hm _ _ Hex).
    apply get_set_other, key_neq; auto; exact (dvar_eq_false_neq _ _ Hxv).
  (* an assignment writes its variable, other than v *)
  - destruct Hm as [[Hlv _] Hm]; rewrite exec_assign in Hex.
    destruct (xeval reals s (oute e)); [| discriminate].
    destruct (assign reals s (oute l) v0) as [s1 |] eqn:E; [| discriminate].
    rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
    destruct (assign_set _ _ _ _ E) as (y & w' & Hy & ->).
    destruct (lhs_var_out _ _ _ Hl) as (x & Hx & Hy' & Hxv); rewrite Hy in Hy'; injection Hy' as ->.
    apply get_set_other, key_neq; auto; [eapply Forall_forall; eauto |].
    exact (dvar_eq_false_neq _ _ (Hxv _ Hlv)).
  - destruct Hm as [[Hlv _] Hm]; rewrite exec_increment in Hex.
    destruct (xeval reals s (oute l)) as [[a | | | |] |]; try discriminate.
    destruct (xeval reals s (oute e)) as [[b | | | |] |]; try discriminate.
    destruct (assign reals s (oute l) _) as [s1 |] eqn:E; [| discriminate].
    rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
    destruct (assign_set _ _ _ _ E) as (y & w' & Hy & ->).
    destruct (lhs_var_out _ _ _ Hl) as (x & Hx & Hy' & Hxv); rewrite Hy in Hy'; injection Hy' as ->.
    apply get_set_other, key_neq; auto; [eapply Forall_forall; eauto |].
    exact (dvar_eq_false_neq _ _ (Hxv _ Hlv)).
  - destruct Hm as [[[_ Htm] Hem] Hm]; rewrite exec_branch in Hex.
    destruct (xeval reals s (oute c)) as [[| | [] | |] |]; try discriminate.
    + destruct (ex t s) as [s1 |] eqn:E; [| discriminate].
      rewrite (IH Hwr Hcs Hv Hm _ _ Hex); exact (IHt Hwr Hcs Hv Htm _ _ E).
    + destruct (ex e s) as [s1 |] eqn:E; [| discriminate].
      rewrite (IH Hwr Hcs Hv Hm _ _ Hex); exact (IHe Hwr Hcs Hv Hem _ _ E).
  - destruct Hm as [[[[Hiv _] _] Hbm] Hm]; rewrite exec_for in Hex.
    destruct (xeval reals s (oute lo)) as [[| l | | |] |]; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |]; try discriminate.
    destruct (exec_up R (ex b) (out i) l (count l h) s) as [s1 |] eqn:E; [| discriminate].
    rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
    apply (exec_up_inv (fun u => store_get u (KVar (out v)) = store_get s (KVar (out v))) (ex b) (out i))
      with (n := count l h) (lo := l) (s := s); auto.
    + intros u w Hu; rewrite get_set_other; [exact Hu |].
      apply key_neq; auto; exact (dvar_eq_false_neq _ _ Hiv).
    + intros u u' Hu Hb'; rewrite <- Hu.
      exact (IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs) Hv Hbm _ _ Hb').
  - destruct Hm as [[[[Hiv _] _] Hbm] Hm]; rewrite exec_forback in Hex.
    destruct (xeval reals s (oute lo)) as [[| l | | |] |]; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |]; try discriminate.
    destruct (exec_down R (ex b) (out i) (h - 1) (count l h) s) as [s1 |] eqn:E; [| discriminate].
    rewrite (IH Hwr Hcs Hv Hm _ _ Hex).
    apply (exec_down_inv (fun u => store_get u (KVar (out v)) = store_get s (KVar (out v))) (ex b) (out i))
      with (n := count l h) (hi := (h - 1)%Z) (s := s); auto.
    + intros u w Hu; rewrite get_set_other; [exact Hu |].
      apply key_neq; auto; exact (dvar_eq_false_neq _ _ Hiv).
    + intros u u' Hu Hb'; rewrite <- Hu.
      exact (IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs) Hv Hbm _ _ Hb').
  - destruct Hm as [_ Hm]; rewrite exec_return in Hex.
    destruct (xeval reals s (oute e)); [| discriminate].
    rewrite (IH Hwr Hcs Hv Hm _ _ Hex); apply get_set_other; discriminate.
Qed.

(* ---------------------------------------------------------------------------
   Adding zero to a location leaves the store as it is. *)

Lemma replace_nth_same {A : Type} k (x : A) l l1 :
  nth_error l k = Some x -> replace_nth k x l = Some l1 -> l1 = l.
Proof.
  revert l l1; induction k as [| k IH]; intros [| y l] l1 Hn Hr; simpl in *; try discriminate.
  - injection Hn as ->; injection Hr as <-; reflexivity.
  - destruct (replace_nth k x l) eqn:E; [| discriminate]; injection Hr as <-.
    rewrite (IH _ _ Hn E); reflexivity.
Qed.

Lemma assign_same sc wr s l a t :
  lhs_ok sc wr l -> xeval reals s (oute l) = Some (VReal a) ->
  assign reals s (oute l) (VReal a) = Some t -> forall k, store_get t k = store_get s k.
Proof.
  intros Hl Hx H k; destruct l as [x | | | [x | | | | |] i | |]; simpl in Hl; try contradiction.
  - simpl in Hx, H; injection H as <-; rewrite get_set.
    destruct (key_eqb (KVar (out x)) k) eqn:E; [| reflexivity].
    apply key_eqb_eq in E; subst k; symmetry; exact Hx.
  - simpl in Hx, H.
    destruct (store_get s (KVar (out x))) as [[| | | l |] |] eqn:Ex; try discriminate.
    destruct (xeval reals s (oute i)) as [[| j | | |] |]; try discriminate.
    destruct (nth_z j l) as [a' |] eqn:En; [| discriminate]; injection Hx as ->.
    unfold nth_z, replace_nth_z in *; destruct (j <? 0)%Z; [discriminate |].
    destruct (replace_nth (Z.to_nat j) a l) as [l1 |] eqn:Er; [| discriminate].
    rewrite (replace_nth_same _ _ _ _ En Er) in H; injection H as <-; rewrite get_set.
    destruct (key_eqb (KVar (out x)) k) eqn:E; [| reflexivity].
    apply key_eqb_eq in E; subst k; symmetry; exact Ex.
Qed.

(* ---------------------------------------------------------------------------
   A transformation of blocks is correct when it keeps the discipline and
   refines every good block. *)

Definition correct (f : list (dstmt W) -> list (dstmt W)) : Prop :=
  forall sc wr ss, gd sc wr ss -> incl wr sc -> Forall consistent sc ->
  gd sc wr (f ss) /\ sim sc ss (f ss).

(* The identity is correct. *)
Lemma id_correct : correct (fun ss => ss).
Proof. intros sc wr ss Hg Hwr Hc; split; [exact Hg | exact (frame_sim _ _ _ Hg Hwr)]. Qed.

(* The head of a definition, with its expression simplified. *)
Lemma head_define sc so v e :
  expr_ok sc e ->
  forall s s' t, agree sc s s' -> exec reals (outs (DDefine so v e)) s = Some t ->
  exists t', exec reals (outs (DDefine so v (simplify_expr nat e))) s' = Some t' /\ agree (v :: sc) t t'.
Proof.
  intros He s s' t Hag H; rewrite exec_define in H |- *.
  destruct (xeval reals s (oute e)) as [w |] eqn:E; [| discriminate]; injection H as <-.
  rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag), (xeval_simplify _ _ _ E).
  eexists; split; [reflexivity | apply agree_set_cons; exact Hag].
Qed.

(* Simplifying each statement of a block, its expressions and the blocks it
   contains, is correct when simplifying the contained blocks is. *)
Lemma simplify_stmt_correct n : correct (simplify_stmts nat n) -> correct (map (simplify_stmt nat (S n))).
Proof.
  intros HA sc wr ss Hg; induction Hg as [sc wr | sc wr ty v e r He Hv Hcv Hr IH | sc wr v e r He Hv Hcv Hr IH
                 | sc wr v r Hv Hcv Hr IH | sc wr v r Hv Hcv Hr IH
                 | sc wr l e r Hl He Hr IH | sc wr l e r Hl He Hr IH
                 | sc wr c t e r Hc Ht IHt He IHe Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr e r He Hr IH];
    intros Hwr Hcs; simpl map.
  - split; [constructor | intros s s' t Hag H; injection H as <-; exists s'; split; [reflexivity | exact Hag]].
  - destruct (IH (incl_tl _ Hwr) (Forall_cons _ Hcv Hcs)) as [Hg' Hs'].
    split; [apply GdConstant; auto; apply expr_ok_simplify; auto |].
    apply sim_cons with (v :: sc); [apply incl_tl, incl_refl | apply head_define; auto | exact Hs'].
  - destruct (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcv Hcs)) as [Hg' Hs'].
    split; [apply GdMutable; auto; apply expr_ok_simplify; auto |].
    apply sim_cons with (v :: sc); [apply incl_tl, incl_refl | apply head_define; auto | exact Hs'].
  - destruct (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcv Hcs)) as [Hg' Hs'].
    split; [apply GdRealVar; auto |].
    apply sim_cons with (v :: sc); [apply incl_tl, incl_refl | | exact Hs'].
    intros s s' t Hag H; simpl simplify_stmt; rewrite exec_realvar in H |- *; injection H as <-.
    eexists; split; [reflexivity | apply agree_set_cons; exact Hag].
  - destruct (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcv Hcs)) as [Hg' Hs'].
    split; [apply GdTape; auto |].
    apply sim_cons with (v :: sc); [apply incl_tl, incl_refl | | exact Hs'].
    intros s s' t Hag H; simpl simplify_stmt; rewrite exec_tape in H |- *; injection H as <-.
    eexists; split; [reflexivity | apply agree_set_cons; exact Hag].
  - destruct (IH Hwr Hcs) as [Hg' Hs'].
    split; [apply GdAssign; auto; [apply lhs_ok_simplify | apply expr_ok_simplify]; auto |].
    apply sim_cons with sc; [apply incl_refl | | exact Hs'].
    intros s s' t Hag H; simpl simplify_stmt; rewrite exec_assign in H |- *.
    destruct (xeval reals s (oute e)) as [w |] eqn:E; [| discriminate].
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag), (xeval_simplify _ _ _ E).
    exact (assign_agree _ _ _ _ _ _ _ Hwr (lhs_ok_simplify _ _ _ Hl) Hag (assign_simplify _ _ _ _ _ _ Hl H)).
  - destruct (IH Hwr Hcs) as [Hg' Hs'].
    split; [apply GdIncrement; auto; [apply lhs_ok_simplify | apply expr_ok_simplify]; auto |].
    apply sim_cons with sc; [apply incl_refl | | exact Hs'].
    intros s s' t Hag H; simpl simplify_stmt; rewrite exec_increment in H |- *.
    destruct (xeval reals s (oute l)) as [[a | | | |] |] eqn:El; try discriminate.
    destruct (xeval reals s (oute e)) as [[b | | | |] |] eqn:E; try discriminate.
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag), (xeval_simplify _ _ _ E).
    rewrite <- (xeval_agree _ _ _ _ (lhs_expr_ok _ _ _ Hwr (lhs_ok_simplify _ _ _ Hl)) Hag),
            (xeval_simplify _ _ _ El).
    exact (assign_agree _ _ _ _ _ _ _ Hwr (lhs_ok_simplify _ _ _ Hl) Hag (assign_simplify _ _ _ _ _ _ Hl H)).
  - destruct (IH Hwr Hcs) as [Hg' Hs'].
    destruct (HA _ _ _ Ht Hwr Hcs) as [Ht' Hst]; destruct (HA _ _ _ He Hwr Hcs) as [He' Hse].
    split; [apply GdBranch; auto; apply expr_ok_simplify; auto |].
    apply sim_cons with sc; [apply incl_refl | | exact Hs'].
    intros s s' t0 Hag H; simpl simplify_stmt; rewrite exec_branch in H |- *.
    destruct (xeval reals s (oute c)) as [w |] eqn:E; [| discriminate].
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hc) Hag), (xeval_simplify _ _ _ E).
    destruct w as [| | [] | |]; try discriminate; [exact (Hst _ _ _ Hag H) | exact (Hse _ _ _ Hag H)].
  - destruct (IH Hwr Hcs) as [Hg' Hs'].
    destruct (HA _ _ _ Hb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs)) as [Hb' Hsb].
    split; [apply GdFor; auto; apply expr_ok_simplify; auto |].
    apply sim_cons with sc; [apply incl_refl | | exact Hs'].
    intros s s' t0 Hag H; simpl simplify_stmt; rewrite exec_for in H |- *.
    destruct (xeval reals s (oute lo)) as [[| l | | |] |] eqn:El; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |] eqn:Eh; try discriminate.
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hlo) Hag), (xeval_simplify _ _ _ El).
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hhi) Hag), (xeval_simplify _ _ _ Eh).
    refine (exec_up_sim (agree sc) (agree (i :: sc)) _ _ _ (agree_index sc i) _ _ _ _ _ _ Hag H).
    intros u u' v Hu Hv; destruct (Hsb _ _ _ Hu Hv) as (v' & Hv' & Ha').
    exists v'; split; [exact Hv' | exact (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Ha')].
  - destruct (IH Hwr Hcs) as [Hg' Hs'].
    destruct (HA _ _ _ Hb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs)) as [Hb' Hsb].
    split; [apply GdForBack; auto; apply expr_ok_simplify; auto |].
    apply sim_cons with sc; [apply incl_refl | | exact Hs'].
    intros s s' t0 Hag H; simpl simplify_stmt; rewrite exec_forback in H |- *.
    destruct (xeval reals s (oute lo)) as [[| l | | |] |] eqn:El; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |] eqn:Eh; try discriminate.
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hlo) Hag), (xeval_simplify _ _ _ El).
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ Hhi) Hag), (xeval_simplify _ _ _ Eh).
    refine (exec_down_sim (agree sc) (agree (i :: sc)) _ _ _ (agree_index sc i) _ _ _ _ _ _ Hag H).
    intros u u' v Hu Hv; destruct (Hsb _ _ _ Hu Hv) as (v' & Hv' & Ha').
    exists v'; split; [exact Hv' | exact (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Ha')].
  - destruct (IH Hwr Hcs) as [Hg' Hs'].
    split; [apply GdReturn; auto; apply expr_ok_simplify; auto |].
    apply sim_cons with sc; [apply incl_refl | | exact Hs'].
    intros s s' t Hag H; simpl simplify_stmt; rewrite exec_return in H |- *.
    destruct (xeval reals s (oute e)) as [w |] eqn:E; [| discriminate]; injection H as <-.
    rewrite <- (xeval_agree _ _ _ _ (expr_ok_simplify _ _ He) Hag), (xeval_simplify _ _ _ E).
    eexists; split; [reflexivity | apply agree_set; exact Hag].
Qed.

(* ---------------------------------------------------------------------------
   The rewrites of fuse, one by one. *)

(* Two stores equal on every key agree with what the first agrees with. *)
(* A real literal, read by the evaluator. *)
Lemma xeval_real s l x : real_lit l = Some x -> xeval reals s (DReal l) = Some (VReal x).
Proof. simpl; intros ->; reflexivity. Qed.

Lemma agree_same sc s1 s s' :
  (forall k, store_get s1 k = store_get s k) -> agree sc s s' -> agree sc s1 s'.
Proof. intros He [H R]; split; [intros x Hx; rewrite He |]; rewrite ?He; auto. Qed.

(* An accumulation of zero is dropped: it rewrites the location with its own value. *)
Lemma sim_zero_increment sc wr l r r' :
  gd sc wr (DIncrement l (DReal "0") :: r) -> sim sc r r' ->
  sim sc (DIncrement l (DReal "0") :: r) r'.
Proof.
  intros Hg Hr s s' t Hag H; inversion Hg as [| | | | | | ? ? ? ? ? Hl | | | |]; subst.
  rewrite ex_cons, exec_increment in H; cbn [out_dexpr] in H; rewrite (xeval_real s "0" 0 lit_0) in H.
  destruct (xeval reals s (oute l)) as [[a | | | |] |] eqn:El; try discriminate.
  rewrite Rplus_0_r in H.
  destruct (assign reals s (oute l) (VReal a)) as [s1 |] eqn:E; [| discriminate].
  exact (Hr _ _ _ (agree_same _ _ _ _ (assign_same _ _ _ _ _ _ Hl El E) Hag) H).
Qed.

(* A definition no later statement reads is dropped. *)
Lemma sim_drop_define sc so v e r r' :
  ~ In v sc -> consistent v -> Forall consistent sc -> sim sc r r' -> sim sc (DDefine so v e :: r) r'.
Proof.
  intros Hv Hcv Hcs Hr s s' t Hag H; rewrite ex_cons, exec_define in H.
  destruct (xeval reals s (oute e)); [| discriminate].
  exact (Hr _ _ _ (agree_set_out _ _ _ _ _ Hcs Hcv Hv Hag) H).
Qed.

(* A definition the simplified rest no longer reads is dropped. *)
Lemma sim_drop_define_after sc wr so v e r r' :
  ~ In v sc -> consistent v -> Forall consistent sc -> incl wr sc ->
  sim (v :: sc) r r' -> gd sc wr r' -> sim sc (DDefine so v e :: r) r'.
Proof.
  intros Hv Hcv Hcs Hwr Hr Hg' s s' t Hag H; rewrite ex_cons, exec_define in H.
  destruct (xeval reals s (oute e)) as [w |]; [| discriminate].
  destruct (Hr _ _ _ (agree_refl _ _) H) as (t1 & H1 & Ha1).
  destruct (frame _ _ _ Hg' Hwr _ _ _ (agree_set_out _ _ _ _ w Hcs Hcv Hv Hag) H1) as (t' & H' & Ha').
  exists t'; split; [exact H' |].
  apply agree_trans with t1; [apply (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Ha1) |].
  exact (agree_incl _ _ _ _ (after_scope_incl _ _) Ha').
Qed.

(* first_mention splits a block before the first statement that mentions v. *)
Lemma first_mention_spec v ss b m a :
  first_mention nat v ss = Some (b, m, a) -> ss = b ++ m :: a /\ existsb (mentions nat v) b = false.
Proof.
  revert b; induction ss as [| st ss IH]; intros b H; simpl in H; [discriminate |].
  destruct (mentions nat v st) eqn:Em.
  - injection H as <- <- <-; auto.
  - destruct (first_mention nat v ss) as [[[b' m'] a'] |] eqn:E; [| discriminate].
    injection H as <- <- <-; destruct (IH _ eq_refl) as [-> Hb]; simpl; rewrite Em, Hb; auto.
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
  revert wr; induction ss as [| [[] | | | | | | | | | | ] r IH]; intros wr; simpl;
    try rewrite IH; simpl; tauto.
Qed.

(* A block that does not mention v does not define it. *)
Lemma defs_unmentioned v ss : existsb (mentions nat v) ss = false -> ~ In v (defs ss).
Proof.
  induction ss as [| st r IH]; simpl; intros H; [auto |].
  rewrite orb_false_iff in H; destruct H as [Hs Hr].
  destruct st; simpl in *; try exact (IH Hr); intros [E | Hin]; try exact (IH Hr Hin);
    subst; rewrite dvar_eq_refl in Hs; simpl in Hs; discriminate.
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
  intros Hg Hwr Hcs Hb Hx He Hso.
  inversion Hg as [| | ? ? ? ? ? He0 Hv Hcv Hrest | | | | | | | |]; subst.
  destruct (gd_app_inv _ _ _ _ Hrest) as [Hbefore Hi].
  inversion Hi as [| | | | | | ? ? ? ? ? Hlx Hee Hafter | | | |]; subst.
  set (SB := after_scope sc before); set (WB := after_wr wr before).
  assert (Hcs' : Forall consistent (v :: sc)) by (constructor; auto).
  assert (Hc_after : Forall consistent (after_scope (v :: sc) before)) by (eapply after_consistent; eauto).
  (* the accumulated variable is v *)
  assert (Hxv : x = v).
  { apply dvar_eq_true_eq; auto. eapply Forall_forall; [exact Hc_after |].
    apply (after_incl (v :: wr) (v :: sc) before (incl_both _ _ _ Hwr)); exact Hlx. }
  subst x.
  assert (HvSB : ~ In v SB).
  { unfold SB; rewrite in_after_scope; intros [Hin | Hin]; [exact (defs_unmentioned _ _ Hb Hin) | contradiction]. }
  assert (Hscope : forall y, In y (after_scope (v :: sc) before) <-> In y (v :: SB)).
  { intros y; unfold SB; rewrite in_after_scope; simpl; rewrite in_after_scope; tauto. }
  assert (Hwscope : forall y, In y (after_wr (v :: wr) before) <-> In y (v :: WB)).
  { intros y; unfold WB; rewrite in_after_wr_iff; simpl; rewrite in_after_wr_iff; tauto. }
  (* the new block is good *)
  assert (Hbefore' : gd sc wr before).
  { apply (gd_remove _ _ _ v Hbefore Hb); [intros y Hy [<- | Hin] | intros y Hy [<- | Hin] |];
      try contradiction; auto; apply incl_tl, incl_refl. }
  assert (HeSB : expr_ok SB e).
  { apply (expr_ok_remove _ _ _ _ Hee He); intros y Hy Hin; apply Hscope in Hin.
    destruct Hin as [E | Hin]; [exfalso; apply Hy; symmetry; exact E | exact Hin]. }
  assert (Hafter' : gd (v :: SB) (v :: WB) after).
  { apply (gd_mono _ _ _ Hafter); intros y Hin; [apply Hscope | apply Hscope | apply Hwscope]; auto. }
  assert (HWB : incl WB SB) by (apply after_incl; exact Hwr).
  assert (Hnew : exists wr', gd (v :: SB) wr' after /\ incl wr' (v :: SB) /\
                             gd SB WB (DDefine so v e :: after)).
  { destruct Hso as [-> | [-> Hw]].
    - exists (v :: WB); split; [exact Hafter' | split; [apply incl_both; exact HWB |]].
      apply GdMutable; auto.
    - assert (Hafter'' : gd (v :: SB) WB after).
      { apply (gd_drop_wr _ _ _ v Hafter' Hw); intros y Hy [<- | Hin]; [contradiction | exact Hin]. }
      exists WB; split; [exact Hafter'' | split; [apply incl_tl; exact HWB |]].
      apply GdConstant; auto. }
  destruct Hnew as (wr' & Hafter_new & Hwr' & Hdef).
  split; [apply gd_app; [exact Hbefore' | exact Hdef] |].
  (* the simulation *)
  intros s s' t Hag H.
  rewrite ex_cons, exec_define in H; cbn [out_dexpr] in H; rewrite (xeval_real s "0" 0 lit_0), ex_app in H.
  set (s1 := store_set s (KVar (out v)) (VReal 0)) in H.
  destruct (ex before s1) as [s2 |] eqn:E2; [| discriminate].
  assert (Hv2 : store_get s2 (KVar (out v)) = Some (VReal 0)).
  { rewrite (preserve_unmentioned _ _ _ v Hbefore (incl_both _ _ _ Hwr) Hcs' Hcv Hb _ _ E2).
    apply get_set_same. }
  destruct (frame _ _ _ Hbefore' Hwr _ _ _ (agree_set_out _ _ _ _ _ Hcs Hcv Hv Hag) E2)
    as (s2' & E2' & Hag2).
  rewrite ex_cons, exec_increment in H; cbn [out_dexpr xeval] in H; rewrite Hv2 in H.
  destruct (xeval reals s2 (oute e)) as [[b | | | |] |] eqn:Eb; try discriminate.
  cbn [assign out_dexpr] in H; rewrite Rplus_0_l in H.
  rewrite ex_app, E2', ex_cons, exec_define.
  rewrite <- (xeval_agree _ _ _ _ HeSB Hag2), Eb.
  destruct (frame _ _ _ Hafter_new Hwr' _ _ _ (agree_set_cons _ _ _ v (VReal b) Hag2) H)
    as (t' & H' & Ha').
  exists t'; split; [exact H' |].
  apply (agree_incl sc (after_scope (v :: SB) after)); [| exact Ha']; intros y Hy.
  apply after_scope_incl; right; unfold SB; apply after_scope_incl; exact Hy.
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
  intros [H R]; split.
  - intros z [<- | Hz] Hzv; rewrite !get_set.
    + rewrite (proj2 (key_eqb_eq _ _) eq_refl); reflexivity.
    + destruct (key_eqb _ _); auto.
  - rewrite !get_set; destruct (key_eqb _ _); auto.
Qed.

Lemma agree_ex_set v sc s s' k w : agree_ex v sc s s' -> agree_ex v sc (store_set s k w) (store_set s' k w).
Proof. intros [H R]; split; [intros z Hz Hzv |]; rewrite !get_set; destruct (key_eqb _ _); auto. Qed.

Lemma agree_ex_incl v sc1 sc2 s s' : incl sc1 sc2 -> agree_ex v sc2 s s' -> agree_ex v sc1 s s'.
Proof. intros Hi [H R]; split; auto. Qed.

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
  intros He Hcs Hag Hv; induction e as [y | | | a IHa i IHi | f a IHa | f a IHa b IHb];
    simpl in *; try reflexivity.
  - destruct (dvar_eq nat y v) eqn:E.
    + rewrite (dvar_eq_true_eq _ _ (proj1 (Forall_forall _ _) Hcs _ He) Hcv E), Hv; simpl; rewrite Hlit; reflexivity.
    + exact (proj1 Hag _ He (dvar_eq_false_neq _ _ E)).
  - rewrite IHa, IHi; tauto.
  - rewrite IHa; tauto.
  - rewrite IHa, IHb; tauto.
Qed.

Lemma expr_ok_replace sc1 sc2 e :
  expr_ok sc1 e -> (forall y, y <> v -> In y sc1 -> In y sc2) -> expr_ok sc2 (re e).
Proof.
  intros He Hs; induction e as [y | | | | |]; simpl in *; intuition.
  destruct (dvar_eq nat y v) eqn:E; simpl; [exact I | exact (Hs _ (dvar_eq_false_neq _ _ E) He)].
Qed.

(* A location assigned is writable, hence not the constant: unchanged by the replacement. *)
Lemma lhs_replace sc wr lh :
  lhs_ok sc wr lh -> incl wr sc -> Forall consistent sc -> ~ In v wr ->
  exists y i, In y wr /\ y <> v /\ (lh = DVar y /\ re lh = DVar y \/ lh = DAt (DVar y) i /\ re lh = DAt (DVar y) (re i)).
Proof.
  intros Hl Hwr Hcs Hv; destruct lh as [y | | | [y | | | | |] i | |]; simpl in Hl; try contradiction.
  - assert (Hyv : y <> v) by (intros ->; contradiction).
    exists y, (DInt 0%Z); repeat split; auto; left; split; [reflexivity |]; simpl.
    rewrite (neq_dvar_eq_false _ _ (proj1 (Forall_forall _ _) Hcs _ (Hwr _ Hl)) Hcv Hyv); reflexivity.
  - destruct Hl as [Hl Hi]; assert (Hyv : y <> v) by (intros ->; contradiction).
    exists y, i; repeat split; auto; right; split; [reflexivity |]; simpl.
    rewrite (neq_dvar_eq_false _ _ (proj1 (Forall_forall _ _) Hcs _ (Hwr _ Hl)) Hcv Hyv); reflexivity.
Qed.

Lemma lhs_ok_replace sc1 sc2 wr lh :
  lhs_ok sc1 wr lh -> incl wr sc1 -> Forall consistent sc1 -> ~ In v wr ->
  (forall y, y <> v -> In y sc1 -> In y sc2) -> lhs_ok sc2 wr (re lh).
Proof.
  intros Hl Hwr Hcs Hv Hs.
  destruct (lhs_replace _ _ _ Hl Hwr Hcs Hv) as (y & i & Hy & Hyv & [[-> ->] | [-> ->]]); simpl; auto.
  split; [exact Hy |]; simpl in Hl; eapply expr_ok_replace; [apply Hl | exact Hs].
Qed.

(* The replaced block keeps the discipline, without the constant in scope. *)
Lemma gd_replace sc0 wr0 ss0 :
  gd sc0 wr0 ss0 -> Forall consistent sc0 -> In v sc0 -> ~ In v wr0 -> incl wr0 sc0 ->
  forall sc2, (forall y, y <> v -> In y sc0 -> In y sc2) -> incl sc2 sc0 -> gd sc2 wr0 (map rs ss0).
Proof.
  assert (Hext : forall (z : dvar W) l1 l2, (forall y, y <> v -> In y l1 -> In y l2) ->
                 forall y, y <> v -> In y (z :: l1) -> In y (z :: l2)).
  { intros z l1 l2 H y Hy [<- | Hin]; [left | right]; auto. }
  assert (Hnew : forall (y : dvar W) sc wr, In v sc -> ~ In y sc -> ~ In v wr -> ~ In v (y :: wr)).
  { intros y sc wr Hvs Hy Hv [E | Hin]; [subst; contradiction | contradiction]. }
  induction 1 as [sc wr | sc wr ty y e r He Hy Hcy Hr IH | sc wr y e r He Hy Hcy Hr IH
                 | sc wr y r Hy Hcy Hr IH | sc wr y r Hy Hcy Hr IH
                 | sc wr lh e r Hl He Hr IH | sc wr lh e r Hl He Hr IH
                 | sc wr c t e r Hc Ht IHt He IHe Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr e r He Hr IH];
    intros Hcs Hvs Hv Hwr sc2 Hs Hb21; simpl.
  - constructor.
  - apply GdConstant; [eapply expr_ok_replace; eauto | intros Hin; apply Hy, Hb21, Hin | exact Hcy |].
    apply IH; [constructor; auto | right; exact Hvs | exact Hv | apply incl_tl; exact Hwr
              | apply Hext; exact Hs | apply incl_both; exact Hb21].
  - apply GdMutable; [eapply expr_ok_replace; eauto | intros Hin; apply Hy, Hb21, Hin | exact Hcy |].
    apply IH; [constructor; auto | right; exact Hvs | eapply Hnew; eauto | apply incl_both; exact Hwr
              | apply Hext; exact Hs | apply incl_both; exact Hb21].
  - apply GdRealVar; [intros Hin; apply Hy, Hb21, Hin | exact Hcy |].
    apply IH; [constructor; auto | right; exact Hvs | eapply Hnew; eauto | apply incl_both; exact Hwr
              | apply Hext; exact Hs | apply incl_both; exact Hb21].
  - apply GdTape; [intros Hin; apply Hy, Hb21, Hin | exact Hcy |].
    apply IH; [constructor; auto | right; exact Hvs | eapply Hnew; eauto | apply incl_both; exact Hwr
              | apply Hext; exact Hs | apply incl_both; exact Hb21].
  - apply GdAssign; [eapply lhs_ok_replace | eapply expr_ok_replace | apply IH]; eauto.
  - apply GdIncrement; [eapply lhs_ok_replace | eapply expr_ok_replace | apply IH]; eauto.
  - apply GdBranch; [eapply expr_ok_replace | apply IHt | apply IHe | apply IH]; eauto.
  - apply GdFor; [intros Hin; apply Hi, Hb21, Hin | exact Hci | eapply expr_ok_replace; eauto
                 | eapply expr_ok_replace; eauto | | apply IH; eauto].
    apply IHb; [constructor; auto | right; exact Hvs | exact Hv | apply incl_tl; exact Hwr
               | apply Hext; exact Hs | apply incl_both; exact Hb21].
  - apply GdForBack; [intros Hin; apply Hi, Hb21, Hin | exact Hci | eapply expr_ok_replace; eauto
                     | eapply expr_ok_replace; eauto | | apply IH; eauto].
    apply IHb; [constructor; auto | right; exact Hvs | exact Hv | apply incl_tl; exact Hwr
               | apply Hext; exact Hs | apply incl_both; exact Hb21].
  - apply GdReturn; [eapply expr_ok_replace | apply IH]; eauto.
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
  intros Hl Hwr Hcs Hv Hag Hx H.
  destruct (lhs_replace _ _ _ Hl Hwr Hcs Hv) as (y & i & Hy & Hyv & [[-> ->] | [-> ->]]).
  - simpl in H |- *; injection H as <-; eexists; split; [reflexivity |]; split; [apply agree_ex_set; exact Hag |].
    rewrite get_set_other; [exact Hx | apply key_neq; auto; eapply Forall_forall; eauto].
  - simpl in Hl; destruct Hl as [_ Hi]; destruct w as [e | | | |]; try discriminate.
    simpl in H |- *.
    rewrite <- (proj1 Hag y (Hwr _ Hy) Hyv), <- (xeval_replace sc s s' i Hi Hcs Hag Hx).
    destruct (store_get s (KVar (out y))) as [[| | | l0 |] |]; try discriminate.
    destruct (xeval reals s (oute i)) as [[| k | | |] |]; try discriminate.
    destruct (replace_nth_z k e l0); [| discriminate]; injection H as <-.
    eexists; split; [reflexivity |]; split; [apply agree_ex_set; exact Hag |].
    rewrite get_set_other; [exact Hx | apply key_neq; auto; eapply Forall_forall; eauto].
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
  assert (Hnew : forall (y : dvar W) sc wr, In v sc -> ~ In y sc -> ~ In v wr -> ~ In v (y :: wr)).
  { intros y sc wr Hvs Hy Hv [E | Hin]; [subst; contradiction | contradiction]. }
  assert (Hdef : forall (y : dvar W) sc s w, Forall consistent sc -> consistent y -> In v sc -> ~ In y sc ->
                 store_get s (KVar (out v)) = Some (VReal x) ->
                 store_get (store_set s (KVar (out y)) w) (KVar (out v)) = Some (VReal x)).
  { intros y sc s w Hcs Hcy Hvs Hy Hx; rewrite get_set_other; [exact Hx |].
    apply key_neq; auto; intros ->; contradiction. }
  induction 1 as [sc wr | sc wr ty y e r He Hy Hcy Hr IH | sc wr y e r He Hy Hcy Hr IH
                 | sc wr y r Hy Hcy Hr IH | sc wr y r Hy Hcy Hr IH
                 | sc wr lh e r Hl He Hr IH | sc wr lh e r Hl He Hr IH
                 | sc wr c t e r Hc Ht IHt He IHe Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr i lo hi b r Hi Hci Hlo Hhi Hb IHb Hr IH
                 | sc wr e r He Hr IH];
    intros Hwr Hcs Hvs Hv s s' t0 Hag Hx H; simpl map; try rewrite ex_cons in H |- *; simpl after_scope.
  - injection H as <-; exists s'; auto.
  - rewrite exec_define in H; simpl replace_stmt; rewrite exec_define.
    rewrite <- (xeval_replace _ _ _ _ He Hcs Hag Hx).
    destruct (xeval reals s (oute e)) as [w |]; [| discriminate].
    exact (IH (incl_tl _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs) Hv _ _ _
              (agree_ex_set_cons _ _ _ _ _ _ Hag) (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
  - rewrite exec_define in H; simpl replace_stmt; rewrite exec_define.
    rewrite <- (xeval_replace _ _ _ _ He Hcs Hag Hx).
    destruct (xeval reals s (oute e)) as [w |]; [| discriminate].
    exact (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs) (Hnew _ _ _ Hvs Hy Hv) _ _ _
              (agree_ex_set_cons _ _ _ _ _ _ Hag) (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
  - simpl replace_stmt; rewrite exec_realvar in H |- *.
    exact (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs) (Hnew _ _ _ Hvs Hy Hv) _ _ _
              (agree_ex_set_cons _ _ _ _ _ _ Hag) (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
  - simpl replace_stmt; rewrite exec_tape in H |- *.
    exact (IH (incl_both _ _ _ Hwr) (Forall_cons _ Hcy Hcs) (or_intror Hvs) (Hnew _ _ _ Hvs Hy Hv) _ _ _
              (agree_ex_set_cons _ _ _ _ _ _ Hag) (Hdef _ _ _ _ Hcs Hcy Hvs Hy Hx) H).
  - rewrite exec_assign in H; simpl replace_stmt; rewrite exec_assign.
    rewrite <- (xeval_replace _ _ _ _ He Hcs Hag Hx).
    destruct (xeval reals s (oute e)) as [w |]; [| discriminate].
    destruct (assign reals s (oute lh) w) as [s1 |] eqn:E; [| discriminate].
    destruct (assign_replace _ _ _ _ _ _ _ Hl Hwr Hcs Hv Hag Hx E) as (s1' & -> & Hag1 & Hx1).
    exact (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H).
  - rewrite exec_increment in H; simpl replace_stmt; rewrite exec_increment.
    rewrite <- (xeval_replace _ _ _ _ He Hcs Hag Hx),
            <- (xeval_replace _ _ _ _ (lhs_expr_ok _ _ _ Hwr Hl) Hcs Hag Hx).
    destruct (xeval reals s (oute lh)) as [[a | | | |] |]; try discriminate.
    destruct (xeval reals s (oute e)) as [[b | | | |] |]; try discriminate.
    destruct (assign reals s (oute lh) _) as [s1 |] eqn:E; [| discriminate].
    destruct (assign_replace _ _ _ _ _ _ _ Hl Hwr Hcs Hv Hag Hx E) as (s1' & -> & Hag1 & Hx1).
    exact (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H).
  - rewrite exec_branch in H; simpl replace_stmt; rewrite exec_branch.
    rewrite <- (xeval_replace _ _ _ _ Hc Hcs Hag Hx).
    destruct (xeval reals s (oute c)) as [[| | [] | |] |]; try discriminate.
    + destruct (ex t s) as [s1 |] eqn:E; [| discriminate].
      destruct (IHt Hwr Hcs Hvs Hv _ _ _ Hag Hx E) as (s1' & -> & Hag1 & Hx1).
      exact (IH Hwr Hcs Hvs Hv _ _ _ (agree_ex_incl _ _ _ _ _ (after_scope_incl _ _) Hag1) Hx1 H).
    + destruct (ex e s) as [s1 |] eqn:E; [| discriminate].
      destruct (IHe Hwr Hcs Hvs Hv _ _ _ Hag Hx E) as (s1' & -> & Hag1 & Hx1).
      exact (IH Hwr Hcs Hvs Hv _ _ _ (agree_ex_incl _ _ _ _ _ (after_scope_incl _ _) Hag1) Hx1 H).
  - rewrite exec_for in H; simpl replace_stmt; rewrite exec_for.
    rewrite <- (xeval_replace _ _ _ _ Hlo Hcs Hag Hx), <- (xeval_replace _ _ _ _ Hhi Hcs Hag Hx).
    destruct (xeval reals s (oute lo)) as [[| l0 | | |] |]; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |]; try discriminate.
    destruct (exec_up R (ex b) (out i) l0 (count l0 h) s) as [s1 |] eqn:E; [| discriminate].
    edestruct (exec_up_sim (fun u u' => agree_ex v sc u u' /\ store_get u (KVar (out v)) = Some (VReal x))
                 (fun u u' => agree_ex v (i :: sc) u u' /\ store_get u (KVar (out v)) = Some (VReal x))
                 (ex b) (ex (map rs b)) (out i)) as (s1' & -> & Hag1 & Hx1);
      [| | exact (conj Hag Hx) | exact E | exact (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H)].
    + intros u u' w [Hu Hxu]; split; [apply agree_ex_set_cons; exact Hu |].
      exact (Hdef _ _ _ _ Hcs Hci Hvs Hi Hxu).
    + intros u u' w [Hu Hxu] Hw.
      destruct (IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs) (or_intror Hvs) Hv _ _ _ Hu Hxu Hw)
        as (w' & Hw' & Hag' & Hx').
      exists w'; split; [exact Hw' | split; [| exact Hx']].
      apply (agree_ex_incl _ _ _ _ _ (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hag').
  - rewrite exec_forback in H; simpl replace_stmt; rewrite exec_forback.
    rewrite <- (xeval_replace _ _ _ _ Hlo Hcs Hag Hx), <- (xeval_replace _ _ _ _ Hhi Hcs Hag Hx).
    destruct (xeval reals s (oute lo)) as [[| l0 | | |] |]; try discriminate.
    destruct (xeval reals s (oute hi)) as [[| h | | |] |]; try discriminate.
    destruct (exec_down R (ex b) (out i) (h - 1) (count l0 h) s) as [s1 |] eqn:E; [| discriminate].
    edestruct (exec_down_sim (fun u u' => agree_ex v sc u u' /\ store_get u (KVar (out v)) = Some (VReal x))
                 (fun u u' => agree_ex v (i :: sc) u u' /\ store_get u (KVar (out v)) = Some (VReal x))
                 (ex b) (ex (map rs b)) (out i)) as (s1' & -> & Hag1 & Hx1);
      [| | exact (conj Hag Hx) | exact E | exact (IH Hwr Hcs Hvs Hv _ _ _ Hag1 Hx1 H)].
    + intros u u' w [Hu Hxu]; split; [apply agree_ex_set_cons; exact Hu |].
      exact (Hdef _ _ _ _ Hcs Hci Hvs Hi Hxu).
    + intros u u' w [Hu Hxu] Hw.
      destruct (IHb (incl_tl _ Hwr) (Forall_cons _ Hci Hcs) (or_intror Hvs) Hv _ _ _ Hu Hxu Hw)
        as (w' & Hw' & Hag' & Hx').
      exists w'; split; [exact Hw' | split; [| exact Hx']].
      apply (agree_ex_incl _ _ _ _ _ (fun y Hy => after_scope_incl _ _ _ (in_cons _ _ _ Hy)) Hag').
  - rewrite exec_return in H; simpl replace_stmt; rewrite exec_return.
    rewrite <- (xeval_replace _ _ _ _ He Hcs Hag Hx).
    destruct (xeval reals s (oute e)) as [w |]; [| discriminate].
    refine (IH Hwr Hcs Hvs Hv _ _ _ (agree_ex_set _ _ _ _ _ _ Hag) _ H).
    rewrite get_set_other; [exact Hx | discriminate].
Qed.

End Replace.

Lemma xeval_real_inv s l w : xeval reals s (DReal l) = Some w -> exists x, real_lit l = Some x /\ w = VReal x.
Proof.
  change (xeval reals s (DReal l)) with (match real_lit l with Some x => Some (VReal x) | None => None end).
  destruct (real_lit l) as [x |]; intros H; [injection H as <-; eauto | discriminate].
Qed.

(* A constant defined by a literal is replaced by the literal in the rest of
   the block, and its definition dropped. *)
Lemma fuse_literal sc wr t v l r :
  gd sc wr (DDefine (DConstant t) v (DReal l) :: r) -> incl wr sc -> Forall consistent sc ->
  gd sc wr (map (replace_stmt nat v (DReal l)) r) /\
  sim sc (DDefine (DConstant t) v (DReal l) :: r) (map (replace_stmt nat v (DReal l)) r).
Proof.
  intros Hg Hwr Hcs; inversion Hg as [| ? ? ? ? ? ? He Hv Hcv Hr | | | | | | | | |]; subst.
  assert (Hvw : ~ In v wr) by (intros Hin; apply Hv, Hwr, Hin).
  split.
  - apply (gd_replace v l Hcv (v :: sc) wr r Hr (Forall_cons _ Hcv Hcs) (or_introl eq_refl) Hvw
             (incl_tl _ Hwr) sc); [| apply incl_tl, incl_refl].
    intros y Hy [<- | Hin]; [contradiction | exact Hin].
  - intros s s' t0 Hag H; rewrite ex_cons, exec_define in H; cbn [out_dexpr] in H.
    destruct (xeval reals s (DReal l)) as [w |] eqn:Ew; [| discriminate].
    destruct (xeval_real_inv _ _ _ Ew) as (x & Hlit & ->).
    set (s1 := store_set s (KVar (out v)) (VReal x)) in H.
    assert (Hag1 : agree_ex v (v :: sc) s1 s').
    { split.
      - intros y Hy Hyv; destruct Hy as [<- | Hy]; [exfalso; apply Hyv; reflexivity |].
        unfold s1; rewrite get_set_other; [exact (proj1 Hag _ Hy) |].
        apply key_neq; [exact Hcv | eapply Forall_forall; eauto | intros E; apply Hyv; symmetry; exact E].
      - unfold s1; rewrite get_set_other; [exact (proj2 Hag) | discriminate]. }
    destruct (replace_sim v l x Hcv Hlit (v :: sc) wr r Hr (incl_tl _ Hwr) (Forall_cons _ Hcv Hcs)
                (or_introl eq_refl) Hvw s1 s' t0 Hag1 (get_set_same _ _ _) H) as (t' & H' & Ha' & _).
    exists t'; split; [exact H' | split; [| exact (proj2 Ha')]].
    intros y Hy; apply (proj1 Ha'); [apply after_scope_incl; right; exact Hy | intros ->; contradiction].
Qed.

(* ---------------------------------------------------------------------------
   fuse and simplify are correct, by induction on the fuel. *)

(* A statement kept in front of the fused rest. *)
Lemma fuse_keep n sc wr st r :
  correct (fuse nat n) -> gd sc wr (st :: r) -> incl wr sc -> Forall consistent sc ->
  gd sc wr (st :: fuse nat n r) /\ sim sc (st :: r) (st :: fuse nat n r).
Proof.
  intros HC Hg Hwr Hcs; destruct (gd_app_inv sc wr [st] r Hg) as [Hst Hr].
  destruct (HC _ _ _ Hr (after_incl _ _ _ Hwr) (after_consistent _ _ _ Hst Hcs)) as [Hg' Hs'].
  split; [exact (gd_app sc wr [st] _ Hst Hg') | exact (sim_keep _ _ _ _ _ Hg Hwr Hs')].
Qed.

Lemma correct_compose f g : correct f -> correct g -> correct (fun ss => g (f ss)).
Proof.
  intros Hf Hg sc wr ss Hss Hwr Hcs; destruct (Hf _ _ _ Hss Hwr Hcs) as [Hf1 Hf2].
  destruct (Hg _ _ _ Hf1 Hwr Hcs) as [Hg1 Hg2]; split; [exact Hg1 | exact (sim_trans _ _ _ _ Hf2 Hg2)].
Qed.

(* The mutable case of fuse, when no accumulation is fused: the definition is
   kept, or dropped when the rest does not mention it. *)
Lemma fuse_mutable_fallback n sc wr v e r :
  correct (fuse nat n) -> gd sc wr (DDefine DMutable v e :: r) -> incl wr sc -> Forall consistent sc ->
  let r' := if negb (existsb (mentions nat v) r) then fuse nat n r else DDefine DMutable v e :: fuse nat n r in
  gd sc wr r' /\ sim sc (DDefine DMutable v e :: r) r'.
Proof.
  intros HC Hg Hwr Hcs r'; unfold r'.
  destruct (existsb (mentions nat v) r) eqn:Em; simpl negb; cbv iota; [exact (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs) |].
  inversion Hg as [| | ? ? ? ? ? He Hv Hcv Hr | | | | | | | |]; subst.
  assert (Hr' : gd sc wr r).
  { apply (gd_remove _ _ _ v Hr Em); [intros y Hy [<- | Hin] | intros y Hy [<- | Hin] |];
      try contradiction; auto; apply incl_tl, incl_refl. }
  destruct (HC _ _ _ Hr' Hwr Hcs) as [Hg' Hs'].
  split; [exact Hg' | exact (sim_drop_define _ _ _ _ _ _ Hv Hcv Hcs Hs')].
Qed.

(* The constant case of fuse, for an expression that is not a literal: the
   definition is kept, or dropped when the fused rest does not mention it. *)
Lemma fuse_constant_other n sc wr t v e r :
  correct (fuse nat n) -> gd sc wr (DDefine (DConstant t) v e :: r) -> incl wr sc -> Forall consistent sc ->
  let r' := fuse nat n r in
  let res := if existsb (mentions nat v) r' then DDefine (DConstant t) v e :: r' else r' in
  gd sc wr res /\ sim sc (DDefine (DConstant t) v e :: r) res.
Proof.
  intros HC Hg Hwr Hcs r' res; unfold res, r'.
  destruct (existsb (mentions nat v) (fuse nat n r)) eqn:Em; [exact (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs) |].
  inversion Hg as [| ? ? ? ? ? ? He Hv Hcv Hr | | | | | | | | |]; subst.
  destruct (HC _ _ _ Hr (incl_tl _ Hwr) (Forall_cons _ Hcv Hcs)) as [Hg' Hs'].
  assert (Hg'' : gd sc wr (fuse nat n r)).
  { apply (gd_remove _ _ _ v Hg' Em); [intros y Hy [<- | Hin] | |]; try contradiction; auto;
      apply incl_tl, incl_refl. }
  split; [exact Hg'' | exact (sim_drop_define_after _ _ _ _ _ _ _ Hv Hcv Hcs Hwr Hs' Hg'')].
Qed.

(* One more unit of fuel for fuse. *)
Lemma fuse_correct_step n :
  correct (fuse nat n) -> correct (simplify_stmts nat n) -> correct (fuse nat (S n)).
Proof.
  intros HC HA sc wr ss Hg Hwr Hcs; destruct ss as [| st r].
  { split; [constructor | intros s s' t Hag H; injection H as <-; exists s'; split; [reflexivity | exact Hag]]. }
  destruct st as [[t | ] v e | | | | l e | | | | | |]; cbn [fuse];
    try exact (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs).
  - (* a constant *)
    destruct e as [| l | | | |]; try exact (fuse_constant_other _ _ _ _ _ _ _ HC Hg Hwr Hcs).
    destruct (fuse_literal _ _ _ _ _ _ Hg Hwr Hcs) as [Hg1 Hs1].
    destruct (HA _ _ _ Hg1 Hwr Hcs) as [Hg2 Hs2]; split; [exact Hg2 | exact (sim_trans _ _ _ _ Hs1 Hs2)].
  - (* a mutable *)
    destruct (is_lit nat "0" e) eqn:E0; [| exact (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs)].
    apply is_lit_eq in E0; subst e.
    destruct (first_mention nat v r) as [[[b m] a] |] eqn:Fm;
      [| exact (fuse_mutable_fallback _ _ _ _ _ _ HC Hg Hwr Hcs)].
    destruct m as [| | | | [x | | | | |] e | | | | | |];
      try exact (fuse_mutable_fallback _ _ _ _ _ _ HC Hg Hwr Hcs).
    destruct (dvar_eq nat x v && negb (mentions_expr nat v e)) eqn:Ec;
      [| exact (fuse_mutable_fallback _ _ _ _ _ _ HC Hg Hwr Hcs)].
    apply andb_true_iff in Ec; destruct Ec as [Hx He]; apply negb_true_iff in He.
    destruct (first_mention_spec _ _ _ _ _ Fm) as [-> Hb].
    set (so := if existsb (writes nat v) a then DMutable else DConstant Real).
    assert (Hso : so = DMutable \/ (so = DConstant Real /\ existsb (writes nat v) a = false)).
    { unfold so; destruct (existsb (writes nat v) a); auto. }
    destruct (fuse_fused _ _ _ _ _ _ _ so Hg Hwr Hcs Hb Hx He Hso) as [Hg1 Hs1].
    destruct (HC _ _ _ Hg1 Hwr Hcs) as [Hg2 Hs2]; split; [exact Hg2 | exact (sim_trans _ _ _ _ Hs1 Hs2)].
  - (* an accumulation *)
    destruct (is_lit nat "0" e) eqn:E0; [| exact (fuse_keep _ _ _ _ _ HC Hg Hwr Hcs)].
    apply is_lit_eq in E0; subst e.
    inversion Hg as [| | | | | | ? ? ? ? ? Hl He Hr | | | |]; subst.
    destruct (HC _ _ _ Hr Hwr Hcs) as [Hg' Hs'].
    split; [exact Hg' | exact (sim_zero_increment _ _ _ _ _ Hg Hs')].
Qed.

Lemma map_simplify_stmt_0 ss : map (simplify_stmt nat 0) ss = ss.
Proof.
  induction ss as [| s ss IH]; [reflexivity |].
  change (simplify_stmt nat 0 s :: map (simplify_stmt nat 0) ss = s :: ss); rewrite IH; reflexivity.
Qed.

(* simplify_stmts, fuse and the simplification of each statement are
   correct at every fuel. *)
Theorem simplify_correct_fuel n :
  correct (simplify_stmts nat n) /\ correct (fuse nat n) /\ correct (map (simplify_stmt nat n)).
Proof.
  induction n as [| n [HA [HC HM]]].
  - split; [| split]; unfold correct; intros sc wr ss; [exact (id_correct sc wr ss) | exact (id_correct sc wr ss) |].
    rewrite map_simplify_stmt_0; exact (id_correct sc wr ss).
  - split; [| split].
    + exact (correct_compose _ _ HM HC).
    + exact (fuse_correct_step _ HC HA).
    + exact (simplify_stmt_correct _ HA).
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
Proof.
  revert k; induction sc as [n f IH | p f IH | [r ps ss]]; intros k; simpl; auto.
Qed.

(* The variables of the parameters. *)
Definition params (ps : list (dparam W)) : list (dvar W) := map (fun '(DParam _ _ x) => x) ps.

Lemma finals_agree ps s1 s1' :
  agree (params ps) s1 s1' ->
  map (fun '(DParam _ _ x) => store_get s1 (KVar x)) (map (out_dparam nat) ps) =
  map (fun '(DParam _ _ x) => store_get s1' (KVar x)) (map (out_dparam nat) ps).
Proof.
  induction ps as [| [pw t x] ps IH]; intros Hag; simpl; [reflexivity |].
  rewrite (proj1 Hag x (or_introl eq_refl)), IH; [reflexivity |].
  exact (agree_incl _ _ _ _ (incl_tl _ (incl_refl _)) Hag).
Qed.

(* A body whose statements are refined, on the variables of the parameters
   and the returned value, returns the same results. *)
Lemma exec_done_sim r ps ss1 ss2 args res :
  (forall s0 s1, ex ss1 s0 = Some s1 -> exists s1', ex ss2 s0 = Some s1' /\ agree (params ps) s1 s1') ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map outs ss1))) 0 args = Some res ->
  exec_scoped reals (Done (DBody r (map (out_dparam nat) ps) (map outs ss2))) 0 args = Some res.
Proof.
  intros Hsim H; cbn [exec_scoped] in H |- *.
  destruct (negb _); [discriminate |].
  destruct (exec_stmts reals (map outs ss1) _) as [s1 |] eqn:E; [| discriminate].
  destruct (Hsim _ _ E) as (s1' & E' & Hag); unfold ex in E'; rewrite E'.
  rewrite <- (finals_agree ps s1 s1' Hag).
  destruct r; [rewrite <- (proj2 Hag) |]; exact H.
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
  intros Hopen Hc Hg Ht H.
  unfold exec_dfunction, simplify; cbn [dfbody].
  rewrite exec_simplify_scoped.
  change (open_pairs (dfbody g (nat * nat)) 0) with (open_pairs (dfbody g W) 0); rewrite Hopen; cbn [fst].
  apply (exec_done_sim r ps ss); [| exact H].
  intros s0 s1 E.
  destruct (proj1 (simplify_correct_fuel (fuel nat ss)) _ _ _ (good_gd _ _ _ Hg Ht) (incl_refl _) Hc)
    as [_ Hs].
  exact (Hs _ _ _ (agree_refl _ _) E).
Qed.
