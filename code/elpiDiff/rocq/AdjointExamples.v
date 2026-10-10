(* AdjointExamples.v — the classes of bodies the adjoint simulation covers
   are not empty: concrete programs the tool accepts (well_formed) whose
   opened bodies are in `nesty`, the premise of `adjoint_nesty_duals`, for
   all arguments.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform Adjoint
  Simplify Scoping AnfEquiv Correctness TangentCorrect TangentTop
  AdjointCorrect AdjointBranch AdjointFold AdjointFoldy AdjointNBody
  AdjointNesty AdjointTop.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope string_scope.

(* The class of an opened body, once computed: conjunctions, binders, the
   choice of a scalar fold (a literal init) or of an in-place fold (on an
   argument), and the trivial facts. *)
Ltac nesty_auto :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- forall _, _ => intro
  | |- True => exact I
  | |- ?a = ?a => reflexivity
  | |- (forall p, ANum _ = AVar p -> _) /\ _ \/ _ =>
      left; split; [by move=> ? | ]
  | |- (forall p, ANat _ = AVar p -> _) /\ _ \/ _ =>
      left; split; [by move=> ? | ]
  | |- _ \/ (exists q, AVar ?q0 = AVar q /\ _) /\ _ =>
      right; split; [by exists q0 | ]
  end.

(* The premise of adjoint_nesty_duals, for a function with two arguments. *)
Definition nesty_args (f : function) : Prop :=
  forall x dx L res bP,
  open_P (afdef (normalize f) pv) 0 (seed_args (decls f) x dx) [] =
    Some (L, res, bP) -> nesty true bP.

(* 1. A straight-line function. *)
(* T f(T x, T y) { return x * y + sin(x); } *)
Definition f_fn : function := Function_ "f" (fun V => Arg "x" Real Independent
  (fun x1 => Arg "y" Real Independent (fun x2 => Body (Returns Real)
  (Op2 Add (Op2 Mul (Var x1) (Var x2)) (Op1 Sin (Var x1)))))).

Lemma f_wf : well_formed (normalize f_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma f_nesty : nesty_args f_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 2. A branch (case 03-branch). *)
Definition branch_fn : function := Function_ "branch" (fun V =>
  Arg "a" Real Independent (fun x1 => Arg "p" Integer Passive (fun x2 =>
  Body (Returns Real) (Let_ (Var x1) (fun x3 =>
  (Let_ (Ite (Op2 Gt (Var x2) (Nat 0)) (Op2 Mul (Num "2") (Var x3))
     (Op2 Mul (Var x3) (Var x3))) (fun x4 => (Op2 Mul (Var x4) (Var x1))))))))).

Lemma branch_wf : well_formed (normalize branch_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma branch_nesty : nesty_args branch_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 3. A map (case 05-map). *)
Definition map_fn : function := Function_ "square_scaled" (fun V =>
  Arg "x" (Array 4) Independent (fun x1 => Arg "y" (Array 4) Dependent
  (fun x2 => Body (Writes (Var x2)) (Map (Nat 0) (Nat 4) (fun x3 =>
  (Let_ (Op2 Mul (Num "2") (Get (Var x1) (Var x3))) (fun x4 =>
     (Op2 Mul (Var x4) (Var x4))))))))).

Lemma map_wf : well_formed (normalize map_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma map_nesty : nesty_args map_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 4. A scalar fold (case 06-fold-sum). *)
Definition sumsq_fn : function := Function_ "sumsq" (fun V =>
  Arg "x" (Array 4) Independent (fun x1 => Body (Returns Real)
  (Fold (Nat 0) (Nat 4) (Num "0") (fun x2 x3 => (Op2 Add (Var x3)
     (Op2 Mul (Get (Var x1) (Var x2)) (Get (Var x1) (Var x2)))))))).

Lemma sumsq_wf : well_formed (normalize sumsq_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma sumsq_nesty : nesty_args sumsq_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| ? ?]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 5. A one-level in-place loop.
   void scale(std::array<T,3>& u, T c) { for (i) u[i] = c * u[i]; } *)
Definition scale_fn : function := Function_ "scale" (fun V =>
  Arg "u" (Array 3) Inout (fun x1 => Arg "c" Real Independent (fun x2 =>
  Body (Writes (Var x1)) (Fold (Nat 0) (Nat 3) (Var x1) (fun x3 x4 =>
  (Set_ (Var x4) (Var x3) (Op2 Mul (Var x2) (Get (Var x4) (Var x3))))))))).

Lemma scale_wf : well_formed (normalize scale_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma scale_nesty : nesty_args scale_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 6. A two-level nest (case 09-array-state). *)
Definition advect_fn : function := Function_ "advect" (fun V =>
  Arg "u" (Array 6) Inout (fun x1 => Arg "c" Real Independent (fun x2 =>
  Body (Writes (Var x1)) (Fold (Nat 0) (Nat 3) (Var x1) (fun x3 x4 =>
  (Fold (Nat 1) (Nat 6) (Var x4) (fun x5 x6 => (Set_ (Var x6) (Var x5)
  (Op2 Sub (Get (Var x6) (Var x5)) (Op2 Mul (Var x2)
  (Op2 Sub (Get (Var x6) (Var x5))
     (Get (Var x6) (Op2 Sub (Var x5) (Nat 1)))))))))))))).

Lemma advect_wf : well_formed (normalize advect_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma advect_nesty : nesty_args advect_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 7. A three-level nest.
   for (n < 2) for (m < 2) for (i = 1; i < 4; i++)
     u[i] = u[i] - c * (u[i] - u[i-1]); *)
Definition nest3_fn : function := Function_ "nest3" (fun V =>
  Arg "u" (Array 4) Inout (fun x1 => Arg "c" Real Independent (fun x2 =>
  Body (Writes (Var x1)) (Fold (Nat 0) (Nat 2) (Var x1) (fun x3 x4 =>
  (Fold (Nat 0) (Nat 2) (Var x4) (fun x5 x6 =>
  (Fold (Nat 1) (Nat 4) (Var x6) (fun x7 x8 => (Set_ (Var x8) (Var x7)
  (Op2 Sub (Get (Var x8) (Var x7)) (Op2 Mul (Var x2)
  (Op2 Sub (Get (Var x8) (Var x7))
     (Get (Var x8) (Op2 Sub (Var x7) (Nat 1)))))))))))))))).

Lemma nest3_wf : well_formed (normalize nest3_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma nest3_nesty : nesty_args nest3_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* 8. Steps that give their state back.
   for (i < 3) { }  and  for (n < 2) for (i < 3) { } *)
Definition idbody_fn : function := Function_ "idbody" (fun V =>
  Arg "u" (Array 3) Inout (fun x1 => Arg "c" Real Independent (fun x2 =>
  Body (Writes (Var x1)) (Fold (Nat 0) (Nat 3) (Var x1) (fun x3 x4 =>
  (Var x4)))))).

Lemma idbody_wf : well_formed (normalize idbody_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma idbody_nesty : nesty_args idbody_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

Definition nest2id_fn : function := Function_ "nest2id" (fun V =>
  Arg "u" (Array 3) Inout (fun x1 => Arg "c" Real Independent (fun x2 =>
  Body (Writes (Var x1)) (Fold (Nat 0) (Nat 2) (Var x1) (fun x3 x4 =>
  (Fold (Nat 0) (Nat 3) (Var x4) (fun x5 x6 => (Var x6)))))))).

Lemma nest2id_wf : well_formed (normalize nest2id_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma nest2id_nesty : nesty_args nest2id_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* A finding: a scalar fold whose init is computed by a let is well formed,
   but not nesty. The class quantifies over every value of the let's binder,
   an array among them, for which the fold is neither scalar nor in place.
   T g(T c) { T s = c * c; for (i < 3) s = s * c; return s; } *)
Definition computed_init_fn : function := Function_ "computed_init" (fun V =>
  Arg "c" Real Independent (fun x1 => Body (Returns Real)
  (Fold (Nat 0) (Nat 3) (Op2 Mul (Var x1) (Var x1)) (fun x2 x3 =>
     (Op2 Mul (Var x3) (Var x1)))))).

Lemma computed_init_wf : well_formed (normalize computed_init_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma computed_init_not_nesty : ~ nesty_args computed_init_fn.
Proof.
move=> H.
have := H [VReal 1%R] [1%R] _ _ _ erefl.
rewrite /= => -[_ /(_ (PV (AV 5 false) (VInfo 5 (Array 1) None) dummy_tvar
  (VInt 0) 5))] [[_ [[Hna _] | [_ Hb]]] _].
  by apply: (Hna _ erefl).
have := Hb (PV (AV 6 false) (VInfo 6 Integer None) dummy_tvar (VInt 0) 6)
  (PV (AV 7 false) (VInfo 7 Real None) dummy_tvar (VInt 0) 7)
  (PV (AV 8 false) (VInfo 8 Real None) dummy_tvar (VInt 0) 8).
by move=> /(f_equal pn).
Qed.
