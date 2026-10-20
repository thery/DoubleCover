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

(* A scalar fold whose init is computed by a let: the let binds a real
   (nesty quantifies over the binders of the type of the value only), so the
   fold is scalar.
   T g(T c) { T s = c * c; for (i < 3) s = s * c; return s; } *)
Definition computed_init_fn : function := Function_ "computed_init" (fun V =>
  Arg "c" Real Independent (fun x1 => Body (Returns Real)
  (Fold (Nat 0) (Nat 3) (Op2 Mul (Var x1) (Var x1)) (fun x2 x3 =>
     (Op2 Mul (Var x3) (Var x1)))))).

Lemma computed_init_wf : well_formed (normalize computed_init_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma computed_init_nesty : nesty_args computed_init_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| ? ?]] //= [_ _ <-] /=.
split=> // y Hy; split; last by [].
split=> //; left; split; last by nesty_auto.
by move=> p [<-]; move: Hy => /= -[->].
Qed.

(* All the functions of the reference cases (~/claudeExp/elpi/cases) that the
   tool accepts, besides those above (03-branch is branch_fn, 05-map map_fn,
   06-fold-sum sumsq_fn, 09-array-state advect_fn); 08-refusal is refused. *)

(* Case 00-wikipedia. *)
Definition c00_f_fn : function := Function_ "f" (fun V => Arg "x1" Real
  Independent (fun x1 => Arg "x2" Real Independent (fun x2 => Body (Returns
  Real) (Let_ (Op2 Mul (Var x1) (Var x2)) (fun x3 => (Let_ (Op1 Sin (Var x1))
  (fun x4 => (Let_ (Op2 Add (Var x3) (Var x4)) (fun x5 => (Var x5)))))))))).

Lemma c00_f_wf : well_formed (normalize c00_f_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c00_f_nesty : nesty_args c00_f_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 01-expression. *)
Definition c01_quad_fn : function := Function_ "quad" (fun V => Arg "x" Real
  Independent (fun x1 => Body (Returns Real) (Op2 Add (Op2 Mul (Var x1) (Var
  x1)) (Var x1)))).

Lemma c01_quad_wf : well_formed (normalize c01_quad_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c01_quad_nesty : nesty_args c01_quad_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| ? ?]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 01-partials. *)
Definition c01_transcend_fn : function := Function_ "transcend" (fun V => Arg
  "x" Real Independent (fun x1 => Arg "y" Real Independent (fun x2 => Body
  (Returns Real) (Op2 Sub (Op2 Sub (Op2 Add (Op2 Divide (Op2 Mul (Op1 Sin (Var
  x1)) (Op1 Exp (Var x2))) (Op1 Sqrt (Var x1))) (Op1 Log (Var x2))) (Op2 Mul
  (Op1 (Pow 3) (Var x1)) (Op1 Cos (Var x2)))) (Op2 Divide (Var x2) (Var
  x1)))))).

Lemma c01_transcend_wf : well_formed (normalize c01_transcend_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c01_transcend_nesty : nesty_args c01_transcend_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 02-overwrite. *)
Definition c02_overwrite_fn : function := Function_ "overwrite" (fun V => Arg
  "x" Real Independent (fun x1 => Body (Returns Real) (Let_ (Op2 Mul (Num "2")
  (Var x1)) (fun x2 => (Op2 Mul (Var x2) (Var x2)))))).

Lemma c02_overwrite_wf : well_formed (normalize c02_overwrite_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c02_overwrite_nesty : nesty_args c02_overwrite_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| ? ?]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 02-reference. *)
Definition c02_rescale_fn : function := Function_ "rescale" (fun V => Arg "x"
  Real Inout (fun x1 => Arg "w" Real Independent (fun x2 => Body (Writes (Var
  x1)) (Op2 Mul (Op2 Mul (Var x2) (Var x1)) (Var x1))))).

Lemma c02_rescale_wf : well_formed (normalize c02_rescale_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c02_rescale_nesty : nesty_args c02_rescale_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 02-reference. *)
Definition c02_energy_fn : function := Function_ "energy" (fun V => Arg "x" Real
  Independent (fun x1 => Arg "w" Real Independent (fun x2 => Arg "e" Real
  Dependent (fun x3 => Body (Writes (Var x3)) (Op2 Mul (Op2 Mul (Var x2) (Var
  x1)) (Var x1)))))).

Lemma c02_energy_wf : well_formed (normalize c02_energy_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c02_energy_nesty : nesty_args c02_energy_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| x3 [| ? ?]]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 04-activity. *)
Definition c04_damped_fn : function := Function_ "damped" (fun V => Arg "x" Real
  Independent (fun x1 => Arg "nu" Real Passive (fun x2 => Body (Returns Real)
  (Let_ (Op2 Mul (Var x2) (Var x2)) (fun x3 => (Let_ (Op2 Add (Var x3) (Num
  "1")) (fun x4 => (Let_ (Op2 Mul (Var x1) (Var x1)) (fun x5 => (Op2 Divide (Var
  x5) (Var x4))))))))))).

Lemma c04_damped_wf : well_formed (normalize c04_damped_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c04_damped_nesty : nesty_args c04_damped_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 07-fold-product. *)
Definition c07_prodx_fn : function := Function_ "prodx" (fun V => Arg "x" (Array
  3) Independent (fun x1 => Body (Returns Real) (Fold (Nat 0) (Nat 3) (Num "1")
  (fun x2 x3 => (Op2 Mul (Var x3) (Get (Var x1) (Var x2))))))).

Lemma c07_prodx_wf : well_formed (normalize c07_prodx_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c07_prodx_nesty : nesty_args c07_prodx_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| ? ?]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 11-weno5. *)
Definition c11_weno5FluxImpl_fn : function := Function_ "weno5FluxImpl" (fun V
  => Arg "v" (Array 5) Independent (fun x1 => Arg "positive" Integer Passive
  (fun x2 => Arg "eps" Real Passive (fun x3 => Body (Returns Real) (Let_ (Get
  (Var x1) (Nat 0)) (fun x4 => (Let_ (Get (Var x1) (Nat 1)) (fun x5 => (Let_
  (Get (Var x1) (Nat 2)) (fun x6 => (Let_ (Get (Var x1) (Nat 3)) (fun x7 =>
  (Let_ (Get (Var x1) (Nat 4)) (fun x8 => (Let_ (Op2 Add (Op2 Mul (Num
  "13.0 / 12.0") (Op1 (Pow 2) (Op2 Add (Op2 Sub (Var x4) (Op2 Mul (Num "2") (Var
  x5))) (Var x6)))) (Op2 Mul (Num "1.0 / 4.0") (Op1 (Pow 2) (Op2 Add (Op2 Sub
  (Var x4) (Op2 Mul (Num "4") (Var x5))) (Op2 Mul (Num "3") (Var x6)))))) (fun
  x9 => (Let_ (Op2 Add (Op2 Mul (Num "13.0 / 12.0") (Op1 (Pow 2) (Op2 Add (Op2
  Sub (Var x5) (Op2 Mul (Num "2") (Var x6))) (Var x7)))) (Op2 Mul (Num
  "1.0 / 4.0") (Op1 (Pow 2) (Op2 Sub (Var x5) (Var x7))))) (fun x10 => (Let_
  (Op2 Add (Op2 Mul (Num "13.0 / 12.0") (Op1 (Pow 2) (Op2 Add (Op2 Sub (Var x6)
  (Op2 Mul (Num "2") (Var x7))) (Var x8)))) (Op2 Mul (Num "1.0 / 4.0") (Op1 (Pow
  2) (Op2 Add (Op2 Sub (Op2 Mul (Num "3") (Var x6)) (Op2 Mul (Num "4") (Var
  x7))) (Var x8))))) (fun x11 => (Let_ (Op2 Gt (Var x2) (Nat 0)) (fun x12 =>
  (Let_ (Ite (Var x12) (Num "0.3") (Num "0.1")) (fun x13 => (Let_ (Ite (Var x12)
  (Num "0.1") (Num "0.3")) (fun x14 => (Let_ (Op2 Divide (Var x13) (Op1 (Pow 2)
  (Op2 Add (Var x3) (Var x9)))) (fun x15 => (Let_ (Op2 Divide (Num "0.6") (Op1
  (Pow 2) (Op2 Add (Var x3) (Var x10)))) (fun x16 => (Let_ (Op2 Divide (Var x14)
  (Op1 (Pow 2) (Op2 Add (Var x3) (Var x11)))) (fun x17 => (Let_ (Op2 Add (Op2
  Add (Var x15) (Var x16)) (Var x17)) (fun x18 => (Let_ (Op2 Divide (Var x15)
  (Var x18)) (fun x19 => (Let_ (Op2 Divide (Var x16) (Var x18)) (fun x20 =>
  (Let_ (Op2 Divide (Var x17) (Var x18)) (fun x21 => (Let_ (Ite (Var x12) (Op2
  Add (Op2 Sub (Op2 Mul (Num "2.0") (Var x4)) (Op2 Mul (Num "7.0") (Var x5)))
  (Op2 Mul (Num "11.0") (Var x6))) (Op2 Add (Op2 Add (Op2 Mul (Num "-1.0") (Var
  x4)) (Op2 Mul (Num "5.0") (Var x5))) (Op2 Mul (Num "2.0") (Var x6)))) (fun x22
  => (Let_ (Ite (Var x12) (Op2 Add (Op2 Add (Op2 Mul (Num "-1.0") (Var x5)) (Op2
  Mul (Num "5.0") (Var x6))) (Op2 Mul (Num "2.0") (Var x7))) (Op2 Sub (Op2 Add
  (Op2 Mul (Num "2.0") (Var x5)) (Op2 Mul (Num "5.0") (Var x6))) (Op2 Mul (Num
  "1.0") (Var x7)))) (fun x23 => (Let_ (Ite (Var x12) (Op2 Sub (Op2 Add (Op2 Mul
  (Num "2.0") (Var x6)) (Op2 Mul (Num "5.0") (Var x7))) (Op2 Mul (Num "1.0")
  (Var x8))) (Op2 Add (Op2 Sub (Op2 Mul (Num "11.0") (Var x6)) (Op2 Mul (Num
  "7.0") (Var x7))) (Op2 Mul (Num "2.0") (Var x8)))) (fun x24 => (Op2 Divide
  (Op2 Add (Op2 Add (Op2 Mul (Var x19) (Var x22)) (Op2 Mul (Var x20) (Var x23)))
  (Op2 Mul (Var x21) (Var x24))) (Num
  "6.0")))))))))))))))))))))))))))))))))))))))))))))))).

Lemma c11_weno5FluxImpl_wf : well_formed (normalize c11_weno5FluxImpl_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c11_weno5FluxImpl_nesty : nesty_args c11_weno5FluxImpl_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| x3 [| ? ?]]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 12-goto. *)
Definition c12_irreducibleUpdate_fn : function := Function_ "irreducibleUpdate"
  (fun V => Arg "w" Real Inout (fun x1 => Arg "i" Integer Passive (fun x2 =>
  Body (Writes (Var x1)) (Let_ (Op2 Mul (Num "1.5") (Var x1)) (fun x3 => (Let_
  (Op1 Sin (Op2 Add (Var x1) (Num "1"))) (fun x4 => (Let_ (Op1 Sin (Op2 Add (Var
  x4) (Num "2"))) (fun x5 => (Let_ (Ite (Op2 Gt (Var x2) (Nat 10)) (Let_ (Op1
  Sin (Op2 Add (Var x5) (Num "3"))) (fun x6 => (Let_ (Op2 Add (Var x4) (Op2 Mul
  (Num "2") (Var x6))) (fun x7 => (Op1 Sin (Op2 Add (Op2 Add (Var x7) (Var x3))
  (Num "6"))))))) (Let_ (Op1 Sin (Op2 Add (Var x5) (Num "4"))) (fun x6 => (Let_
  (Op2 Add (Var x4) (Var x6)) (fun x7 => (Op1 Sin (Op2 Add (Op2 Add (Var x7)
  (Var x3)) (Num "5")))))))) (fun x6 => (Op1 Sin (Op2 Add (Var x6) (Num
  "7")))))))))))))).

Lemma c12_irreducibleUpdate_wf :
  well_formed (normalize c12_irreducibleUpdate_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c12_irreducibleUpdate_nesty : nesty_args c12_irreducibleUpdate_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* Case 13-branch-inplace. *)
Definition c13_bri_fn : function := Function_ "bri" (fun V => Arg "u" (Array 2)
  Inout (fun x1 => Arg "c" Real Independent (fun x2 => Body (Writes (Var x1))
  (Let_ (Ite (Op2 Gt (Var x2) (Num "0")) (Op2 Mul (Get (Var x1) (Nat 0)) (Get
  (Var x1) (Nat 0))) (Num "0")) (fun x3 => (Fold (Nat 0) (Nat 2) (Var x1) (fun
  x4 x5 => (Set_ (Var x5) (Var x4) (Op2 Add (Get (Var x5) (Var x4)) (Var
  x3)))))))))).

Lemma c13_bri_wf : well_formed (normalize c13_bri_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma c13_bri_nesty : nesty_args c13_bri_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.

(* A one-level in-place loop at a constant index.
   void constidx(std::array<T,3>& u, T c) { for (i < 3) u[0] = c * u[0]; } *)
Definition constidx_fn : function := Function_ "constidx" (fun V =>
  Arg "u" (Array 3) Inout (fun x1 => Arg "c" Real Independent (fun x2 =>
  Body (Writes (Var x1)) (Fold (Nat 0) (Nat 3) (Var x1) (fun x3 x4 =>
  (Set_ (Var x4) (Nat 0) (Op2 Mul (Var x2) (Get (Var x4) (Nat 0))))))))).

Lemma constidx_wf : well_formed (normalize constidx_fn) = Ok.
Proof. by vm_compute. Qed.

Lemma constidx_nesty : nesty_args constidx_fn.
Proof.
move=> x dx L res bP; move: (seed_args _ x dx) => xs.
case: xs => [| x1 [| x2 [| ? ?]]] //= [_ _ <-] /=.
by nesty_auto.
Qed.
