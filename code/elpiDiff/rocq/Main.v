(* Main.v — the correctness of elpiDiff, in short: the encoding of what is
   computed (value, derivative, runs of the generated programs), then the
   theorems, each proved from the detailed one (TangentMode.v, AdjointMode.v,
   ModesAgree.v).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia.
From Coquelicot Require Import Coquelicot.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Normalize WellFormed Annotate Adjoint Tangent Simplify Correctness Smooth.
From ElpiDiff Require TangentTop.
From ElpiDiff Require Import Euclidean DualsDerive AdjointSpec TangentMode
  AdjointMode ModesAgree.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* ---------------------------------------------------------------------------
   The encoding. *)

(* f is accepted at x: parametric (the binders of f are not inspected),
   well-formed (elpiDiff accepts its normal form), the arguments x fit the
   declarations of f, and f is defined at x (it is smooth around x). *)
Definition accepted (f : function) (x : list (val R)) : Prop :=
  parametric f /\ well_formed (normalize f) = Ok /\
  Forall2 fits (decls f) x /\ defined f x.

(* The value of f at x. *)
Definition value (f : function) (x : list (val R)) : option (val R) :=
  eval_function smooth_reals f x.

(* df is the Fréchet derivative at x of f, as a map R^in_dim -> R^out_dim
   on the reals of the arguments and of the value. *)
Definition derivative (f : function) (x : list (val R))
  (df : Rn (in_dim x) -> Rn (out_dim f x)) : Prop :=
  filterdiff (value_of f x) (locally (point_of x)) df.

(* The derivative applied to a tangent dx, masked by seed (the arguments
   that carry no derivative on entry), as a list of reals. *)
Definition D (f : function) (x : list (val R))
  (df : Rn (in_dim x) -> Rn (out_dim f x)) (dx : list R) : list R :=
  list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx))).

(* Run the tangent program on x and dx: the value and the tangent. *)
Definition run_tangent (f : function) (x : list (val R)) (dx : list R) :
  option (val R * list R) :=
  match exec_dfunction reals (tangent_code f)
          (tangent_inputs (decls f) x dx) with
  | Some out =>
      match tangent_output (decls f) out with
      | Some (v, w) => Some (v, reals_of_val w)
      | None => None
      end
  | None => None
  end.

(* Run the adjoint program on x, initial adjoints xb and a seed yb: the
   gradient. *)
Definition run_adjoint (cv : bool) (f : function) (x : list (val R))
  (xb yb : list R) : option (list R) :=
  match exec_dfunction reals (adjoint_code cv f)
          (adjoint_inputs (decls f) x xb yb) with
  | Some out => adjoint_output (decls f) x xb out
  | None => None
  end.

(* Run the adjoint-value program: the value it gives back. *)
Definition run_adjoint_value (f : function) (x : list (val R))
  (xb yb : list R) : option (val R) :=
  match exec_dfunction reals (adjoint_code true f)
          (adjoint_inputs (decls f) x xb yb) with
  | Some out => value_given (decls f) out
  | None => None
  end.

(* ---------------------------------------------------------------------------
   The theorems. *)

(* An accepted f has a derivative at x. *)
Theorem derivative_exists f x : accepted f x -> exists df, derivative f x df.
Proof.
move=> [Hp [Hw [Hf Hd]]].
have [_ [df [_ [Hdf _]]]] := tangent_mode_correct f x Hp Hw Hf Hd.
by exists df.
Qed.

(* The tangent program computes the value of f and its derivative: run on x
   and a tangent dx, it gives back v, the value of f at x, and D df f x dx,
   the derivative applied to dx. *)
Theorem tangent_correct f x df v :
  accepted f x -> derivative f x df -> value f x = Some v ->
  forall dx, length dx = in_dim x ->
    run_tangent f x dx = Some (v, D f x df dx).
Proof.
move=> [Hp [Hw [Hf Hd]]] Hdf Hv dx Hl.
have [v0 [df0 [Hs [Hdf0 Ht]]]] := tangent_mode_correct f x Hp Hw Hf Hd.
move: Hv; rewrite /value Hs => -[<-].
have [out [w [Hex [Hout Hw']]]] := Ht dx Hl.
rewrite /run_tangent /tangent_code Hex Hout Hw' /D.
by rewrite (filterdiff_locally_unique _ _ _ _ Hdf0 Hdf).
Qed.

(* The adjoint program computes the transpose of the derivative: run on x,
   initial adjoints xb and a seed yb, it gives a gradient g, one real per
   real of the arguments, such that for every tangent dx,
   ⟨D df dx, yb⟩ = ⟨seed dx, g⟩. *)
Theorem adjoint_correct cv f x df :
  accepted f x -> derivative f x df ->
  forall xb yb, length xb = in_dim x -> length yb = out_dim f x ->
  exists g, run_adjoint cv f x xb yb = Some g /\ length g = in_dim x /\
    forall dx, length dx = in_dim x ->
      ⟨D f x df dx, yb⟩ = ⟨seed (decls f) x dx, g⟩.
Proof.
move=> [Hp [Hw [Hf Hd]]] Hdf xb yb Hxb Hyb.
have [v0 [df0 [Hs [Hdf0 Ha]]]] := adjoint_mode_correct cv f x Hp Hw Hf Hd.
have [out [g [Hex [Hg [Hlg [_ Hdot]]]]]] := Ha xb yb Hxb Hyb.
exists g; split; first by rewrite /run_adjoint /adjoint_code Hex.
split=> // dx Hl; rewrite -(Hdot dx Hl) /D.
by rewrite (filterdiff_locally_unique _ _ _ _ Hdf Hdf0).
Qed.

(* The adjoint-value program also gives back the value of f, unless f writes
   an inout argument (passed by value). *)
Theorem adjoint_value_correct f x xb yb :
  accepted f x -> length xb = in_dim x -> length yb = out_dim f x ->
  writes_inout (decls f) = false ->
  run_adjoint_value f x xb yb = value f x.
Proof.
move=> [Hp [Hw [Hf Hd]]] Hxb Hyb Hio.
have [v0 [df0 [Hs [_ Ha]]]] := adjoint_mode_correct true f x Hp Hw Hf Hd.
have [out [g [Hex [_ [_ [Hval _]]]]]] := Ha xb yb Hxb Hyb.
by rewrite /run_adjoint_value /adjoint_code Hex (Hval erefl Hio) /value Hs.
Qed.

(* The two modes agree: the tangent program and the adjoint program are
   adjoint to each other, ⟨w, yb⟩ = ⟨seed dx, g⟩. *)
Corollary modes_agree cv f x dx xb yb :
  accepted f x -> length dx = in_dim x ->
  length xb = in_dim x -> length yb = out_dim f x ->
  exists v w g, run_tangent f x dx = Some (v, w) /\
    run_adjoint cv f x xb yb = Some g /\
    ⟨w, yb⟩ = ⟨seed (decls f) x dx, g⟩.
Proof.
move=> [Hp [Hw [Hf Hd]]] Hdx Hxb Hyb.
have [tout [v [w [aout [g [Ht [Hto [Ha [Hao Hdot]]]]]]]]] :=
  adjoint_tangent_agree cv f x Hp Hw Hf Hd dx xb yb Hdx Hxb Hyb.
exists v, (reals_of_val w), g; split; first by rewrite /run_tangent Ht Hto.
by split; first by rewrite /run_adjoint Ha.
Qed.
