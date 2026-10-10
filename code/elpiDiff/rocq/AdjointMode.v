(* AdjointMode.v — the correctness of the adjoint modes of elpiDiff, adjoint
   (Value = false) and adjoint-value (Value = true).

   Where a parametric, well-formed source function f is defined (Smooth.v),
   it is Fréchet-differentiable with a linear derivative df (DualsDerive.v),
   and the generated code — annotate Value, adjoint Value, then simplify —
   run over the reals from the primal arguments x, initial adjoints xb and a
   seed yb, computes the transpose of df applied to yb: for every tangent dx,
   <df (seed dx), yb> = <seed dx, g>, where g is the gradient (adjoint_output,
   AdjointSpec.v: the final adjoints minus the initial ones). seed masks the
   arguments that carry no derivative on entry (dependent, passive). In mode
   adjoint-value, the function also gives the value of f back, unless it
   writes an inout argument (passed by value).

   The proof follows the tangent mode (TangentMode.v): the dual numbers in
   direction dx (theorem 3, duals_derive) give df (seed dx), and the reverse
   sweep keeps the sum of the tangents times the adjoints of the variables in
   scope. *)

From Stdlib Require Import String ZArith List Bool Reals Lia.
From Coquelicot Require Import Coquelicot.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Normalize WellFormed Annotate Adjoint Simplify Correctness Smooth.
From ElpiDiff Require TangentTop.
From ElpiDiff Require Import Euclidean DualsDerive AdjointSpec.
From ElpiDiff Require AdjointClassify AdjointGoodTop AdjointModeProof.
From Corelib Require Import ssreflect.

Import ListNotations.
Open Scope list_scope.

Notation fits := TangentTop.fits.
Notation decls := TangentTop.decls.
Notation seed := TangentTop.seed.

(* The adjoint modes are correct: where a parametric, well-formed function f
   is defined at the arguments x (fitting its declarations), it is Fréchet-
   differentiable at x with a linear derivative df; and for all initial
   adjoints xb and every seed yb, the simplified adjoint program, run over
   the reals, succeeds and computes a gradient g such that, for every tangent
   dx, <df (seed dx), yb> = <seed dx, g>; the adjoint-value program also gives
   the value of f back, unless f writes an inout argument. *)
Theorem adjoint_mode_correct (cv : bool) (f : function) (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok ->
  Forall2 fits (decls f) x -> defined f x ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (point_of x)) df /\
    forall xb yb, length xb = in_dim x -> length yb = out_dim f x ->
      exists out g,
        exec_dfunction reals (simplify (adjoint cv (annotate cv (normalize f))))
          (adjoint_inputs (decls f) x xb yb) = Some out /\
        adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
        (cv = true -> writes_inout (decls f) = false ->
           value_given (decls f) out = Some v) /\
        forall dx, length dx = in_dim x ->
          dotl (list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx)))) yb =
            dotl (seed (decls f) x dx) g.
Proof.
move=> Hpar Hwf Hfit Hdef.
apply: (AdjointModeProof.adjoint_mode_correct_from _ cv f x Hpar Hwf Hfit
  Hdef).
move=> cv' f' x' xb yb dx v Hp Hw Hf Hxb Hyb Hdx Hev.
apply: (AdjointGoodTop.adjoint_nesty_simplified cv' f' x' xb yb dx v) => //.
move=> L res bP Ho.
exact: (AdjointClassify.well_formed_nesty f' x' dx L res bP Hp Hw Hf Ho).
Qed.
