(* AdjointWf.v — the adjoint simulation for every well-formed function
   (milestone M7): adjoint_nesty_duals, its class premise discharged by
   well_formed_nesty (AdjointClassify.v).

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia Lra.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Operations Normalize WellFormed Atoms Activity Tbr Annotate Transform
  Adjoint Simplify Scoping AnfEquiv Correctness TangentCorrect TangentTop
  AdjointCorrect AdjointBranch AdjointSpec DualsDerive AdjointFold
  AdjointFoldy AdjointNBody AdjointNesty AdjointClassify AdjointTop.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* The adjoint function of a parametric, well-formed function, run on the
   primal arguments, their adjoints and the seed, computes the gradient: the
   transpose of the tangent of the dual evaluation, applied to the seed. *)
Corollary adjoint_wf_duals (cv : bool) (f : function) (x : list (val R))
  (xb yb dx : list R) (v : val (dual R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x -> length yb = length (reals_of_val (primal v)) ->
  length dx = in_dim x ->
  aeval_function (duals reals) (normalize f) (seed_args (decls f) x dx) =
    Some v ->
  exists r ps ss k out g,
    open_pairs (dfbody (Adjoint.adjoint cv (annotate cv (normalize f))) W) 0 =
      (DBody r ps ss, k) /\
    exec_scoped reals
      (Done (DBody r (map (out_dparam nat) ps) (map (out_dstmt nat) ss))) 0
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb =
      dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false ->
     value_given (decls f) out = Some (TangentCorrect.primal v)).
Proof.
move=> Hp Hw Hf Hxb Hyb Hdx Hev.
apply: adjoint_nesty_duals => // L res bP Ho.
exact: well_formed_nesty Ho.
Qed.
