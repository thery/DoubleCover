(* AdjointModeProof.v — the adjoint modes are correct (adjoint_mode_correct,
   AdjointMode.v), from the simulation of the simplified adjoint function
   (Hypothesis adjoint_simplified, to be discharged by the M6 assembly and
   the classification of the well-formed bodies).

   The bridge is the one of the tangent mode (TangentMode.v): the dual
   numbers in the direction of the seed of dx compute the value of f and its
   derivative applied to the seed (duals_derive); the adjoint function, which
   does not depend on dx, pairs the tangent of the dual evaluation with yb as
   the seed with its gradient, for every dx.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import String ZArith List Bool Reals Lia.
From Coquelicot Require Import Coquelicot.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec
  Normalize WellFormed Annotate Adjoint Simplify Correctness Smooth.
From ElpiDiff Require TangentCorrect TangentTop.
From ElpiDiff Require Import Euclidean DualsDerive AdjointSpec TangentMode
  AdjointMode.
From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

(* Where smooth_reals computes, the reals compute the same. *)
Lemma eval_smooth_reals (f : function) (x : list (val R)) v :
  parametric f -> eval_function smooth_reals f x = Some v ->
  eval_function reals f x = Some v.
Proof.
move=> Hpar Hv.
have Hnil : graph (fun r : R => r) [] by move=> ? ? [].
have := eval_definition_forward R R smooth_reals reals (fun r => r)
  (fun s a H => H) smooth_op1_real smooth_op2_real smooth_cmp_real []
  _ _ (Hpar _ _) Hnil x v Hv.
by rewrite /eval_function !(map_ext _ _ (val_map_id (A := R))) map_id
  val_map_id.
Qed.

(* So the number of reals of the value of f is out_dim. *)
Lemma out_dim_value (f : function) (x : list (val R)) v :
  parametric f -> eval_function smooth_reals f x = Some v ->
  out_dim f x = length (reals_of_val v).
Proof.
by move=> Hpar Hv; rewrite /out_dim (eval_smooth_reals _ _ _ Hpar Hv).
Qed.

Section ModeProof.

(* The simplified adjoint function simulates the dual evaluation of the
   normal form of f, for every well-formed f (adjoint_wf_duals, then
   simplify_correct_tapes through the scoping discipline good). *)
Hypothesis adjoint_simplified : forall (cv : bool) (f : function)
  (x : list (val R)) (xb yb dx : list R) (v : val (dual R)),
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  length xb = in_dim x ->
  length yb = length (reals_of_val (TangentCorrect.primal v)) ->
  length dx = in_dim x ->
  aeval_function (duals reals) (normalize f)
    (TangentTop.seed_args (decls f) x dx) = Some v ->
  exists out g,
    exec_dfunction reals (simplify (adjoint cv (annotate cv (normalize f))))
      (adjoint_inputs (decls f) x xb yb) = Some out /\
    adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
    dotl (reals_of_val (TangentCorrect.tangent v)) yb =
      dotl (seed (decls f) x dx) g /\
    (cv = true -> writes_inout (decls f) = false ->
       value_given (decls f) out = Some (TangentCorrect.primal v)).

Theorem adjoint_mode_correct_from (cv : bool) (f : function) (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x -> defined f x ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (point_of x)) df /\
    forall xb yb, length xb = in_dim x -> length yb = out_dim f x ->
      exists out g,
        exec_dfunction reals (simplify (adjoint cv (annotate cv (normalize f))))
          (adjoint_inputs (decls f) x xb yb) = Some out /\
        adjoint_output (decls f) x xb out = Some g /\ length g = in_dim x /\
        (cv = true -> writes_inout (decls f) = false -> value_given (decls f) out = Some v) /\
        forall dx, length dx = in_dim x ->
          dotl (list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx)))) yb = dotl (seed (decls f) x dx) g.
Proof.
move=> Hpar Hwf Hfit Hdef.
have [v [df [Hs [Hd Hdual]]]] := duals_derive f x Hpar Hdef.
exists v, df; split; first exact: Hs.
split; first exact: Hd.
move=> xb yb Hxb Hyb.
(* the dual evaluation of the normal form, in the direction of seed dx *)
have Hrun : forall dx, length dx = in_dim x ->
    exists vd, aeval_function (duals reals) (normalize f)
      (TangentTop.seed_args (decls f) x dx) = Some vd /\
    TangentCorrect.primal vd = v /\
    reals_of_val (TangentCorrect.tangent vd) =
      list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx))).
  move=> dx Hl.
  have Hle : (in_dim x <= length dx)%nat by lia.
  have Hl' : length (seed (decls f) x dx) = in_dim x by exact: seed_length.
  have [vd [Hev [Hp Ht]]] := Hdual _ Hl'.
  move/(normalize_correct _ _ _ _ _ Hpar): Hev => Hev.
  rewrite -(seed_args_dual _ _ _ Hfit Hle) in Hev.
  exists vd; split=> //; split; first by rewrite primal_primal_val.
  by rewrite tangent_reals_tangent.
have Hyb' : forall vd, TangentCorrect.primal vd = v ->
    length yb = length (reals_of_val (TangentCorrect.primal vd)).
  by move=> vd ->; rewrite Hyb (out_dim_value _ _ _ Hpar Hs).
(* the adjoint function does not depend on dx: run it with dx = 0 *)
set dx0 := repeat 0%R (in_dim x).
have Hdx0 : length dx0 = in_dim x by exact: repeat_length.
have [vd0 [Hev0 [Hp0 _]]] := Hrun dx0 Hdx0.
have [out [g [Hex [Hg [Hlg [_ Hval]]]]]] :=
  adjoint_simplified cv f x xb yb dx0 vd0 Hpar Hwf Hfit Hxb (Hyb' _ Hp0) Hdx0
    Hev0.
exists out, g; split; first exact: Hex.
split; first exact: Hg.
split; first exact: Hlg.
split; first by move=> Hcv Hio; rewrite (Hval Hcv Hio) Hp0.
(* for every dx, the pairing identity *)
move=> dx Hl.
have [vd [Hev [Hp Ht]]] := Hrun dx Hl.
have [out' [g' [Hex' [Hg' [_ [Hdot _]]]]]] :=
  adjoint_simplified cv f x xb yb dx vd Hpar Hwf Hfit Hxb (Hyb' _ Hp) Hl Hev.
move: Hex'; rewrite Hex => -[Eo]; subst out'.
move: Hg'; rewrite Hg => -[Eg]; subst g'.
by rewrite -Ht.
Qed.

End ModeProof.
