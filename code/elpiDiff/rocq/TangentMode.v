(* TangentMode.v — the correctness of the tangent mode of elpiDiff.

   Where a parametric, well-formed source function f is defined, in the sense
   of Abadi and Plotkin (Smooth.v), it is Fréchet-differentiable as a function
   of the reals of its arguments (DualsDerive.v: Coquelicot's filterdiff, on
   R^n), and the generated code — tangent, then simplify — run over the reals
   from the primal arguments and a seed computes the value of f and its
   derivative applied to the seed. The seed has the tangents dx on the reals of
   the independent and inout arguments, 0 on the others (seed, TangentTop.v).

   The proof composes theorem 3 (duals_derive: the dual numbers compute the
   derivative), normalize_correct (Correctness.v), theorem 1
   (tangent_simulates_duals: the tangent program computes the dual numbers),
   and theorem 2 (simplify_correct_tapes: simplify preserves the execution). *)

From Stdlib Require Import String ZArith List Bool Reals Lia.
From Coquelicot Require Import Coquelicot.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Normalize WellFormed
  Annotate Tangent Simplify Scoping AnfEquiv Correctness Smooth SimplifyCorrect.
From ElpiDiff Require TangentCorrect TangentTop.
From ElpiDiff Require Import Euclidean DualsDerive.

From Corelib Require Import ssreflect ssrbool ssrfun.
Set Bullet Behavior "None".

Import ListNotations.
Open Scope list_scope.

Notation fits := TangentTop.fits.
Notation decls := TangentTop.decls.
Notation seed := TangentTop.seed.
Notation tangent_inputs := TangentTop.tangent_inputs.
Notation tangent_output := TangentTop.tangent_output.

(* ---------------------------------------------------------------------------
   The seeded dual arguments of theorem 1 are those of theorem 3. *)

Lemma nreals_length v : TangentTop.nreals v = length (reals_of_val v).
Proof. by case: v. Qed.

Lemma lay_list_pair (pre B rest l : list R) :
  length B = length l ->
  lay_list (fun j r => Dual r (nth j (pre ++ B ++ rest) 0%R)) l (length pre) = TangentTop.pair_with l B.
Proof.
elim: l pre B => [| r l IH] pre [| b B] //= [Hl].
rewrite app_nth2 // Nat.sub_diag /=; congr (_ :: _).
have -> : S (length pre) = length (pre ++ [b]) by rewrite length_app /=; lia.
have -> : pre ++ b :: B ++ rest = (pre ++ [b]) ++ B ++ rest.
  by rewrite -app_assoc.
exact: IH.
Qed.

Lemma lay_head nm t r v x (pre B rest : list R) :
  fits (Decl nm t r) v -> length B = TangentTop.nreals v ->
  lay (fun j r => Dual r (nth j (pre ++ B ++ rest) 0%R)) (fun r => Dual r 0%R) (v :: x) (length pre) =
  TangentTop.val_dual v B ::
  lay (fun j r => Dual r (nth j (pre ++ B ++ rest) 0%R)) (fun r => Dual r 0%R) x (length pre + TangentTop.nreals v).
Proof.
move=> Hf HB.
destruct v as [rv | z | b | l | l]; destruct t; rewrite /= in Hf HB *;
  try contradiction; rewrite ?Nat.add_0_r ?Nat.add_1_r //.
  by case: B HB => [| b0 [|]] //= _; rewrite app_nth2 // Nat.sub_diag.
by rewrite lay_list_pair.
Qed.

Lemma seed_args_dual ds x dx :
  Forall2 fits ds x -> (in_dim x <= length dx)%nat ->
  TangentTop.seed_args ds x dx = dual_args x (seed ds x dx).
Proof.
rewrite /dual_args /in_dim /reals_of_args.
have Hgen : forall pre, Forall2 fits ds x ->
    (length (concat (map reals_of_val x)) <= length dx)%nat ->
    lay (fun j r => Dual r (nth j (pre ++ seed ds x dx) 0%R))
      (fun r => Dual r 0%R) x (length pre) =
    TangentTop.seed_args ds x dx.
  move=> pre H.
  elim: H pre dx => [| [nm t r] v ds' x' Hf Hfs IH] pre dx' Hl //.
  cbn [map concat] in Hl; rewrite length_app in Hl.
  set m := TangentTop.nreals v.
  set B := if varied_role r then firstn m dx' else repeat 0%R m.
  have HB : length B = m.
    rewrite /B; case: (varied_role r); last exact: repeat_length.
    by rewrite length_firstn /m nreals_length; lia.
  change (seed (Decl nm t r :: ds') (v :: x') dx')
    with (B ++ seed ds' x' (skipn m dx')).
  change (TangentTop.seed_args (Decl nm t r :: ds') (v :: x') dx')
    with (TangentTop.val_dual v B :: TangentTop.seed_args ds' x' (skipn m dx')).
  rewrite (lay_head nm t r v x' pre B (seed ds' x' (skipn m dx')) Hf HB).
  congr (_ :: _).
  have -> : (length pre + TangentTop.nreals v)%nat = length (pre ++ B).
    by rewrite length_app HB.
  rewrite app_assoc; apply: IH.
  by rewrite length_skipn /m nreals_length; lia.
by move=> H Hl; rewrite -(Hgen [] H Hl).
Qed.

Lemma seed_length ds x dx :
  Forall2 fits ds x -> (in_dim x <= length dx)%nat -> length (seed ds x dx) = in_dim x.
Proof.
rewrite /in_dim /reals_of_args => H.
elim: H dx => [| [nm t r] v ds' x' Hf Hfs IH] dx Hl //.
cbn [map concat] in Hl |- *; rewrite length_app in Hl *.
change (seed (Decl nm t r :: ds') (v :: x') dx) with
  ((if varied_role r then firstn (TangentTop.nreals v) dx
    else repeat 0%R (TangentTop.nreals v)) ++
   seed ds' x' (skipn (TangentTop.nreals v) dx)).
rewrite length_app IH; last by rewrite length_skipn nreals_length; lia.
rewrite nreals_length; congr (_ + _)%nat.
by case: (varied_role r); [rewrite length_firstn; lia | exact: repeat_length].
Qed.

Lemma primal_primal_val vd : TangentCorrect.primal vd = primal_val vd.
Proof.
by case: vd => [[a b] | | | l | l] //=; congr VArray; apply: map_ext => -[a b].
Qed.

Lemma tangent_reals_tangent vd : reals_of_val (TangentCorrect.tangent vd) = tangent_reals vd.
Proof. by case: vd => [[a b] | | | l | l] //=; apply: map_ext => -[a b]. Qed.

(* ---------------------------------------------------------------------------
   The final theorem. *)

(* The tangent mode is correct: where a parametric, well-formed function f is
   defined at the arguments x (fitting its declarations), it is Fréchet-
   differentiable at x as a function of the reals of its arguments (value_of,
   from R^n to R^m), with a linear derivative df; and for every tangent dx of
   the reals of x, the simplified tangent program, run over the reals on the
   inputs laid out from x and dx, with any initial values in its output-only
   tangent parameters (tangent_inputs_with: dd v for a written dependent
   argument of primal v, fitting its declaration, r0 for the tangent of a
   returned real; they are not read), succeeds and gives the value of f at x
   and, as the reals of its tangent output, df applied to the seed of dx (dx
   on the reals of the independent and inout arguments, 0 on the others). *)
Theorem tangent_mode_correct_with (dd : val R -> val R) (r0 : val R)
  (f : function) (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x ->
  defined f x ->
  (forall i d w, nth_error (decls f) i = Some d -> nth_error x i = Some w ->
     TangentTop.dot_out d = true -> fits d (dd w)) ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (point_of x)) df /\
    forall dx, length dx = in_dim x ->
      exists out w,
        exec_dfunction reals
          (simplify (tangent (annotate false (normalize f))))
          (TangentTop.tangent_inputs_with dd r0 (decls f) x dx) = Some out /\
        tangent_output (decls f) out = Some (v, w) /\
        reals_of_val w =
          list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx))).
Proof.
move=> Hpar Hwf Hfit Hdef Hdd.
have [v [df [Hs [Hd Hdual]]]] := duals_derive f x Hpar Hdef.
exists v, df; split; first exact: Hs.
split; first exact: Hd.
move=> dx Hl.
have Hl' : length (seed (decls f) x dx) = in_dim x.
  by apply: seed_length => //; lia.
have [vd [Hev [Hp Ht]]] := Hdual _ Hl'.
move/(normalize_correct _ _ _ _ _ Hpar): Hev => Hev.
have Hle : (in_dim x <= length dx)%nat by lia.
rewrite -(seed_args_dual _ _ _ Hfit Hle) in Hev.
have [r [ps [ss [k [out [Ho [Hc [Hg [Hex Hout]]]]]]]]] :=
  TangentTop.tangent_simulates_duals_with dd r0 f x dx vd Hpar Hwf Hfit Hdd Hev.
exists out, (TangentCorrect.tangent vd); split.
  exact: (simplify_correct_tapes _ _ r ps ss k out Ho Hc Hg Hex).
split; first by rewrite Hout primal_primal_val Hp.
by rewrite tangent_reals_tangent Ht.
Qed.

(* The same, with zeros in the output-only tangent parameters
   (tangent_inputs). *)
Theorem tangent_mode_correct (f : function) (x : list (val R)) :
  parametric f -> well_formed (normalize f) = Ok -> Forall2 fits (decls f) x -> defined f x ->
  exists v df,
    eval_function smooth_reals f x = Some v /\
    filterdiff (value_of f x) (locally (point_of x)) df /\
    forall dx, length dx = in_dim x ->
      exists out w,
        exec_dfunction reals (simplify (tangent (annotate false (normalize f))))
          (tangent_inputs (decls f) x dx) = Some out /\
        tangent_output (decls f) out = Some (v, w) /\
        reals_of_val w = list_of_vec _ (df (vec_of_list _ (seed (decls f) x dx))).
Proof.
move=> Hpar Hwf Hfit Hdef.
have [v [df [Hs [Hd Hc]]]] := tangent_mode_correct_with TangentTop.zero_dot
  (VReal 0%R) f x Hpar Hwf Hfit Hdef (TangentTop.zero_dot_fits _ _ Hfit).
exists v, df; split; first exact: Hs.
split; first exact: Hd.
by move=> dx Hl; rewrite TangentTop.tangent_inputs_zero; exact: Hc.
Qed.
