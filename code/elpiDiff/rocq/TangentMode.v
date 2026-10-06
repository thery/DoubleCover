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
   and theorem 2 (simplify_correct: simplify preserves the execution). *)

From Stdlib Require Import String ZArith List Bool Reals Lia.
From Coquelicot Require Import Coquelicot.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Normalize WellFormed
  Annotate Tangent Simplify Scoping AnfEquiv Correctness Smooth SimplifyCorrect.
From ElpiDiff Require TangentCorrect TangentTop.
From ElpiDiff Require Import Euclidean DualsDerive.

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
Proof. destruct v; reflexivity. Qed.

Lemma lay_list_pair (pre B rest l : list R) :
  length B = length l ->
  lay_list (fun j r => Dual r (nth j (pre ++ B ++ rest) 0%R)) l (length pre) = TangentTop.pair_with l B.
Proof.
  revert pre B; induction l as [| r l IH]; intros pre B Hl; simpl; [reflexivity |].
  destruct B as [| b B]; simpl in Hl; [discriminate |].
  rewrite app_nth2, Nat.sub_diag by lia; simpl; f_equal.
  replace (S (length pre)) with (length (pre ++ [b])) by (rewrite length_app; simpl; lia).
  replace (pre ++ b :: B ++ rest) with ((pre ++ [b]) ++ B ++ rest) by (rewrite <- app_assoc; reflexivity).
  apply IH; lia.
Qed.

Lemma lay_head nm t r v x (pre B rest : list R) :
  fits (Decl nm t r) v -> length B = TangentTop.nreals v ->
  lay (fun j r => Dual r (nth j (pre ++ B ++ rest) 0%R)) (fun r => Dual r 0%R) (v :: x) (length pre) =
  TangentTop.val_dual v B ::
  lay (fun j r => Dual r (nth j (pre ++ B ++ rest) 0%R)) (fun r => Dual r 0%R) x (length pre + TangentTop.nreals v).
Proof.
  intros Hf HB; destruct v as [rv | z | b | l | l]; destruct t; simpl in Hf; try contradiction;
    simpl in HB |- *; rewrite ?Nat.add_0_r, ?Nat.add_1_r; f_equal.
  - destruct B as [| b0 [| ]]; simpl in HB; try discriminate.
    rewrite app_nth2, Nat.sub_diag by lia; reflexivity.
  - f_equal; apply lay_list_pair; exact HB.
Qed.

Lemma seed_args_dual ds x dx :
  Forall2 fits ds x -> (in_dim x <= length dx)%nat ->
  TangentTop.seed_args ds x dx = dual_args x (seed ds x dx).
Proof.
  unfold dual_args, in_dim, reals_of_args.
  assert (Hgen : forall pre, Forall2 fits ds x -> (length (concat (map reals_of_val x)) <= length dx)%nat ->
            lay (fun j r => Dual r (nth j (pre ++ seed ds x dx) 0%R)) (fun r => Dual r 0%R) x (length pre) =
            TangentTop.seed_args ds x dx).
  { intros pre H; revert pre dx; induction H as [| [nm t r] v ds x Hf Hfs IH]; intros pre dx Hl; [reflexivity |].
    cbn [map concat] in Hl; rewrite length_app in Hl.
    set (m := TangentTop.nreals v).
    set (B := if varied_role r then firstn m dx else repeat 0%R m).
    assert (HB : length B = m).
    { unfold B; destruct (varied_role r); [rewrite firstn_length; unfold m; rewrite nreals_length; lia
                                          | apply repeat_length]. }
    change (seed (Decl nm t r :: ds) (v :: x) dx) with (B ++ seed ds x (skipn m dx)).
    change (TangentTop.seed_args (Decl nm t r :: ds) (v :: x) dx)
      with (TangentTop.val_dual v B :: TangentTop.seed_args ds x (skipn m dx)).
    rewrite (lay_head nm t r v x pre B (seed ds x (skipn m dx)) Hf HB); f_equal.
    replace (length pre + TangentTop.nreals v)%nat with (length (pre ++ B)) by (rewrite length_app, HB; reflexivity).
    rewrite app_assoc; apply IH.
    rewrite length_skipn; unfold m; rewrite nreals_length; lia. }
  intros H Hl; symmetry; exact (Hgen [] H Hl).
Qed.

Lemma seed_length ds x dx :
  Forall2 fits ds x -> (in_dim x <= length dx)%nat -> length (seed ds x dx) = in_dim x.
Proof.
  unfold in_dim, reals_of_args; intros H; revert dx; induction H as [| [nm t r] v ds x Hf Hfs IH]; intros dx Hl;
    [reflexivity |].
  cbn [map concat] in Hl |- *; rewrite length_app in Hl |- *.
  change (seed (Decl nm t r :: ds) (v :: x) dx) with
    ((if varied_role r then firstn (TangentTop.nreals v) dx else repeat 0%R (TangentTop.nreals v)) ++
     seed ds x (skipn (TangentTop.nreals v) dx)).
  rewrite length_app, IH by (rewrite length_skipn, nreals_length; lia).
  rewrite nreals_length; f_equal; destruct (varied_role r);
    [rewrite firstn_length; lia | apply repeat_length].
Qed.

Lemma primal_primal_val vd : TangentCorrect.primal vd = primal_val vd.
Proof.
  destruct vd as [[a b] | | | l | l]; simpl; auto; f_equal; apply map_ext; intros [a b]; reflexivity.
Qed.

Lemma tangent_reals_tangent vd : reals_of_val (TangentCorrect.tangent vd) = tangent_reals vd.
Proof. destruct vd as [[a b] | | | l | l]; simpl; auto; apply map_ext; intros [a b]; reflexivity. Qed.

(* ---------------------------------------------------------------------------
   The final theorem. *)

(* The tangent mode is correct: where a parametric, well-formed function f is
   defined at the arguments x (fitting its declarations), it is Fréchet-
   differentiable at x as a function of the reals of its arguments (value_of,
   from R^n to R^m), with a linear derivative df; and for every tangent dx of
   the reals of x, the simplified tangent program, run over the reals on the
   inputs laid out from x and dx (tangent_inputs), succeeds and gives the
   value of f at x and, as the reals of its tangent output, df applied to the
   seed of dx (dx on the reals of the independent and inout arguments, 0 on
   the others). *)
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
  intros Hpar Hwf Hfit Hdef.
  destruct (duals_derive f x Hpar Hdef) as [v [df [Hs [Hd Hdual]]]].
  exists v, df; split; [exact Hs | split; [exact Hd |]].
  intros dx Hl.
  assert (Hl' : length (seed (decls f) x dx) = in_dim x) by (apply seed_length; [exact Hfit | lia]).
  destruct (Hdual _ Hl') as [vd [Hev [Hp Ht]]].
  apply (normalize_correct _ _ _ _ _ Hpar) in Hev.
  rewrite <- seed_args_dual in Hev by (auto; lia).
  destruct (TangentTop.tangent_simulates_duals f x dx vd Hpar Hwf Hfit Hev)
    as [r [ps [ss [k [out [Ho [Hc [Hg [Hnt [Hex Hout]]]]]]]]]].
  exists out, (TangentCorrect.tangent vd); split; [exact (simplify_correct _ _ r ps ss k out Ho Hc Hg Hnt Hex) |].
  split; [rewrite Hout, primal_primal_val, Hp; reflexivity | rewrite tangent_reals_tangent, Ht; reflexivity].
Qed.
