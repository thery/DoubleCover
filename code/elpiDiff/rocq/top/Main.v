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

(* ---------------------------------------------------------------------------
   The gradient, component by component. *)

(* basis n i: the i-th vector e_i of the standard basis of R^n, 1 at
   position i and 0 elsewhere. *)
Fixpoint basis (n i : nat) : list R :=
  match n, i with
  | O, _ => []
  | S n', O => 1%R :: repeat 0%R n'
  | S n', S i' => 0%R :: basis n' i'
  end.

Lemma basis_length n i : length (basis n i) = n.
Proof.
elim: n i => [| n IH] [| i] //=; first by rewrite repeat_length.
by rewrite IH.
Qed.

(* <e_i, g> is the i-th component of g. *)
Lemma dotl_unit n i (g : list R) : length g = n -> (i < n)%nat ->
  ⟨basis n i, g⟩ = nth i g 0%R.
Proof.
elim: g n i => [| b g IH] [| n] [| i] //= [Hl] Hi; try lia.
- by rewrite dotl_cons dotl_zeros_l; ring.
- by rewrite dotl_cons IH //; [ring | lia].
Qed.

(* e x i: the i-th basis vector of the space of the reals of the arguments
   x. *)
Definition e (x : list (val R)) (i : nat) : list R := basis (in_dim x) i.

(* The positions differentiated with respect to: for each argument, one
   flag per real, true when the argument is independent or inout. *)
Fixpoint wrt_mask (ds : list decl) (x : list (val R)) : list bool :=
  match ds, x with
  | Decl _ _ r :: ds', v :: x' =>
      repeat (varied_role r) (length (reals_of_val v)) ++ wrt_mask ds' x'
  | _, _ => []
  end.

(* diff_wrt f x i: the i-th real of the arguments x is one f is
   differentiated with respect to (it belongs to an independent or inout
   argument). *)
Definition diff_wrt (f : function) (x : list (val R)) (i : nat) : Prop :=
  nth i (wrt_mask (decls f) x) false = true.

Lemma wrt_mask_length ds x : length ds = length x ->
  length (wrt_mask ds x) = length (reals_of_args x).
Proof.
elim: ds x => [| [n t r] ds IH] [| v x] //= [Hl].
by rewrite length_app repeat_length IH // /reals_of_args /= length_app.
Qed.

Lemma split_at (l1 l2 : list R) m : length l1 = m ->
  firstn m (l1 ++ l2) = l1 /\ skipn m (l1 ++ l2) = l2.
Proof.
move=> <-; split.
- by rewrite firstn_app Nat.sub_diag firstn_O app_nil_r firstn_all.
- by rewrite skipn_app Nat.sub_diag skipn_O skipn_all.
Qed.

Lemma basis_lt m k i : (i < m)%nat ->
  basis (m + k) i = basis m i ++ repeat 0%R k.
Proof.
elim: m i => [| m IH] [| i] Hi //=; try lia.
- by rewrite repeat_app.
- by rewrite IH //; lia.
Qed.

Lemma basis_ge m k i : (m <= i)%nat ->
  basis (m + k) i = repeat 0%R m ++ basis k (i - m).
Proof.
elim: m i => [| m IH] [| i] Hi //=; try lia.
by rewrite IH //; lia.
Qed.

Lemma seed_zeros ds (x : list (val R)) : length ds = length x ->
  TangentTop.seed ds x (repeat 0%R (length (reals_of_args x))) =
  repeat 0%R (length (reals_of_args x)).
Proof.
elim: ds x => [| [n t r] ds IH] [| v x] //= [Hl].
rewrite /reals_of_args /= length_app -/(reals_of_args x) repeat_app.
have [Hf Hs] := split_at (repeat 0%R (length (reals_of_val v)))
  (repeat 0%R (length (reals_of_args x))) _ (repeat_length _ _).
rewrite nreals_length Hf Hs IH //.
by case: (varied_role r).
Qed.

(* On a position differentiated with respect to, seed keeps e_i. *)
Lemma seed_unit_wrt ds (x : list (val R)) i :
  length ds = length x -> nth i (wrt_mask ds x) false = true ->
  TangentTop.seed ds x (basis (length (reals_of_args x)) i) =
  basis (length (reals_of_args x)) i.
Proof.
elim: ds x i => [| [n t r] ds IH] [| v x] i //=.
move=> [Hl]; rewrite /reals_of_args /= length_app -/(reals_of_args x).
set m := length (reals_of_val v); set k := length (reals_of_args x).
rewrite nreals_length -/m.
case: (Nat.lt_ge_cases i m) => Hi.
- move=> Hn.
  have Hr : varied_role r = true.
    by move: Hn; rewrite app_nth1 ?repeat_length // nth_repeat_lt.
  rewrite basis_lt //.
  have [Hf Hs] := split_at (basis m i) (repeat 0%R k) m (basis_length m i).
  by rewrite Hr Hf Hs seed_zeros.
- move=> Hn.
  have Hn' : nth (i - m) (wrt_mask ds x) false = true.
    by move: Hn; rewrite app_nth2 ?repeat_length.
  rewrite basis_ge //.
  have [Hf Hs] := split_at (repeat 0%R m) (basis k (i - m)) m
    (repeat_length _ _).
  rewrite Hf Hs IH //.
  by case: (varied_role r).
Qed.

Lemma diff_wrt_lt f x i : length (decls f) = length x -> diff_wrt f x i ->
  (i < in_dim x)%nat.
Proof.
move=> Hl Hw; rewrite /in_dim -(wrt_mask_length _ _ Hl).
case: (Nat.lt_ge_cases i (length (wrt_mask (decls f) x))) => // Hge.
by move: Hw; rewrite /diff_wrt nth_overflow.
Qed.

(* The adjoint program computes the transpose of the derivative applied to
   the seed yb, component by component: for every input real i that f is
   differentiated with respect to, the i-th component of the gradient g is
   <D f x df (e x i), yb>, the sum over the outputs j of yb_j times the partial
   derivative of the j-th output with respect to the i-th input. *)
Corollary adjoint_componentwise cv f x df :
  accepted f x -> derivative f x df ->
  forall xb yb, length xb = in_dim x -> length yb = out_dim f x ->
  exists g, run_adjoint cv f x xb yb = Some g /\ length g = in_dim x /\
    forall i, diff_wrt f x i ->
      nth i g 0%R = ⟨D f x df (e x i), yb⟩.
Proof.
move=> Hacc Hdf xb yb Hxb Hyb.
have [g [Hr [Hlg Hdot]]] := adjoint_correct cv f x df Hacc Hdf xb yb Hxb Hyb.
exists g; split=> //; split=> // i Hw.
have Hds : length (decls f) = length x.
  by case: Hacc => [_ [_ [Hf _]]]; exact: Forall2_length Hf.
have Hi := diff_wrt_lt f x i Hds Hw.
rewrite /e (Hdot _ (basis_length _ _)) /in_dim seed_unit_wrt //.
by rewrite dotl_unit.
Qed.
