(* Xsin.v — xsin(x) = x * sin x through the Rocq passes: L0 (the term
   printed by tools/torocq.elpi from the L0 of xsin.hpp), the simplified tangent and
   adjoint programs in L2′, printed as Elpi terms (ToElpi.v) for the Elpi tool
   to print as C++, and the theorems of Main.v on xsin. *)

From Stdlib Require Import String ZArith List Reals.
From ElpiDiff Require Import Syntax Normalize WellFormed Annotate Derivative
  Tangent Adjoint Simplify Dump ToElpi Domain Correctness Smooth Main ModesAgree
  Dot TangentTop Eval.
From Corelib Require Import ssreflect.

Import ListNotations.
Open Scope string_scope.

(* L0. *)
Definition xsin_fn : function := Function_ "xsin" (fun V => Arg "x" Real
  Independent (fun x1 => Body (Returns Real) (Op2 Mul (Var x1) (Op1 Sin (Var
  x1))))).

(* L2′: the programs whose correctness Main.v states. *)
Definition xsin_tangent := tangent_code xsin_fn.
Definition xsin_adjoint := adjoint_code false xsin_fn.

(* Readable, as `elpi … -exec dump -- simplified <mode>`. *)
Compute pr_dfunction xsin_tangent.
Compute pr_dfunction xsin_adjoint.

(* As Elpi terms, for the Elpi tool (run.sh reads these two lines). *)
Compute to_elpi xsin_tangent.
Compute to_elpi xsin_adjoint.

(* ---------------------------------------------------------------------------
   The theorems on xsin. *)

Open Scope R_scope.

Lemma xsin_accepted x : accepted xsin_fn [VReal x].
Proof.
split; first by move=> V1 V2; repeat constructor.
split; first by [].
split; first by repeat constructor.
by eexists.
Qed.

(* The tangent program gives the value x sin x and the derivative along dx. *)
Corollary xsin_tangent_correct x df dx :
  derivative xsin_fn [VReal x] df ->
  run_tangent xsin_fn [VReal x] [dx] =
    Some (VReal (x * sin x), D xsin_fn [VReal x] df [dx]).
Proof.
move=> Hdf; apply: tangent_correct => //; exact: xsin_accepted.
Qed.

(* The adjoint program gives the gradient g: ⟨D dx, yb⟩ = ⟨dx, g⟩. *)
Corollary xsin_adjoint_correct x df xb yb :
  derivative xsin_fn [VReal x] df ->
  exists g, run_adjoint false xsin_fn [VReal x] [xb] [yb] = Some g /\
    length g = 1%nat /\
    forall dx, ⟨D xsin_fn [VReal x] df [dx], [yb]⟩ =
               ⟨[dx], g⟩.
Proof.
move=> Hdf.
have [g [Hg [Hl Hdot]]] := adjoint_correct false _ _ _ (xsin_accepted x) Hdf
  [xb] [yb] eq_refl eq_refl.
by exists g; split=> //; split=> // dx; apply: Hdot.
Qed.
