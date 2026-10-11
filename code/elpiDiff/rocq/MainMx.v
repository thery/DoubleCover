(* MainMx.v — the adjoint theorem as a matrix identity: the gradient is the
   transpose of the Jacobian applied to the seed, g = Jᵀ yb, component by
   component, with mathcomp's matrices and sums.

   The reals are a mathcomp ring through RMat.v, which adds the axiom
   constructive_indefinite_description; this file and RMat.v only use it.

   The proofs of this file use the ssreflect tactic language. *)

From Stdlib Require Import List Reals.
From Coquelicot Require Import Hierarchy.
From ElpiDiff Require Import Syntax Eval Euclidean DualsDerive AdjointSpec
  Main.
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import choice fintype bigop ssralg matrix.
From ElpiDiff Require Import RMat.

Local Open Scope ring_scope.

(* The Jacobian of f at x: the entry (j, i) is the partial derivative of the
   j-th real of the value with respect to the i-th real of the arguments,
   the j-th component of D f x df (e x i). *)
Definition J f x (df : Rn (in_dim x) -> Rn (out_dim f x)) :
  'M[R]_(out_dim f x, in_dim x) :=
  \matrix_(j, i) List.nth j (D f x df (e x i)) 0%R.

(* The dot product of two lists of length n, as a sum. *)
Lemma dotl_sum n (a b : list R) :
  length a = n -> length b = n ->
  ⟨a, b⟩ = \sum_(j < n) List.nth j a 0%R * List.nth j b 0%R.
Proof.
elim: n a b => [| n IH] [| u a] [| v b] //=; first by rewrite big_ord0.
move=> [Ha] [Hb].
by rewrite dotl_cons big_ord_recl (IH a b Ha Hb).
Qed.

Lemma length_list_of_vec n (v : Rn n) : length (list_of_vec n v) = n.
Proof. by elim: n v => [| n IH] //= [u v]; rewrite IH. Qed.

(* The adjoint program computes g = Jᵀ yb: run on x, initial adjoints xb
   and a seed yb, it gives a gradient g whose component i, for an input i
   that f is differentiated with respect to, is the sum over the outputs j
   of yb_j times the entry (j, i) of the Jacobian. *)
Theorem adjoint_jacobian cv f x df xb yb (i : 'I_(in_dim x)) :
  accepted f x -> derivative f x df -> diff_wrt f x i ->
  length xb = in_dim x -> length yb = out_dim f x ->
  exists g, run_adjoint cv f x xb yb = Some g /\
    List.nth i g 0%R =
      \sum_(j < out_dim f x) List.nth j yb 0%R * J f x df j i.
Proof.
move=> Hacc Hdf Hw Hxb Hyb.
have [g [Hr [_ Hc]]] := adjoint_componentwise cv f x df Hacc Hdf xb yb Hxb Hyb.
exists g; split=> //; rewrite (Hc i Hw).
rewrite (dotl_sum (out_dim f x)) ?length_list_of_vec //.
by apply: eq_bigr => j _; rewrite mxE GRing.mulrC.
Qed.
