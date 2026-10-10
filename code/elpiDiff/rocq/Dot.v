(* Dot.v — the dot product of two lists of reals, shared by the statement of
   the adjoint mode (AdjointSpec.v) and its proofs (AdjointCorrect.v). *)

From Stdlib Require Import List Reals.
From Corelib Require Import ssreflect.

Import ListNotations.
Open Scope R_scope.

(* The dot product of two lists of reals, on their common prefix. *)
Definition dotl (a b : list R) : R :=
  fold_right Rplus 0 (map (fun '(p, q) => p * q) (combine a b)).

Lemma dotl_nil_l b : dotl [] b = 0.
Proof. by []. Qed.

Lemma dotl_cons a l b m : dotl (a :: l) (b :: m) = a * b + dotl l m.
Proof. by []. Qed.
