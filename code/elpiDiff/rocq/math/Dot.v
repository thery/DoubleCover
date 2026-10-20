(* Dot.v — the dot product of two lists of reals, shared by the statement of
   the adjoint mode (AdjointSpec.v) and its proofs (AdjointCorrect.v). *)

From Stdlib Require Import List Reals Lra.
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

(* ⟨ u , v ⟩: the dot product of u and v. *)
Notation "⟨ u , v ⟩" := (dotl u v) (at level 0, format "⟨ u ,  v ⟩").

(* The dot product with a list of zeros. *)
Lemma dotl_zeros_l n b : ⟨repeat 0 n, b⟩ = 0.
Proof.
elim: n b => [| n IH] [| y b] //=.
by rewrite dotl_cons IH; ring.
Qed.

(* Two vectors with the same dot product against every vector are equal:
   (forall dx, <dx, v> = <dx, g>) is the same as v = g, component by
   component. Testing with dx = (1, 0, ..., 0) gives the first component,
   then dx = (0, dx') gives the others. *)
Lemma dotl_ext (v g : list R) : length v = length g ->
  (forall dx, length dx = length v -> ⟨dx, v⟩ = ⟨dx, g⟩) <-> v = g.
Proof.
split; last by move=> -> .
elim: v g H => [| a v IH] [| b g] //= [Hl] Hd.
have Hab : a = b.
  have := Hd (1 :: repeat 0 (length v)).
  rewrite /= repeat_length !dotl_cons !dotl_zeros_l => /(_ eq_refl).
  by lra.
have Hvg : v = g.
  apply: IH => // dx Hdx.
  have := Hd (0 :: dx); rewrite /= Hdx !dotl_cons => /(_ eq_refl).
  by lra.
by rewrite Hab Hvg.
Qed.
