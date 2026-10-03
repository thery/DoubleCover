(** * Hard-to-round inputs of exp

    An input x is hard to round when exp x is within 2^-m_hard v of a
    multiple of v, v being half an ulp of exp x: exp x / v is within
    2^-m_hard of an integer. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Exp100 Require Import ExpModel.

Open Scope R_scope.

(** 2^e as a real. *)
Definition bp (e : Z) : R := bpow radix2 e.

(** The exponent of half an ulp in the binade e (subnormals included). *)
Definition vexp (e : Z) : Z := Z.max e emin - prec.

(** The binade e of y > 0: 2^e <= y < 2^(e+1). *)
Definition binade (y : R) : Z := (mag radix2 y - 1)%Z.

(** Half an ulp of exp x. *)
Definition vof (x : R) : R := bp (vexp (binade (exp x))).

(** exp x / v is within 2^-m_hard of an integer. *)
Definition hard (x : R) : Prop :=
  exists z : Z, Rabs (exp x / vof x - IZR z) < bp (- m_hard).

Lemma binadeP y : 0 < y -> bp (binade y) <= y < bp (binade y + 1).
Proof.
intros y0; unfold binade, bp.
replace (mag radix2 y - 1 + 1)%Z with (mag radix2 y : Z) by lia.
destruct (mag radix2 y) as [e he]; simpl.
rewrite <- (Rabs_pos_eq y) by lra; apply he; lra.
Qed.
