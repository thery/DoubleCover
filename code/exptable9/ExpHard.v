(** * Hard-to-round inputs of exp

    An input [x] is hard to round when [exp x] is within [2^-m v] of a
    multiple of [v], [v] being half an ulp of [exp x]: [exp x / v] is
    within [2^-m] of an integer.  [vof] is the [v] of [line_ok]. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From ExpTable9 Require Import ExpCheck.

Open Scope R_scope.

(** The binade [e] of [y > 0]: [2^e <= y < 2^(e+1)]. *)
Definition binade (y : R) : Z := (mag radix2 y - 1)%Z.

(** Half an ulp of [exp x], as [line_ok] takes it. *)
Definition vof (x : R) : R := bp (vexp (binade (exp x))).

(** [exp x / v] is within [2^-m] of an integer. *)
Definition hard (x : R) : Prop :=
  exists z : Z, Rabs (exp x / vof x - IZR z) < bp (- m).

Lemma binadeP y : 0 < y -> bp (binade y) <= y < bp (binade y + 1).
Proof.
intros y0; unfold binade, bp.
replace (mag radix2 y - 1 + 1)%Z with (mag radix2 y : Z) by lia.
destruct (mag radix2 y) as [e he]; simpl.
rewrite <- (Rabs_pos_eq y) by lra; apply he; lra.
Qed.

(** Condition 2 of [line_ok]: [v] is [vof x] for every [x] of the line. *)
Lemma vof_line (e : Z) (x0 xl x : R) :
  bp e <= exp x0 -> exp xl < bp (Z.max e emin + 1) -> x0 <= x <= xl ->
  vof x = bp (vexp e).
Proof.
intros h0 hl [hx0 hxl].
assert (h1 : exp x0 <= exp x).
{ destruct (Req_dec x0 x) as [->|d]; [lra|].
  apply Rlt_le, exp_increasing; lra. }
assert (h2 : exp x <= exp xl).
{ destruct (Req_dec x xl) as [->|d]; [lra|].
  apply Rlt_le, exp_increasing; lra. }
destruct (binadeP (exp x) (exp_pos x)) as [lo up].
assert (he : (e <= binade (exp x))%Z).
{ apply Z.lt_succ_r, (lt_bpow radix2).
  apply Rle_lt_trans with (exp x); [exact (Rle_trans _ _ _ h0 h1)|].
  exact up. }
assert (hb : (binade (exp x) <= Z.max e emin)%Z).
{ apply Z.lt_succ_r, (lt_bpow radix2).
  apply Rle_lt_trans with (exp x); [exact lo|].
  exact (Rle_lt_trans _ _ _ h2 hl). }
unfold vof, vexp; f_equal; lia.
Qed.

(** [fracR] is the standard library's [frac_part]. *)
Lemma fracR_frac_part r : fracR r = frac_part r.
Proof.
unfold fracR, frac_part.
replace (Zfloor r) with (Int_part r); [reflexivity|].
symmetry; apply Zfloor_imp.
destruct (base_Int_part r) as [h1 h2].
rewrite plus_IZR; change (IZR 1) with 1; lra.
Qed.
