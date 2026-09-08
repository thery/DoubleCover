From Stdlib Require Import ZArith Reals Psatz.
From Flocq Require Import Core Plus_error Sterbenz Operations.
From mathcomp Require Import ssreflect.

(* Being an integer multiple of a power of the radix.                         *)
(* A float is a multiple of its own last place, and anything on that grid     *)
(* whose own last place is no finer is itself a float.  Those two facts turn  *)
(* questions about exactness into questions about grids, which is how the     *)
(* exactness of a subtraction is decided.                                     *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

Section Imul.

Variable emin p : Z.
Hypothesis Hp2 : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p }.

Let beta := radix2.
Local Notation pow e := (bpow beta e).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).

Definition is_imul x y := exists z : Z, x = IZR z * y.

Lemma is_imul_minus x1 x2 y :
  is_imul x1 y -> is_imul x2 y -> is_imul (x1 - x2) y.
Proof. by move=> [z1 ->] [z2 ->]; exists (z1 - z2)%Z; rewrite minus_IZR; lra. Qed.

(* A coarser grid is contained in a finer one.                                *)
Lemma is_imul_pow_le x y1 y2 :
  is_imul x (pow y1) -> (y2 <= y1)%Z -> is_imul x (pow y2).
Proof.
move=> [z ->] y2Ly1; exists (z * beta ^ (y1 - y2))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
by rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
Qed.

(* Nothing nonzero is smaller than the grid it sits on.                       *)
Lemma is_imul_pow_le_abs x y : is_imul x (pow y) -> x <> 0 -> pow y <= Rabs x.
Proof.
case=> [k ->] kn0.
have powy_gt_0 : 0 < pow y by apply: bpow_gt_0.
rewrite Rabs_mult [Rabs (pow _)]Rabs_pos_eq; last by lra.
suff : 1 <= Rabs (IZR k) by nra.
rewrite -abs_IZR; apply: IZR_le.
suff : k <> 0%Z by lia.
by contradict kn0; rewrite kn0 /=; ring.
Qed.

(* A float sits on the grid of its own last place.                            *)
Lemma format_imul_cexp x : format x -> is_imul x (pow (cexp x)).
Proof. by move=> Fx; exists (Ztrunc (mant x)); rewrite {1}Fx /F2R /=. Qed.

(* And conversely, on a grid no finer than its own last place.                *)
Lemma imul_cexp_format x e : is_imul x (pow e) -> (cexp x <= e)%Z -> format x.
Proof.
move=> [k Hk] Hce; rewrite Hk in Hce *.
by apply: generic_format_F2R => _; exact: Hce.
Qed.

(* The last place grows with the number, on the positives.                    *)
Lemma cexp_le_pos x y : 0 < x -> x <= y -> (cexp x <= cexp y)%Z.
Proof.
move=> x_gt0 xLy; apply: FLT_exp_monotone.
by apply: mag_le_abs; [lra | rewrite !Rabs_pos_eq; lra].
Qed.

(* A difference is exact as soon as the smaller number sits on the grid of    *)
(* the larger.  This is the easy half of the exactness of a subtraction on    *)
(* an interval; the other half needs the finest grid a float sits on.         *)
Lemma exact_minus_imul a c : format a -> format c -> 0 <= a -> a <= c ->
  is_imul a (pow (cexp c)) -> format (c - a).
Proof.
move=> Fa Fc a_ge0 aLc Hia.
have [->|ca_n0] := Req_dec a c; first by rewrite Rminus_diag; apply: generic_format_0.
have ca_gt0 : 0 < c - a by lra.
apply: imul_cexp_format (is_imul_minus (format_imul_cexp Fc) Hia) _.
by apply: cexp_le_pos => //; lra.
Qed.

End Imul.
