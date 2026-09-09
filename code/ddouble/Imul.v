From Stdlib Require Import ZArith Reals Psatz.
From Flocq Require Import Core Plus_error Sterbenz Operations.
From mathcomp Require Import ssreflect ssrbool.

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

(* -------------------------------------------------------------------------- *)
(*  The finest grid a float sits on                                           *)
(* -------------------------------------------------------------------------- *)

(* A float sits on the grid of its last place, but usually on a finer one     *)
(* still: the weight of its last nonzero digit.  That weight is the finest    *)
(* grid it sits on, and being the finest it is the one that says which of     *)
(* two floats is the more finely placed.                                      *)

(* How many times two divides a positive number.                              *)
Fixpoint trP (q : positive) : nat := if q is xO q1 then S (trP q1) else O.

(* The same for an integer, sign ignored, and none at all at zero.            *)
Definition trZ (z : Z) : nat :=
  match z with Zpos q => trP q | Zneg q => trP q | Z0 => O end.

(* That many twos really do divide the number.                                *)
Lemma trPE q : (2 ^ Z.of_nat (trP q) | Zpos q)%Z.
Proof.
elim: q => [q _|q IH|].
- by rewrite (_ : trP q~1 = O) // Z.pow_0_r; apply: Z.divide_1_l.
- rewrite (_ : trP q~0 = S (trP q)) // (_ : Z.pos q~0 = 2 * Z.pos q)%Z //.
  rewrite Nat2Z.inj_succ Z.pow_succ_r; last by apply: Zle_0_nat.
  by apply: Z.mul_divide_mono_l.
by rewrite (_ : trP 1 = O) // Z.pow_0_r; apply: Z.divide_1_l.
Qed.

Lemma trZE z : (2 ^ Z.of_nat (trZ z) | z)%Z.
Proof.
case: z => [|q|q]; first by apply: Z.divide_0_r.
  exact: trPE.
by rewrite (_ : Z.neg q = - Z.pos q)%Z //; apply/Z.divide_opp_r/trPE.
Qed.

(* And no more: what is left after dividing them out is odd.                  *)
Lemma trP_odd q : Z.odd (Zpos q / 2 ^ Z.of_nat (trP q)).
Proof.
elim: q => [q IH|q IH|] //.
  by rewrite [Z.of_nat (trP q~1)]/= Z.pow_0_r Zdiv_1_r.
have hpow : (2 ^ Z.of_nat (trP q) <> 0)%Z by apply: Z.pow_nonzero; lia.
have -> : trP q~0 = S (trP q) by [].
rewrite Nat2Z.inj_succ Z.pow_succ_r; last by apply: Zle_0_nat.
by have -> : (Z.pos q~0 = 2 * Z.pos q)%Z by []; rewrite Z.div_mul_cancel_l.
Qed.

Lemma trZ_odd z : (z <> 0)%Z -> Z.odd (z / 2 ^ Z.of_nat (trZ z)).
Proof.
case: z => [//|q _|q _]; first by exact: trP_odd.
have hne : (2 ^ Z.of_nat (trP q) <> 0)%Z by apply: Z.pow_nonzero; lia.
have Hmod : (Z.pos q mod 2 ^ Z.of_nat (trP q) = 0)%Z :=
  proj2 (Z.mod_divide _ _ hne) (trZE (Z.pos q)).
have -> : (Z.neg q = - Z.pos q)%Z by [].
by rewrite (_ : trZ (- Z.pos q) = trP q) // Z.div_opp_l_z // Z.odd_opp;
   exact: trP_odd.
Qed.

(* The weight of the last nonzero digit, and nothing at zero.                 *)
Definition uls (x : R) : R :=
  if Req_bool x 0 then 0 else
  pow (cexp x + Z.of_nat (trZ (Ztrunc (mant x)))).

Lemma uls0 : uls 0 = 0.
Proof. by rewrite /uls; case: Req_bool_spec. Qed.

Lemma uls_pow x : x <> 0 -> exists e, uls x = pow e.
Proof.
move=> xn0; exists (cexp x + Z.of_nat (trZ (Ztrunc (mant x))))%Z.
by rewrite /uls; case: Req_bool_spec.
Qed.

(* A float is an odd number of those weights: that is what makes the weight   *)
(* the last nonzero digit and not merely one of the digits.                   *)
Lemma ulsE x : format x ->
  x = IZR (Ztrunc (mant x) / 2 ^ Z.of_nat (trZ (Ztrunc (mant x))))%Z * uls x.
Proof.
move=> Fx; rewrite /uls.
case: Req_bool_spec => [->|xn0].
  by rewrite scaled_mantissa_0 Ztrunc_IZR Rmult_0_l.
rewrite -[X in X = _](scaled_mantissa_mult_bpow beta fexp) bpow_plus.
rewrite -[X in _ = _ * (_ * X)]IZR_Zpower; last by lia.
rewrite [X in _ = _ * X]Rmult_comm -[RHS]Rmult_assoc -mult_IZR.
rewrite Zmult_comm -Znumtheory.Zdivide_Zdiv_eq.
- by rewrite -scaled_mantissa_generic.
- by apply: Zpower_gt_0; lia.
by apply: trZE.
Qed.

(* So a float does sit on that grid.                                          *)
Lemma uls_imul x : format x -> is_imul x (uls x).
Proof.
move=> Fx.
by exists (Ztrunc (mant x) / 2 ^ Z.of_nat (trZ (Ztrunc (mant x))))%Z;
   exact: ulsE.
Qed.

(* And on no finer one.  A finer grid would make the odd number above even.   *)
Lemma is_imul_uls_ge x e : format x -> x <> 0 -> is_imul x (pow e) ->
  pow e <= uls x.
Proof.
move=> Fx xn0 [z Hz].
set m := Ztrunc (mant x).
have Huls : uls x = pow (cexp x + Z.of_nat (trZ m)) by rewrite /uls;
  case: Req_bool_spec.
have Hx : x = IZR (m / 2 ^ Z.of_nat (trZ m))%Z * uls x by exact: ulsE.
have mn0 : (m <> 0)%Z by move=> H0; apply: xn0; rewrite Hx H0 Zdiv_0_l; lra.
rewrite Huls.
set g := (cexp x + Z.of_nat (trZ m))%Z.
case: (Rle_lt_dec (pow e) (pow g)) => [//|Hlt]; exfalso.
have He : (g < e)%Z by apply: (lt_bpow beta).
have Hpow : pow e = pow g * IZR (2 ^ (e - g)).
  by rewrite (IZR_Zpower beta (e - g));
     [rewrite -bpow_plus; congr bpow; lia | lia].
have Heq : IZR (m / 2 ^ Z.of_nat (trZ m))%Z * pow g =
           IZR z * (pow g * IZR (2 ^ (e - g))).
  by rewrite -Hpow -/g -Huls -Hx.
have Hodeq : (m / 2 ^ Z.of_nat (trZ m) = z * 2 ^ (e - g))%Z.
  apply: eq_IZR; rewrite mult_IZR.
  apply: (Rmult_eq_reg_r (pow g)); last by have := bpow_gt_0 beta g; lra.
  by rewrite Heq; ring.
have Ho := trZ_odd mn0; rewrite -/m Hodeq Z.odd_mul in Ho.
have Hev : Z.odd (2 ^ (e - g)) = false.
  have He1 : (e - g = Z.succ (e - g - 1))%Z by lia.
  by rewrite He1 Z.pow_succ_r; [rewrite Z.odd_mul | lia].
by rewrite Hev andbF in Ho.
Qed.

(* A nonzero float is not on the grid one step coarser than its last digit.   *)
Lemma not_imul_uls_succ x e : format x -> x <> 0 -> uls x = pow e ->
  ~ is_imul x (pow (e + 1)).
Proof.
move=> Fx xn0 Hu Hc.
by have := is_imul_uls_ge Fx xn0 Hc; rewrite Hu => /le_bpow; lia.
Qed.

(* A float off a grid has its last place no coarser than that grid, since     *)
(* otherwise it would sit on it.                                              *)
Lemma format_not_imul_cexp_le x e : format x -> ~ is_imul x (pow (e + 1)) ->
  (cexp x <= e)%Z.
Proof.
move=> Fx Hn; case: (Z_le_gt_dec (cexp x) e) => // Hgt.
by case: Hn; apply: is_imul_pow_le (format_imul_cexp Fx) _; lia.
Qed.

(* -------------------------------------------------------------------------- *)
(*  A subtraction that is exact stays exact on the whole interval             *)
(* -------------------------------------------------------------------------- *)

(* If the far difference is a float then so is every nearer one.  Either the  *)
(* smaller number sits on the grid of the nearer one, and the easy half above *)
(* applies; or it is more finely placed, and then the far difference is as    *)
(* finely placed as it is.  Being a float the far difference then has its     *)
(* last place no coarser than that, and the nearer difference, being no       *)
(* larger, needs no finer a place either.                                     *)
Lemma exact_minus_interval a b c :
  format a -> format b -> format c -> format (b - a) ->
  0 <= a -> a <= b -> a <= c -> c <= b -> format (c - a).
Proof.
move=> Fa Fb Fc Fba a_ge0 aLb aLc cLb.
have [ca0|ca_n0] := Req_dec (c - a) 0.
  by rewrite ca0; exact: generic_format_0.
have ca_gt0 : 0 < c - a by lra.
have [a0|a_n0] := Req_dec a 0; first by rewrite a0 Rminus_0_r.
have a_gt0 : 0 < a by lra.
have c_gt0 : 0 < c by lra.
have [ea Hulsa] := uls_pow a_n0.
have Hia : is_imul a (pow ea) by rewrite -Hulsa; exact: uls_imul.
have [Hcase|Hcase] := Z_le_gt_dec (cexp c) ea.
  have Hia' : is_imul a (pow (cexp c)) by apply: is_imul_pow_le Hia _.
  have Hic : is_imul c (pow (cexp c)) by exact: format_imul_cexp.
  apply: imul_cexp_format (is_imul_minus Hic Hia') _.
  by apply: cexp_le_pos => //; lra.
have Hcb : (cexp c <= cexp b)%Z by apply: cexp_le_pos => //; lra.
have Hib : is_imul b (pow (ea + 1)).
  by apply: is_imul_pow_le (format_imul_cexp Fb) _; lia.
have Hna : ~ is_imul a (pow (ea + 1)) by apply: not_imul_uls_succ.
have Hnd : ~ is_imul (b - a) (pow (ea + 1)).
  move=> Hd; apply: Hna.
  have -> : a = b - (b - a) by lra.
  by apply: is_imul_minus.
have Hcd : (cexp (b - a) <= ea)%Z by apply: format_not_imul_cexp_le.
have Hic : is_imul c (pow ea).
  by apply: is_imul_pow_le (format_imul_cexp Fc) _; lia.
apply: imul_cexp_format (is_imul_minus Hic Hia) _.
by apply: Z.le_trans Hcd; apply: cexp_le_pos => //; lra.
Qed.

End Imul.
