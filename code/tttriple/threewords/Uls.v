(* ---------------------------------------------------------------------------*)
(* [uls x] -- the weight of the rightmost nonzero bit of a float -- and its   *)
(* supporting 2-adic valuation ([trP]/[trZ]) and [is_imul] "multiples of a"   *)
(* "power grid" bridge.  split out of the addition development: this is format-generic    *)
(* (independent of round-to-nearest [choice] and of the triple-word layer),   *)
(* so it stands alone and is imported by the triple-word development.         *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Uls.

(* Generic over the precision [p]: the binary64 value (p = 53) is one         *)
(* instance, so these lemmas are reusable at any FLX format.  Radix is        *)
(* binary ([trP]/[trZ]                                                       *)
(* are 2-adic valuations).                                                    *)
Variable p : Z.
Context { prec_gt_0 : Prec_gt_0 p }.

Let beta := radix2.

Local Notation pow e := (bpow beta e).

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation ulp := (ulp beta fexp).

(* [uls x] -- "unit in the last significant place": the weight of the         *)
(* RIGHTMOST NONZERO bit of [x].  ([ulp x = 2^(cexp x)] is the weight of the  *)
(* last *representable* place -- the grid spacing; the weight of the leftmost *)
(* bit is [ufp x], the other extreme.)  If [x = m * 2^(cexp x)] with          *)
(* [m = Ztrunc (mant x)] the mantissa, then [uls x = 2^(cexp x + v2 m)]       *)
(* where [v2 m] is the 2-adic valuation of [m] -- here [trZ m], the count of  *)
(* trailing binary zeros of [m], built from [trP] on the positive part below. *)
(* Hence [uls x = ulp x * 2^(v2 m) >= ulp x] (lemma [ulp_le_ulps]), equality  *)
(* iff the mantissa is odd -- e.g. for [x = -1.01101_2 * 2^364] the paper has *)
(* [ulp x = 2^312] but [uls x = 2^359].  At [x = 0] we set [uls 0 = ulp 0].   *)

(* [trP p] : number of trailing binary zeros of the positive [p] (its 2-adic  *)
(* valuation).                                                                *)
Fixpoint trP (p : positive) := if p is xO p1 then (trP p1).+1 else 0%N.

(* [two_power_pos n] : [2^n] as a positive.                                   *)
Definition two_power_pos n := iter n xO 1%positive.

(* [2^(trP p)] divides [p] (i.e. [trP p] trailing zeros can be factored out). *)
Lemma trPE p1 : (two_power_pos (trP p1) | p1)%positive.
Proof.
have div1 q : (1 | q)%positive by exists q; rewrite Pos.mul_comm.
elim: p1 => //= p1 [q {2}->] /=; exists q; lia.
Qed.

(* [trZ z] : 2-adic valuation of [z] (its trailing binary zeros), [0] at [0]; *)
(* it ignores the sign, using [trP] on the positive part.                     *)
Definition trZ (z : Z) := if z is Zpos p1 then (trP p1) else
                          if z is Zneg p1 then (trP p1) else 0%N.

Lemma trZ0 : trZ 0 = 0%N.
Proof. by []. Qed.

(* [trN z] : the 2-adic valuation as an integer, [Z.of_nat (trZ z)] -- the    *)
(* form in which it enters exponents ([cexp x + trN (mantissa)]).             *)
Definition trN (z : Z) := Z.of_nat (trZ z).

Lemma two_power_nat_pos n : (Zpos (two_power_pos n) = two_power_nat n)%Z.
Proof. by elim: n. Qed.

(* [2^(trZ z)] divides [z]: the valuation really is extractable.              *)
Lemma trZE p1 : (2 ^ Z.of_nat (trZ p1) | p1)%Z.
Proof.
rewrite -two_power_nat_equiv.
case: p1 => [|p1|p1]; first by apply: Z.divide_0_r.
  by rewrite -two_power_nat_pos /=; apply/Z.divide_Zpos/trPE.
rewrite -two_power_nat_pos /=.
by apply/Z.divide_Zpos_Zneg_r/Z.divide_Zpos/trPE.
Qed.

(* uls, as above: [ulp 0] at zero, else [2^(cexp x + v2(mantissa))].          *)
Definition uls (x : R) : R :=
  if Req_bool x 0 then 0 else
  let m := Ztrunc (mant x) in pow (cexp x + Z.of_nat (trZ m))%Z.

Lemma uls0 : uls 0 = 0.
Proof. by rewrite /uls; case: Req_bool_spec. Qed.

(* [x] factors as (its odd mantissa part) * [uls x] -- the defining property  *)
(* of [uls] as the weight of the rightmost nonzero bit.                       *)
Lemma ulsE x :
 format x -> 
 x = IZR (Ztrunc (mant x) / (2 ^ Z.of_nat (trZ (Ztrunc (mant x)))))%Z * uls x.
Proof.
move=> xF; rewrite /uls.
case: (Req_bool_spec x 0) => [->|x_neq0].
  by rewrite scaled_mantissa_0 Ztrunc_IZR Rmult_0_l.
rewrite -[X in X = _](scaled_mantissa_mult_bpow beta fexp) bpow_plus.
rewrite -[X in _ = _ * (_ * X)]IZR_Zpower; last by lia.
rewrite [X in _ = _ * X]Rmult_comm -[RHS]Rmult_assoc -mult_IZR.
rewrite Zmult_comm -Znumtheory.Zdivide_Zdiv_eq.
- by rewrite -scaled_mantissa_generic //.
- by apply: Zpower_gt_0; lia.
by apply: trZE.
Qed.

(* [ulp x <= uls x]: the rightmost nonzero bit is at or above the last place. *)
Lemma ulp_le_ulps x : ulp x <= uls x.
Proof.
rewrite /uls.
case: Req_bool_spec => [->//|x_neq0]; first by rewrite ulp_FLX_0; lra.
rewrite ulp_neq_0 //;apply: bpow_le; lia.
Qed.

(* [uls] is always positive (a power of two, or [ulp 0] at zero).             *)
Lemma uls_gt_0 x : x <> 0 -> 0 < uls x.
Proof.
by rewrite /uls; case: Req_bool_spec => // _ _; exact: bpow_gt_0.
Qed.

Lemma uls_ge_0 x : 0 <= uls x.
Proof.
rewrite /uls; case: Req_bool_spec => [|_]; first by lra.
by exact: bpow_ge_0.
Qed.

(* The rightmost nonzero bit is at most the magnitude: [uls x <= |x|] for a   *)
(* nonzero float.  [x = M' * uls x] with [M'] a nonzero integer, so           *)
(* [|x| = |M'| * uls x >= uls x].                                             *)
Lemma uls_le_abs x : format x -> x <> 0 -> uls x <= Rabs x.
Proof.
move=> xF xn0; have Hu := uls_gt_0 xn0.
have Hx := ulsE xF.
set M := (Ztrunc (mant x) / 2 ^ Z.of_nat (trZ (Ztrunc (mant x))))%Z in Hx.
have M0 : M <> 0%Z by move=> H0; apply: xn0; rewrite Hx H0 /= Rmult_0_l.
have H1 : 1 <= Rabs (IZR M) by rewrite -abs_IZR; apply: IZR_le; lia.
have -> : Rabs x = Rabs (IZR M) * uls x.
  by rewrite {1}Hx Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ Hu)).
nra.
Qed.

(* A float closer to zero than TWICE its [uls] IS its [uls] in magnitude.     *)
(* [x = M * uls x] with [M] a nonzero integer, so [|M| < 2] forces [|M| = 1]. *)
(* This is what makes a [uls] boundary case identifiable: below [2 * uls x]   *)
(* there is exactly one admissible magnitude.                                 *)
Lemma abs_eq_uls_of_lt_2uls x :
  format x -> x <> 0 -> Rabs x < 2 * uls x -> Rabs x = uls x.
Proof.
move=> xF xn0 Hlt; have Hu := uls_gt_0 xn0.
have Hx := ulsE xF.
set M := (Ztrunc (mant x) / 2 ^ Z.of_nat (trZ (Ztrunc (mant x))))%Z in Hx.
have M0 : M <> 0%Z by move=> H0; apply: xn0; rewrite Hx H0 /= Rmult_0_l.
have HxM : Rabs x = Rabs (IZR M) * uls x.
  by rewrite {1}Hx Rabs_mult (Rabs_pos_eq _ (Rlt_le _ _ Hu)).
have HA : Rabs (IZR M) = IZR (Z.abs M) by rewrite abs_IZR.
have H1 : 1 <= IZR (Z.abs M) by apply: IZR_le; lia.
have H2 : IZR (Z.abs M) < 2 by move: Hlt; rewrite HxM HA; nra.
have HM : Z.abs M = 1%Z by have := lt_IZR _ _ H2; have := le_IZR _ _ H1; lia.
by move: HxM; rewrite HA HM => ->; lra.
Qed.

(* ===========================================================================*)
(*  [is_imul] bridge: reusable "multiples of a power grid" facts, feeding the *)
(*  paper's "multiples of 2u" argument (Theorem 1) via Flocq's [is_imul].     *)
(* ===========================================================================*)

(* [x] is an integer multiple of its [uls] (the weight of its rightmost bit). *)
Lemma uls_imul x : format x -> is_imul x (uls x).
Proof.
move=> xF.
by exists (Ztrunc (mant x) / 2 ^ Z.of_nat (trZ (Ztrunc (mant x))))%Z;
  exact: ulsE.
Qed.

(* A float is an integer multiple of its own [ulp] ([= bpow (cexp x)]).       *)
Lemma format_imul_cexp x : format x -> is_imul x (bpow beta (cexp x)).
Proof.
by move=> xF; apply: (is_imul_format_mag_pow xF);
  rewrite /cexp; apply: Z.le_refl.
Qed.


(* The odd part of a positive is odd: [p / 2^(trP p)] strips all trailing     *)
(* zeros.  So [trP] (and [trZ]) really is the MAXIMAL power of two dividing.  *)
Lemma trP_odd q : Z.odd (Zpos q / 2 ^ Z.of_nat (trP q)).
Proof.
elim: q => [q IH|q IH|] //.
- by rewrite [Z.of_nat (trP q~1)]/= Z.pow_0_r Zdiv_1_r.
have hpow : (2 ^ Z.of_nat (trP q) <> 0)%Z by apply: Z.pow_nonzero; lia.
have -> : trP q~0 = (trP q).+1 by [].
rewrite Nat2Z.inj_succ Z.pow_succ_r; last by apply: Zle_0_nat.
by have -> : (Z.pos q~0 = 2 * Z.pos q)%Z by []; rewrite Z.div_mul_cancel_l.
Qed.

Lemma trZ_odd z : (z <> 0)%Z -> Z.odd (z / 2 ^ Z.of_nat (trZ z)).
Proof.
case: z => [//|q _|q _]; first exact: trP_odd.
have hne : (2 ^ Z.of_nat (trP q) <> 0)%Z by apply: Z.pow_nonzero; lia.
have Hmod : (Z.pos q mod 2 ^ Z.of_nat (trP q) = 0)%Z :=
  (Z.mod_divide _ _ hne).2 (trZE (Z.pos q)).
have -> : (Z.neg q = - Z.pos q)%Z by [].
by rewrite (_ : trZ (- Z.pos q) = trP q) // Z.div_opp_l_z // Z.odd_opp;
  exact: trP_odd.
Qed.

(* Converse of [uls_imul]: any power grid a nonzero float lies on is at most  *)
(* its [uls].  If [g > uls x] then [x] is an ODD multiple of [uls x] that     *)
(* is also a multiple of [2 * uls x] -- impossible.                           *)
Lemma is_imul_uls_ge x e : format x -> x <> 0 ->
  is_imul x (bpow beta e) -> bpow beta e <= uls x.
Proof.
move=> xF xn0 [z Hz].
set m := Ztrunc (mant x).
have Huls : uls x = bpow beta (cexp x + Z.of_nat (trZ m)).
  by rewrite /uls; case: Req_bool_spec.
have Hx : x = IZR (m / 2 ^ Z.of_nat (trZ m)) * uls x by exact: ulsE.
have mn0 : (m <> 0)%Z by move=> H0; apply: xn0; rewrite Hx H0 Zdiv_0_l; lra.
rewrite Huls.
case: (Rle_lt_dec (bpow beta e) (bpow beta (cexp x + Z.of_nat (trZ m)))) =>
  [//|Hlt]; exfalso.
set g := (cexp x + Z.of_nat (trZ m))%Z in Hlt.
have He : (g < e)%Z by apply: (lt_bpow beta).
have Hpow : bpow beta e = bpow beta g * IZR (2 ^ (e - g)).
  by rewrite (IZR_Zpower beta (e - g));
     [rewrite -bpow_plus; congr bpow; lia | lia].
have Heq : IZR (m / 2 ^ Z.of_nat (trZ m)) * bpow beta g =
           IZR z * (bpow beta g * IZR (2 ^ (e - g))).
  by rewrite -Hpow -Huls -Hx.
have Hodeq : (m / 2 ^ Z.of_nat (trZ m) = z * 2 ^ (e - g))%Z.
  apply: eq_IZR; rewrite mult_IZR.
  apply: (Rmult_eq_reg_r (bpow beta g)); last by have := bpow_gt_0 beta g; lra.
  by rewrite Heq; ring.
have Ho := trZ_odd mn0; rewrite Hodeq Z.odd_mul in Ho.
have Hev : Z.odd (2 ^ (e - g)) = false.
  have He1 : (e - g = Z.succ (e - g - 1))%Z by lia.
  rewrite He1 Z.pow_succ_r; last by lia.
  by rewrite Z.odd_mul.
by rewrite Hev andbF in Ho.
Qed.

End Uls.
