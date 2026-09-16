From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Relative Plus_error Mult_error BinarySingleNaN.
From Flocq Require Import PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn dwtwosum dwprod dwflx.
From dwarith Require Import dwbound dwdivflx.

(* The square root of a double word, and the error of it.                     *)
(*                                                                            *)
(* `sqrtDw' of dwarith.v is ONE STEP OF NEWTON'S METHOD: the machine root of  *)
(* the two words added is the guess, the double word is divided by it, the    *)
(* two are added and the sum is halved.  Nothing in the ported development    *)
(* says anything about it, so unlike the sum and the quotient this is not a   *)
(* theorem carried down but one proved here -- out of the quotient's bound,   *)
(* the sum's bound, and the quadratic convergence of Newton's step.           *)

Open Scope R_scope.

(* Rounding in the format with no bottom is within one unit roundoff.         *)
Lemma Xrnd_err r : Rabs (Xrnd r - r) <= Du * Rabs r.
Proof.
have H := relative_error_N_FLX radix2 prec (refl_equal _) Dchoice r.
have E : / 2 * bpow radix2 (- prec + 1) = Du.
  by rewrite bpow_plus [bpow radix2 1]/=; lra.
by rewrite E in H.
Qed.

(* The smallest normal number is below one.                                   *)
Lemma Dnorm_le1 : Dnorm <= 1.
Proof.
have -> : (1 = bpow radix2 0)%R by [].
by apply: bpow_le.
Qed.

(* Two square roots are as far apart as their squares, divided by the         *)
(* smaller root at worst.                                                     *)
Lemma sqrt_diff a b : 0 <= a -> 0 < b ->
  Rabs (R_sqrt.sqrt a - R_sqrt.sqrt b) <= Rabs (a - b) / R_sqrt.sqrt b.
Proof.
move=> Ha Hb.
have Hsa := sqrt_pos a.
have Hsb : 0 < R_sqrt.sqrt b by apply: sqrt_lt_R0.
have Ea : R_sqrt.sqrt a * R_sqrt.sqrt a = a by apply: sqrt_sqrt.
have Eb : R_sqrt.sqrt b * R_sqrt.sqrt b = b by apply: sqrt_sqrt; lra.
have E : (R_sqrt.sqrt a - R_sqrt.sqrt b) *
         (R_sqrt.sqrt a + R_sqrt.sqrt b) = a - b by nra.
have H1 : Rabs (R_sqrt.sqrt a - R_sqrt.sqrt b) *
          (R_sqrt.sqrt a + R_sqrt.sqrt b) = Rabs (a - b).
  by rewrite -E Rabs_mult (Rabs_pos_eq (_ + _)) //; lra.
apply: (Rmult_le_reg_r (R_sqrt.sqrt b)) => //.
rewrite /Rdiv Rmult_assoc Rinv_l; last lra.
rewrite Rmult_1_r -H1.
by apply: Rmult_le_compat_l; [exact: Rabs_pos | lra].
Qed.

(* A root grows no faster than its square.                                    *)
Lemma sqrt_le_scale a b c : 0 <= a -> 0 < b -> 0 <= c ->
  a <= b * (1 + c) * (1 + c) ->
  R_sqrt.sqrt a <= R_sqrt.sqrt b * (1 + c).
Proof.
move=> Ha Hb Hc Hle.
have Hsb : 0 < R_sqrt.sqrt b by apply: sqrt_lt_R0.
have Eb : R_sqrt.sqrt b * R_sqrt.sqrt b = b by apply: sqrt_sqrt; lra.
have -> : R_sqrt.sqrt b * (1 + c) =
          R_sqrt.sqrt ((R_sqrt.sqrt b * (1 + c)) * (R_sqrt.sqrt b * (1 + c))).
  by rewrite sqrt_square //; nra.
by apply: sqrt_le_1_alt; nra.
Qed.

(* The machine root of a normal number is within one unit roundoff of the     *)
(* true root.                                                                 *)
Lemma sqrt_guess a :
  Dnorm <= D2R a ->
  Rabs (D2R (PrimFloat.sqrt a) - R_sqrt.sqrt (D2R a)) <=
  Du * R_sqrt.sqrt (D2R a).
Proof.
move=> Hn.
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have HA : 0 < D2R a by lra.
have HS : 0 < R_sqrt.sqrt (D2R a) by apply: sqrt_lt_R0.
have HSn : Dnorm <= R_sqrt.sqrt (D2R a).
  have HD1 := Dnorm_le1.
  have -> : Dnorm = R_sqrt.sqrt (Dnorm * Dnorm) by rewrite sqrt_square //; lra.
  by apply: sqrt_le_1_alt; nra.
have HSa : Dnorm <= Rabs (R_sqrt.sqrt (D2R a)) by rewrite Rabs_pos_eq; lra.
rewrite Dsqrt (Drnd_FLX _ HSa).
have T := Xrnd_err (R_sqrt.sqrt (D2R a)).
have E : Rabs (R_sqrt.sqrt (D2R a)) = R_sqrt.sqrt (D2R a)
  by apply: Rabs_pos_eq; lra.
by rewrite E in T.
Qed.

(* And so of the number a double word stands for, with the extra rounding of  *)
(* the two words into one taken into account.                                 *)
Lemma sqrtDw_guess xh xl :
  Dfin xh -> Dfin xl -> Dfin (xh + xl)%float ->
  Dnorm < D2R (xh + xl)%float ->
  Rabs (D2R (PrimFloat.sqrt (xh + xl)%float) -
        R_sqrt.sqrt (D2R xh + D2R xl)) <=
  Du * (2 + Du) * R_sqrt.sqrt (D2R xh + D2R xl).
Proof.
move=> Fh Fl Fs Hn.
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have Hu := Du_gt0.
have Hp0 : Prec_gt_0 prec by [].
have Ve : Valid_exp Dfexp by rewrite DfexpE; apply: FLT_exp_valid.
have [EA _] := Dfin_add _ _ Fh Fl Fs.
have HA0 : 0 < D2R (xh + xl)%float by lra.
have HXn : Dnorm <= Rabs (D2R xh + D2R xl).
  apply: Dnorm_of_rnd; rewrite -EA.
  have E : Rabs (D2R (xh + xl)%float) = D2R (xh + xl)%float
    by apply: Rabs_pos_eq; lra.
  by rewrite E.
have HX0 : 0 < D2R xh + D2R xl.
  case: (Rle_lt_dec (D2R xh + D2R xl) 0) => [HX|//].
  have T : Drnd (D2R xh + D2R xl) <= Drnd 0 by apply: round_le.
  rewrite round_0 -EA in T.
  by lra.
have HAX : Rabs (D2R (xh + xl)%float - (D2R xh + D2R xl)) <=
           Du * (D2R xh + D2R xl).
  rewrite EA (Drnd_FLX _ HXn).
  have T := Xrnd_err (D2R xh + D2R xl).
  have E : Rabs (D2R xh + D2R xl) = D2R xh + D2R xl
    by apply: Rabs_pos_eq; lra.
  by rewrite E in T.
have HsX : 0 < R_sqrt.sqrt (D2R xh + D2R xl) by apply: sqrt_lt_R0.
have HsA : 0 <= R_sqrt.sqrt (D2R (xh + xl)%float) by apply: sqrt_pos.
have EX : R_sqrt.sqrt (D2R xh + D2R xl) * R_sqrt.sqrt (D2R xh + D2R xl) =
          D2R xh + D2R xl by apply: sqrt_sqrt; lra.
have H1 : Rabs (R_sqrt.sqrt (D2R (xh + xl)%float) -
                R_sqrt.sqrt (D2R xh + D2R xl)) <=
          Du * R_sqrt.sqrt (D2R xh + D2R xl).
  apply: Rle_trans (sqrt_diff _ _ _ _) _; try lra.
  apply: (Rmult_le_reg_r (R_sqrt.sqrt (D2R xh + D2R xl))) => //.
  rewrite /Rdiv Rmult_assoc Rinv_l; last lra.
  by rewrite Rmult_1_r; nra.
have H2 : R_sqrt.sqrt (D2R (xh + xl)%float) <=
          R_sqrt.sqrt (D2R xh + D2R xl) * (1 + Du).
  by apply: sqrt_le_scale; try lra; move: HAX; split_Rabs; nra.
have H3 := sqrt_guess (xh + xl)%float (Rlt_le _ _ Hn).
have HT : Rabs (D2R (PrimFloat.sqrt (xh + xl)%float) -
                R_sqrt.sqrt (D2R xh + D2R xl)) <=
          Rabs (D2R (PrimFloat.sqrt (xh + xl)%float) -
                R_sqrt.sqrt (D2R (xh + xl)%float)) +
          Rabs (R_sqrt.sqrt (D2R (xh + xl)%float) -
                R_sqrt.sqrt (D2R xh + D2R xl)).
  have -> : D2R (PrimFloat.sqrt (xh + xl)%float) -
            R_sqrt.sqrt (D2R xh + D2R xl) =
            (D2R (PrimFloat.sqrt (xh + xl)%float) -
             R_sqrt.sqrt (D2R (xh + xl)%float)) +
            (R_sqrt.sqrt (D2R (xh + xl)%float) -
             R_sqrt.sqrt (D2R xh + D2R xl)) by ring.
  exact: Rabs_triang.
by nra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Newton's step, and why sixteen units cover it                             *)
(* ---------------------------------------------------------------------------*)

(* THE STEP IS QUADRATIC, and that is the whole of why one step suffices.     *)
(* The guess is within two unit roundoffs of the true root, and the step      *)
(* squares that: `(S - R)^2 / (2 S)', four squared roundoffs over two, so     *)
(* two and a half once the divisor is allowed to be a little small.  The      *)
(* quotient contributes half of its own error, eight, and the sum all of      *)
(* its, four.  Fourteen and a half in all, which the fifteen below has room   *)
(* for, and the sixteen of the shift covers with a sixteenth to spare.        *)
(*                                                                            *)
(* The quotient is written `T' and pinned by `T * S = R * R' rather than as   *)
(* `R * R / S', because every bound below then stays a polynomial and `nra'   *)
(* can see it.  Where a division cannot be avoided it is done by hand, by     *)
(* multiplying through and cancelling a positive factor.                      *)

Lemma newton_step R S T D P eD eP :
  0 < R -> 0 < S -> T * S = R * R ->
  Rabs (S - R) <= 2 * Du * R ->
  Rabs (D - T) <= eD * T ->
  Rabs (P - (S + D)) <= eP * (S + D) ->
  0 <= eD -> eD <= 15 * Du ^ 2 + 56 * Du ^ 3 ->
  0 <= eP -> eP <= 4 * Du ^ 2 ->
  Rabs (P / 2 - R) <= 15 * Du ^ 2 * R.
Proof.
move=> HR HS HTS HSR HDT HP HeD0 HeD HeP0 HeP.
have Hu := Du_gt0.
have Hu1 : Du * 1024 <= 1 by exact: Du_small.
have HP2 := Dupos 2.
have HS1 : R * (1 - 2 * Du) <= S by move: HSR; split_Rabs; nra.
have HS2 : S <= R * (1 + 2 * Du) by move: HSR; split_Rabs; nra.
have HT0 : 0 < T by nra.
have HTa : T * (1 - 2 * Du) <= R by nra.
have HT2 : T <= 2 * R by nra.
have HTb : T <= R * (1 + 4 * Du) by nra.
(* Newton's step is quadratic: its error is the square of the guess's *)
have HE1 : (S + T - 2 * R) * S = (S - R) * (S - R) by nra.
have HE10 : 0 <= S + T - 2 * R.
  apply: (Rmult_le_reg_r S); first exact: HS.
  by rewrite Rmult_0_l HE1; apply: Rle_0_sqr.
have HE1a : (S + T - 2 * R) * S <= 4 * Du ^ 2 * (R * R).
  by rewrite HE1; move: HSR; split_Rabs; nra.
have HE1d : ((S + T - 2 * R) * (1 - 2 * Du) - 4 * Du ^ 2 * R) * R <= 0 by nra.
have HE1c : (S + T - 2 * R) * (1 - 2 * Du) <= 4 * Du ^ 2 * R by nra.
have HE1b : S + T - 2 * R <= 5 * Du ^ 2 * R by nra.
(* the quotient's error and the sum's *)
have HDb : eD * T <= 16 * Du ^ 2 * R by nra.
have HD1 : - (16 * Du ^ 2 * R) <= D - T by move: HDT; split_Rabs; nra.
have HD2 : D - T <= 16 * Du ^ 2 * R by move: HDT; split_Rabs; nra.
have HSD : S + D <= R * (2 + 8 * Du) by nra.
have HSD0 : 0 < S + D by nra.
have HP1 : - (4 * Du ^ 2 * (R * (2 + 8 * Du))) <= P - (S + D)
  by move: HP; split_Rabs; nra.
have HP3 : P - (S + D) <= 4 * Du ^ 2 * (R * (2 + 8 * Du))
  by move: HP; split_Rabs; nra.
have HEq : P / 2 - R =
           (P - (S + D)) / 2 + (D - T) / 2 + (S + T - 2 * R) / 2 by field.
by rewrite HEq; apply: Rabs_le; split; nra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The guards the operation tests                                            *)
(* ---------------------------------------------------------------------------*)

Lemma Deqb_eq x y : Dfin x -> Dfin y -> (x =? y)%float = true ->
  D2R x = D2R y.
Proof.
rewrite /Dfin /D2R eqb_equiv => Fx Fy.
rewrite (Beqb_correct _ _ _ _ Fx Fy).
by case: Req_bool_spec.
Qed.

Lemma Deqb_fin x y : Dfin y -> (x =? y)%float = true -> Dfin x.
Proof.
rewrite /Dfin eqb_equiv /Beqb /B2SF.
case: (Prim2B x) => [sx|sx||sx mx ex Hx] //=.
by case: sx; case: (Prim2B y) => [sy|sy||sy my ey Hy] //=; case: sy.
Qed.

(* A root is a number only if what it was taken of was one.                  *)
Lemma Dfin_sqrtI x : Dfin (PrimFloat.sqrt x) -> Dfin x.
Proof.
rewrite /Dfin sqrt_equiv.
have [_ [Hf _]] := Bsqrt_correct _ _ Hprec Hmax mode_NE (Prim2B x).
by rewrite Hf; case: (Prim2B x) => [sx|sx||sx mx ex Hx] //=; case: sx.
Qed.

(* Doubling a number of the format is exact: the same digits, one exponent   *)
(* up, and the top of the range is what `Dfin' rules out.                    *)
Lemma Dformat_double z : generic_format radix2 Dfexp z ->
  generic_format radix2 Dfexp (2 * z).
Proof.
have Hp0 : Prec_gt_0 prec by [].
rewrite DfexpE => Hz.
case: (FLT_format_generic _ _ _ _ Hz) => f Hf1 Hf2 Hf3.
apply: generic_format_FLT.
apply: (FLT_spec _ _ _ _ (Float radix2 (Fnum f) (Fexp f + 1))) => //=; last lia.
rewrite Hf1 /F2R /= bpow_plus.
have -> : bpow radix2 1 = 2 by [].
by ring.
Qed.

(* HALVING IS NOT EXACT, AND THE OPERATION TESTS IT RATHER THAN REASONING    *)
(* ABOUT IT.  Halving a word whose last digit is the smallest there is       *)
(* loses that digit.  Doubling, on the other hand, is always exact, so a     *)
(* word that comes back from its half doubled is a word whose half was       *)
(* exact, and that is one multiplication and one comparison.                 *)
Lemma half_exact a :
  Dfin a -> Dfin (a / 2)%float -> ((a / 2) * 2 =? a)%float = true ->
  D2R (a / 2)%float = D2R a / 2.
Proof.
move=> Fa Fh Ht.
have Ft := Deqb_fin _ _ Fa Ht.
have F2 : Dfin 2%float by [].
have [Em _] := Dfin_mul _ _ Fh F2 Ft.
have Ee := Deqb_eq _ _ Ft Fa Ht.
have E2 : D2R 2%float = 2 by rewrite /D2R; compute; lra.
rewrite Em E2 in Ee.
have Hf : generic_format radix2 Dfexp (D2R (a / 2)%float * 2).
  by rewrite Rmult_comm; apply/Dformat_double/Dformat.
by rewrite (round_generic _ _ _ _ Hf) in Ee; lra.
Qed.

(* And the halving of a pair, which is the last step of the root.            *)
Lemma halfDw_val d :
  Dfin (dwhi d) -> Dfin (dwlo d) ->
  Dfin (dwhi (halfDw d)) -> Dfin (dwlo (halfDw d)) ->
  halfOk d = true ->
  D2R (dwhi (halfDw d)) + D2R (dwlo (halfDw d)) =
  (D2R (dwhi d) + D2R (dwlo d)) / 2.
Proof.
case: d => a b /= Fa Fb Fha Fhb /andb_prop [H1 H2].
by rewrite (half_exact _ Fa Fha H1) (half_exact _ Fb Fhb H2); lra.
Qed.

(* The sum's guard, from the one test a program makes, read as the           *)
(* division's was.                                                           *)
Lemma plusDwDw_finI xh xl yh yl :
  Dfin (dwlo (plusDwDw (DWFloat xh xl) (DWFloat yh yl))) ->
  DplusDwDwFin xh xl yh yl.
Proof.
rewrite /DplusDwDwFin.
set sh := dwhi (twoSum xh yh).
set sl := dwlo (twoSum xh yh).
set th := dwhi (twoSum xl yl).
set tl := dwlo (twoSum xl yl).
set c := (sl + th)%float.
set v := fastTwoSum sh c.
set w := (tl + dwlo v)%float.
have Ez : plusDwDw (DWFloat xh xl) (DWFloat yh yl) = fastTwoSum (dwhi v) w
  by [].
rewrite Ez => Fz.
have G2 := fastTwoSum_finI _ _ Fz.
have [Fvh Fw] := Dfin_addI _ _ (proj1 G2).
have [Ftl Fvl] := Dfin_addI _ _ Fw.
have G1 := fastTwoSum_finI _ _ Fvl.
have [Fsh Fc] := Dfin_addI _ _ (proj1 G1).
have [Fsl Fth] := Dfin_addI _ _ Fc.
have T1 := twoSum_finI _ _ Fsl.
have T2 := twoSum_finI _ _ Ftl.
have [Fxh Fyh] := Dfin_addI _ _ (proj1 T1).
have [Fxl Fyl] := Dfin_addI _ _ (proj1 T2).
by tauto.
Qed.
