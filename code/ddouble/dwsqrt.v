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
