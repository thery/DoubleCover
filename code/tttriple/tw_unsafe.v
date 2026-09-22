From Stdlib Require Import ZArith Reals.
From Stdlib Require Import Floats.
From Flocq Require Import Zaux Raux Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Float Float_full Transcend.
From mathcomp Require Import ssreflect.
From twarith Require Import twarith tw_updn tw_ops.

(* THIS FILE IS NOT PROVED, AND WHAT IT ADMITS IS FALSE.                      *)
(*                                                                            *)
(* Interval's functors take a float module whose `sensible_format` is         *)
(* true, and that field is what excuses `div2_correct`.  A triple word        *)
(* cannot meet `div2_correct`: every binary64 number is a whole multiple of   *)
(* two to the minus one thousand and seventy-four, so a sum of three of them  *)
(* is one as well, and the half of such a sum need not be.  So the statement  *)
(* admitted below is not merely unproved - it is refutable, and from it       *)
(* anything at all follows.                                                   *)
(*                                                                            *)
(* It is here so the arithmetic can be measured through Interval before the   *)
(* format is narrowed.  A number computed through this module is a real       *)
(* number and can be compared with any other; a THEOREM obtained through it   *)
(* is worth nothing.  Nothing outside this file depends on it.                *)
(*                                                                            *)
(* The obligations tw_ops.v itself admits are a separate matter, and they     *)
(* are listed at the top of that file.                                        *)

Module TwFloatU <: FloatOps.

(* The one field that differs, and the whole reason for the file.             *)
Definition sensible_format := true.

(* Everything else is what tw_ops.v states.                                   *)
Definition radix := TwFloat.radix.
Definition type := TwFloat.type.
Definition toF := TwFloat.toF.
Definition convert := TwFloat.convert.
Definition toX := TwFloat.toX.
Definition toR := TwFloat.toR.
Definition precision := TwFloat.precision.
Definition sfactor := TwFloat.sfactor.
Definition prec := TwFloat.prec.
Definition PtoP := TwFloat.PtoP.
Definition ZtoS := TwFloat.ZtoS.
Definition StoZ := TwFloat.StoZ.
Definition incr_prec := TwFloat.incr_prec.
Definition zero := TwFloat.zero.
Definition nan := TwFloat.nan.
Definition fromZ := TwFloat.fromZ.
Definition fromZ_DN := TwFloat.fromZ_DN.
Definition fromZ_UP := TwFloat.fromZ_UP.
Definition fromF := TwFloat.fromF.
Definition classify := TwFloat.classify.
Definition real := TwFloat.real.
Definition is_nan := TwFloat.is_nan.
Definition mag := TwFloat.mag.
Definition valid_ub := TwFloat.valid_ub.
Definition valid_lb := TwFloat.valid_lb.
Definition cmp := TwFloat.cmp.
Definition min := TwFloat.min.
Definition max := TwFloat.max.
Definition neg := TwFloat.neg.
Definition abs := TwFloat.abs.
Definition scale := TwFloat.scale.
Definition div2 := TwFloat.div2.
Definition add_UP := TwFloat.add_UP.
Definition add_DN := TwFloat.add_DN.
Definition sub_UP := TwFloat.sub_UP.
Definition sub_DN := TwFloat.sub_DN.
Definition mul_UP := TwFloat.mul_UP.
Definition mul_DN := TwFloat.mul_DN.
Definition pow2_UP := TwFloat.pow2_UP.
Definition div_UP := TwFloat.div_UP.
Definition div_DN := TwFloat.div_DN.
Definition sqrt_UP := TwFloat.sqrt_UP.
Definition sqrt_DN := TwFloat.sqrt_DN.
Definition nearbyint_UP := TwFloat.nearbyint_UP.
Definition nearbyint_DN := TwFloat.nearbyint_DN.
Definition midpoint := TwFloat.midpoint.
Definition zero_correct := TwFloat.zero_correct.
Definition nan_correct := TwFloat.nan_correct.
Definition ZtoS_correct := TwFloat.ZtoS_correct.
Definition fromZ_correct := TwFloat.fromZ_correct.
Definition fromZ_DN_correct := TwFloat.fromZ_DN_correct.
Definition fromZ_UP_correct := TwFloat.fromZ_UP_correct.
Definition classify_correct := TwFloat.classify_correct.
Definition real_correct := TwFloat.real_correct.
Definition is_nan_correct := TwFloat.is_nan_correct.
Definition mag_correct := TwFloat.mag_correct.
Definition valid_lb_correct := TwFloat.valid_lb_correct.
Definition valid_ub_correct := TwFloat.valid_ub_correct.
Definition cmp_correct := TwFloat.cmp_correct.
Definition min_correct := TwFloat.min_correct.
Definition max_correct := TwFloat.max_correct.
Definition neg_correct := TwFloat.neg_correct.
Definition abs_correct := TwFloat.abs_correct.
Definition add_UP_correct := TwFloat.add_UP_correct.
Definition add_DN_correct := TwFloat.add_DN_correct.
Definition sub_UP_correct := TwFloat.sub_UP_correct.
Definition sub_DN_correct := TwFloat.sub_DN_correct.
Definition is_non_neg := TwFloat.is_non_neg.
Definition is_non_neg' := TwFloat.is_non_neg'.
Definition is_pos := TwFloat.is_pos.
Definition is_non_pos := TwFloat.is_non_pos.
Definition is_non_pos' := TwFloat.is_non_pos'.
Definition is_neg := TwFloat.is_neg.
Definition is_non_neg_real := TwFloat.is_non_neg_real.
Definition is_pos_real := TwFloat.is_pos_real.
Definition is_non_pos_real := TwFloat.is_non_pos_real.
Definition is_neg_real := TwFloat.is_neg_real.
Definition mul_UP_correct := TwFloat.mul_UP_correct.
Definition mul_DN_correct := TwFloat.mul_DN_correct.
Definition pow2_UP_correct := TwFloat.pow2_UP_correct.
Definition is_real_ub := TwFloat.is_real_ub.
Definition is_real_lb := TwFloat.is_real_lb.
Definition div_UP_correct := TwFloat.div_UP_correct.
Definition div_DN_correct := TwFloat.div_DN_correct.
Definition sqrt_UP_correct := TwFloat.sqrt_UP_correct.
Definition sqrt_DN_correct := TwFloat.sqrt_DN_correct.
Definition nearbyint_UP_correct := TwFloat.nearbyint_UP_correct.
Definition nearbyint_DN_correct := TwFloat.nearbyint_DN_correct.

(* And the two that cannot be had.  The first is false; the second is about   *)
(* `midpoint`, which is built on `div2` and on the plain half sum, for which no *)
(* bound is proved either.                                                    *)
Lemma div2_correct x :
  sensible_format = true -> (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = (toX x / Xreal 2)%XR.
Proof. Admitted.

Lemma midpoint_correct x y :
  sensible_format = true -> real x = true -> real y = true ->
  (toR x <= toR y)%R ->
  real (midpoint x y) = true /\
  (toR x <= toR (midpoint x y))%R /\ (toR (midpoint x y) <= toR y)%R.
Proof. Admitted.

End TwFloatU.

(* With that, Interval's interval arithmetic and its transcendental           *)
(* functions are built over triple words.                                     *)
Module I := FloatIntervalFull TwFloatU.
Module T := TranscendentalFloatFast TwFloatU.
