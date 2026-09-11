From Stdlib Require Import ZArith Reals.
From Stdlib Require Import Floats.
From Flocq Require Import Zaux Raux Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Float Float_full Transcend.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dw_updn dw_ops.

(* THIS FILE IS NOT PROVED, AND WHAT IT ADMITS IS FALSE.                      *)
(*                                                                            *)
(* Interval's functors take a float module whose `sensible_format` is         *)
(* true, and that field is what excuses `div2_correct`.  A double word        *)
(* cannot meet `div2_correct`: the pair one and two to the minus one          *)
(* thousand and seventy-four denotes a number whose half is an odd            *)
(* multiple of two to the minus one thousand and seventy-five, and no sum     *)
(* of two binary64 numbers is that.  So the statement admitted below is       *)
(* not merely unproved - it is refutable, and from it anything at all         *)
(* follows.                                                                   *)
(*                                                                            *)
(* It is here so the arithmetic can be measured through Interval before       *)
(* the format is narrowed.  A number computed through this module is a        *)
(* real number and can be compared with any other; a THEOREM obtained         *)
(* through it is worth nothing.  dw_ops.v itself stays proved and             *)
(* admit-free; nothing outside this file depends on it.                       *)

Module DwFloatU <: FloatOps.

(* The one field that differs, and the whole reason for the file.             *)
Definition sensible_format := true.

(* Everything else is what dw_ops.v proved.                                   *)
Definition radix := DwFloat.radix.
Definition type := DwFloat.type.
Definition toF := DwFloat.toF.
Definition convert := DwFloat.convert.
Definition toX := DwFloat.toX.
Definition toR := DwFloat.toR.
Definition precision := DwFloat.precision.
Definition sfactor := DwFloat.sfactor.
Definition prec := DwFloat.prec.
Definition PtoP := DwFloat.PtoP.
Definition ZtoS := DwFloat.ZtoS.
Definition StoZ := DwFloat.StoZ.
Definition incr_prec := DwFloat.incr_prec.
Definition zero := DwFloat.zero.
Definition nan := DwFloat.nan.
Definition fromZ := DwFloat.fromZ.
Definition fromZ_DN := DwFloat.fromZ_DN.
Definition fromZ_UP := DwFloat.fromZ_UP.
Definition fromF := DwFloat.fromF.
Definition classify := DwFloat.classify.
Definition real := DwFloat.real.
Definition is_nan := DwFloat.is_nan.
Definition mag := DwFloat.mag.
Definition valid_ub := DwFloat.valid_ub.
Definition valid_lb := DwFloat.valid_lb.
Definition cmp := DwFloat.cmp.
Definition min := DwFloat.min.
Definition max := DwFloat.max.
Definition neg := DwFloat.neg.
Definition abs := DwFloat.abs.
Definition scale := DwFloat.scale.
Definition div2 := DwFloat.div2.
Definition add_UP := DwFloat.add_UP.
Definition add_DN := DwFloat.add_DN.
Definition sub_UP := DwFloat.sub_UP.
Definition sub_DN := DwFloat.sub_DN.
Definition mul_UP := DwFloat.mul_UP.
Definition mul_DN := DwFloat.mul_DN.
Definition pow2_UP := DwFloat.pow2_UP.
Definition div_UP := DwFloat.div_UP.
Definition div_DN := DwFloat.div_DN.
Definition sqrt_UP := DwFloat.sqrt_UP.
Definition sqrt_DN := DwFloat.sqrt_DN.
Definition nearbyint_UP := DwFloat.nearbyint_UP.
Definition nearbyint_DN := DwFloat.nearbyint_DN.
Definition midpoint := DwFloat.midpoint.
Definition zero_correct := DwFloat.zero_correct.
Definition nan_correct := DwFloat.nan_correct.
Definition ZtoS_correct := DwFloat.ZtoS_correct.
Definition fromZ_correct := DwFloat.fromZ_correct.
Definition fromZ_DN_correct := DwFloat.fromZ_DN_correct.
Definition fromZ_UP_correct := DwFloat.fromZ_UP_correct.
Definition classify_correct := DwFloat.classify_correct.
Definition real_correct := DwFloat.real_correct.
Definition is_nan_correct := DwFloat.is_nan_correct.
Definition mag_correct := DwFloat.mag_correct.
Definition valid_lb_correct := DwFloat.valid_lb_correct.
Definition valid_ub_correct := DwFloat.valid_ub_correct.
Definition cmp_correct := DwFloat.cmp_correct.
Definition min_correct := DwFloat.min_correct.
Definition max_correct := DwFloat.max_correct.
Definition neg_correct := DwFloat.neg_correct.
Definition abs_correct := DwFloat.abs_correct.
Definition add_UP_correct := DwFloat.add_UP_correct.
Definition add_DN_correct := DwFloat.add_DN_correct.
Definition sub_UP_correct := DwFloat.sub_UP_correct.
Definition sub_DN_correct := DwFloat.sub_DN_correct.
Definition is_non_neg := DwFloat.is_non_neg.
Definition is_non_neg' := DwFloat.is_non_neg'.
Definition is_pos := DwFloat.is_pos.
Definition is_non_pos := DwFloat.is_non_pos.
Definition is_non_pos' := DwFloat.is_non_pos'.
Definition is_neg := DwFloat.is_neg.
Definition is_non_neg_real := DwFloat.is_non_neg_real.
Definition is_pos_real := DwFloat.is_pos_real.
Definition is_non_pos_real := DwFloat.is_non_pos_real.
Definition is_neg_real := DwFloat.is_neg_real.
Definition mul_UP_correct := DwFloat.mul_UP_correct.
Definition mul_DN_correct := DwFloat.mul_DN_correct.
Definition pow2_UP_correct := DwFloat.pow2_UP_correct.
Definition is_real_ub := DwFloat.is_real_ub.
Definition is_real_lb := DwFloat.is_real_lb.
Definition div_UP_correct := DwFloat.div_UP_correct.
Definition div_DN_correct := DwFloat.div_DN_correct.
Definition sqrt_UP_correct := DwFloat.sqrt_UP_correct.
Definition sqrt_DN_correct := DwFloat.sqrt_DN_correct.
Definition nearbyint_UP_correct := DwFloat.nearbyint_UP_correct.
Definition nearbyint_DN_correct := DwFloat.nearbyint_DN_correct.

(* And the two that cannot be had.  The first is false; the second is         *)
(* about `midpoint`, which is built on `div2` and on `plusDwDw`, for          *)
(* which no bound is proved either.                                           *)
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

End DwFloatU.

(* With that, Interval's interval arithmetic and its transcendental           *)
(* functions are built over double words.                                     *)
Module I := FloatIntervalFull DwFloatU.
Module T := TranscendentalFloatFast DwFloatU.
