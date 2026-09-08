From Stdlib Require Import ZArith Reals.
From Stdlib Require Import Floats PrimInt63.
From Flocq Require Import Zaux Raux BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Generic_proof Primitive_ops.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dw_updn.

(* Double words as a float format for Interval.                               *)
(* Phase one: the operations only.  The module is not yet declared to meet    *)
(* FloatOps, because that declaration is a check of the theorems, and those   *)
(* come next.  Every obligation of that signature is an inequality, so an     *)
(* operation is allowed to be wider than necessary; the ones marked below as  *)
(* only ordinarily tight can be sharpened later without changing a single     *)
(* statement.                                                                 *)

Module DwFloat.

Definition radix := radix2.
Definition sensible_format := true.
Definition type := dwfloat.

(* A double word denotes the sum of its two words, and that sum is exact.     *)
Definition toF (x : type) : Basic.float radix2 :=
  let: DWFloat xh xl := x in
  Generic.Fadd_exact (PrimitiveFloat.toF xh) (PrimitiveFloat.toF xl).

Definition toX x := FtoX (toF x).
Definition toR x := proj_val (toX x).
Definition convert x := FtoX (toF x).

(* The precision is fixed: two binary64 words give what they give, and there  *)
(* is no way to ask for more.  Interval may ask; the answer does not change.  *)
Definition precision := unit.
Definition sfactor := Z.
Definition prec (_ : precision) := 107%positive.
Definition PtoP (_ : positive) : precision := tt.
Definition ZtoS (x : Z) := x.
Definition StoZ (x : Z) := x.
Definition incr_prec (p : precision) (_ : positive) := p.

(* The precision the underlying binary64 operations are asked for.            *)
Definition fprec := PrimitiveFloat.PtoP 53.

Definition zero := DWFloat PrimFloat.zero PrimFloat.zero.
Definition nan := DWFloat PrimFloat.nan PrimFloat.zero.

Definition fromZ (n : Z) := fp2dw (PrimitiveFloat.fromZ n).
Definition fromZ_UP (_ : precision) (n : Z) :=
  fp2dw (PrimitiveFloat.fromZ_UP fprec n).
Definition fromZ_DN (_ : precision) (n : Z) :=
  fp2dw (PrimitiveFloat.fromZ_DN fprec n).
Definition fromF (f : Basic.float radix) := fp2dw (PrimitiveFloat.fromF f).

(* A double word is a real number when both its words are, an infinity when   *)
(* either is, and not a number as soon as either is not.                      *)
Definition classify x :=
  let: DWFloat xh xl := x in
  match PrimFloat.classify xh, PrimFloat.classify xl with
  | NaN, _ | _, NaN => Sig.Fnan
  | PInf, _ | _, PInf => Fpinfty
  | NInf, _ | _, NInf => Fminfty
  | _, _ => Freal
  end.

Definition real x := match classify x with Freal => true | _ => false end.
Definition is_nan x := match classify x with Sig.Fnan => true | _ => false end.

(* The low word is below one unit in the last place of the high one, so the   *)
(* high word alone gives the magnitude.                                       *)
Definition mag x := PrimitiveFloat.mag (dwhi x).

(* Only an infinity of the wrong sign is barred from being a bound.           *)
Definition valid_ub x := match classify x with Fminfty => false | _ => true end.
Definition valid_lb x := match classify x with Fpinfty => false | _ => true end.

(* Two double words compare on their high words, and on the low ones when     *)
(* the high ones agree.                                                       *)
Definition cmp x y :=
  match PrimitiveFloat.cmp (dwhi x) (dwhi y) with
  | Xeq => PrimitiveFloat.cmp (dwlo x) (dwlo y)
  | c => c
  end.

Definition min x y :=
  match cmp x y with Xeq | Xlt => x | Xgt => y | Xund => nan end.
Definition max x y :=
  match cmp x y with Xeq | Xgt => x | Xlt => y | Xund => nan end.

Definition neg x := negDw x.

(* The two words of a double word have the sign of their sum, so the sign of  *)
(* the high word decides.                                                     *)
Definition abs x :=
  if PrimFloat.get_sign (dwhi x) then negDw x else x.

(* Scaling by a power of two moves both words by the same amount and is       *)
(* exact, barring overflow.                                                   *)
Definition scale x (e : sfactor) :=
  let: DWFloat xh xl := x in
  DWFloat (PrimitiveFloat.scale xh e) (PrimitiveFloat.scale xl e).

Definition div2 x :=
  let: DWFloat xh xl := x in DWFloat (xh / 2)%float (xl / 2)%float.

Definition pow2_UP (_ : precision) (e : sfactor) :=
  fp2dw (PrimitiveFloat.pow2_UP fprec e).

Definition add_UP (_ : precision) x y := addDwUp x y.
Definition add_DN (_ : precision) x y := addDwDn x y.
Definition sub_UP (_ : precision) x y := subDwUp x y.
Definition sub_DN (_ : precision) x y := subDwDn x y.
Definition mul_UP (_ : precision) x y := mulDwUp x y.
Definition mul_DN (_ : precision) x y := mulDwDn x y.
Definition div_UP (_ : precision) x y := divDwUp x y.
Definition div_DN (_ : precision) x y := divDwDn x y.
Definition sqrt_UP (_ : precision) x := sqrtDwUp x.
Definition sqrt_DN (_ : precision) x := sqrtDwDn x.

(* Rounding to an integer is monotone, so rounding a bound of the value       *)
(* gives a bound of the rounded value.  Only ordinarily tight.                *)
Definition nearbyint_UP (mode : rounding_mode) x :=
  fp2dw (PrimitiveFloat.nearbyint_UP mode (addUpFp (dwhi x) (dwlo x))).
Definition nearbyint_DN (mode : rounding_mode) x :=
  fp2dw (PrimitiveFloat.nearbyint_DN mode (addDnFp (dwhi x) (dwlo x))).

(* The midpoint is the plain half sum: rounding to nearest keeps it between   *)
(* the two, which is all that is asked of it.                                 *)
Definition midpoint x y := div2 (plusDwDw x y).

End DwFloat.
