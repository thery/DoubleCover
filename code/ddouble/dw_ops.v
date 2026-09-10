From Stdlib Require Import ZArith Reals.
From Stdlib Require Import Floats PrimInt63.
From Flocq Require Import Zaux Raux BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Generic_proof Primitive_ops.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn dwbound.

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
(* A pair that is not a double word denotes nothing at all: it is read as     *)
(* Xnan, which Interval takes as the whole line.  So a bad pair is never      *)
(* unsound, only useless, and no operation has to promise a good one.         *)
Definition toF (x : type) : Basic.float radix2 :=
  let: DWFloat xh xl := x in
  if wellFormed x
  then Generic.Fadd_exact (PrimitiveFloat.toF xh) (PrimitiveFloat.toF xl)
  else Basic.Fnan.

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

(* A double word is a real number when both its words are and the pair is     *)
(* one, an infinity when either word is, and not a number otherwise.  A pair  *)
(* that is not a double word lands in the same class as a NaN, which leaves   *)
(* it a valid bound, just one that says nothing.                              *)
Definition classify x :=
  let: DWFloat xh xl := x in
  match PrimFloat.classify xh with
  | PInf => Fpinfty
  | NInf => Fminfty
  | NaN => Sig.Fnan
  | _ =>
    match PrimFloat.classify xl with
    | PInf => Fpinfty
    | NInf => Fminfty
    | NaN => Sig.Fnan
    | _ => if wellFormed x then Freal else Sig.Fnan
    end
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
(* the high ones agree.  Anything that is not a real number compares to       *)
(* nothing.                                                                   *)
Definition cmp x y :=
  match classify x, classify y with
  | Sig.Fnan, _ | _, Sig.Fnan => Xund
  | Fminfty, Fminfty => Xeq
  | Fminfty, _ => Xlt
  | _, Fminfty => Xgt
  | Fpinfty, Fpinfty => Xeq
  | _, Fpinfty => Xlt
  | Fpinfty, _ => Xgt
  | Freal, Freal =>
    match PrimitiveFloat.cmp (dwhi x) (dwhi y) with
    | Xeq => PrimitiveFloat.cmp (dwlo x) (dwlo y)
    | c => c
    end
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

(* An argument that denotes nothing must give a result that denotes nothing,  *)
(* or the operation would be claiming to know more than it was told.  And a   *)
(* result that is not a number is checked for as well: an operation that ran  *)
(* off the top of the range has no claim to make either, and what it returns  *)
(* has to be a bound on both sides.  Not a number is such a bound - it is     *)
(* the whole line - so falling back on it is always allowed, and it is the    *)
(* one answer that needs nothing proved about the numbers.                    *)
Definition guard (r : type) := if real r then r else nan.

Definition onReal (f : type -> type) x := if real x then guard (f x) else nan.
Definition onReal2 (f : type -> type -> type) x y :=
  if real x && real y then guard (f x y) else nan.

(* Whatever the operation did, what comes back is a bound on either side.     *)
Lemma classify_guard r :
  classify (guard r) = Freal \/ classify (guard r) = Sig.Fnan.
Proof.
rewrite /guard; case E: (real r); last by right.
by left; move: E; rewrite /real; case: (classify r).
Qed.

Lemma valid_ub_onReal2 f x y : valid_ub (onReal2 f x y) = true.
Proof.
rewrite /onReal2; case: (andb (real x) (real y)) => //.
by rewrite /valid_ub; case: (classify_guard (f x y)) => ->.
Qed.

Lemma valid_lb_onReal2 f x y : valid_lb (onReal2 f x y) = true.
Proof.
rewrite /onReal2; case: (andb (real x) (real y)) => //.
by rewrite /valid_lb; case: (classify_guard (f x y)) => ->.
Qed.

Lemma valid_ub_onReal f x : valid_ub (onReal f x) = true.
Proof.
rewrite /onReal; case: (real x) => //.
by rewrite /valid_ub; case: (classify_guard (f x)) => ->.
Qed.

Lemma valid_lb_onReal f x : valid_lb (onReal f x) = true.
Proof.
rewrite /onReal; case: (real x) => //.
by rewrite /valid_lb; case: (classify_guard (f x)) => ->.
Qed.

(* Not a number reads as the whole line, so it is above and below             *)
(* everything: an operation that gave up says nothing, and nothing is         *)
(* always true.                                                               *)
Lemma classify_nan : classify nan = Sig.Fnan.
Proof. by []. Qed.

Lemma toX_nan : toX nan = Xnan.
Proof. by []. Qed.

Definition add_UP (_ : precision) x y := onReal2 addDwUp x y.
Definition add_DN (_ : precision) x y := onReal2 addDwDn x y.
Definition sub_UP (_ : precision) x y := onReal2 subDwUp x y.
Definition sub_DN (_ : precision) x y := onReal2 subDwDn x y.
Definition mul_UP (_ : precision) x y := onReal2 mulDwUp x y.
Definition mul_DN (_ : precision) x y := onReal2 mulDwDn x y.
Definition div_UP (_ : precision) x y := onReal2 divDwUp x y.
Definition div_DN (_ : precision) x y := onReal2 divDwDn x y.
Definition sqrt_UP (_ : precision) x := onReal sqrtDwUp x.
Definition sqrt_DN (_ : precision) x := onReal sqrtDwDn x.

(* Rounding to an integer is monotone, so rounding a bound of the value       *)
(* gives a bound of the rounded value.  Only ordinarily tight.                *)
Definition nearbyint_UP (mode : rounding_mode) x :=
  onReal (fun x => fp2dw (PrimitiveFloat.nearbyint_UP mode
                            (addUpFp (dwhi x) (dwlo x)))) x.
Definition nearbyint_DN (mode : rounding_mode) x :=
  onReal (fun x => fp2dw (PrimitiveFloat.nearbyint_DN mode
                            (addDnFp (dwhi x) (dwlo x)))) x.

(* The midpoint is the plain half sum: rounding to nearest keeps it between   *)
(* the two, which is all that is asked of it.                                 *)
Definition midpoint x y := div2 (plusDwDw x y).

(* ---------------------------------------------------------------------------*)
(*  What the signature asks of a two-argument operation                       *)
(* ---------------------------------------------------------------------------*)

(* Half of every obligation needs no arithmetic at all: whatever the          *)
(* operation did, the guard leaves either a real number or nothing, and       *)
(* neither is an infinity of the wrong sign.  That is valid_ub_onReal2        *)
(* and valid_lb_onReal2 above.  The other half comes down to a single         *)
(* inequality, about an operation given two double words that returned        *)
(* one.  The value it is compared to is left open, so the sum and the         *)
(* difference use the same two lemmas.  Where the operation gave up, the      *)
(* answer is the whole line and there is nothing to prove.                    *)
Lemma onReal2_upper (v : type -> type -> ExtendedR) f x y :
  (forall x y, real x = true -> real y = true -> real (f x y) = true ->
     le_upper (v x y) (toX (f x y))) ->
  le_upper (v x y) (toX (onReal2 f x y)).
Proof.
move=> H; rewrite /onReal2.
case Ex: (real x); last by rewrite toX_nan.
case Ey: (real y); last by rewrite toX_nan.
rewrite /guard; case Er: (real (f x y)); last by rewrite toX_nan.
by apply: H.
Qed.

Lemma onReal2_lower (v : type -> type -> ExtendedR) f x y :
  (forall x y, real x = true -> real y = true -> real (f x y) = true ->
     le_lower (toX (f x y)) (v x y)) ->
  le_lower (toX (onReal2 f x y)) (v x y).
Proof.
move=> H; rewrite /onReal2.
case Ex: (real x); last by rewrite toX_nan.
case Ey: (real y); last by rewrite toX_nan.
rewrite /guard; case Er: (real (f x y)); last by rewrite toX_nan.
by apply: H.
Qed.

(* A float is finite exactly when it reads as a real number.                  *)
Definition Dfinb f := PrimitiveFloat.real f.

Lemma DfinbW f : Dfinb f = true -> Dfin f.
Proof.
by rewrite /Dfinb -{1}(B2Prim_Prim2B f) PrimitiveFloat.real_is_finite.
Qed.

(* A double word is a real number exactly when both its words are numbers     *)
(* and the pair is one, and then it denotes their sum.  These two are all     *)
(* that is needed to read the bounds proved on the program in the shape the   *)
(* signature asks for.                                                        *)
Lemma realE x :
  real x = (Dfinb (dwhi x) && Dfinb (dwlo x) && wellFormed x)%bool.
Proof.
case: x => xh xl; rewrite /real /classify /Dfinb.
rewrite PrimitiveFloat.classify_correct (PrimitiveFloat.classify_correct xl).
by rewrite /PrimitiveFloat.classify /wellFormed;
   case: (PrimFloat.classify xh); case: (PrimFloat.classify xl);
   case: (xh + xl =? xh)%float.
Qed.

Lemma real_fin x :
  real x = true -> Dfin (dwhi x) /\ Dfin (dwlo x) /\ wellFormed x = true.
Proof.
rewrite realE.
case Eh: (Dfinb (dwhi x)) => //=; case El: (Dfinb (dwlo x)) => //= Ew.
by split; [apply: DfinbW|split; [apply: DfinbW|]].
Qed.

Lemma toXE f : Dfin f -> FtoX (PrimitiveFloat.toF f) = Xreal (D2R f).
Proof.
move=> Ff; rewrite -/(PrimitiveFloat.toX f) PrimitiveFloat.toX_Prim2B.
by rewrite PrimitiveFloat.B2R_BtoX.
Qed.

Lemma toX_real x :
  real x = true -> toX x = Xreal (D2R (dwhi x) + D2R (dwlo x)).
Proof.
case: x => xh xl Rx; have [Fh [Fl Ew]] := real_fin _ Rx.
by rewrite /toX /toF Ew Fadd_exact_correct (toXE xh Fh) (toXE xl Fl).
Qed.

(* The obligation itself.  Both arguments are double words, the tests came    *)
(* back true, and what the program returned is at or above the exact sum.     *)
Lemma add_UP_correct p x y :
  valid_ub x = true -> valid_ub y = true ->
  valid_ub (add_UP p x y) = true /\
  le_upper (toX x + toX y)%XR (toX (add_UP p x y)).
Proof.
move=> _ _; split; first exact: valid_ub_onReal2.
apply: (onReal2_upper (fun x y => (toX x + toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [Fxh [Fxl _]] := real_fin _ Rx.
have [Fyh [Fyl _]] := real_fin _ Ry.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /=.
by apply: addDwUp_geP.
Qed.

Lemma add_DN_correct p x y :
  valid_lb x = true -> valid_lb y = true ->
  valid_lb (add_DN p x y) = true /\
  le_lower (toX (add_DN p x y)) (toX x + toX y)%XR.
Proof.
move=> _ _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x + toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [Fxh [Fxl _]] := real_fin _ Rx.
have [Fyh [Fyl _]] := real_fin _ Ry.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; apply: addDwDn_leP.
Qed.

(* And the difference, which is the sum with the second double word           *)
(* negated.  Only the values of its two words are used, so nothing has to     *)
(* be said about the negated pair itself.                                     *)
Lemma sub_UP_correct p x y :
  valid_ub x = true -> valid_lb y = true ->
  valid_ub (sub_UP p x y) = true /\
  le_upper (toX x - toX y)%XR (toX (sub_UP p x y)).
Proof.
move=> _ _; split; first exact: valid_ub_onReal2.
apply: (onReal2_upper (fun x y => (toX x - toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [Fxh [Fxl _]] := real_fin _ Rx.
have [Fyh [Fyl _]] := real_fin _ Ry.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /=.
by apply: subDwUp_geP.
Qed.

Lemma sub_DN_correct p x y :
  valid_lb x = true -> valid_ub y = true ->
  valid_lb (sub_DN p x y) = true /\
  le_lower (toX (sub_DN p x y)) (toX x - toX y)%XR.
Proof.
move=> _ _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x - toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [Fxh [Fxl _]] := real_fin _ Rx.
have [Fyh [Fyl _]] := real_fin _ Ry.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; apply: subDwDn_leP.
Qed.

End DwFloat.
