From Stdlib Require Import ZArith Reals Psatz.
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

(* The magnitude: the larger of the two words, one binary step up.  The       *)
(* high word alone would nearly do, but a low word of the same sign can       *)
(* push the pair past its exponent, and one step covers that with nothing     *)
(* to prove about how the two words sit.                                      *)
Definition mag x :=
  (Z.max (PrimitiveFloat.mag (dwhi x)) (PrimitiveFloat.mag (dwlo x)) + 1)%Z.

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

(* The same for an operation of one argument.                                 *)
Lemma onReal_upper (v : type -> ExtendedR) f x :
  (forall x, real x = true -> real (f x) = true ->
     le_upper (v x) (toX (f x))) ->
  le_upper (v x) (toX (onReal f x)).
Proof.
move=> H; rewrite /onReal.
case Ex: (real x); last by rewrite toX_nan.
rewrite /guard; case Er: (real (f x)); last by rewrite toX_nan.
by apply: H.
Qed.

Lemma onReal_lower (v : type -> ExtendedR) f x :
  (forall x, real x = true -> real (f x) = true ->
     le_lower (toX (f x)) (v x)) ->
  le_lower (toX (onReal f x)) (v x).
Proof.
move=> H; rewrite /onReal.
case Ex: (real x); last by rewrite toX_nan.
rewrite /guard; case Er: (real (f x)); last by rewrite toX_nan.
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
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /=.
exact: (addDwUp_geP _ _ Fzl).
Qed.

Lemma add_DN_correct p x y :
  valid_lb x = true -> valid_lb y = true ->
  valid_lb (add_DN p x y) = true /\
  le_lower (toX (add_DN p x y)) (toX x + toX y)%XR.
Proof.
move=> _ _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x + toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; exact: (addDwDn_leP _ _ Fzl).
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
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /=.
exact: (subDwUp_geP _ _ Fzl).
Qed.

Lemma sub_DN_correct p x y :
  valid_lb x = true -> valid_ub y = true ->
  valid_lb (sub_DN p x y) = true /\
  le_lower (toX (sub_DN p x y)) (toX x - toX y)%XR.
Proof.
move=> _ _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x - toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; exact: (subDwDn_leP _ _ Fzl).
Qed.

(* The signature states its product bounds under four sign conditions, so     *)
(* they are written out here.  The proof does not use them: the bound         *)
(* holds whatever the signs are, because it never looks at an infinity.       *)
Definition is_non_neg' x :=
  match toX x with Xnan => valid_ub x = true | Xreal r => (0 <= r)%R end.
Definition is_non_pos' x :=
  match toX x with Xnan => valid_lb x = true | Xreal r => (r <= 0)%R end.
Definition is_non_neg_real x :=
  match toX x with Xnan => False | Xreal r => (0 <= r)%R end.
Definition is_non_pos_real x :=
  match toX x with Xnan => False | Xreal r => (r <= 0)%R end.

(* And the product.  The two high words are multiplied by Dekker's way,       *)
(* which gives two numbers that all but add up to their product; the three    *)
(* remaining products are rounded the way the bound needs; and the whole      *)
(* is folded back into a pair.                                                *)
Lemma mul_UP_correct p x y :
  is_non_neg' x /\ is_non_neg' y \/ is_non_pos' x /\ is_non_pos' y \/
  is_non_pos_real x /\ is_non_neg_real y \/
  is_non_neg_real x /\ is_non_pos_real y ->
  valid_ub (mul_UP p x y) = true /\
  le_upper (toX x * toX y)%XR (toX (mul_UP p x y)).
Proof.
move=> _; split; first exact: valid_ub_onReal2.
apply: (onReal2_upper (fun x y => (toX x * toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /=.
exact: (mulDwUp_geP _ _ Fzl).
Qed.

Lemma mul_DN_correct p x y :
  is_non_neg_real x /\ is_non_neg_real y \/
  is_non_pos_real x /\ is_non_pos_real y \/
  is_non_neg' x /\ is_non_pos' y \/ is_non_pos' x /\ is_non_neg' y ->
  valid_lb (mul_DN p x y) = true /\
  le_lower (toX (mul_DN p x y)) (toX x * toX y)%XR.
Proof.
move=> _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x * toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; exact: (mulDwDn_leP _ _ Fzl).
Qed.

(* The signature states its quotient bounds under two sign conditions, so     *)
(* these are written out too.  They are not used either: the operation        *)
(* only answers when it has bounded the divisor away from zero itself.        *)
Definition is_real_ub x :=
  match toX x with Xnan => valid_ub x = true | Xreal _ => True end.
Definition is_real_lb x :=
  match toX x with Xnan => valid_lb x = true | Xreal _ => True end.
Definition is_pos_real x :=
  match toX x with Xnan => False | Xreal r => (0 < r)%R end.
Definition is_neg_real x :=
  match toX x with Xnan => False | Xreal r => (r < 0)%R end.

(* A quotient of two real numbers is a real number when the second is not     *)
(* zero; otherwise it is the whole line, which is not what is claimed.        *)
Lemma XdivE a b : b <> 0%R -> (Xreal a / Xreal b)%XR = Xreal (a / b).
Proof. by move=> Hb; rewrite /Xbind2 /Xdiv' (is_zero_false _ Hb). Qed.

(* And the quotient.  Whatever the algorithm made of the two double           *)
(* words, the answer is bounded by its own residual, so nothing has to be     *)
(* known about how it was arrived at.                                         *)
Lemma div_UP_correct p x y :
  is_real_ub x /\ is_pos_real y \/ is_real_lb x /\ is_neg_real y ->
  valid_ub (div_UP p x y) = true /\
  le_upper (toX x / toX y)%XR (toX (div_UP p x y)).
Proof.
move=> _; split; first exact: valid_ub_onReal2.
apply: (onReal2_upper (fun x y => (toX x / toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [_ [Fzl _]] := real_fin _ Rz.
have Hnz := divDwUp_nz _ _ Fzl.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) (XdivE _ _ Hnz) /=.
exact: (divDwUp_geP _ _ Fzl).
Qed.

Lemma div_DN_correct p x y :
  is_real_ub x /\ is_neg_real y \/ is_real_lb x /\ is_pos_real y ->
  valid_lb (div_DN p x y) = true /\
  le_lower (toX (div_DN p x y)) (toX x / toX y)%XR.
Proof.
move=> _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x / toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [_ [Fzl _]] := real_fin _ Rz.
have Hnz := divDwDn_nz _ _ Fzl.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz) (XdivE _ _ Hnz).
rewrite /le_lower /=.
by apply: Ropp_le_contravar; exact: (divDwDn_leP _ _ Fzl).
Qed.

(* And the square root.  Interval reads the root of a negative number as      *)
(* nought, so a bound below it would be a claim about nothing; that is why    *)
(* the operation tests the sign of what it is given as well as the sign of    *)
(* the divisor it needs.                                                      *)
Lemma sqrt_UP_correct p x :
  valid_ub (sqrt_UP p x) = true /\
  le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof.
split; first exact: valid_ub_onReal.
apply: (onReal_upper (fun x => Xsqrt (toX x))) => {p}{}x Rx Rz.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Rz) /=.
exact: (sqrtDwUp_geP _ Fzl).
Qed.

Lemma sqrt_DN_correct p x :
  valid_lb x = true ->
  valid_lb (sqrt_DN p x) = true /\
  le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x)).
Proof.
move=> _; split; first exact: valid_lb_onReal.
apply: (onReal_lower (fun x => Xsqrt (toX x))) => {p}{}x Rx Rz.
have [_ [Fzl _]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; exact: (sqrtDwDn_leP _ Fzl).
Qed.

(* ---------------------------------------------------------------------------*)
(*  What the signature asks of the rest                                       *)
(* ---------------------------------------------------------------------------*)

(* A pair with nothing in the low word denotes just its high word, and is     *)
(* a bound on the same side.  That carries over everything the interface      *)
(* borrows from the primitive floats.                                         *)
Lemma toX_fp2dw f : toX (fp2dw f) = PrimitiveFloat.toX f.
Proof.
have Hz : (f + 0 =? f)%float = false -> PrimitiveFloat.toX f = Xnan.
  rewrite eqb_equiv add_equiv /PrimitiveFloat.toX /PrimitiveFloat.toF.
  rewrite -B2SF_Prim2B.
  have -> : Prim2B 0%float = B754_zero false by [].
  case: (Prim2B f) => [s1|s1||s1 m1 e1 H1] //=; last first.
    by rewrite (Beqb_refl _ _ (B754_finite s1 m1 e1 H1)).
  by case: s1.
rewrite /toX /toF /fp2dw /wellFormed.
case E: (f + 0 =? f)%float; last by rewrite (Hz E).
by rewrite Fadd_exact_correct /= Xadd_0_r.
Qed.

(* A float that is not an infinity is not classified as one.  The last        *)
(* case below asks whether the mantissa is of full length, which is how a     *)
(* normal number is told from a subnormal one; neither is an infinity.        *)
Lemma Dninf f : (f =? neg_infinity)%float = false ->
  match PrimFloat.classify f with NInf => false | _ => true end = true.
Proof.
rewrite eqb_equiv classify_spec -B2SF_Prim2B.
have -> : Prim2B neg_infinity = B754_infinity true by [].
by case: (Prim2B f) => [[]|[]||[] m1 e1 H1] //=;
   case: (match digits2_pos m1 with 53%positive => true | _ => false end).
Qed.

Lemma Dpinf f : (f =? infinity)%float = false ->
  match PrimFloat.classify f with PInf => false | _ => true end = true.
Proof.
rewrite eqb_equiv classify_spec -B2SF_Prim2B.
have -> : Prim2B infinity = B754_infinity false by [].
by case: (Prim2B f) => [[]|[]||[] m1 e1 H1] //=;
   case: (match digits2_pos m1 with 53%positive => true | _ => false end).
Qed.

Lemma valid_ub_fp2dw f :
  PrimitiveFloat.valid_ub f = true -> valid_ub (fp2dw f) = true.
Proof.
rewrite /PrimitiveFloat.valid_ub /valid_ub /classify.
case E: (f =? neg_infinity)%float => //= _.
by move: (Dninf _ E); case: (PrimFloat.classify f) => //=;
   case: (f + 0 =? f)%float.
Qed.

Lemma valid_lb_fp2dw f :
  PrimitiveFloat.valid_lb f = true -> valid_lb (fp2dw f) = true.
Proof.
rewrite /PrimitiveFloat.valid_lb /valid_lb /classify.
case E: (f =? infinity)%float => //= _.
by move: (Dpinf _ E); case: (PrimFloat.classify f) => //=;
   case: (f + 0 =? f)%float.
Qed.

(* The obligations that are true by the way the definitions were written.     *)
Lemma classify_correct f :
  real f = match classify f with Freal => true | _ => false end.
Proof. by []. Qed.

Lemma is_nan_correct f :
  is_nan f = match classify f with Sig.Fnan => true | _ => false end.
Proof. by []. Qed.

Lemma valid_lb_correct f :
  valid_lb f = match classify f with Fpinfty => false | _ => true end.
Proof. by []. Qed.

Lemma valid_ub_correct f :
  valid_ub f = match classify f with Fminfty => false | _ => true end.
Proof. by []. Qed.

Lemma nan_correct : classify nan = Sig.Fnan.
Proof. by []. Qed.

Lemma zero_correct : toX zero = Xreal 0.
Proof. by []. Qed.

(* A pair denotes a real number exactly when it reads as one.  The other      *)
(* way round is the reading itself; this way round, a pair that is not a      *)
(* double word, or has a word that is not a number, denotes nothing.          *)
Lemma real_correct f :
  real f = match toX f with Xnan => false | Xreal _ => true end.
Proof.
case E: (real f); first by rewrite (toX_real _ E).
have Hn : forall g, Dfinb g = false -> PrimitiveFloat.toX g = Xnan.
  move=> g; rewrite /Dfinb PrimitiveFloat.real_correct.
  by case: (PrimitiveFloat.toX g).
move: E; rewrite realE; case: f => xh xl /=.
case Eh: (Dfinb xh) => /=; last first.
  by rewrite /toX /toF /wellFormed; case: (xh + xl =? xh)%float => //;
     rewrite Fadd_exact_correct -/(PrimitiveFloat.toX xh) (Hn _ Eh).
case El: (Dfinb xl) => /=; last first.
  by rewrite /toX /toF /wellFormed; case: (xh + xl =? xh)%float => //;
     rewrite Fadd_exact_correct -/(PrimitiveFloat.toX xl) (Hn _ El) Xadd_comm.
by move=> Ew; rewrite /toX /toF /wellFormed Ew.
Qed.

(* Whole numbers, powers of two, and the scale factor: each is the            *)
(* primitive float's own answer, put in the high word.                        *)
Lemma fromZ_correct n : (Z.abs n <= 256)%Z -> toX (fromZ n) = Xreal (IZR n).
Proof. by move=> Hn; rewrite /fromZ toX_fp2dw PrimitiveFloat.fromZ_correct. Qed.

Lemma fromZ_UP_correct p n :
  valid_ub (fromZ_UP p n) = true /\
  le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
Proof.
rewrite /fromZ_UP toX_fp2dw.
have [Hv Hb] := PrimitiveFloat.fromZ_UP_correct fprec n.
by split => //; apply: valid_ub_fp2dw.
Qed.

Lemma fromZ_DN_correct p n :
  valid_lb (fromZ_DN p n) = true /\
  le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
Proof.
rewrite /fromZ_DN toX_fp2dw.
have [Hv Hb] := PrimitiveFloat.fromZ_DN_correct fprec n.
by split => //; apply: valid_lb_fp2dw.
Qed.

Lemma pow2_UP_correct p s :
  valid_ub (pow2_UP p s) = true /\
  le_upper (Xscale radix2 (Xreal 1) (StoZ s)) (toX (pow2_UP p s)).
Proof.
rewrite /pow2_UP toX_fp2dw.
have [Hv Hb] := PrimitiveFloat.pow2_UP_correct fprec s.
by split => //; apply: valid_ub_fp2dw.
Qed.

Lemma ZtoS_correct p z :
  (z <= StoZ (ZtoS z))%Z \/ toX (pow2_UP p (ZtoS z)) = Xnan.
Proof. by left; apply: Z.le_refl. Qed.

(* Negating a float turns each class into its mirror, and leaves a number     *)
(* that is not an infinity one.  The last case asks whether the mantissa      *)
(* is of full length, which is how a normal number is told from a             *)
(* subnormal one.                                                             *)
Lemma Dclassify_opp f :
  PrimFloat.classify (- f)%float =
  match PrimFloat.classify f with
  | PInf => NInf | NInf => PInf
  | PNormal => NNormal | NNormal => PNormal
  | PSubn => NSubn | NSubn => PSubn
  | PZero => NZero | NZero => PZero
  | NaN => NaN
  end.
Proof.
rewrite !classify_spec -!B2SF_Prim2B opp_equiv.
by case: (Prim2B f) => [[]|[]||[] m1 e1 H1] //=;
   case: (match digits2_pos m1 with 53%positive => true | _ => false end).
Qed.

(* Negating a double word negates what it denotes, and turns an infinity      *)
(* into the other one.                                                        *)
(* Negating twice is doing nothing, so being a double word survives a         *)
(* change of sign both ways round.                                            *)
Lemma Dopp_opp f : (- - f)%float = f.
Proof.
have H : Prim2B (- - f)%float = Prim2B f by rewrite !opp_equiv Bopp_involutive.
by rewrite -(B2Prim_Prim2B (- - f)%float) H B2Prim_Prim2B.
Qed.

Lemma wellFormed_negE xh xl : Dfin xh -> Dfin xl ->
  wellFormed (DWFloat (- xh) (- xl))%float = wellFormed (DWFloat xh xl).
Proof.
move=> Fh Fl; case E: (wellFormed (DWFloat xh xl)).
  exact: wellFormed_neg.
case E2: (wellFormed (DWFloat (- xh) (- xl))%float) => //.
have := wellFormed_neg _ _ (Dfin_opp _ Fh) (Dfin_opp _ Fl) E2.
by rewrite !Dopp_opp E.
Qed.

(* So a negated pair falls in the mirror class.                               *)
Lemma classify_neg x :
  classify (neg x) =
  match classify x with
  | Freal => Freal | Sig.Fnan => Sig.Fnan
  | Fminfty => Fpinfty | Fpinfty => Fminfty
  end.
Proof.
case: x => xh xl; rewrite /neg /negDw /classify !Dclassify_opp.
have Hw : Dfin xh -> Dfin xl ->
   ((- xh) + (- xl) =? (- xh))%float = (xh + xl =? xh)%float
  by move=> *; apply: wellFormed_negE.
have Hf : forall g,
   match PrimFloat.classify g with
   | PInf | NInf | NaN => True | _ => Dfin g end.
  move=> g; case Ec: (PrimFloat.classify g) => //;
  by apply: DfinbW; rewrite /Dfinb PrimitiveFloat.classify_correct
                            /PrimitiveFloat.classify Ec.
by case Eh: (PrimFloat.classify xh) => //=;
   case El: (PrimFloat.classify xl) => //=;
   (rewrite Hw; [by case: (xh + xl =? xh)%float
                | by have := Hf xh; rewrite Eh
                | by have := Hf xl; rewrite El]).
Qed.

(* Negating a double word negates what it denotes.                            *)
Lemma neg_correct x :
  match classify x with
  | Freal => toX (neg x) = (- toX x)%XR
  | Sig.Fnan => classify (neg x) = Sig.Fnan
  | Fminfty => classify (neg x) = Fpinfty
  | Fpinfty => classify (neg x) = Fminfty
  end.
Proof.
case E: (classify x); rewrite ?classify_neg ?E //.
have Rx : real x = true by rewrite /real E.
have [Fh [Fl Ew]] := real_fin _ Rx.
move: Fh Fl Ew; case: x Rx E => xh xl Rx E Fh Fl Ew.
rewrite (toX_real _ Rx) /toX /toF /neg /negDw.
rewrite (wellFormed_neg _ _ Fh Fl Ew).
rewrite Fadd_exact_correct (toXE _ (Dfin_opp _ Fh)) (toXE _ (Dfin_opp _ Fl)).
by rewrite /= !D2R_opp; congr Xreal; ring.
Qed.

(* The magnitude bounds the pair: each word is below its own power of         *)
(* two, so their sum is below the larger of the two, doubled.                 *)
Lemma mag_correct f : (Rabs (toR f) < bpow radix (StoZ (mag f)))%R.
Proof.
have Hh := PrimitiveFloat.mag_correct (dwhi f).
have Hl := PrimitiveFloat.mag_correct (dwlo f).
have Hb : forall a b : Z, (a <= Z.max a b)%Z /\ (b <= Z.max a b)%Z.
  by move=> a b; split; [apply: Z.le_max_l | apply: Z.le_max_r].
have [Ha Hbb] := Hb (PrimitiveFloat.mag (dwhi f)) (PrimitiveFloat.mag (dwlo f)).
have Mh := bpow_le radix2 _ _ Ha; have Ml := bpow_le radix2 _ _ Hbb.
have E1 : bpow radix2
   ((Z.max (PrimitiveFloat.mag (dwhi f)) (PrimitiveFloat.mag (dwlo f)) + 1)%Z)
   = (2 * bpow radix2
   (Z.max (PrimitiveFloat.mag (dwhi f)) (PrimitiveFloat.mag (dwlo f))))%R.
  by rewrite bpow_plus_1.
rewrite /mag /StoZ /radix E1.
case Ex: (real f); last first.
  have -> : toR f = 0%R.
    by move: Ex; rewrite real_correct /toR; case: (toX f).
  rewrite Rabs_R0.
  by have := bpow_gt_0 radix2
     (Z.max (PrimitiveFloat.mag (dwhi f)) (PrimitiveFloat.mag (dwlo f))); lra.
have [Fh [Fl _]] := real_fin _ Ex.
have -> : toR f = (D2R (dwhi f) + D2R (dwlo f))%R.
  by rewrite /toR (toX_real _ Ex).
move: Hh Hl; rewrite /PrimitiveFloat.toR !PrimitiveFloat.toX_Prim2B.
rewrite !PrimitiveFloat.B2R_BtoX // /PrimitiveFloat.StoZ.
rewrite -/(D2R (dwhi f)) -/(D2R (dwlo f)).
by move=> /= Hh Hl; move: (Rabs_triang (D2R (dwhi f)) (D2R (dwlo f))); lra.
Qed.

End DwFloat.
