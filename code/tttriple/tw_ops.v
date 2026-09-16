From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats PrimInt63.
From Flocq Require Import Zaux Raux Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Generic_proof Primitive_ops.
From mathcomp Require Import ssreflect ssrbool.
From twarith Require Import twarith tw_updn twpaper.
(* The bridge from primitive floats to the reals is the double-word    *)
(* development's `dwbridge.v'.  It says nothing about pairs -- only     *)
(* what one primitive float is and what one operation on it does -- so  *)
(* it serves three words as well as two, and is used rather than        *)
(* copied.                                                             *)
From dwarith Require Import dwbridge.

(* Triple words as a float format for Interval.                               *)
(*                                                                            *)
(* Rocq already gives primitive floats an interface - the operations and the  *)
(* theorems that say what they compute.  This is an interface of the same     *)
(* kind for triple words, so that a proof can be carried out over them        *)
(* instead.  Interval's `FloatOps` signature was chosen for one reason: its   *)
(* obligations are inequalities, `le_upper` and `le_lower`.  That matters,    *)
(* because a triple word is not a floating-point format - its operations are  *)
(* not correctly rounded to a hundred and fifty-nine bits, and no equation    *)
(* of that kind is promised.  Every statement here is a bound.                *)
(*                                                                            *)
(* THE SHAPE IS CHECKED, THE ARITHMETIC IS NOT YET.  The module below meets   *)
(* the signature - the sealing at the bottom of the file is what says so -    *)
(* but the obligations that need a fact about the arithmetic are `Admitted`,  *)
(* each marked where it stands.  Those that need nothing of the kind are      *)
(* proved.  Nothing in this file may be relied on until the list below is     *)
(* empty.  It is here so that the whole chain, up to Interval's own tactic    *)
(* over triple words, can be assembled and measured before it is proved -     *)
(* which is the order the double-word work went in as well.                   *)
(*                                                                            *)
(* Admitted, and each of them is a real statement about the arithmetic:       *)
(*   add/sub/mul/div/sqrt _UP_correct and _DN_correct  (ten)                  *)
(*   fromZ_correct, fromZ_UP_correct, fromZ_DN_correct                        *)
(*   pow2_UP_correct, ZtoS_correct                                            *)
(*   zero_correct, real_correct, mag_correct                                  *)
(*   neg_correct, abs_correct, cmp_correct, min_correct, max_correct          *)
(*   nearbyint_UP_correct, nearbyint_DN_correct                               *)
(*   div2_correct, midpoint_correct   (excused by `sensible_format = false`)  *)

Module TwFloat.

Definition radix := radix2.

(* A triple of floats cannot always halve what it denotes, for the same       *)
(* reason a pair cannot: every binary64 number is a whole multiple of two to  *)
(* the minus one thousand and seventy-four, so a sum of three of them is one  *)
(* as well, and the half of such a sum need not be.  So no definition of      *)
(* div2 can meet the equation the signature asks for, and the format          *)
(* declares itself not sensible, which is the escape the signature provides   *)
(* for div2 and midpoint.                                                     *)
Definition sensible_format := false.
Definition type := twfloat.

(* A triple word denotes the sum of its three words, and that sum is exact.   *)
(* A triple that is not a triple word denotes nothing at all: it is read as   *)
(* Xnan, which Interval takes as the whole line.  So a bad triple is never   *)
(* unsound, only useless, and no operation has to promise a good one.         *)
Definition toF (x : type) : Basic.float radix2 :=
  let: TWFloat x0 x1 x2 := x in
  if wellFormed x
  then Generic.Fadd_exact
         (Generic.Fadd_exact (PrimitiveFloat.toF x0) (PrimitiveFloat.toF x1))
         (PrimitiveFloat.toF x2)
  else Basic.Fnan.

Definition toX x := FtoX (toF x).
Definition toR x := proj_val (toX x).
Definition convert x := FtoX (toF x).

(* The precision is fixed: three binary64 words give what they give, and      *)
(* there is no way to ask for more.  Interval may ask; the answer does not    *)
(* change.                                                                    *)
Definition precision := unit.
Definition sfactor := Z.
Definition prec (_ : precision) := 159%positive.
Definition PtoP (_ : positive) : precision := tt.
Definition ZtoS (x : Z) := x.
Definition StoZ (x : Z) := x.
Definition incr_prec (p : precision) (_ : positive) := p.

(* The precision the underlying binary64 operations are asked for.            *)
Definition fprec := PrimitiveFloat.PtoP 53.

Definition zero := TWFloat PrimFloat.zero PrimFloat.zero PrimFloat.zero.
Definition nan := TWFloat PrimFloat.nan PrimFloat.zero PrimFloat.zero.

Definition fromZ (n : Z) := fp2tw (PrimitiveFloat.fromZ n).
Definition fromF (f : Basic.float radix) := fp2tw (PrimitiveFloat.fromF f).

(* A triple word is a real number when all three of its words are and the     *)
(* triple is one, an infinity when any word is, and not a number otherwise.   *)
(* A triple that is not a triple word lands in the same class as a NaN,       *)
(* which leaves it a valid bound, just one that says nothing.                 *)
Definition classifyFp f :=
  match PrimFloat.classify f with
  | PInf => Some Fpinfty
  | NInf => Some Fminfty
  | NaN => Some Sig.Fnan
  | _ => None
  end.

Definition classify x :=
  let: TWFloat x0 x1 x2 := x in
  match classifyFp x0 with
  | Some c => c
  | None =>
    match classifyFp x1 with
    | Some c => c
    | None =>
      match classifyFp x2 with
      | Some c => c
      | None => if wellFormed x then Freal else Sig.Fnan
      end
    end
  end.

Definition real x := match classify x with Freal => true | _ => false end.
Definition is_nan x := match classify x with Sig.Fnan => true | _ => false end.

(* The magnitude: the largest of the three words, two binary steps up.  The   *)
(* leading word alone would nearly do, but the other two can push the triple  *)
(* past its exponent; the value is below three times the largest word, and    *)
(* two steps cover that with nothing to prove about how the words sit.        *)
(* The magnitude, and it has to be TIGHT.  Interval gets the size of a unit  *)
(* in the last place from this, and a goal whose whole content is a bound of  *)
(* half such a unit fails if it is one bit out - Interval's own 120-bit goal  *)
(* is exactly that goal.  So it is not the leading word's magnitude with a    *)
(* step for safety, which is always one too big; it is the magnitude of the   *)
(* VALUE, got by adding the three words once upwards and once downwards and   *)
(* taking whichever of the two is larger in absolute value.                   *)
(* The three words are added in absolute value, rounded upwards, which is at  *)
(* or above the value whatever the signs are.  One directed sum, and nothing  *)
(* to choose between.                                                         *)
(*                                                                            *)
(* AND IT CAN LEAVE THE RANGE.  A step up from the largest float there is     *)
(* gives an infinity, and `PrimitiveFloat.mag' of an infinity is the LEAST    *)
(* exponent, not the greatest - so reading it would claim the value is tiny   *)
(* when it is enormous, and a pair of the largest float and nought is a real  *)
(* triple word, so it is reachable.  Where the sum left the range the answer  *)
(* is one past the largest exponent, which every sum of three floats is       *)
(* below.                                                                      *)
Definition mag x :=
  let: TWFloat x0 x1 x2 := x in
  let m := addUpFp (addUpFp (PrimFloat.abs x0) (PrimFloat.abs x1))
                    (PrimFloat.abs x2) in
  if ((0 <? m) && (m <? infinity))%float then PrimitiveFloat.mag m else 1025%Z.

(* Only an infinity of the wrong sign is barred from being a bound.           *)
Definition valid_ub x := match classify x with Fminfty => false | _ => true end.
Definition valid_lb x := match classify x with Fpinfty => false | _ => true end.

(* Three words compare on the leading word, and on the next when the ones     *)
(* before agree.  Anything that is not a real number compares to nothing.     *)
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
    match PrimitiveFloat.cmp (tw0 x) (tw0 y) with
    | Xeq =>
      match PrimitiveFloat.cmp (tw1 x) (tw1 y) with
      | Xeq => PrimitiveFloat.cmp (tw2 x) (tw2 y)
      | c => c
      end
    | c => c
    end
  end.

(* The smaller and the larger of two triple words.  When they compare equal   *)
(* the second is returned, not the first: the signature asks for the triple   *)
(* itself in some of its cases, and two triples can denote the same number -  *)
(* or the same infinity - without being the same triple.                      *)
Definition min x y :=
  match cmp x y with Xlt => x | Xeq | Xgt => y | Xund => nan end.
Definition max x y :=
  match cmp x y with Xgt => x | Xeq | Xlt => y | Xund => nan end.

Definition neg x := negTw x.

(* Scaling by a power of two moves every word by the same amount and is       *)
(* exact, barring overflow.                                                    *)
Definition scale x (e : sfactor) :=
  let: TWFloat x0 x1 x2 := x in
  TWFloat (PrimitiveFloat.scale x0 e) (PrimitiveFloat.scale x1 e)
          (PrimitiveFloat.scale x2 e).

Definition div2 x := halfTw x.

Definition pow2_UP (_ : precision) (e : sfactor) :=
  fp2tw (PrimitiveFloat.pow2_UP fprec e).

(* An argument that denotes nothing must give a result that denotes nothing,  *)
(* or the operation would be claiming to know more than it was told.  And a   *)
(* result that is not a number is checked for as well: an operation that ran  *)
(* off the top of the range has no claim to make either, and what it returns  *)
(* has to be a bound on both sides.  Not a number is such a bound - it is     *)
(* the whole line - so falling back on it is always allowed, and it is the    *)
(* one answer that needs nothing proved about the numbers.                     *)
Definition guard (r : type) := if real r then r else nan.

Definition onReal (f : type -> type) x := if real x then guard (f x) else nan.
Definition onReal2 (f : type -> type -> type) x y :=
  if real x && real y then guard (f x y) else nan.

(* The words of a triple word have the sign of their sum, so the sign of the  *)
(* leading word decides.  A triple that is not a triple word is left out:     *)
(* its leading word says nothing about the others, so the sign test would be  *)
(* reading a number that is not there.                                        *)
Definition abs x :=
  onReal (fun x => if PrimFloat.get_sign (tw0 x) then negTw x else x) x.

Definition add_UP (_ : precision) x y := onReal2 addTwUp x y.
Definition add_DN (_ : precision) x y := onReal2 addTwDn x y.
Definition sub_UP (_ : precision) x y := onReal2 subTwUp x y.
Definition sub_DN (_ : precision) x y := onReal2 subTwDn x y.
Definition mul_UP (_ : precision) x y := onReal2 mulTwUp x y.
Definition mul_DN (_ : precision) x y := onReal2 mulTwDn x y.
(* The paper's Algorithm 14 for the quotient, bounded by a shift of eight    *)
(* units in the last place - see twpaper.v, where the eight is measured and   *)
(* not proved.  The root still uses the seed of twarith.v, since Algorithm 15 *)
(* is not transcribed yet, with the same shift.                               *)
Definition div_UP (_ : precision) x y := onReal2 divTwUpP x y.
Definition div_DN (_ : precision) x y := onReal2 divTwDnP x y.
Definition sqrt_UP (_ : precision) x := onReal sqrtTwUpP x.
Definition sqrt_DN (_ : precision) x := onReal sqrtTwDnP x.

(* A whole number as a triple word.  Putting it in the leading word alone     *)
(* would hold fifty-three bits of it and drop the rest, which is what every   *)
(* constant in a goal would then be worth.  So the number is peeled twice:    *)
(* its top fifty-three bits, the next fifty-three, and what is left.          *)
(*                                                                            *)
(* A peeling is done on the whole number, never on a float.  What comes off   *)
(* is a whole number below two to the fifty-third, which is a float exactly,  *)
(* times a power of two; and scaling a float by a power of two is exact as    *)
(* well.  So each of the two parts peeled is a float and the number it        *)
(* stands for is the part itself - nothing is estimated and no test is        *)
(* needed.  What is left over after the two peelings is bounded by a single   *)
(* float, which is the third word.                                            *)
(*                                                                            *)
(* A scaling that ran off the top of the range gives an infinity, and an      *)
(* infinity travels: the sum below then denotes nothing and the guard         *)
(* returns nothing, which is the whole line and always a bound.               *)
(*                                                                            *)
(* The three are added with the interface's own addition rather than written  *)
(* into the three words by hand.  A peeled part can be very nearly a whole    *)
(* step of the part above it, so writing them down side by side need not      *)
(* give a triple word at all, and the addition is what separates them.        *)
(*                                                                            *)
(* A number small enough for fewer words is peeled fewer times, and for a     *)
(* number one float holds the answer is that float, which is exact.           *)

(* Two to the fifty-third.  A whole number below it is a float exactly.       *)
Definition mmax := 9007199254740992%Z.

(* Scaling a float by a power of two.  The name is written out in full on     *)
(* purpose: Interval carries a scaling of its own that does nothing, for the  *)
(* versions of Rocq whose floats had none, and a bare `Z.ldexp` picks that    *)
(* one up and silently returns its argument.                                  *)
Definition ldexp2 (f : PrimFloat.float) (e : Z) := FloatOps.Z.ldexp f e.

(* The top part, as a multiplier and an exponent, and what is left over.      *)
Definition splitZ (n : Z) : Z * Z * Z :=
  let e := Z.max 0 (Z.log2 (Z.abs n) - 52) in
  let m := (Z.sgn n * (Z.abs n / 2 ^ e))%Z in
  (m, e, (n - m * 2 ^ e)%Z).

(* One peeling: the top part as a float, and what is left over.  A number a   *)
(* single float holds whole is refused here, since the shorter answer is      *)
(* already exact for it.                                                      *)
Definition nearZ (n : Z) : option (PrimFloat.float * Z) :=
  if (Z.abs n <? mmax)%Z then None else
  let: (m, e, r) := splitZ n in
  Some (ldexp2 (PrimitiveFloat.fromZ m) e, r).

Definition fromZ_UP (p : precision) (n : Z) :=
  match nearZ n with
  | Some (a1, r1) =>
      match nearZ r1 with
      | Some (a2, r2) =>
          add_UP p (add_UP p (fp2tw a1) (fp2tw a2))
                   (fp2tw (PrimitiveFloat.fromZ_UP fprec r2))
      | None =>
          add_UP p (fp2tw a1) (fp2tw (PrimitiveFloat.fromZ_UP fprec r1))
      end
  | None => fp2tw (PrimitiveFloat.fromZ_UP fprec n)
  end.

Definition fromZ_DN (p : precision) (n : Z) :=
  match nearZ n with
  | Some (a1, r1) =>
      match nearZ r1 with
      | Some (a2, r2) =>
          add_DN p (add_DN p (fp2tw a1) (fp2tw a2))
                   (fp2tw (PrimitiveFloat.fromZ_DN fprec r2))
      | None =>
          add_DN p (fp2tw a1) (fp2tw (PrimitiveFloat.fromZ_DN fprec r1))
      end
  | None => fp2tw (PrimitiveFloat.fromZ_DN fprec n)
  end.

(* Rounding to an integer is monotone, so rounding a bound of the value       *)
(* gives a bound of the rounded value.  Only ordinarily tight.                *)
Definition nearbyint_UP (mode : rounding_mode) x :=
  onReal (fun x => fp2tw (PrimitiveFloat.nearbyint_UP mode
                            (addUpFp (addUpFp (tw0 x) (tw1 x)) (tw2 x)))) x.
Definition nearbyint_DN (mode : rounding_mode) x :=
  onReal (fun x => fp2tw (PrimitiveFloat.nearbyint_DN mode
                            (addDnFp (addDnFp (tw0 x) (tw1 x)) (tw2 x)))) x.

(* The midpoint is the plain half sum: rounding to nearest keeps it between   *)
(* the two, which is all that is asked of it.                                 *)
Definition midpoint x y := div2 (plusTwTw x y).

(* ---------------------------------------------------------------------------*)
(*  What needs no arithmetic                                                  *)
(* ---------------------------------------------------------------------------*)

(* Whatever an operation did, the guard leaves either a real number or        *)
(* nothing, and neither is an infinity of the wrong sign.  That is half of    *)
(* every obligation, and it is free.                                          *)
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

Lemma nan_correct : classify nan = Sig.Fnan.
Proof. by []. Qed.

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

(* What an operation of two arguments has to be shown, once the guard has     *)
(* taken care of the rest: a single inequality, about an operation given two  *)
(* triple words that returned one.  The value it is compared to is left       *)
(* open, so the sum and the difference use the same two lemmas.  Where the    *)
(* operation gave up, the answer is the whole line and there is nothing to    *)
(* prove.                                                                     *)
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

(* ---------------------------------------------------------------------------*)
(*  Reading a triple word                                                     *)
(* ---------------------------------------------------------------------------*)

(* A float is finite exactly when it reads as a real number.                  *)
Definition Dfinb f := PrimitiveFloat.real f.

Lemma DfinbI f : Dfin f -> Dfinb f = true.
Proof.
by rewrite /Dfinb -{2}(B2Prim_Prim2B f) PrimitiveFloat.real_is_finite.
Qed.

Lemma DfinbW f : Dfinb f = true -> Dfin f.
Proof.
by rewrite /Dfinb -{1}(B2Prim_Prim2B f) PrimitiveFloat.real_is_finite.
Qed.

(* A triple word is a real number exactly when all three of its words are     *)
(* numbers and the triple is one, and then it denotes their sum.              *)
Lemma realE x :
  real x = andb (andb (andb (Dfinb (tw0 x)) (Dfinb (tw1 x)))
                      (Dfinb (tw2 x))) (wellFormed x).
Proof.
case: x => x0 x1 x2; rewrite /real /classify /classifyFp /Dfinb.
rewrite !PrimitiveFloat.classify_correct /PrimitiveFloat.classify /wellFormed.
by case: (PrimFloat.classify x0); case: (PrimFloat.classify x1);
   case: (PrimFloat.classify x2);
   case: (((x0 + x1 =? x0) && (x1 + x2 =? x1))%float).
Qed.

Lemma real_fin x :
  real x = true ->
  Dfin (tw0 x) /\ Dfin (tw1 x) /\ Dfin (tw2 x) /\ wellFormed x = true.
Proof.
rewrite realE.
case E0: (Dfinb (tw0 x)) => //=; case E1: (Dfinb (tw1 x)) => //=.
case E2: (Dfinb (tw2 x)) => //= Ew.
by split; [|split; [|split]]; try apply: DfinbW.
Qed.

Lemma toXE f : Dfin f -> FtoX (PrimitiveFloat.toF f) = Xreal (D2R f).
Proof.
move=> Ff; rewrite -/(PrimitiveFloat.toX f) PrimitiveFloat.toX_Prim2B.
by rewrite PrimitiveFloat.B2R_BtoX.
Qed.

Lemma toX_real x :
  real x = true -> toX x = Xreal (D2R (tw0 x) + D2R (tw1 x) + D2R (tw2 x)).
Proof.
case: x => x0 x1 x2 Rx; have [F0 [F1 [F2 Ew]]] := real_fin _ Rx.
rewrite /toX /toF Ew !Fadd_exact_correct.
by rewrite (toXE x0 F0) (toXE x1 F1) (toXE x2 F2).
Qed.

Lemma toX_fp2tw f : toX (fp2tw f) = PrimitiveFloat.toX f.
Proof.
have Hz : (f + 0 =? f)%float = false -> PrimitiveFloat.toX f = Xnan.
  rewrite eqb_equiv add_equiv /PrimitiveFloat.toX /PrimitiveFloat.toF.
  rewrite -B2SF_Prim2B.
  have -> : Prim2B 0%float = B754_zero false by [].
  case: (Prim2B f) => [s1|s1||s1 m1 e1 H1] //=; last first.
    by rewrite (Beqb_refl _ _ (B754_finite s1 m1 e1 H1)).
  by case: s1.
rewrite /toX /toF /fp2tw /wellFormed.
have -> : (0 + 0 =? 0)%float = true by [].
case E: (f + 0 =? f)%float => /=; last by rewrite (Hz E).
by rewrite !Fadd_exact_correct /= !Xadd_0_r.
Qed.

Lemma zero_correct : toX zero = Xreal 0.
Proof. by []. Qed.

Lemma real_correct f :
  real f = match toX f with Xnan => false | Xreal _ => true end.
Proof.
case E: (real f); first by rewrite (toX_real _ E).
have Hn : forall g, Dfinb g = false -> PrimitiveFloat.toX g = Xnan.
  move=> g; rewrite /Dfinb PrimitiveFloat.real_correct.
  by case: (PrimitiveFloat.toX g).
move: E; rewrite realE; case: f => x0 x1 x2 /=.
case E0: (Dfinb x0) => /=; last first.
  rewrite /toX /toF /wellFormed.
  case: (((x0 + x1 =? x0) && (x1 + x2 =? x1))%float) => //.
  rewrite !Fadd_exact_correct -/(PrimitiveFloat.toX x0)
          -/(PrimitiveFloat.toX x1) -/(PrimitiveFloat.toX x2) (Hn _ E0).
  by case: (PrimitiveFloat.toX x0); case: (PrimitiveFloat.toX x1);
     case: (PrimitiveFloat.toX x2).
case E1: (Dfinb x1) => /=; last first.
  rewrite /toX /toF /wellFormed.
  case: (((x0 + x1 =? x0) && (x1 + x2 =? x1))%float) => //.
  rewrite !Fadd_exact_correct -/(PrimitiveFloat.toX x0)
          -/(PrimitiveFloat.toX x1) -/(PrimitiveFloat.toX x2) (Hn _ E1).
  by case: (PrimitiveFloat.toX x0); case: (PrimitiveFloat.toX x1);
     case: (PrimitiveFloat.toX x2).
case E2: (Dfinb x2) => /=; last first.
  rewrite /toX /toF /wellFormed.
  case: (((x0 + x1 =? x0) && (x1 + x2 =? x1))%float) => //.
  rewrite !Fadd_exact_correct -/(PrimitiveFloat.toX x0)
          -/(PrimitiveFloat.toX x1) -/(PrimitiveFloat.toX x2) (Hn _ E2).
  by case: (PrimitiveFloat.toX x0); case: (PrimitiveFloat.toX x1);
     case: (PrimitiveFloat.toX x2).
by move=> Ew; rewrite /toX /toF /wellFormed Ew.
Qed.

(* ---------------------------------------------------------------------------*)
(*  What needs the arithmetic, and is not proved yet                          *)
(* ---------------------------------------------------------------------------*)

(* Each statement below is a fact about what the operations of tw_updn.v      *)
(* compute.  None of them is proved.  The `valid_` halves are the free        *)
(* lemmas above; what is missing every time is the inequality.                *)

Definition is_non_neg x :=
  valid_ub x = true /\
  match toX x with Xnan => True | Xreal r => (0 <= r)%R end.
Definition is_pos x :=
  valid_ub x = true /\
  match toX x with Xnan => True | Xreal r => (0 < r)%R end.
Definition is_non_pos x :=
  valid_lb x = true /\
  match toX x with Xnan => True | Xreal r => (r <= 0)%R end.
Definition is_neg x :=
  valid_lb x = true /\
  match toX x with Xnan => True | Xreal r => (r < 0)%R end.

Definition is_non_neg' x :=
  match toX x with Xnan => valid_ub x = true | Xreal r => (0 <= r)%R end.
Definition is_non_pos' x :=
  match toX x with Xnan => valid_lb x = true | Xreal r => (r <= 0)%R end.
Definition is_non_neg_real x :=
  match toX x with Xnan => False | Xreal r => (0 <= r)%R end.
Definition is_non_pos_real x :=
  match toX x with Xnan => False | Xreal r => (r <= 0)%R end.

Definition is_real_ub x :=
  match toX x with Xnan => valid_ub x = true | Xreal _ => True end.
Definition is_real_lb x :=
  match toX x with Xnan => valid_lb x = true | Xreal _ => True end.
Definition is_pos_real x :=
  match toX x with Xnan => False | Xreal r => (0 < r)%R end.
Definition is_neg_real x :=
  match toX x with Xnan => False | Xreal r => (r < 0)%R end.

Lemma ZtoS_correct p z :
  (z <= StoZ (ZtoS z))%Z \/ toX (pow2_UP p (ZtoS z)) = Xnan.
Proof. Admitted.

Lemma fromZ_correct n : (Z.abs n <= 256)%Z -> toX (fromZ n) = Xreal (IZR n).
Proof. by move=> Hn; rewrite /fromZ toX_fp2tw PrimitiveFloat.fromZ_correct. Qed.

Lemma fromZ_UP_correct p n :
  valid_ub (fromZ_UP p n) = true /\
  le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
Proof. Admitted.

Lemma fromZ_DN_correct p n :
  valid_lb (fromZ_DN p n) = true /\
  le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
Proof. Admitted.

Lemma mag_correct f : (Rabs (toR f) < bpow radix (StoZ (mag f)))%R.
Proof. Admitted.

Lemma neg_correct x :
  match classify x with
  | Freal => toX (neg x) = (- toX x)%XR
  | Sig.Fnan => classify (neg x) = Sig.Fnan
  | Fminfty => classify (neg x) = Fpinfty
  | Fpinfty => classify (neg x) = Fminfty
  end.
Proof. Admitted.

Lemma abs_correct x :
  toX (abs x) = Xabs (toX x) /\ valid_ub (abs x) = true.
Proof. Admitted.

Lemma cmp_correct x y :
  cmp x y =
  match classify x with
  | Freal =>
      match classify y with
      | Freal => Xcmp (toX x) (toX y)
      | Sig.Fnan => Xund | Fminfty => Xgt | Fpinfty => Xlt
      end
  | Sig.Fnan => Xund
  | Fminfty =>
      match classify y with
      | Sig.Fnan => Xund | Fminfty => Xeq | _ => Xlt end
  | Fpinfty =>
      match classify y with
      | Sig.Fnan => Xund | Fpinfty => Xeq | _ => Xgt end
  end.
Proof. Admitted.

Lemma min_correct x y :
  match classify x with
  | Freal =>
      match classify y with
      | Freal => toX (min x y) = Xmin (toX x) (toX y)
      | Sig.Fnan => classify (min x y) = Sig.Fnan
      | Fminfty => classify (min x y) = Fminfty
      | Fpinfty => min x y = x
      end
  | Sig.Fnan => classify (min x y) = Sig.Fnan
  | Fminfty =>
      match classify y with
      | Sig.Fnan => classify (min x y) = Sig.Fnan
      | _ => classify (min x y) = Fminfty
      end
  | Fpinfty =>
      match classify y with
      | Sig.Fnan => classify (min x y) = Sig.Fnan
      | Fminfty => classify (min x y) = Fminfty
      | _ => min x y = y
      end
  end.
Proof. Admitted.

Lemma max_correct x y :
  match classify x with
  | Freal =>
      match classify y with
      | Freal => toX (max x y) = Xmax (toX x) (toX y)
      | Sig.Fnan => classify (max x y) = Sig.Fnan
      | Fminfty => max x y = x
      | Fpinfty => classify (max x y) = Fpinfty
      end
  | Sig.Fnan => classify (max x y) = Sig.Fnan
  | Fminfty =>
      match classify y with
      | Sig.Fnan => classify (max x y) = Sig.Fnan
      | Fpinfty => classify (max x y) = Fpinfty
      | _ => max x y = y
      end
  | Fpinfty =>
      match classify y with
      | Sig.Fnan => classify (max x y) = Sig.Fnan
      | _ => classify (max x y) = Fpinfty
      end
  end.
Proof. Admitted.

Lemma add_UP_correct p x y :
  valid_ub x = true -> valid_ub y = true ->
  valid_ub (add_UP p x y) = true /\
  le_upper (toX x + toX y)%XR (toX (add_UP p x y)).
Proof. Admitted.

Lemma add_DN_correct p x y :
  valid_lb x = true -> valid_lb y = true ->
  valid_lb (add_DN p x y) = true /\
  le_lower (toX (add_DN p x y)) (toX x + toX y)%XR.
Proof. Admitted.

Lemma sub_UP_correct p x y :
  valid_ub x = true -> valid_lb y = true ->
  valid_ub (sub_UP p x y) = true /\
  le_upper (toX x - toX y)%XR (toX (sub_UP p x y)).
Proof. Admitted.

Lemma sub_DN_correct p x y :
  valid_lb x = true -> valid_ub y = true ->
  valid_lb (sub_DN p x y) = true /\
  le_lower (toX (sub_DN p x y)) (toX x - toX y)%XR.
Proof. Admitted.

Lemma mul_UP_correct p x y :
  is_non_neg' x /\ is_non_neg' y \/ is_non_pos' x /\ is_non_pos' y \/
  is_non_pos_real x /\ is_non_neg_real y \/
  is_non_neg_real x /\ is_non_pos_real y ->
  valid_ub (mul_UP p x y) = true /\
  le_upper (toX x * toX y)%XR (toX (mul_UP p x y)).
Proof. Admitted.

Lemma mul_DN_correct p x y :
  is_non_neg_real x /\ is_non_neg_real y \/
  is_non_pos_real x /\ is_non_pos_real y \/
  is_non_neg' x /\ is_non_pos' y \/ is_non_pos' x /\ is_non_neg' y ->
  valid_lb (mul_DN p x y) = true /\
  le_lower (toX (mul_DN p x y)) (toX x * toX y)%XR.
Proof. Admitted.

Lemma pow2_UP_correct p s :
  valid_ub (pow2_UP p s) = true /\
  le_upper (Xscale radix2 (Xreal 1) (StoZ s)) (toX (pow2_UP p s)).
Proof. Admitted.

Lemma div_UP_correct p x y :
  is_real_ub x /\ is_pos_real y \/ is_real_lb x /\ is_neg_real y ->
  valid_ub (div_UP p x y) = true /\
  le_upper (toX x / toX y)%XR (toX (div_UP p x y)).
Proof. Admitted.

Lemma div_DN_correct p x y :
  is_real_ub x /\ is_neg_real y \/ is_real_lb x /\ is_pos_real y ->
  valid_lb (div_DN p x y) = true /\
  le_lower (toX (div_DN p x y)) (toX x / toX y)%XR.
Proof. Admitted.

Lemma sqrt_UP_correct p x :
  valid_ub (sqrt_UP p x) = true /\
  le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof. Admitted.

Lemma sqrt_DN_correct p x :
  valid_lb x = true ->
  valid_lb (sqrt_DN p x) = true /\
  le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x)).
Proof. Admitted.

Lemma nearbyint_UP_correct mode x :
  valid_ub (nearbyint_UP mode x) = true /\
  le_upper (Xnearbyint mode (toX x)) (toX (nearbyint_UP mode x)).
Proof. Admitted.

Lemma nearbyint_DN_correct mode x :
  valid_lb (nearbyint_DN mode x) = true /\
  le_lower (toX (nearbyint_DN mode x)) (Xnearbyint mode (toX x)).
Proof. Admitted.

(* The two the signature lets a format decline, and this one declines them:   *)
(* `sensible_format` is false, so both statements are read with a false       *)
(* premise and cost nothing.  They are written out so that the escape is      *)
(* visible rather than implied.                                               *)
Lemma div2_correct x :
  sensible_format = true -> (1 / 256 <= Rabs (toR x))%R ->
  toX (div2 x) = (toX x / Xreal 2)%XR.
Proof. by []. Qed.

Lemma midpoint_correct x y :
  sensible_format = true -> real x = true -> real y = true ->
  (toR x <= toR y)%R ->
  real (midpoint x y) = true /\
  (toR x <= toR (midpoint x y))%R /\ (toR (midpoint x y) <= toR y)%R.
Proof. by []. Qed.

End TwFloat.

(* The module meets the signature.  This is a check of the shape, not of the  *)
(* arithmetic: the obligations marked above are admitted.                     *)
Module TwFloatCheck <: FloatOps := TwFloat.
