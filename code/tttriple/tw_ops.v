From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats PrimInt63.
From Flocq Require Import Zaux Raux Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Generic_proof Primitive_ops.
From mathcomp Require Import ssreflect ssrbool.
From twarith Require Import twarith tw_updn twbound twpaper twdiv twsqrt.
(* The bridge from primitive floats to the reals is the double-word    *)
(* development's `dwbridge.v'.  It says nothing about pairs -- only     *)
(* what one primitive float is and what one operation on it does -- so  *)
(* it serves three words as well as two, and is used rather than        *)
(* copied.                                                             *)
From dwarith Require Import dwbridge dwsign dwbound.

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
(* WHAT IS PROVED AND WHAT IS ASSUMED.  The module below meets the signature  *)
(* - the sealing at the bottom of the file is what says so - and EVERY ONE OF *)
(* ITS OBLIGATIONS IS PROVED.  Nothing here is `Admitted'.                    *)
(*                                                                            *)
(* AND NOTHING IS ASSUMED.  The quotient and the root leant on one measured   *)
(* number each; both are now proved.  `Print Assumptions' on any obligation   *)
(* names only Rocq's own primitive-float axioms and classical reals.  The     *)
(* two algorithms carry a guard, which the operation evaluates and which      *)
(* answers `nan' where it fails - and for the root, where it fails the        *)
(* number is scaled into the band instead.                                    *)
(*                                                                            *)
(* PROVED: the reading (`zero_correct', `real_correct',                       *)
(* `fromZ_correct'); the six bounds on the sum, the difference and the        *)
(* product -- `add/sub/mul _UP_correct' and `_DN_correct' -- which come from  *)
(* `twbound.v' and take nothing from the three-word paper; the sign           *)
(* (`neg_correct', `abs_correct'); the power of two and the scaling           *)
(* (`pow2_UP_correct', `ZtoS_correct'); and a whole number as a triple word   *)
(* (`fromZ_UP_correct', `fromZ_DN_correct'), where the two parts peeled off   *)
(* are exact and only the last float carries a bound; the magnitude           *)
(* (`mag_correct'); rounding to a whole number either way                     *)
(* (`nearbyint_UP_correct', `nearbyint_DN_correct'); and the comparison with  *)
(* the two that rest on it (`cmp_correct', `min_correct', `max_correct'),     *)
(* which read the VALUE and not the words - see the note on `cmp' below and   *)
(* the pair in `tw_cmpbad.v'.                                                 *)
(*                                                                            *)
(* PROVED THROUGH A GUARD: `div_UP_correct', `div_DN_correct',                *)
(* `sqrt_UP_correct' and `sqrt_DN_correct', from `kstep_div_testable' and     *)
(* `kstep_sqrt_testable' in `twdivflx.v' and `twflx.v'.                       *)
(*                                                                            *)
(* `div2_correct' and `midpoint_correct' are excused by                       *)
(* `sensible_format = false' and say nothing.                                 *)


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

(* WRITTEN WITHOUT THE OPTION.  `classifyFp' answers `Some' or `None', and    *)
(* three of those are three allocations on a path that every operation walks  *)
(* several times over -- `I.mul' alone asks for it fourteen times, four of    *)
(* them inside the two comparisons `sign_large_' makes against nought.  The   *)
(* nested match below is the same function and allocates nothing;             *)
(* `classifyE' says so, for the proofs that read the old shape.               *)
Definition classify x :=
  let: TWFloat x0 x1 x2 := x in
  match PrimFloat.classify x0 with
  | PInf => Fpinfty | NInf => Fminfty | NaN => Sig.Fnan
  | _ =>
    match PrimFloat.classify x1 with
    | PInf => Fpinfty | NInf => Fminfty | NaN => Sig.Fnan
    | _ =>
      match PrimFloat.classify x2 with
      | PInf => Fpinfty | NInf => Fminfty | NaN => Sig.Fnan
      | _ => if wellFormed x then Freal else Sig.Fnan
      end
    end
  end.

Lemma classifyE x :
  classify x =
  (let: TWFloat x0 x1 x2 := x in
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
   end).
Proof.
case: x => x0 x1 x2; rewrite /classify /classifyFp.
by case: (PrimFloat.classify x0) => //;
   case: (PrimFloat.classify x1) => //;
   case: (PrimFloat.classify x2).
Qed.

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

(* COMPARING THREE WORDS ON THEIR WORDS IS WRONG, so this does not do that.   *)
(* A double word rounds to its leading word, so for two words the leading     *)
(* words are in the order the values are, and comparing on the words is       *)
(* sound.  A TRIPLE WORD DOES NOT ROUND TO ITS LEADING WORD -- being one is   *)
(* two tests, each on a pair, and the two together do not give the three-way  *)
(* statement -- and `tw_cmpbad.v' has the pair that shows what goes wrong:    *)
(* the smaller leading word on the larger value.  So the words are no use     *)
(* and the VALUE has to be read.                                             *)
(*                                                                            *)
(* It is read exactly, and as a whole number.  Every binary64 number is a     *)
(* whole number times a power of two, and Interval's own `toF' hands over     *)
(* both halves; three of them brought to a common power of two add as whole   *)
(* numbers, and two such are compared as whole numbers.  Nothing is rounded   *)
(* anywhere, so there is no error term to bound and no range condition to     *)
(* test -- which is what the six-word sweep would have cost, since the sign   *)
(* of a swept sum is the sign of what leads it only once the sweep is known   *)
(* to separate its terms, and that is the paper's analysis all over again.    *)
(*                                                                            *)
(* The numbers are as wide as the exponent range, so a little over two        *)
(* thousand bits in the worst case and far less in the ordinary one.  The     *)
(* cost is measured in `bench_ops.v'.                                         *)

(* One float as a whole number times a power of two.  A float that is not a   *)
(* number does not reach here: the callers test `real' first.                 *)
Definition fZ (f : PrimFloat.float) : Z * Z :=
  match PrimitiveFloat.toF f with
  | Basic.Float s m e => (SpecFloat.cond_Zopp s (Zpos m), e)
  | _ => (0%Z, 0%Z)
  end.

(* And a triple word the same way: the three brought down to the smallest of  *)
(* the three powers, where they add as whole numbers.                         *)
Definition twZ (t : twfloat) : Z * Z :=
  let: (m0, e0) := fZ (tw0 t) in
  let: (m1, e1) := fZ (tw1 t) in
  let: (m2, e2) := fZ (tw2 t) in
  let e := Z.min e0 (Z.min e1 e2) in
  ((Z.shiftl m0 (e0 - e) + Z.shiftl m1 (e1 - e) + Z.shiftl m2 (e2 - e))%Z, e).

Definition cmpZ (t u : twfloat) : comparison :=
  let: (a, ea) := twZ t in
  let: (b, eb) := twZ u in
  let e := Z.min ea eb in
  Z.compare (Z.shiftl a (ea - e)) (Z.shiftl b (eb - e)).

(* AND READING THE VALUE IS DEAR, so it is not done unless it has to be.      *)
(* `Prim2SF' takes a float apart into a whole number and a power of two, and  *)
(* the whole number comes out of `Uint63.to_Z', which walks sixty-three bits  *)
(* one at a time -- measured, twenty-three microseconds a float, so six of    *)
(* them is a fifth of a millisecond a comparison.  Put in front of Interval's *)
(* tactic that is not a slowdown but a stop.                                  *)
(*                                                                            *)
(* So the words are asked first, and they are allowed to answer only when     *)
(* they can prove it.  Two questions, both in floats:                         *)
(*                                                                            *)
(*   are the three words the same?              then the values are the same  *)
(*   do the leading words differ by more than   then the leading words decide *)
(*     the two tails can be worth?                                            *)
(*                                                                            *)
(* The second is what a triple word does NOT give for nothing -- that is      *)
(* `tw_cmpbad.v' -- so the amount is not guessed, it is added up: the last    *)
(* two words of each, in absolute value, rounded up.  When the gap clears     *)
(* that, the order is settled whatever the tails are.  Otherwise the answer   *)
(* is `Xund', which here means NOT DECIDED rather than not a number, and the  *)
(* whole number is built after all.                                           *)
(*                                                                            *)
(* What is left for the dear path is two values within a step of one another  *)
(* without being the same, which is rare and is the only case where the       *)
(* words genuinely say nothing.                                               *)
Definition tailUp (t : twfloat) :=
  addUpFp (PrimFloat.abs (tw1 t)) (PrimFloat.abs (tw2 t)).
Definition tailBoth (x y : twfloat) := addUpFp (tailUp x) (tailUp y).

(* The band is passed in rather than written twice, so it is added up once.   *)
Definition cmpBand (s : PrimFloat.float) (x y : twfloat) : Xcomparison :=
  if posFp (subDnFp (subDnFp (tw0 x) (tw0 y)) s) then Xgt
  else if posFp (subDnFp (- subUpFp (tw0 x) (tw0 y))%float s) then Xlt
  else Xund.

Definition cmpFast (x y : twfloat) : Xcomparison :=
  if ((tw0 x =? tw0 y) && (tw1 x =? tw1 y) && (tw2 x =? tw2 y))%float then Xeq
  else cmpBand (tailBoth x y) x y.

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
    match cmpFast x y with
    | Xund => match cmpZ x y with Eq => Xeq | Lt => Xlt | Gt => Xgt end
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
(* The paper's Algorithm 14 for the quotient and Algorithm 15 for the root,  *)
(* each bounded by `kstep' and each behind a guard the operation evaluates.   *)
(* `divTwUpK' and `sqrtTwUpK' are `twdiv.v''s and `twsqrt.v''s -- they add   *)
(* the ways round a failed guard to `divTwUpQ' and `sqrtTwUpP'.  Both names   *)
(* were once declared in `tw_updn.v' as well, for the long-division and       *)
(* Newton routes, and which one arrived here was decided by the order of the  *)
(* imports above.  Those are gone; see the note in `tw_updn.v'.               *)
Definition div_UP (_ : precision) x y := onReal2 divTwUpK x y.
Definition div_DN (_ : precision) x y := onReal2 divTwDnK x y.
Definition sqrt_UP (_ : precision) x := onReal sqrtTwUpK x.
Definition sqrt_DN (_ : precision) x := onReal sqrtTwDnK x.

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

(* THE MIDPOINT, AND WHY IT IS NOT THE PLAIN HALF SUM.  `plusTwTw' (now in `nearest/') adds to *)
(* nearest but does not sweep, so its three words can overlap: a third and a  *)
(* third came back as `0x1.5555555555556p-1' beside `-0x1.5555555555555p-54', *)
(* and two thirds of a step of the leading word is more than half of one, so  *)
(* `wellFormed' is false and the whole triple reads as nothing.  Interval     *)
(* then has no point to halve its range at, and every goal that bisects is    *)
(* refused -- which is what `method_error' was.                               *)
(*                                                                            *)
(* So the sum is the one that sweeps, and the half of it is held between the  *)
(* two ends by hand: a bound rounded outwards can leave the range it was cut  *)
(* from, and the two ends are themselves the answer when it does.             *)
Definition midpoint x y :=
  let m := div2 (addTwUp x y) in
  if real m then max x (min y m) else x.

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

(* The same, said of the float's own reading rather than of the triple's.     *)
Lemma toXfE f : Dfin f -> PrimitiveFloat.toX f = Xreal (D2R f).
Proof. exact: toXE. Qed.

(* And the way back: a float that reads as a number is one, and is that one.  *)
Lemma toX_D2R a u : PrimitiveFloat.toX a = Xreal u -> Dfin a /\ D2R a = u.
Proof.
rewrite PrimitiveFloat.toX_Prim2B /Dfin /D2R => H.
split; last by rewrite (PrimitiveFloat.BtoX_B2R _ _ H).
by move: H; case: (Prim2B a) => [s|s||s m e Hm].
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

(* A float that is not minus infinity makes a triple that may bound above.    *)
Lemma Dninf f : (f =? neg_infinity)%float = false ->
  match PrimFloat.classify f with NInf => false | _ => true end = true.
Proof.
rewrite eqb_equiv classify_spec -B2SF_Prim2B.
have -> : Prim2B neg_infinity = B754_infinity true by [].
by case: (Prim2B f) => [[]|[]||[] m1 e1 H1] //=;
   case: (match digits2_pos m1 with 53%positive => true | _ => false end).
Qed.

Lemma valid_ub_fp2tw f :
  PrimitiveFloat.valid_ub f = true -> valid_ub (fp2tw f) = true.
Proof.
rewrite /PrimitiveFloat.valid_ub /valid_ub /classify /classifyFp.
case E: (f =? neg_infinity)%float => //= _.
by move: (Dninf _ E); case: (PrimFloat.classify f) => //= _;
   case: ((f + 0 =? f)%float && true).
Qed.

(* And the mirror of it, for a float that is not plus infinity.               *)
Lemma Dpinf f : (f =? infinity)%float = false ->
  match PrimFloat.classify f with PInf => false | _ => true end = true.
Proof.
rewrite eqb_equiv classify_spec -B2SF_Prim2B.
have -> : Prim2B infinity = B754_infinity false by [].
by case: (Prim2B f) => [[]|[]||[] m1 e1 H1] //=;
   case: (match digits2_pos m1 with 53%positive => true | _ => false end).
Qed.

Lemma valid_lb_fp2tw f :
  PrimitiveFloat.valid_lb f = true -> valid_lb (fp2tw f) = true.
Proof.
rewrite /PrimitiveFloat.valid_lb /valid_lb /classify /classifyFp.
case E: (f =? infinity)%float => //= _.
by move: (Dpinf _ E); case: (PrimFloat.classify f) => //= _;
   case: ((f + 0 =? f)%float && true).
Qed.

Lemma ZtoS_correct p z :
  (z <= StoZ (ZtoS z))%Z \/ toX (pow2_UP p (ZtoS z)) = Xnan.
Proof. by left; apply: Z.le_refl. Qed.

Lemma fromZ_correct n : (Z.abs n <= 256)%Z -> toX (fromZ n) = Xreal (IZR n).
Proof. by move=> Hn; rewrite /fromZ toX_fp2tw PrimitiveFloat.fromZ_correct. Qed.

(* The inequality half of the obligation for the sum, on its own.  The whole  *)
(* number below is built by adding the parts it was peeled into, so it needs  *)
(* the inequality before the obligation that carries it is stated.            *)
Lemma add_UP_le p x y : le_upper (toX x + toX y)%XR (toX (add_UP p x y)).
Proof.
rewrite /add_UP; apply: (onReal2_upper (fun a b => (toX a + toX b)%XR)) => a b Ra Rb Rr.
have [F0 [F1 [F2 _]]] := real_fin _ Ra.
have [G0 [G1 [G2 _]]] := real_fin _ Rb.
have [H0 [H1 [H2 _]]] := real_fin _ Rr.
rewrite (toX_real _ Ra) (toX_real _ Rb) (toX_real _ Rr) /=.
by apply: addTwUp_ge; apply: finL_tw2l.
Qed.

Lemma add_DN_le p x y : le_lower (toX (add_DN p x y)) (toX x + toX y)%XR.
Proof.
rewrite /add_DN; apply: (onReal2_lower (fun a b => (toX a + toX b)%XR)) => a b Ra Rb Rr.
have [F0 [F1 [F2 _]]] := real_fin _ Ra.
have [G0 [G1 [G2 _]]] := real_fin _ Rb.
have [H0 [H1 [H2 _]]] := real_fin _ Rr.
rewrite (toX_real _ Ra) (toX_real _ Rb) (toX_real _ Rr) /le_lower /=.
by apply: Ropp_le_contravar; apply: addTwDn_le; apply: finL_tw2l.
Qed.

(* A whole number below two to the fifty-third is a float, and the float is   *)
(* the number.  This is the whole range a single float holds.                 *)
Lemma fromZ_exact n : (Z.abs n < mmax)%Z ->
  PrimitiveFloat.toX (PrimitiveFloat.fromZ n) = Xreal (IZR n).
Proof.
rewrite /mmax; case: n => [|q|q] Hq //.
  rewrite /PrimitiveFloat.fromZ; case: Pos.compare_spec => Hq'.
  - by move: Hq; rewrite Hq'.
  - by rewrite (PrimitiveFloat.of_int63_of_pos_exact _ Hq').
  - by lia.
rewrite /PrimitiveFloat.fromZ; case: Pos.compare_spec => Hq'.
- by move: Hq; rewrite Hq'.
- change (Xreal _) with (- (Xreal (IZR (Zpos q))))%XR.
  by rewrite -(PrimitiveFloat.of_int63_of_pos_exact _ Hq') PrimitiveFloat.toX_neg.
- by lia.
Qed.

(* Such a number, scaled up by a power of two, is a float as well - the       *)
(* scaling moves the exponent and leaves the fifty-three bits where they      *)
(* were.  Either it runs off the top of the range, and then it is nothing at  *)
(* all, or it is the product exactly.  Nothing is estimated, so the peeling   *)
(* below has no error term to pay for.                                        *)
Lemma ldexp2_exact m e : (Z.abs m < mmax)%Z -> (0 <= e)%Z ->
  PrimitiveFloat.toX (ldexp2 (PrimitiveFloat.fromZ m) e) = Xnan \/
  PrimitiveFloat.toX (ldexp2 (PrimitiveFloat.fromZ m) e)
    = Xreal (IZR m * bpow radix2 e).
Proof.
move=> Hm He.
have [Fm Vm] := toX_D2R _ _ (fromZ_exact _ Hm).
have Hfmt : generic_format radix2 (SpecFloat.fexp FloatOps.prec FloatOps.emax)
              (IZR m * bpow radix2 e).
  rewrite DfexpE; apply: generic_format_FLT.
  apply: (FLT_spec _ _ _ _ (Defs.Float radix2 m e)) => //=.
  by have -> : (SpecFloat.emin FloatOps.prec FloatOps.emax = -1074)%Z; [|lia].
have Hld := Bldexp_correct FloatOps.prec FloatOps.emax Hprec Hmax mode_NE
              (Prim2B (PrimitiveFloat.fromZ m)) e.
rewrite /D2R in Vm; rewrite Vm round_generic // in Hld.
move: Hld; case: Rlt_bool_spec => Hlt.
  case=> HB [Hf _]; right.
  have Fld : Dfin (ldexp2 (PrimitiveFloat.fromZ m) e).
    by rewrite /Dfin /ldexp2 ldexp_equiv Hf.
  by rewrite (toXfE _ Fld) /D2R /ldexp2 ldexp_equiv HB.
move=> HB; left.
rewrite /ldexp2 PrimitiveFloat.toX_Prim2B ldexp_equiv.
by move: HB; rewrite /binary_overflow /=; case: (Bldexp _ _ _).
Qed.

(* So one peeling takes off exactly what it says it does: the float it        *)
(* returns is the number less what is left over, or it is nothing at all.     *)
(* There is no error term, which is what the scaling above bought.            *)
Lemma Zabs_sgn n : n <> 0%Z -> Z.abs (Z.sgn n) = 1%Z.
Proof. by case: n => [|p|p] //=; lia. Qed.

Lemma nearZE n a r : nearZ n = Some (a, r) ->
  PrimitiveFloat.toX a = Xnan \/
  PrimitiveFloat.toX a = Xreal (IZR n - IZR r).
Proof.
rewrite /nearZ; case En: (Z.abs n <? mmax)%Z => //.
case E: (splitZ n) => [[m e] r'] [<- <-].
have Hmx : mmax = (2 ^ 53)%Z by [].
have Hn : (mmax <= Z.abs n)%Z by apply/Z.ltb_ge.
have Hn0 : (0 < Z.abs n)%Z by move: Hn; rewrite Hmx; lia.
have He : (0 <= e)%Z by move: E; rewrite /splitZ; case=> _ <- _; apply: Z.le_max_l.
have Hr : (n - r' = m * 2 ^ e)%Z.
  by move: E; rewrite /splitZ; case=> <- <- <-; ring.
have Hm : (Z.abs m < mmax)%Z.
  move: E; rewrite /splitZ; case=> <- _ _.
  (* Fifty-three bits or more are there, so the exponent is the one the      *)
  (* logarithm gives and not the nought the maximum guards with.             *)
  have Hl : (53 <= Z.log2 (Z.abs n))%Z.
    by rewrite -(Z.log2_pow2 53) //; apply: Z.log2_le_mono; rewrite -Hmx.
  have -> : Z.max 0 (Z.log2 (Z.abs n) - 52) = (Z.log2 (Z.abs n) - 52)%Z.
    by lia.
  set k := (Z.log2 (Z.abs n) - 52)%Z.
  have Hk : (0 < 2 ^ k)%Z by apply: Z.pow_pos_nonneg; rewrite /k; lia.
  rewrite Z.abs_mul Zabs_sgn; last by move=> Hz; move: Hn0; rewrite Hz /=; lia.
  rewrite Z.mul_1_l Z.abs_eq; last by apply: Z.div_pos; lia.
  apply: Z.div_lt_upper_bound => //.
  rewrite Hmx -Z.pow_add_r; [|by rewrite /k; lia|by []].
  have -> : (k + 53 = Z.log2 (Z.abs n) + 1)%Z by rewrite /k; ring.
  by have := Z.log2_spec _ Hn0; lia.
have -> : (IZR n - IZR r' = IZR m * bpow radix2 e)%R.
  by rewrite -minus_IZR Hr mult_IZR (IZR_Zpower radix2 _ He).
exact: ldexp2_exact.
Qed.

(* A whole number enters as a triple word: the two parts peeled exactly, and *)
(* what is left of them bounded by the float's own whole-number reading.      *)
(* Each case below is the same reckoning - the peelings cancel and the last   *)
(* float's bound is what remains - said once for a part that ran off the top  *)
(* of the range, where the sum denotes nothing and nothing is a bound.        *)
Lemma fromZ_UP_correct p n :
  valid_ub (fromZ_UP p n) = true /\
  le_upper (Xreal (IZR n)) (toX (fromZ_UP p n)).
Proof.
rewrite /fromZ_UP; case E1: (nearZ n) => [[a1 r1]|]; last first.
  rewrite toX_fp2tw.
  have [Hv Hb] := PrimitiveFloat.fromZ_UP_correct fprec n.
  by split => //; apply: valid_ub_fp2tw.
have [_ Hr1] := PrimitiveFloat.fromZ_UP_correct fprec r1.
case E2: (nearZ r1) => [[a2 r2]|]; last first.
  (* One peeling was enough: the part taken off, and the float that bounds   *)
  (* what was left.                                                          *)
  split; first exact: valid_ub_onReal2.
  have H1 := add_UP_le p (fp2tw a1) (fp2tw (PrimitiveFloat.fromZ_UP fprec r1)).
  rewrite !toX_fp2tw in H1.
  have [Ha1|Ha1] := nearZE _ _ _ E1.
    by rewrite Ha1 /= in H1; move: H1; case: (toX _).
  rewrite Ha1 in H1.
  by move: Hr1 H1;
     case: (PrimitiveFloat.toX _) => [|w]; case: (toX _) => [|z] //=;
     move=> *; lra.
(* Two peelings, and the same reckoning once more.                            *)
split; first exact: valid_ub_onReal2.
have [_ Hr2] := PrimitiveFloat.fromZ_UP_correct fprec r2.
have H1 := add_UP_le p (fp2tw a1) (fp2tw a2).
have H2 := add_UP_le p (add_UP p (fp2tw a1) (fp2tw a2))
             (fp2tw (PrimitiveFloat.fromZ_UP fprec r2)).
rewrite !toX_fp2tw in H1; rewrite toX_fp2tw in H2.
have [Ha1|Ha1] := nearZE _ _ _ E1.
  by rewrite Ha1 /= in H1; move: H1 H2;
     case: (toX _) => [|u]; case: (toX _) => [|v] //=.
have [Ha2|Ha2] := nearZE _ _ _ E2.
  by rewrite Ha1 Ha2 /= in H1; move: H1 H2;
     case: (toX _) => [|u]; case: (toX _) => [|v] //=.
rewrite Ha1 Ha2 /= in H1.
by move: Hr2 H1 H2;
   case: (PrimitiveFloat.toX _) => [|w]; case: (toX _) => [|u];
   case: (toX _) => [|v] //=; move=> *; lra.
Qed.

Lemma fromZ_DN_correct p n :
  valid_lb (fromZ_DN p n) = true /\
  le_lower (toX (fromZ_DN p n)) (Xreal (IZR n)).
Proof.
rewrite /fromZ_DN; case E1: (nearZ n) => [[a1 r1]|]; last first.
  rewrite toX_fp2tw.
  have [Hv Hb] := PrimitiveFloat.fromZ_DN_correct fprec n.
  by split => //; apply: valid_lb_fp2tw.
have [_ Hr1] := PrimitiveFloat.fromZ_DN_correct fprec r1.
case E2: (nearZ r1) => [[a2 r2]|]; last first.
  split; first exact: valid_lb_onReal2.
  have H1 := add_DN_le p (fp2tw a1) (fp2tw (PrimitiveFloat.fromZ_DN fprec r1)).
  rewrite !toX_fp2tw in H1.
  have [Ha1|Ha1] := nearZE _ _ _ E1.
    by rewrite Ha1 /= in H1; move: H1; rewrite /le_lower /=; case: (toX _).
  rewrite Ha1 in H1.
  by move: Hr1 H1; rewrite /le_lower /=;
     case: (PrimitiveFloat.toX _) => [|w]; case: (toX _) => [|z] //=;
     move=> *; lra.
split; first exact: valid_lb_onReal2.
have [_ Hr2] := PrimitiveFloat.fromZ_DN_correct fprec r2.
have H1 := add_DN_le p (fp2tw a1) (fp2tw a2).
have H2 := add_DN_le p (add_DN p (fp2tw a1) (fp2tw a2))
             (fp2tw (PrimitiveFloat.fromZ_DN fprec r2)).
rewrite !toX_fp2tw in H1; rewrite toX_fp2tw in H2.
have [Ha1|Ha1] := nearZE _ _ _ E1.
  by rewrite Ha1 /= in H1; move: H1 H2; rewrite /le_lower /=;
     case: (toX _) => [|u]; case: (toX _) => [|v] //=.
have [Ha2|Ha2] := nearZE _ _ _ E2.
  by rewrite Ha1 Ha2 /= in H1; move: H1 H2; rewrite /le_lower /=;
     case: (toX _) => [|u]; case: (toX _) => [|v] //=.
rewrite Ha1 Ha2 /= in H1.
by move: Hr2 H1 H2; rewrite /le_lower /=;
   case: (PrimitiveFloat.toX _) => [|w]; case: (toX _) => [|u];
   case: (toX _) => [|v] //=; move=> *; lra.
Qed.

(* THE LEADING WORD DECIDES THE SIGN.  Each word is within half a step of     *)
(* the one before it, so the second is at most half the first and the third    *)
(* at most a quarter of it: what follows the leading word cannot reach it,     *)
(* and the sum is on the side the leading word is.                             *)
Lemma wellFormed_lead x0 x1 x2 : Dfin x0 -> Dfin x1 -> Dfin x2 ->
  wellFormed (TWFloat x0 x1 x2) = true ->
  (Rabs (D2R x1 + D2R x2) <= Rabs (D2R x0))%R.
Proof.
move=> F0 F1 F2; rewrite /wellFormed => /andb_prop [E1 E2].
have H1 := wellFormed_half x0 x1 F0 F1 E1.
have H2 := wellFormed_half x1 x2 F1 F2 E2.
have T := Rabs_triang (D2R x1) (D2R x2).
by move: H1 H2 T; split_Rabs; lra.
Qed.

(* The magnitude bounds the triple: the three words are added in absolute     *)
(* value and rounded upwards, which is at or above whatever the signs make    *)
(* of them, and the magnitude of that sum is what is returned.                *)
Lemma mag_correct f : (Rabs (toR f) < bpow radix (StoZ (mag f)))%R.
Proof.
(* A triple that denotes nothing is read as nought, and every power is above  *)
(* nought.                                                                    *)
case Ex: (real f); last first.
  have -> : toR f = 0%R by move: Ex; rewrite real_correct /toR; case: (toX f).
  by rewrite Rabs_R0; apply: bpow_gt_0.
have [F0 [F1 [F2 Ew]]] := real_fin _ Ex.
have -> : toR f = (D2R (tw0 f) + D2R (tw1 f) + D2R (tw2 f))%R.
  by rewrite /toR (toX_real _ Ex).
(* Whatever the signs, the value is at most the three words added in          *)
(* absolute value.                                                            *)
have Hab : (Rabs (D2R (tw0 f) + D2R (tw1 f) + D2R (tw2 f))
            <= D2R (PrimFloat.abs (tw0 f)) + D2R (PrimFloat.abs (tw1 f))
               + D2R (PrimFloat.abs (tw2 f)))%R.
  rewrite !D2R_abs.
  have T1 := Rabs_triang (D2R (tw0 f) + D2R (tw1 f)) (D2R (tw2 f)).
  have T2 := Rabs_triang (D2R (tw0 f)) (D2R (tw1 f)).
  by lra.
rewrite /mag /StoZ; case: f Ex F0 F1 F2 Ew Hab =>
  x0 x1 x2 /= Ex F0 F1 F2 Ew Hab.
have Hlead := wellFormed_lead _ _ _ F0 F1 F2 Ew.
set u := addUpFp (PrimFloat.abs x0) (PrimFloat.abs x1).
set m := addUpFp u (PrimFloat.abs x2).
case Em: (((0 <? m)%float && (m <? infinity)%float)%bool); last first.
  (* The sum left the range.  What follows the leading word cannot reach it,  *)
  (* so the value is below twice the largest float there is, which is the     *)
  (* power claimed.                                                           *)
  have E0 : emax = 1024%Z by [].
  have E : (bpow radix 1025 = bpow radix2 emax * 2)%R.
    rewrite /radix; have -> : (1025 = emax + 1)%Z by rewrite E0.
    by rewrite bpow_plus /= /Z.pow_pos /=; lra.
  have H0 : (Rabs (D2R x0) < bpow radix2 emax)%R by apply: abs_B2R_lt_emax.
  have -> : (D2R x0 + D2R x1 + D2R x2 = D2R x0 + (D2R x1 + D2R x2))%R by ring.
  have T := Rabs_triang (D2R x0) (D2R x1 + D2R x2).
  by rewrite E; lra.
(* The sum is a number above nought, so it is what the magnitude was taken    *)
(* of, and each of the two steps is at or above what it was given.            *)
have [Hz Hi] := proj1 (Bool.andb_true_iff _ _) Em.
have [Fm Hm] := Dpos _ Hz Hi.
have Fs2 : Dfin (u + PrimFloat.abs x2)%float.
  by apply: Dfin_upFpI; move: Fm; rewrite /m /addUpFp.
have [Fu Fa2] := Dfin_addI _ _ Fs2.
have Fs1 : Dfin (PrimFloat.abs x0 + PrimFloat.abs x1)%float.
  by apply: Dfin_upFpI; move: Fu; rewrite /u /addUpFp.
have Hge1 := addUpFp_ge _ _ (Dfin_abs _ F0) (Dfin_abs _ F1) Fs1 Fu.
have Hge2 := addUpFp_ge _ _ Fu Fa2 Fs2 Fm.
have Hmc := PrimitiveFloat.mag_correct m.
have Etr : PrimitiveFloat.toR m = D2R m.
  by rewrite /PrimitiveFloat.toR (toXfE _ Fm).
rewrite Etr (Rabs_pos_eq _ (Rlt_le _ _ Hm)) in Hmc.
rewrite /PrimitiveFloat.StoZ in Hmc.
rewrite /radix -/u -/m in Hge1 Hge2 *.
by lra.
Qed.

(* Being a triple word survives a change of sign: each of the two tests is    *)
(* the double-word one, and that one survives it.                             *)
Lemma Dwf_negE a b : Dfin a -> Dfin b ->
  ((- a) + (- b) =? (- a))%float = (a + b =? a)%float.
Proof. exact: wellFormed_negE. Qed.

Lemma wellFormed_negT x0 x1 x2 : Dfin x0 -> Dfin x1 -> Dfin x2 ->
  wellFormed (TWFloat (- x0) (- x1) (- x2))%float =
  wellFormed (TWFloat x0 x1 x2).
Proof.
by move=> F0 F1 F2; rewrite /wellFormed (Dwf_negE _ _ F0 F1) (Dwf_negE _ _ F1 F2).
Qed.

(* So a negated triple falls in the mirror class.                             *)
Lemma classify_neg x :
  classify (neg x) =
  match classify x with
  | Freal => Freal | Sig.Fnan => Sig.Fnan
  | Fminfty => Fpinfty | Fpinfty => Fminfty
  end.
Proof.
case: x => x0 x1 x2.
rewrite /neg /negTw /classify /classifyFp /wellFormed !Dclassify_opp.
have Hw : Dfin x0 -> Dfin x1 -> Dfin x2 ->
   ((((- x0) + (- x1) =? (- x0)) && ((- x1) + (- x2) =? (- x1))))%float =
   ((x0 + x1 =? x0) && (x1 + x2 =? x1))%float
  by move=> F0 F1 F2; rewrite (Dwf_negE _ _ F0 F1) (Dwf_negE _ _ F1 F2).
have Hf : forall g,
   match PrimFloat.classify g with
   | PInf | NInf | NaN => True | _ => Dfin g end.
  move=> g; case Ec: (PrimFloat.classify g) => //;
  by apply: DfinbW; rewrite /Dfinb PrimitiveFloat.classify_correct
                            /PrimitiveFloat.classify Ec.
by case E0: (PrimFloat.classify x0) => //=;
   case E1: (PrimFloat.classify x1) => //=;
   case E2: (PrimFloat.classify x2) => //=;
   (rewrite Hw;
     [by case: (((x0 + x1 =? x0) && (x1 + x2 =? x1))%float)
     | by have := Hf x0; rewrite E0 | by have := Hf x1; rewrite E1
     | by have := Hf x2; rewrite E2]).
Qed.

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
have [F0 [F1 [F2 Ew]]] := real_fin _ Rx.
move: F0 F1 F2 Ew; case: x Rx E => x0 x1 x2 Rx E F0 F1 F2 Ew.
rewrite (toX_real _ Rx) /toX /toF /neg /negTw.
rewrite (_ : wellFormed (TWFloat (- x0) (- x1) (- x2))%float = true);
  last by rewrite wellFormed_negT.
rewrite !Fadd_exact_correct (toXE _ (Dfin_opp _ F0)) (toXE _ (Dfin_opp _ F1))
        (toXE _ (Dfin_opp _ F2)).
by rewrite /= !D2R_opp; congr Xreal; ring.
Qed.

Lemma abs_correct x :
  toX (abs x) = Xabs (toX x) /\ valid_ub (abs x) = true.
Proof.
split; last exact: valid_ub_onReal.
rewrite /abs /onReal.
case Rx: (real x); last first.
  have -> : toX x = Xnan by move: Rx; rewrite real_correct; case: (toX x).
  by rewrite toX_nan.
have [F0 [F1 [F2 Ew]]] := real_fin _ Rx.
have Hle : (Rabs (D2R (tw1 x) + D2R (tw2 x)) <= Rabs (D2R (tw0 x)))%R.
  by move: F0 F1 F2 Ew {Rx}; case: x => a b c; exact: wellFormed_lead.
have [Hn Hp] := Dget_sign _ F0.
case E: (PrimFloat.get_sign (tw0 x)); last first.
  rewrite /guard Rx (toX_real _ Rx) /=.
  by congr Xreal; rewrite Rabs_right //; apply: Rle_ge;
     move: (Hp E) Hle; split_Rabs; lra.
have Rn : real (negTw x) = true.
  by move: Rx; rewrite /real classify_neg; case: (classify x).
have Hneg : toX (negTw x) = (- toX x)%XR.
  by have := neg_correct x; rewrite /neg; move: Rx; rewrite /real;
     case: (classify x).
rewrite /guard Rn Hneg (toX_real _ Rx) /=.
by congr Xreal; rewrite Rabs_left1; [ring | move: (Hn E) Hle; split_Rabs; lra].
Qed.

(* ---------------------------------------------------------------------------*)
(*  The value read exactly, as a whole number times a power of two            *)
(* ---------------------------------------------------------------------------*)

(* Bringing a whole number down to a smaller power of two is a shift, and a   *)
(* shift is a multiplication.                                                 *)
Lemma shiftl_bpow m k e : (0 <= k)%Z ->
  (IZR (Z.shiftl m k) * bpow radix2 e = IZR m * bpow radix2 (k + e))%R.
Proof.
move=> Hk; rewrite Z.shiftl_mul_pow2 // mult_IZR (IZR_Zpower radix2 _ Hk).
by rewrite bpow_plus; ring.
Qed.

(* A float that is a number is the whole number `fZ' gives times the power    *)
(* `fZ' gives, and exactly so.                                                *)
Lemma fZ_val f : Dfin f ->
  (IZR (fst (fZ f)) * bpow radix2 (snd (fZ f)) = D2R f)%R.
Proof.
move=> Ff; have := toXE _ Ff; rewrite -/(PrimitiveFloat.toX f) /PrimitiveFloat.toX.
rewrite /fZ; case: (PrimitiveFloat.toF f) => [|| s m e] //=.
  by case=> <-; rewrite /=; ring.
by rewrite FtoR_split /F2R /=; case=> <-.
Qed.

(* And a triple word is the sum of its three, brought to the smallest of the  *)
(* three powers, where they add as whole numbers.                             *)
Lemma twZ_val t : finL (tw2l t) ->
  (IZR (fst (twZ t)) * bpow radix2 (snd (twZ t)) = twval t)%R.
Proof.
case: t => x0 x1 x2 [F0 [F1 [F2 _]]].
have V0 := fZ_val _ F0; have V1 := fZ_val _ F1; have V2 := fZ_val _ F2.
rewrite /twZ /twval /=.
case: (fZ x0) V0 => m0 e0 V0; case: (fZ x1) V1 => m1 e1 V1.
case: (fZ x2) V2 => m2 e2 V2 /=.
set e := Z.min e0 (Z.min e1 e2).
have H0 : (0 <= e0 - e)%Z by rewrite /e; have := Z.le_min_l e0 (Z.min e1 e2); lia.
have H1 : (0 <= e1 - e)%Z.
  rewrite /e; have := Z.le_min_r e0 (Z.min e1 e2).
  by have := Z.le_min_l e1 e2; lia.
have H2 : (0 <= e2 - e)%Z.
  rewrite /e; have := Z.le_min_r e0 (Z.min e1 e2).
  by have := Z.le_min_r e1 e2; lia.
rewrite !plus_IZR !Rmult_plus_distr_r.
rewrite (shiftl_bpow _ _ _ H0) (shiftl_bpow _ _ _ H1) (shiftl_bpow _ _ _ H2).
have -> : (e0 - e + e = e0)%Z by lia.
have -> : (e1 - e + e = e1)%Z by lia.
have -> : (e2 - e + e = e2)%Z by lia.
by rewrite V0 V1 V2.
Qed.

(* So two triple words compare as the two whole numbers do, and that is the   *)
(* order of the values with nothing rounded and nothing assumed.              *)
Lemma cmpZ_correct t u : finL (tw2l t) -> finL (tw2l u) ->
  cmpZ t u = Rcompare (twval t) (twval u).
Proof.
move=> Ft Fu; have Vt := twZ_val _ Ft; have Vu := twZ_val _ Fu.
rewrite /cmpZ.
case: (twZ t) Vt => a ea Vt; case: (twZ u) Vu => b eb Vu /=.
set e := Z.min ea eb.
have Ha : (0 <= ea - e)%Z by rewrite /e; have := Z.le_min_l ea eb; lia.
have Hb : (0 <= eb - e)%Z by rewrite /e; have := Z.le_min_r ea eb; lia.
have He : forall m k, (0 <= k)%Z ->
    (IZR m * bpow radix2 (k + e) = IZR (Z.shiftl m k) * bpow radix2 e)%R.
  by move=> m k Hk; rewrite (shiftl_bpow _ _ _ Hk).
rewrite -Vt -Vu /=.
have -> : (IZR a * bpow radix2 ea = IZR (Z.shiftl a (ea - e)) * bpow radix2 e)%R.
  by rewrite -(He a _ Ha); congr (IZR a * bpow radix2 _)%R; lia.
have -> : (IZR b * bpow radix2 eb = IZR (Z.shiftl b (eb - e)) * bpow radix2 e)%R.
  by rewrite -(He b _ Hb); congr (IZR b * bpow radix2 _)%R; lia.
by rewrite (Rcompare_mult_r _ _ _ (bpow_gt_0 radix2 e)) Rcompare_IZR.
Qed.

(* ---------------------------------------------------------------------------*)
(*  And what the cheap test is worth when it answers                          *)
(* ---------------------------------------------------------------------------*)

(* Two floats that compare equal and are both numbers stand for the same      *)
(* number.                                                                    *)
Lemma Deqb a b : (a =? b)%float = true -> Dfin a -> Dfin b -> D2R a = D2R b.
Proof.
rewrite eqb_equiv /Dfin /D2R => H Fa Fb.
by move: H; rewrite (Beqb_correct _ _ _ _ Fa Fb); case: Req_bool_spec.
Qed.

(* What the last two words can be worth, rounded up, is at or above what      *)
(* they are worth.                                                            *)
Lemma tailUp_ge t : Dfin (tailUp t) ->
  (Rabs (D2R (tw1 t) + D2R (tw2 t)) <= D2R (tailUp t))%R.
Proof.
move=> Fu; rewrite /tailUp in Fu *.
have Fs := Dfin_upI _ _ Fu.
have [F1 F2] := Dfin_addI _ _ Fs.
have H := addUpFp_ge _ _ F1 F2 Fs Fu.
rewrite !D2R_abs in H.
have T := Rabs_triang (D2R (tw1 t)) (D2R (tw2 t)).
by lra.
Qed.

(* WHEN THE CHEAP TEST ANSWERS IT IS RIGHT, and `Xund' is it declining to     *)
(* answer rather than saying anything about the two.                          *)
Lemma cmpFast_correct x y : finL (tw2l x) -> finL (tw2l y) ->
  match cmpFast x y with
  | Xeq => twval x = twval y
  | Xlt => (twval x < twval y)%R
  | Xgt => (twval y < twval x)%R
  | Xund => True
  end.
Proof.
move=> Fx Fy.
have [F0 [F1 F2]] := tw2l_finLI _ Fx.
have [G0 [G1 G2]] := tw2l_finLI _ Fy.
rewrite /cmpFast.
case E: (((tw0 x =? tw0 y) && (tw1 x =? tw1 y) && (tw2 x =? tw2 y))%float).
  move: E => /andb_prop [/andb_prop [E0 E1] E2].
  by rewrite /twval (Deqb _ _ E0 F0 G0) (Deqb _ _ E1 F1 G1)
             (Deqb _ _ E2 F2 G2).
(* What the two tails can be worth together.                                  *)
have Hs : Dfin (tailBoth x y) ->
  (Rabs (D2R (tw1 x) + D2R (tw2 x)) + Rabs (D2R (tw1 y) + D2R (tw2 y))
   <= D2R (tailBoth x y))%R.
  rewrite /tailBoth => Fs; have Fa := Dfin_upI _ _ Fs.
  have [Fu Fv] := Dfin_addI _ _ Fa.
  have H := addUpFp_ge _ _ Fu Fv Fa Fs.
  have Hu := tailUp_ge _ Fu; have Hv := tailUp_ge _ Fv.
  by lra.
(* The leading words, both ways, and what is left after the tails.            *)
rewrite /cmpBand.
case Eg: (posFp (subDnFp (subDnFp (tw0 x) (tw0 y)) (tailBoth x y))).
  have [Fd Hd] := posFpP _ Eg.
  have Fw := Dfin_dnFpI _ Fd.
  have [Flo Fs] := Dfin_subI _ _ Fw.
  have Hlo : (D2R (subDnFp (tw0 x) (tw0 y)) <= D2R (tw0 x) - D2R (tw0 y))%R.
    by apply: subDnFp_le => //; apply: Dfin_dnFpI Flo.
  have H := subDnFp_le _ _ Flo Fs Fw Fd.
  by move: (Hs Fs) Hd Hlo H; rewrite /twval; split_Rabs; lra.
case El: (posFp (subDnFp (- subUpFp (tw0 x) (tw0 y))%float (tailBoth x y)));
  last by [].
have [Fd Hd] := posFpP _ El.
have Fw := Dfin_dnFpI _ Fd.
have [Fno Fs] := Dfin_subI _ _ Fw.
have Fhi := Dfin_oppI _ Fno.
have Hhi : (D2R (tw0 x) - D2R (tw0 y) <= D2R (subUpFp (tw0 x) (tw0 y)))%R.
  by apply: subUpFp_ge => //; apply: Dfin_upFpI Fhi.
have H := subDnFp_le _ _ Fno Fs Fw Fd.
rewrite D2R_opp in H.
by move: (Hs Fs) Hd Hhi H; rewrite /twval; split_Rabs; lra.
Qed.

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
Proof.
rewrite /cmp; case Ex: (classify x) => //; case Ey: (classify y) => //.
have Rx : real x = true by rewrite /real Ex.
have Ry : real y = true by rewrite /real Ey.
have [F0 [F1 [F2 _]]] := real_fin _ Rx.
have [G0 [G1 [G2 _]]] := real_fin _ Ry.
have Flx := finL_tw2l _ F0 F1 F2; have Fly := finL_tw2l _ G0 G1 G2.
rewrite (toX_real _ Rx) (toX_real _ Ry) /=.
have := cmpFast_correct _ _ Flx Fly.
case: (cmpFast x y) => H.
- by rewrite (Rcompare_Eq _ _ H).
- by rewrite (Rcompare_Lt _ _ H).
- by rewrite (Rcompare_Gt _ _ H).
by rewrite (cmpZ_correct _ _ Flx Fly); case: Rcompare.
Qed.

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
Proof.
rewrite /min; case Ex: (classify x); case Ey: (classify y);
  rewrite ?(cmp_correct x y) ?Ex ?Ey //=.
have Rx : real x = true by rewrite /real Ex.
have Ry : real y = true by rewrite /real Ey.
have [a Ea] : exists a, toX x = Xreal a by eexists; exact: toX_real.
have [b Eb] : exists b, toX y = Xreal b by eexists; exact: toX_real.
rewrite Ea Eb /Xcmp /Xmin.
case: Rcompare_spec => H; rewrite ?Ea ?Eb; congr Xreal.
- by rewrite Rbasic_fun.Rmin_left //; lra.
- by rewrite Rbasic_fun.Rmin_right //; lra.
by rewrite Rbasic_fun.Rmin_right //; lra.
Qed.

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
Proof.
rewrite /max; case Ex: (classify x); case Ey: (classify y);
  rewrite ?(cmp_correct x y) ?Ex ?Ey //=.
have Rx : real x = true by rewrite /real Ex.
have Ry : real y = true by rewrite /real Ey.
have [a Ea] : exists a, toX x = Xreal a by eexists; exact: toX_real.
have [b Eb] : exists b, toX y = Xreal b by eexists; exact: toX_real.
rewrite Ea Eb /Xcmp /Xmax.
case: Rcompare_spec => H; rewrite ?Ea ?Eb; congr Xreal.
- by rewrite Rbasic_fun.Rmax_right //; lra.
- by rewrite Rbasic_fun.Rmax_left //; lra.
by rewrite Rbasic_fun.Rmax_left //; lra.
Qed.

Lemma add_UP_correct p x y :
  valid_ub x = true -> valid_ub y = true ->
  valid_ub (add_UP p x y) = true /\
  le_upper (toX x + toX y)%XR (toX (add_UP p x y)).
Proof. by move=> _ _; split; [exact: valid_ub_onReal2|exact: add_UP_le]. Qed.

Lemma add_DN_correct p x y :
  valid_lb x = true -> valid_lb y = true ->
  valid_lb (add_DN p x y) = true /\
  le_lower (toX (add_DN p x y)) (toX x + toX y)%XR.
Proof. by move=> _ _; split; [exact: valid_lb_onReal2|exact: add_DN_le]. Qed.

Lemma sub_UP_correct p x y :
  valid_ub x = true -> valid_lb y = true ->
  valid_ub (sub_UP p x y) = true /\
  le_upper (toX x - toX y)%XR (toX (sub_UP p x y)).
Proof.
move=> _ _; split; first exact: valid_ub_onReal2.
rewrite /sub_UP; apply: (onReal2_upper (fun a b => (toX a - toX b)%XR)) => a b Ra Rb Rr.
have [F0 [F1 [F2 _]]] := real_fin _ Ra.
have [G0 [G1 [G2 _]]] := real_fin _ Rb.
have [H0 [H1 [H2 _]]] := real_fin _ Rr.
rewrite (toX_real _ Ra) (toX_real _ Rb) (toX_real _ Rr) /=.
by apply: subTwUp_ge; apply: finL_tw2l.
Qed.

Lemma sub_DN_correct p x y :
  valid_lb x = true -> valid_ub y = true ->
  valid_lb (sub_DN p x y) = true /\
  le_lower (toX (sub_DN p x y)) (toX x - toX y)%XR.
Proof.
move=> _ _; split; first exact: valid_lb_onReal2.
rewrite /sub_DN; apply: (onReal2_lower (fun a b => (toX a - toX b)%XR)) => a b Ra Rb Rr.
have [F0 [F1 [F2 _]]] := real_fin _ Ra.
have [G0 [G1 [G2 _]]] := real_fin _ Rb.
have [H0 [H1 [H2 _]]] := real_fin _ Rr.
rewrite (toX_real _ Ra) (toX_real _ Rb) (toX_real _ Rr) /le_lower /=.
by apply: Ropp_le_contravar; apply: subTwDn_le; apply: finL_tw2l.
Qed.

Lemma mul_UP_correct p x y :
  is_non_neg' x /\ is_non_neg' y \/ is_non_pos' x /\ is_non_pos' y \/
  is_non_pos_real x /\ is_non_neg_real y \/
  is_non_neg_real x /\ is_non_pos_real y ->
  valid_ub (mul_UP p x y) = true /\
  le_upper (toX x * toX y)%XR (toX (mul_UP p x y)).
Proof.
move=> _; split; first exact: valid_ub_onReal2.
rewrite /mul_UP; apply: (onReal2_upper (fun a b => (toX a * toX b)%XR)) => a b Ra Rb Rr.
have [F0 [F1 [F2 _]]] := real_fin _ Ra.
have [G0 [G1 [G2 _]]] := real_fin _ Rb.
have [H0 [H1 [H2 _]]] := real_fin _ Rr.
rewrite (toX_real _ Ra) (toX_real _ Rb) (toX_real _ Rr) /=.
by apply: mulTwUp_ge; apply: finL_tw2l.
Qed.

Lemma mul_DN_correct p x y :
  is_non_neg_real x /\ is_non_neg_real y \/
  is_non_pos_real x /\ is_non_pos_real y \/
  is_non_neg' x /\ is_non_pos' y \/ is_non_pos' x /\ is_non_neg' y ->
  valid_lb (mul_DN p x y) = true /\
  le_lower (toX (mul_DN p x y)) (toX x * toX y)%XR.
Proof.
move=> _; split; first exact: valid_lb_onReal2.
rewrite /mul_DN; apply: (onReal2_lower (fun a b => (toX a * toX b)%XR)) => a b Ra Rb Rr.
have [F0 [F1 [F2 _]]] := real_fin _ Ra.
have [G0 [G1 [G2 _]]] := real_fin _ Rb.
have [H0 [H1 [H2 _]]] := real_fin _ Rr.
rewrite (toX_real _ Ra) (toX_real _ Rb) (toX_real _ Rr) /le_lower /=.
by apply: Ropp_le_contravar; apply: mulTwDn_le; apply: finL_tw2l.
Qed.

Lemma pow2_UP_correct p s :
  valid_ub (pow2_UP p s) = true /\
  le_upper (Xscale radix2 (Xreal 1) (StoZ s)) (toX (pow2_UP p s)).
Proof.
rewrite /pow2_UP toX_fp2tw.
have [Hv Hb] := PrimitiveFloat.pow2_UP_correct fprec s.
by split => //; apply: valid_ub_fp2tw.
Qed.

(* A quotient by nought denotes nothing, and the guard on the divisor is what *)
(* says the divisor is not nought.                                            *)
Lemma XdivE a b : b <> 0%R -> (Xreal a / Xreal b)%XR = Xreal (a / b).
Proof. by move=> Hb; rewrite /Xbind2 /Xdiv' (is_zero_false _ Hb). Qed.

(* THE FOUR THAT LEAN ON THE MEASURED STEP.  Everything below the line the    *)
(* reading draws is proved, and so now is the step the two operations add    *)
(* in `twpaper.v', and those two are named so that `Print Assumptions' on any *)
(* of the four says which.                                                    *)
Lemma div_UP_correct p x y :
  is_real_ub x /\ is_pos_real y \/ is_real_lb x /\ is_neg_real y ->
  valid_ub (div_UP p x y) = true /\
  le_upper (toX x / toX y)%XR (toX (div_UP p x y)).
Proof.
move=> _; split; first exact: valid_ub_onReal2.
apply: (onReal2_upper (fun x y => (toX x / toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [F0 [F1 [F2 Wx]]] := real_fin _ Rx.
have [G0 [G1 [G2 Wy]]] := real_fin _ Ry.
have [H0 [H1 [H2 _]]] := real_fin _ Rz.
have Flz := finL_tw2l _ H0 H1 H2.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz).
rewrite (XdivE _ _ (divTwUpK_nz _ _ (finL_tw2l _ G0 G1 G2) Flz)) /=.
by apply: divTwUpK_ge => //; apply: finL_tw2l.
Qed.

Lemma div_DN_correct p x y :
  is_real_ub x /\ is_neg_real y \/ is_real_lb x /\ is_pos_real y ->
  valid_lb (div_DN p x y) = true /\
  le_lower (toX (div_DN p x y)) (toX x / toX y)%XR.
Proof.
move=> _; split; first exact: valid_lb_onReal2.
apply: (onReal2_lower (fun x y => (toX x / toX y)%XR)) => {p}{}x{}y Rx Ry Rz.
have [F0 [F1 [F2 Wx]]] := real_fin _ Rx.
have [G0 [G1 [G2 Wy]]] := real_fin _ Ry.
have [H0 [H1 [H2 _]]] := real_fin _ Rz.
have Flz := finL_tw2l _ H0 H1 H2.
rewrite (toX_real _ Rx) (toX_real _ Ry) (toX_real _ Rz).
rewrite (XdivE _ _ (divTwDnK_nz _ _ (finL_tw2l _ G0 G1 G2) Flz)) /le_lower /=.
by apply: Ropp_le_contravar; apply: divTwDnK_le => //; apply: finL_tw2l.
Qed.

Lemma sqrt_UP_correct p x :
  valid_ub (sqrt_UP p x) = true /\
  le_upper (Xsqrt (toX x)) (toX (sqrt_UP p x)).
Proof.
split; first exact: valid_ub_onReal.
apply: (onReal_upper (fun x => Xsqrt (toX x))) => {p}{}x Rx Rz.
have [F0 [F1 [F2 Wx]]] := real_fin _ Rx.
have [H0 [H1 [H2 _]]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Rz) /=.
by apply: sqrtTwUpK_ge => //; apply: finL_tw2l.
Qed.

Lemma sqrt_DN_correct p x :
  valid_lb x = true ->
  valid_lb (sqrt_DN p x) = true /\
  le_lower (toX (sqrt_DN p x)) (Xsqrt (toX x)).
Proof.
move=> _; split; first exact: valid_lb_onReal.
apply: (onReal_lower (fun x => Xsqrt (toX x))) => {p}{}x Rx Rz.
have [F0 [F1 [F2 Wx]]] := real_fin _ Rx.
have [H0 [H1 [H2 _]]] := real_fin _ Rz.
rewrite (toX_real _ Rx) (toX_real _ Rz) /le_lower /=.
by apply: Ropp_le_contravar; apply: sqrtTwDnK_le => //; apply: finL_tw2l.
Qed.

(* Rounding to a whole number is monotone, so the three words added in the    *)
(* direction wanted, rounded to a whole number in the same direction, is on   *)
(* the right side of the value's own.  Two widening steps rather than the     *)
(* one a pair needs, and they compose.                                       *)
Lemma nearbyint_UP_correct mode x :
  valid_ub (nearbyint_UP mode x) = true /\
  le_upper (Xnearbyint mode (toX x)) (toX (nearbyint_UP mode x)).
Proof.
split; first exact: valid_ub_onReal.
rewrite /nearbyint_UP /onReal.
case Rx: (real x); last first.
  by have -> : toX x = Xnan by move: Rx; rewrite real_correct; case: (toX x).
have [F0 [F1 [F2 _]]] := real_fin _ Rx.
set u := addUpFp (addUpFp (tw0 x) (tw1 x)) (tw2 x).
rewrite /guard.
case Er: (real (fp2tw (PrimitiveFloat.nearbyint_UP mode u)));
  last by rewrite toX_nan.
rewrite toX_fp2tw (toX_real _ Rx).
have [_ Hb] := PrimitiveFloat.nearbyint_UP_correct mode u.
move: Hb; case Es: (PrimitiveFloat.toX u) => [|w] /=;
  first by move: Er; rewrite real_correct toX_fp2tw;
     case: (PrimitiveFloat.toX _).
move=> Hb.
have [Fu Ew] := toX_D2R _ _ Es.
have Fs2 := Dfin_upI _ _ Fu.
have [Fv F2'] := Dfin_addI _ _ Fs2.
have Hge1 := addUpFp_ge _ _ F0 F1 (Dfin_upI _ _ Fv) Fv.
have Hge2 := addUpFp_ge _ _ Fv F2' Fs2 Fu.
move: Hb; case: (PrimitiveFloat.toX _) => //= z Hb.
apply: Rle_trans Hb; apply: Rnearbyint_le.
by rewrite -Ew; move: Hge1 Hge2; rewrite /u; lra.
Qed.

Lemma nearbyint_DN_correct mode x :
  valid_lb (nearbyint_DN mode x) = true /\
  le_lower (toX (nearbyint_DN mode x)) (Xnearbyint mode (toX x)).
Proof.
split; first exact: valid_lb_onReal.
rewrite /nearbyint_DN /onReal.
case Rx: (real x); last first.
  by have -> : toX x = Xnan by move: Rx; rewrite real_correct; case: (toX x).
have [F0 [F1 [F2 _]]] := real_fin _ Rx.
set u := addDnFp (addDnFp (tw0 x) (tw1 x)) (tw2 x).
rewrite /guard.
case Er: (real (fp2tw (PrimitiveFloat.nearbyint_DN mode u)));
  last by rewrite toX_nan.
rewrite toX_fp2tw (toX_real _ Rx).
have [_ Hb] := PrimitiveFloat.nearbyint_DN_correct mode u.
move: Hb; case Es: (PrimitiveFloat.toX u) => [|w] /=;
  first by move: Er; rewrite real_correct toX_fp2tw;
     case: (PrimitiveFloat.toX _).
move=> Hb.
have [Fu Ew] := toX_D2R _ _ Es.
have Fs2 := Dfin_dnI _ _ Fu.
have [Fv F2'] := Dfin_addI _ _ Fs2.
have Hle1 := addDnFp_le _ _ F0 F1 (Dfin_dnI _ _ Fv) Fv.
have Hle2 := addDnFp_le _ _ Fv F2' Fs2 Fu.
have Hm : (Rnearbyint mode w <=
           Rnearbyint mode (D2R (tw0 x) + D2R (tw1 x) + D2R (tw2 x)))%R.
  by apply: Rnearbyint_le; rewrite -Ew; move: Hle1 Hle2; rewrite /u; lra.
move: Hb; rewrite /le_lower /=; case: (PrimitiveFloat.toX _) => //= z Hb.
by move: Hb Hm; lra.
Qed.

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
