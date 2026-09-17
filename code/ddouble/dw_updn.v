From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.
From Stdlib Require Import ZArith.
From dwarith Require Import dwarith.

(* Directed rounding for double words.                                        *)
(* An interval bound must never fall on the wrong side of the exact result,   *)
(* so each operation returns its own error bound and widens by it.  The       *)
(* bounds are computed from the intermediates the algorithm has just made,    *)
(* never from a constant, so nothing here has to be trusted in advance.       *)

Implicit Type d : dwfloat.
Implicit Type f : float.

(* The unit roundoff of binary64, 2^-53.  A rounded sum or product differs    *)
(* from the exact one by at most u times the rounded value.                   *)
Definition u := Eval compute in (1 / 9007199254740992)%float.

(* One step up, and one step down.  A step up from minus infinity would       *)
(* give a number back, and a step down from plus infinity likewise, which     *)
(* would hide the fact that something ran off the range.  So a step that      *)
(* meets the infinity it would undo leaves it alone: the infinity then        *)
(* travels to the end of the computation, where it is seen.                   *)
Definition upFp s := if (s =? neg_infinity)%float then s else next_up s.
Definition dnFp s := if (s =? infinity)%float then s else next_down s.

(* Upper and lower bounds of the three operations, whatever the rounding did. *)
Definition addUpFp a b := upFp (a + b)%float.
Definition addDnFp a b := dnFp (a + b)%float.
Definition mulUpFp a b := upFp (a * b)%float.
Definition mulDnFp a b := dnFp (a * b)%float.
Definition divUpFp a b := upFp (a / b)%float.
Definition divDnFp a b := dnFp (a / b)%float.

(* The high word of a double word carries its value, the low word its tail.   *)
Definition dwhi d := let: DWFloat xh _ := d in xh.
Definition dwlo d := let: DWFloat _ xl := d in xl.

(* Widening a double word by a positive amount, upwards and downwards.        *)
(* The final twoSum only tidies the pair; it changes no value, and it asks    *)
(* nothing of its two arguments, which a fastTwoSum would.                    *)
Definition widenUp d f :=
  let: DWFloat zh zl := d in twoSum zh (addUpFp zl f).
Definition widenDn d f :=
  let: DWFloat zh zl := d in twoSum zh (addDnFp zl (- f)).

(* The sum of two double words, together with a bound on its error.  The two  *)
(* twoSum and the two fastTwoSum are exact, so the whole error is the         *)
(* rounding of c and the rounding of w, each at most u times its result.      *)
Definition plusDwDwErr (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat sh sl := twoSum xh yh in
  let: DWFloat th tl := twoSum xl yl in
  let: c := (sl + th)%float in
  let: DWFloat vh vl := fastTwoSum sh c in
  let: w := (tl + vl)%float in
  let: e := mulUpFp u (addUpFp (abs c) (abs w)) in
  (fastTwoSum vh w, e).

(* The sum of two double words, bounded above.  The two twoSum are exact, so  *)
(* the exact sum is sh + sl + th + tl with all four numbers in hand, and the  *)
(* last twoSum is exact too.  So the only thing that can miss is the adding   *)
(* of the three small ones, and adding them upwards settles that.  Nothing    *)
(* is estimated and no error bound is needed.                                 *)
(*                                                                            *)
(* WHEN BOTH LOW WORDS ARE NOUGHT THE SUM IS EXACT, and the first line says   *)
(* so.  The twoSum of the two high words is the whole answer then, and the    *)
(* widening step is not just needless but harmful: `next_up' of nought is     *)
(* the smallest number there is, so the answer would carry a subnormal low    *)
(* word where the true low word is nought.  Divide by such a pair and the     *)
(* division's guard fails on `yl * t' at once -- which is what it cost.  The  *)
(* line is also the cheaper of the two, since it leaves out the second        *)
(* twoSum, the two widening steps and the last twoSum.                        *)
Definition addDwUp (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  if ((xl =? 0) && (yl =? 0))%float then twoSum xh yh else
  let: DWFloat sh sl := twoSum xh yh in
  let: DWFloat th tl := twoSum xl yl in
  twoSum sh (addUpFp (addUpFp sl th) tl).

Definition addDwDn (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  if ((xl =? 0) && (yl =? 0))%float then twoSum xh yh else
  let: DWFloat sh sl := twoSum xh yh in
  let: DWFloat th tl := twoSum xl yl in
  twoSum sh (addDnFp (addDnFp sl th) tl).

(* Negating a double word is exact, so subtraction is addition.               *)
Definition negDw d := let: DWFloat xh xl := d in DWFloat (- xh) (- xl).

Definition subDwUp x y := addDwUp x (negDw y).
Definition subDwDn x y := addDwDn x (negDw y).

(* Two lines on the range.  Two to the minus one thousand and twenty-two is   *)
(* the smallest normal number; two to the minus nine hundred and sixty-nine   *)
(* is where the two-product stops being exact.  Both are used twice below:    *)
(* by the products, to know when nothing has to be added for what the         *)
(* two-product may have missed, and by the division's guard.                  *)
Definition dnorm := Eval compute in 0x1p-1022%float.
Definition dprodlo := Eval compute in 0x1p-969%float.

(* Four times the smallest number there is.  The two-product can miss the     *)
(* product it is given, but never by more than three and a half of those,     *)
(* so a step of this size covers it wherever it happens.                      *)
Definition deps := Eval compute in 0x1p-1072%float.

(* The product of two double words, bounded above.  The product of the two    *)
(* high words comes back as two numbers that all but add up to it, and the    *)
(* three remaining products are each rounded upwards, so every piece is at    *)
(* or above the piece it stands for.  Adding them upwards, and the step       *)
(* above for what the two-product may have missed, keeps that true, and       *)
(* the last twoSum changes no value.  Nothing is estimated.                   *)
(*                                                                            *)
(* AND WHEN BOTH LOW WORDS ARE NOUGHT AND THE TWO-PRODUCT IS EXACT, so is     *)
(* the product, and the first line says so.  The two-product is exact above   *)
(* `dprodlo', which is what the third test asks of its high word, and then    *)
(* the pair it returns adds up to the product outright.  Without this line    *)
(* `mulDwUp (DWFloat 1 0) (DWFloat 1 0)' comes back with a low word of        *)
(* eleven of the smallest numbers there are, all of it `next_up' noise, and   *)
(* a pair like that fails the division's guard on `yl * t'.                   *)
Definition mulDwUp (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat ch cl := twoProd xh yh in
  if ((xl =? 0) && (yl =? 0) && (dprodlo <? abs ch))%float then DWFloat ch cl
  else
  twoSum ch (addUpFp (addUpFp (addUpFp cl (mulUpFp xh yl))
                              (addUpFp (mulUpFp xl yh) (mulUpFp xl yl)))
                     deps).

Definition mulDwDn (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat ch cl := twoProd xh yh in
  if ((xl =? 0) && (yl =? 0) && (dprodlo <? abs ch))%float then DWFloat ch cl
  else
  twoSum ch (addDnFp (addDnFp (addDnFp cl (mulDnFp xh yl))
                              (addDnFp (mulDnFp xl yh) (mulDnFp xl yl)))
                     (- deps)).

(* How small a double word can be, from its two words alone: a sum is at      *)
(* least the first term less the second, in absolute value, and the step      *)
(* down keeps that true.                                                      *)
Definition magDnDw d :=
  let: DWFloat yh yl := d in dnFp (abs yh - abs yl)%float.

(* A number is a usable divisor when it is above zero and not an infinity.    *)
(* Both tests are needed: an infinity passes the first one and stands for     *)
(* no number at all.                                                          *)
Definition posFp m := ((0 <? m) && (m <? infinity))%float.

(* The quotient is not bounded by an analysis of its own algorithm but by     *)
(* its residual: whatever q is, the true quotient is within the distance      *)
(* |x - q*y| / |y| of it.  So the algorithm that produced q is free to be     *)
(* anything at all, and only the residual is computed with care - bounded     *)
(* on both sides, its two words added in absolute value, and divided by a     *)
(* divisor made smaller.  When the divisor cannot be told from zero there     *)
(* is nothing to say, and nothing is what comes back.                         *)
Definition divDwErr (x y : dwfloat) :=
  let: m := magDnDw y in
  let: q := divDwDw2 x y in
  let: rup := subDwUp x (mulDwDn q y) in
  let: rdn := subDwDn x (mulDwUp q y) in
  let: r := addUpFp (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
                    (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))) in
  (q, divUpFp r m, m).

Definition divDwUp (x y : dwfloat) :=
  let: (d, e, m) := divDwErr x y in
  if posFp m then widenUp d e else DWFloat nan nan.
Definition divDwDn (x y : dwfloat) :=
  let: (d, e, m) := divDwErr x y in
  if posFp m then widenDn d e else DWFloat nan nan.

(* ===========================================================================*)
(*  The same bound as a shift of so many units in the last place              *)
(* ===========================================================================*)

(* The residual above computes how wrong the answer is: the product of the    *)
(* answer with the divisor, taken both ways, subtracted from what was to be   *)
(* divided, and divided by the divisor.  Four double-word operations.         *)
(* Measured on 200000 divisions, twice each: the quotient alone 0.22 seconds, *)
(* the quotient with its guard and its shift 0.29, the quotient with its      *)
(* residual 2.15.  So the shift costs a third over the bare division, and the *)
(* residual costs ten times it.                                               *)
(*                                                                            *)
(* None of that is needed.  Each of these algorithms is known to be within a  *)
(* fixed number of units in the last place, so the enclosure is the answer     *)
(* shifted that far up and that far down - which is exactly what Interval's   *)
(* own primitive-float module does, `next_up (x + y)', one level down.        *)
(*                                                                            *)
(* SIXTEEN, and where it comes from.  The double-word paper proves the sum     *)
(* within three of the square of the unit roundoff, the product within about   *)
(* five and the quotient within about ten.  Run on two hundred thousand        *)
(* random double words (`c/probek.py'), these very algorithms come out at      *)
(* 1.97, 3.74, 5.82 and 2.14 for the root.  Sixteen is above every one of      *)
(* them and is a power of two, so the shift is an exponent change and exact.   *)
(* Sixteen units of a word a hundred and six bits below the leading one is     *)
(* the leading one shifted down a hundred and two.                            *)
(*                                                                            *)
(* THE SUM NEEDS NO RANGE TEST, THE QUOTIENT DOES.  The sum's proofs in this  *)
(* development are in the bounded format, subnormals and all - `F2SumFLT.v',  *)
(* `TwoSumFLT.v' - so its bound holds everywhere.  The quotient's is the      *)
(* paper's Theorem 7.1, proved in the format with no smallest exponent, so    *)
(* it has to be told that its steps stay out of the subnormal range; that is  *)
(* `divDwDw2G' below.                                                         *)
(*                                                                            *)
(* THE STEP IS A MULTIPLICATION, AND NOT AN EXPONENT SHIFT.  Shifting an      *)
(* exponent is one instruction on the machine, and `FloatOps.Z.ldexp' is      *)
(* exactly that - but inside Rocq's evaluator it is not one instruction at    *)
(* all: it goes through `Z.max', `Z.min' and a conversion of a whole number   *)
(* to a machine integer on every call.  Measured, 4.8 microseconds against    *)
(* 0.2 for a float multiplication, for the same answer - twenty-four times.   *)
(* And the multiplication by this constant is exact anyway, since the         *)
(* constant is a power of two.                                                *)
Definition dscale := Eval compute in 0x1p-102%float.

(* THE STEP IS TAKEN FROM BOTH WORDS, and it has to be.  The paper's bound   *)
(* is relative to the exact quotient, so something computed has to stand for  *)
(* the quotient, and the two words added in absolute value are at or above    *)
(* the answer whatever the low word does.  The high word alone would be       *)
(* enough only if the answer were known to be a double word, which is a       *)
(* further theorem the paper does not leave - see `divDwDw2_step' of          *)
(* dwdivflx.v.  The sweep of `widenUp' is kept, since a seed need not be a    *)
(* double word.                                                               *)
Definition dstep d :=
  let: DWFloat xh xl := d in
  mulUpFp dscale (addUpFp (abs xh) (abs xl)).

Definition shiftUp d := widenUp d (dstep d).
Definition shiftDn d := widenDn d (dstep d).

(* THE RANGE THE ERROR ANALYSIS NEEDS, AND THE TEST FOR IT.  Theorem 7.1 is   *)
(* proved in the format with no smallest exponent, so it says nothing about   *)
(* a step that lands in the subnormal range: down there the bounded format    *)
(* rounds and the other does not.  Four steps of the division can land there  *)
(* - the two quotients, the two-product and the lone product - and the test   *)
(* below is exactly that they do not.  The sum needs no such test, since a    *)
(* sum too small for the bounded format to round is exact and neither format  *)
(* rounds it; a product and a quotient have no such property.                 *)
(*                                                                            *)
(* TWO OF THE FOUR HAVE AN ESCAPE, AND MUST.  The low word of a double word   *)
(* is often nought, and then `yl * t' is nought, which no magnitude test can  *)
(* pass; a division that comes out exact leaves `d' nought, and the same      *)
(* again.  Both formats round nought to nought, so nought serves as well as   *)
(* being normal, and the test says so.                                        *)
(*                                                                            *)
(* The lines are `dnorm' and `dprodlo' above: two to the minus one thousand   *)
(* and twenty-two is the smallest normal number, and two to the minus nine    *)
(* hundred and sixty-nine is where the two-product stops being exact.         *)

(* The test on its own, for the proof to read.  The operation does not use    *)
(* this one: it would compute the division a second time.                     *)
Definition divOk (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: t := (xh / yh)%float in
  let: DWFloat rh rl := timesDwFp1 y t in
  let: d := ((xh - rh) + (xl - rl))%float in
  (dnorm <? abs t)%float && (dprodlo <? abs (yh * t))%float &&
  ((yl =? 0)%float || (dnorm <? abs (yl * t))%float) &&
  ((d =? 0)%float || (dnorm <? abs (d / yh))%float).

(* The division, with its own intermediates tested as they are made.          *)
(* Computing them a second time for the test would cost as much again.        *)
Definition divDwDw2G (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: t := (xh / yh)%float in
  let: DWFloat rh rl := timesDwFp1 y t in
  let: pih := (xh - rh)%float in
  let: dl := (xl - rl)%float in
  let: d := (pih + dl)%float in
  let tl := (d / yh)%float in
  (fastTwoSum t tl,
   (dnorm <? abs t)%float && (dprodlo <? abs (yh * t))%float &&
   ((yl =? 0)%float || (dnorm <? abs (yl * t))%float) &&
   ((d =? 0)%float || (dnorm <? abs tl)%float)).

Lemma divDwDw2GE x y : divDwDw2G x y = (divDwDw2 x y, divOk x y).
Proof.
case: x => xh xl; case: y => yh yl.
by rewrite /divDwDw2G /divOk /divDwDw2; case: (timesDwFp1 _ _).
Qed.

(* WHEN THE TEST FAILS THE RESIDUAL ANSWERS, and that is what keeps the       *)
(* operation total.  The residual form needs no range at all -- it measures   *)
(* how wrong the answer is rather than appealing to a theorem about it -- so  *)
(* it covers exactly the cases the shift cannot.  It costs ten times the      *)
(* division where the shift costs a third, which is why it is the second      *)
(* choice and not the first.                                                  *)
(*                                                                            *)
(* IT IS NOT A RARE PATH.  The two-product stops being exact below two to     *)
(* the minus nine hundred and sixty-nine, and a Taylor model at eighty bits   *)
(* divides numbers smaller than that; without this the tactic loses the goal. *)
(*                                                                            *)
(* Nought divided is nought, and it is worth saying so rather than sending it *)
(* down the slow path: the test cannot pass on a nought numerator, and an     *)
(* interval with nought for an endpoint is not a rare thing.                  *)
Definition divDwUpK (x y : dwfloat) :=
  let: DWFloat xh _ := x in
  if posFp (magDnDw y) then
    if (xh =? 0)%float then DWFloat 0 0
    else let: (q, ok) := divDwDw2G x y in
         if ok then shiftUp q else divDwUp x y
  else DWFloat nan nan.
Definition divDwDnK (x y : dwfloat) :=
  let: DWFloat xh _ := x in
  if posFp (magDnDw y) then
    if (xh =? 0)%float then DWFloat 0 0
    else let: (q, ok) := divDwDw2G x y in
         if ok then shiftDn q else divDwDn x y
  else DWFloat nan nan.

(* The last step of the root halves both words, and HALVING IS NOT EXACT: a   *)
(* word whose last digit is the smallest there is loses that digit.  Doubling *)
(* always is, so a word that comes back from its half doubled is a word whose *)
(* half was exact, and that is what this tests -- two multiplications and two *)
(* comparisons, against an argument about where the bottom of the range is.   *)
Definition halfOk (d : dwfloat) :=
  let: DWFloat a b := d in
  ((a / 2) * 2 =? a)%float && ((b / 2) * 2 =? b)%float.

(* Fast2Sum's own precondition on the last call of the division: the          *)
(* correction is no larger than what it corrects.  That is what makes the     *)
(* answer a double word, which is asked of the arguments of a sum of two      *)
(* double words.  The division does not need it -- its step is read off both  *)
(* words -- but the square root, which adds the quotient to a guess, does.    *)
Definition divDwOk (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: t := (xh / yh)%float in
  let: DWFloat rh rl := timesDwFp1 y t in
  let: d := ((xh - rh) + (xl - rl))%float in
  (abs (d / yh) <=? abs t)%float.

(* The two operations as the proof wants to read them: the test named, and    *)
(* the division named, instead of the one expression that shares them.        *)
Lemma divDwUpKE x y :
  divDwUpK x y =
  (let: DWFloat xh _ := x in
   if posFp (magDnDw y) then
     if (xh =? 0)%float then DWFloat 0 0
     else if divOk x y then shiftUp (divDwDw2 x y) else divDwUp x y
   else DWFloat nan nan).
Proof. by case: x => xh xl; rewrite /divDwUpK divDwDw2GE. Qed.

Lemma divDwDnKE x y :
  divDwDnK x y =
  (let: DWFloat xh _ := x in
   if posFp (magDnDw y) then
     if (xh =? 0)%float then DWFloat 0 0
     else if divOk x y then shiftDn (divDwDw2 x y) else divDwDn x y
   else DWFloat nan nan).
Proof. by case: x => xh xl; rewrite /divDwDnK divDwDw2GE. Qed.

(* How small a double word's value can be, from its two words: the sum of     *)
(* the two, rounded down.                                                     *)
Definition valDnDw d := let: DWFloat h l := d in addDnFp h l.

(* The square root is bounded by its residual too.  Whatever q is, the        *)
(* root and q differ by (x - q*q) / (root + q), and the root is never         *)
(* negative, so the sum below it is q itself - no guess at how good q is      *)
(* enters the bound.  Two tests: q must be above zero to divide by, and so    *)
(* must the number itself, because the root of a negative is taken to be      *)
(* zero and a bound below it would then be a claim about nothing.             *)
Definition sqrtDwErr (x : dwfloat) :=
  let: DWFloat xh xl := x in
  let: q := sqrtDw x in
  let: m := valDnDw q in
  let: rup := subDwUp x (mulDwDn q q) in
  let: rdn := subDwDn x (mulDwUp q q) in
  let: r := addUpFp (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
                    (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))) in
  (q, divUpFp r m, m, (xh + xl)%float).

Definition sqrtDwUp (x : dwfloat) :=
  let: (d, e, m, t) := sqrtDwErr x in
  if posFp m && posFp t then widenUp d e else DWFloat nan nan.
Definition sqrtDwDn (x : dwfloat) :=
  let: (d, e, m, t) := sqrtDwErr x in
  if posFp m && posFp t then widenDn d e else DWFloat nan nan.

(* THE ROOT'S GUARD.  One step of Newton's method is a quotient, a sum and a  *)
(* halving, and each of the three asks something.  The value must be normal,  *)
(* so that the guess has a relative error at all; the quotient must be in     *)
(* range and must come back as a double word, which is what the sum of two    *)
(* double words asks of its arguments; and the halving must be exact.  Four   *)
(* tests, all of them on numbers the operation has computed anyway.           *)
Definition sqrtOk (x : dwfloat) :=
  let: DWFloat xh xl := x in
  let s := fp2dw (PrimFloat.sqrt (xh + xl)%float) in
  (dnorm <? (xh + xl))%float && divOk x s && divDwOk x s &&
  halfOk (plusDwDw s (divDwDw2 x s)).

(* And the root falls back on its residual in the same way, for the same      *)
(* reason: the quotient inside it has the same range to keep.                 *)
Definition sqrtDwUpK (x : dwfloat) :=
  if sqrtOk x then shiftUp (sqrtDw x) else sqrtDwUp x.
Definition sqrtDwDnK (x : dwfloat) :=
  if sqrtOk x then shiftDn (sqrtDw x) else sqrtDwDn x.

Compute addDwUp (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute plusDwDw (DWFloat 20000000000000004 (-1.75))
                 (DWFloat 20000000000000004 (-1.75)).
Compute addDwDn (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute sqrtDwUp (fp2dw 2).
Compute sqrtDwDn (fp2dw 2).
