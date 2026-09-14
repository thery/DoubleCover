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
Definition addDwUp (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat sh sl := twoSum xh yh in
  let: DWFloat th tl := twoSum xl yl in
  twoSum sh (addUpFp (addUpFp sl th) tl).

Definition addDwDn (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat sh sl := twoSum xh yh in
  let: DWFloat th tl := twoSum xl yl in
  twoSum sh (addDnFp (addDnFp sl th) tl).

(* Negating a double word is exact, so subtraction is addition.               *)
Definition negDw d := let: DWFloat xh xl := d in DWFloat (- xh) (- xl).

Definition subDwUp x y := addDwUp x (negDw y).
Definition subDwDn x y := addDwDn x (negDw y).

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
Definition mulDwUp (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat ch cl := twoProd xh yh in
  twoSum ch (addUpFp (addUpFp (addUpFp cl (mulUpFp xh yl))
                              (addUpFp (mulUpFp xl yh) (mulUpFp xl yl)))
                     deps).

Definition mulDwDn (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat ch cl := twoProd xh yh in
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
(* divided, and divided by the divisor.  Four double-word operations, and     *)
(* measured, five times the cost of the quotient itself.                      *)
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
(* NO RANGE TEST IS NEEDED HERE.  The double-word proofs of this development  *)
(* are in the bounded format, subnormals and all - `F2SumFLT.v',              *)
(* `TwoSumFLT.v' - so the bound holds everywhere.  That is not so for triple   *)
(* words, whose proofs have no smallest exponent.                             *)
Definition dbits := (-102)%Z.

Definition ldexp2 (f : float) (e : Z) := FloatOps.Z.ldexp f e.

(* The step is taken from the LEADING word: a double word is within one part  *)
(* in two to the fifty-second of it, which is nothing beside the shift.  And  *)
(* the sweep of `widenUp' is kept, since a seed need not be a double word.    *)
Definition dstep d := let: DWFloat xh _ := d in ldexp2 (abs xh) dbits.

Definition shiftUp d := widenUp d (dstep d).
Definition shiftDn d := widenDn d (dstep d).

Definition divDwUpK (x y : dwfloat) :=
  let q := divDwDw2 x y in
  if posFp (magDnDw y) then shiftUp q else DWFloat nan nan.
Definition divDwDnK (x y : dwfloat) :=
  let q := divDwDw2 x y in
  if posFp (magDnDw y) then shiftDn q else DWFloat nan nan.

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

Definition sqrtDwUpK (x : dwfloat) :=
  let: DWFloat xh xl := x in
  let q := sqrtDw x in
  if posFp (valDnDw q) && posFp (xh + xl)%float
  then shiftUp q else DWFloat nan nan.
Definition sqrtDwDnK (x : dwfloat) :=
  let: DWFloat xh xl := x in
  let q := sqrtDw x in
  if posFp (valDnDw q) && posFp (xh + xl)%float
  then shiftDn q else DWFloat nan nan.

Compute addDwUp (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute plusDwDw (DWFloat 20000000000000004 (-1.75))
                 (DWFloat 20000000000000004 (-1.75)).
Compute addDwDn (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute sqrtDwUp (fp2dw 2).
Compute sqrtDwDn (fp2dw 2).
