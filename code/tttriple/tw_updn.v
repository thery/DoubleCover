From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.
From twarith Require Import twarith.

(* Directed rounding for triple words.                                        *)
(* An interval bound must never fall on the wrong side of the exact result,   *)
(* so every step that rounds is made to round the way the bound needs, and    *)
(* every step that does not round is left alone.  The bounds are computed     *)
(* from the numbers the algorithm has just made, never from a constant, so    *)
(* nothing here has to be trusted in advance.                                 *)

Implicit Type t : twfloat.
Implicit Type f : float.

(* One step up, and one step down.  A step up from minus infinity would       *)
(* give a number back, and a step down from plus infinity likewise, which     *)
(* would hide the fact that something ran off the range.  So a step that      *)
(* meets the infinity it would undo leaves it alone: the infinity then        *)
(* travels to the end of the computation, where it is seen.                   *)
Definition upFp s := if (s =? neg_infinity)%float then s else next_up s.
Definition dnFp s := if (s =? infinity)%float then s else next_down s.

(* Upper and lower bounds of the four operations, whatever the rounding did.  *)
Definition addUpFp a b := upFp (a + b)%float.
Definition addDnFp a b := dnFp (a + b)%float.
Definition subUpFp a b := upFp (a - b)%float.
Definition subDnFp a b := dnFp (a - b)%float.
Definition mulUpFp a b := upFp (a * b)%float.
Definition mulDnFp a b := dnFp (a * b)%float.
Definition divUpFp a b := upFp (a / b)%float.
Definition divDnFp a b := dnFp (a / b)%float.

(* ===========================================================================*)
(*  Cutting an expansion down to three words                                  *)
(* ===========================================================================*)

(* A list of floats standing for its sum is cut to three words by keeping     *)
(* the first two and adding everything below into the third.  Adding it       *)
(* upwards keeps the answer at or above the sum, downwards at or below it.    *)
(*                                                                            *)
(* The list is separated first, and this is not a tidying step: what one       *)
(* sweep leaves can have two terms of the same size next to each other, so    *)
(* cutting straight away would round at the size of the second word and cost  *)
(* the whole of the third.  The second sweep is what puts each term below     *)
(* the one before it, and only then is the tail small enough that rounding    *)
(* it costs nothing.  The last sweep, on the three words that are left,       *)
(* changes no value at all - it only separates them again.                    *)
Definition expUp (l : seq float) :=
  match vseb l with
  | [:: e0, e1, e2 & tl] => l2tw (vseb [:: e0; e1; foldr addUpFp e2 tl])
  | m => l2tw m
  end.

Definition expDn (l : seq float) :=
  match vseb l with
  | [:: e0, e1, e2 & tl] => l2tw (vseb [:: e0; e1; foldr addDnFp e2 tl])
  | m => l2tw m
  end.

(* Widening a triple word by a positive amount, upwards and downwards.        *)
Definition widenUp t f :=
  expUp [:: tw0 t; tw1 t; addUpFp (tw2 t) f].
Definition widenDn t f :=
  expDn [:: tw0 t; tw1 t; addDnFp (tw2 t) (- f)].

(* ===========================================================================*)
(*  Sum and difference                                                        *)
(* ===========================================================================*)

(* The sum of two triple words, bounded above.  Merging the six terms         *)
(* changes nothing and the sweep that follows changes nothing either, so      *)
(* what comes out of them is the exact sum, written as six numbers all in     *)
(* hand.  The only thing that can miss is the cutting down to three, and      *)
(* cutting upwards settles that.  Nothing is estimated and no error bound     *)
(* is needed.                                                                 *)
Definition addTwUp (x y : twfloat) :=
  expUp (vecSum (Merge (tw2l x) (tw2l y))).

Definition addTwDn (x y : twfloat) :=
  expDn (vecSum (Merge (tw2l x) (tw2l y))).

(* Negating a triple word is exact, so subtraction is addition.               *)
Definition subTwUp x y := addTwUp x (negTw y).
Definition subTwDn x y := addTwDn x (negTw y).

(* ===========================================================================*)
(*  Product                                                                   *)
(* ===========================================================================*)

(* Sixteen times the smallest number there is.  Each of the four              *)
(* two-products can miss the product it is given, but never by more than      *)
(* three and a half of those, so a step of this size covers all four          *)
(* wherever it happens.                                                       *)
Definition teps := Eval compute in 0x1p-1070%float.

(* The product of two triple words, bounded above.  Of the nine products      *)
(* the four that carry the value come back as two numbers each that all but   *)
(* add up to them; the five that are smaller than the last word of the        *)
(* answer are each rounded upwards.  So every piece is at or above the piece  *)
(* it stands for, and the step above covers what the two-products may have    *)
(* missed.  The sweep changes no value, and cutting down to three words       *)
(* upwards keeps the answer above the product.                                *)
Definition mulTwUp (x y : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat y0 y1 y2 := y in
  let: DWFloat p00 e00 := twoProd x0 y0 in
  let: DWFloat p01 e01 := twoProd x0 y1 in
  let: DWFloat p10 e10 := twoProd x1 y0 in
  let: DWFloat p11 e11 := twoProd x1 y1 in
  expUp (vecSum (sortMag
    [:: p00; p01; p10; p11; e00; e01; e10; e11;
        mulUpFp x0 y2; mulUpFp x2 y0;
        mulUpFp x1 y2; mulUpFp x2 y1; mulUpFp x2 y2; teps])).

Definition mulTwDn (x y : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat y0 y1 y2 := y in
  let: DWFloat p00 e00 := twoProd x0 y0 in
  let: DWFloat p01 e01 := twoProd x0 y1 in
  let: DWFloat p10 e10 := twoProd x1 y0 in
  let: DWFloat p11 e11 := twoProd x1 y1 in
  expDn (vecSum (sortMag
    [:: p00; p01; p10; p11; e00; e01; e10; e11;
        mulDnFp x0 y2; mulDnFp x2 y0;
        mulDnFp x1 y2; mulDnFp x2 y1; mulDnFp x2 y2;
        (- teps)%float])).

(* ===========================================================================*)
(*  Quotient and root                                                         *)
(* ===========================================================================*)

(* How small a triple word can be, from its three words alone: a sum is at    *)
(* least the first term less the other two, in absolute value, and the steps  *)
(* down keep that true.                                                       *)
Definition magDnTw t :=
  let: TWFloat x0 x1 x2 := t in
  subDnFp (subDnFp (abs x0) (abs x1)) (abs x2).

(* How small a triple word's value can be: the sum of its three words,        *)
(* rounded down.                                                              *)
Definition valDnTw t :=
  let: TWFloat x0 x1 x2 := t in addDnFp (addDnFp x0 x1) x2.

(* The three words of a triple word added in absolute value, rounded up.      *)
Definition absSumUp t :=
  let: TWFloat x0 x1 x2 := t in
  addUpFp (addUpFp (abs x0) (abs x1)) (abs x2).

(* A number is a usable divisor when it is above zero and not an infinity.    *)
(* Both tests are needed: an infinity passes the first one and stands for     *)
(* no number at all.                                                          *)
Definition posFp m := ((0 <? m) && (m <? infinity))%float.

(* The quotient is not bounded by an analysis of its own algorithm but by     *)
(* its residual: whatever q is, the true quotient is within the distance      *)
(* |x - q*y| / |y| of it.  So the algorithm that produced q is free to be     *)
(* anything at all, and only the residual is computed with care - bounded     *)
(* on both sides, its words added in absolute value, and divided by a         *)
(* divisor made smaller.  When the divisor cannot be told from zero there     *)
(* is nothing to say, and nothing is what comes back.                         *)
Definition divTwErr (x y : twfloat) :=
  let: m := magDnTw y in
  let: q := divTwTw x y in
  let: rup := subTwUp x (mulTwDn q y) in
  let: rdn := subTwDn x (mulTwUp q y) in
  let: r := addUpFp (absSumUp rup) (absSumUp rdn) in
  (q, divUpFp r m, m).

Definition divTwUp (x y : twfloat) :=
  let: (d, e, m) := divTwErr x y in
  if posFp m then widenUp d e else TWFloat nan nan nan.
Definition divTwDn (x y : twfloat) :=
  let: (d, e, m) := divTwErr x y in
  if posFp m then widenDn d e else TWFloat nan nan nan.

(* The square root is bounded by its residual too.  Whatever q is, the        *)
(* root and q differ by (x - q*q) / (root + q), and the root is never         *)
(* negative, so the sum below it is q itself - no guess at how good q is      *)
(* enters the bound.  Two tests: q must be above zero to divide by, and so    *)
(* must the number itself, because the root of a negative is taken to be      *)
(* zero and a bound below it would then be a claim about nothing.             *)
Definition sqrtTwErr (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let: q := sqrtTw x in
  let: m := valDnTw q in
  let: rup := subTwUp x (mulTwDn q q) in
  let: rdn := subTwDn x (mulTwUp q q) in
  let: r := addUpFp (absSumUp rup) (absSumUp rdn) in
  (q, divUpFp r m, m, (x0 + x1 + x2)%float).

Definition sqrtTwUp (x : twfloat) :=
  let: (d, e, m, s) := sqrtTwErr x in
  if posFp m && posFp s then widenUp d e else TWFloat nan nan nan.
Definition sqrtTwDn (x : twfloat) :=
  let: (d, e, m, s) := sqrtTwErr x in
  if posFp m && posFp s then widenDn d e else TWFloat nan nan nan.

(* ===========================================================================*)
(*  What the bounds come out as                                               *)
(* ===========================================================================*)

Compute addTwUp (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute addTwDn (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute mulTwUp (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute mulTwDn (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute divTwUp (fp2tw 1) (fp2tw 3).
Compute divTwDn (fp2tw 1) (fp2tw 3).
Compute sqrtTwUp (fp2tw 2).
Compute sqrtTwDn (fp2tw 2).
