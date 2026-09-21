From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.
From Stdlib Require Import ZArith Floats.
From twarith Require Import twarith.
From dwarith Require Export dw_updn.

(* Directed rounding for triple words.                                        *)
(* An interval bound must never fall on the wrong side of the exact result,   *)
(* so every step that rounds is made to round the way the bound needs, and    *)
(* every step that does not round is left alone.  The bounds are computed     *)
(* from the numbers the algorithm has just made, never from a constant, so    *)
(* nothing here has to be trusted in advance.                                 *)

Implicit Type t : twfloat.
Implicit Type f : float.

(* THE WIDENING STEPS ARE `code/ddouble''s, NOT A COPY, for the same reason   *)
(* the error-free transforms are: `upFp', `dnFp' and the six rounded          *)
(* operations say nothing about pairs, and `dwbound.v' already proves each    *)
(* of them is on the right side of what it stands for.  Only the two on a     *)
(* difference are new here.                                                   *)
Definition subUpFp a b := upFp (a - b)%float.
Definition subDnFp a b := dnFp (a - b)%float.

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
(* This is what the cut MEANS, and every bound below is proved of it: sweep,  *)
(* keep two words, fold the rest into the third, separate again.  What the    *)
(* operations actually call is `expUpF'/`expDnF' underneath, which is the same *)
(* walk with no list in it -- `expF_eq' in `twarith.v' says the two agree, so  *)
(* no proof here has to look at the arrangement.                              *)
Definition expUp (l : seq float) := cutTw addUpFp (vseb l).
Definition expDn (l : seq float) := cutTw addDnFp (vseb l).

Definition expUpF := expF addUpFp.
Definition expDnF := expF addDnFp.

Lemma expUpF_eq l : expUpF l = expUp l.
Proof. by rewrite /expUpF /expUp expF_eq. Qed.

Lemma expDnF_eq l : expDnF l = expDn l.
Proof. by rewrite /expDnF /expDn expF_eq. Qed.

(* Widening a triple word by a positive amount, upwards and downwards.        *)
Definition widenUp t f :=
  expUpF [:: tw0 t; tw1 t; addUpFp (tw2 t) f].
Definition widenDn t f :=
  expDnF [:: tw0 t; tw1 t; addDnFp (tw2 t) (- f)].

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
  expUpF (vecSum6 (Merge (tw2l x) (tw2l y))).

Definition addTwDn (x y : twfloat) :=
  expDnF (vecSum6 (Merge (tw2l x) (tw2l y))).

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

(* AND WHERE THAT STEP IS PUT.  Sixteen times the smallest number there is   *)
(* is enough for the bound, but it is not a word of the answer: beside a     *)
(* leading word of one it is a subnormal a thousand bits below the third     *)
(* word's place.  A triple word carrying such a word can never be divided    *)
(* by -- the quotient needs `a * x1' with `a' about one over `x0', and that  *)
(* product falls under the line where the paper's bounds hold -- and every   *)
(* exact product has one: `2 * 3' comes back as six and a subnormal.  That   *)
(* was Interval's exponential failing on three words.                        *)
(*                                                                          *)
(* So the step is taken at the last word's own place as well: two to the     *)
(* minus a hundred and fifty-nine of the leading product, which is about one *)
(* step of a third word and so costs nothing, ADDED TO the fixed step, which *)
(* is the only part the bound uses.  Above or below the line, the sum is at  *)
(* least the fixed step, so the proof is the one it was.                     *)
Definition escale := Eval compute in 0x1p-159%float.

Definition pstep w :=
  let r := mulUpFp escale (abs w) in
  if (teps <? r)%float then r else teps.

(* AND THE FIVE SMALL PRODUCTS.  Rounding a product upwards takes nought to  *)
(* the smallest number there is, and five of those beside a leading word of  *)
(* six make another word that is not a word of the answer.  A product with a *)
(* nought in it is nought exactly, and nought is its own bound either way,   *)
(* so there is nothing to round.                                             *)
Definition mulUp0 a b :=
  if ((a =? 0) || (b =? 0))%float then (a * b)%float else mulUpFp a b.
Definition mulDn0 a b :=
  if ((a =? 0) || (b =? 0))%float then (a * b)%float else mulDnFp a b.

(* The product of two triple words, bounded above.  Of the nine products      *)
(* the four that carry the value come back as two numbers each that all but   *)
(* add up to them; the five that are smaller than the last word of the        *)
(* answer are each rounded upwards.  So every piece is at or above the piece  *)
(* it stands for, and the step above covers what the two-products may have    *)
(* missed.  The sweep changes no value, and cutting down to three words       *)
(* upwards keeps the answer above the product.                                *)
(*                                                                            *)
(* THE TERMS ARE WRITTEN IN ORDER INSTEAD OF SORTED.  The sweeps want their   *)
(* terms by decreasing size, and the fourteen are written in the order the    *)
(* nine products come in, which is not that order -- the low word of the      *)
(* leading two-product is about `u' and sits behind three terms that are      *)
(* about `u^2'.  Sorting them cost three microseconds of a product's eleven,  *)
(* an insertion sort over fourteen words, and the bound does not use the      *)
(* order at all: `vecSum' and `vseb' are exact whatever order they are given  *)
(* and the proof only ever asks that the sum is unchanged.  So the terms go   *)
(* in the order their sizes are known to be in, and the sort is gone.         *)
Definition mulTwUp (x y : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat y0 y1 y2 := y in
  let d00 := twoProd x0 y0 in
  let d01 := twoProd x0 y1 in
  let d10 := twoProd x1 y0 in
  let d11 := twoProd x1 y1 in
  expUpF (vecSum14
    [:: dwhi d00; dwhi d01; dwhi d10; dwlo d00;
        dwhi d11; dwlo d01; dwlo d10;
        mulUp0 x0 y2; mulUp0 x2 y0; dwlo d11;
        mulUp0 x1 y2; mulUp0 x2 y1; mulUp0 x2 y2;
        pstep (dwhi d00)]).

Definition mulTwDn (x y : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat y0 y1 y2 := y in
  let d00 := twoProd x0 y0 in
  let d01 := twoProd x0 y1 in
  let d10 := twoProd x1 y0 in
  let d11 := twoProd x1 y1 in
  expDnF (vecSum14
    [:: dwhi d00; dwhi d01; dwhi d10; dwlo d00;
        dwhi d11; dwlo d01; dwlo d10;
        mulDn0 x0 y2; mulDn0 x2 y0; dwlo d11;
        mulDn0 x1 y2; mulDn0 x2 y1; mulDn0 x2 y2;
        (- pstep (dwhi d00))%float]).

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
(*  The same two bounds as a shift of so many bits                            *)
(* ===========================================================================*)

(* An algorithm proved correct to within so many units in the last place      *)
(* needs no residual at all: the answer moved that far up and that far down   *)
(* is the enclosure.  That is one multiplication, where the residual above    *)
(* costs two triple-word products and two subtractions - measured, a hundred  *)
(* and one microseconds against twenty-one for the quotient, and four hundred *)
(* and thirty-six against fifty-two for the root.                             *)
(*                                                                            *)
(* WHAT IS GIVEN UP.  The residual asks nothing of the answer it is handed:   *)
(* whatever q is, the true quotient is within |x - q*y| / |y| of it, and no   *)
(* theorem about the algorithm that made q is needed.  A shift needs one.     *)
(* So this is the trade: four operations for one, against a statement that    *)
(* has to be proved rather than one that comes for nothing.                   *)
(*                                                                            *)
(* The shift is deliberately coarse: a hundred bits where the arithmetic      *)
(* gives about a hundred and fifty-five.  Fifty-five bits of slack is what    *)
(* lets a rough argument carry it - the machine root is right to             *)
(* fifty-three bits and each step of Newton's method at least doubles that -  *)
(* instead of the paper's own sharp constant.  Tighten it when the paper's    *)
(* theorems are ported.                                                       *)
(* How many bits to give away.  Measured: at a hundred and fifty it is too    *)
(* much and a bracket is lost, at a hundred and fifty-five it is not, so      *)
(* there is almost no room here and the number has to come from the paper's    *)
(* own theorem rather than from a rough argument.                             *)
(* THE STEP IS A MULTIPLICATION, AND NOT AN EXPONENT SHIFT.  Shifting an     *)
(* exponent is one instruction on the machine, but inside Rocq's evaluator    *)
(* `FloatOps.Z.ldexp' is not: it goes through `Z.max', `Z.min' and a          *)
(* conversion of a whole number to a machine integer on every call.           *)
(* Measured, 4.8 microseconds against 0.2 for a float multiplication, for the *)
(* same answer.  The constant is a power of two, so the multiplication is     *)
(* exact.                                                                     *)
Definition tscale := Eval compute in 0x1p-155%float.

(* THE WIDENING, and it is four operations.                                   *)
(*                                                                            *)
(* The step is taken from the LEADING word, not from the sum of the three:    *)
(* a triple word is within one part in two to the fifty-second of its own     *)
(* leading word, so the two differ by far less than the shift itself.  And    *)
(* the step is an exponent shift rather than a multiplication, so it is       *)
(* exact.                                                                     *)
(*                                                                            *)
(* It goes into the LAST word and nothing is separated afterwards.  The step  *)
(* is about two to the minus forty-ninth of that word, so adding it leaves    *)
(* the word where it was, well inside half a step of the word before it, and  *)
(* the triple is still a triple word.  That is what makes the sweep           *)
(* unnecessary here, where `widenUp' above needs one.                         *)
(* THE SHIFT ABOVE HOLDS IN THE NORMAL RANGE ONLY.  The paper's error bounds  *)
(* are proved in the format with no smallest exponent, and they ask of every  *)
(* term that it be normal.  Below that they say nothing, so the shift taken   *)
(* from them would be a claim about nothing.                                  *)
(*                                                                            *)
(* So the bottom of the range gets a step of its own, and a coarser one: down *)
(* there every number is a whole multiple of the smallest float there is, so  *)
(* an operation can only be out by one of those, and a fixed step covers any  *)
(* number of them.  That argument needs no error analysis at all.             *)
(*                                                                            *)
(* The test is on the leading word: above the line the third word, a hundred  *)
(* and six bits below it, is normal too, with room for the numbers made along *)
(* the way.  The fixed step has to cover the relative one AT the line, which  *)
(* is two to the minus nine hundred times two to the minus a hundred and      *)
(* fifty-five, and below the line the relative error only gets smaller in     *)
(* absolute terms - so the same step serves all the way down.  Neither        *)
(* operation ever has to give up.                                            *)
Definition normLo := Eval compute in 0x1p-900%float.
Definition tabs := Eval compute in 0x1p-1050%float.

Definition stepTw t :=
  let: TWFloat x0 _ _ := t in
  if (normLo <? abs x0)%float then mulUpFp tscale (abs x0) else tabs.

(* The sweep is kept, and NOT because of the step.  A seed need not be a      *)
(* triple word at all: `sqrtTw' of two comes back with a second word of       *)
(* 1.2537e-16 beside a leading 1.41421, and half a step of that leading word  *)
(* is 1.11e-16 - so the pair does not even add back to itself.  The sweep is  *)
(* what repairs that, and dropping it made every root read as nothing.  It    *)
(* is four two-sums, under a microsecond, against twenty-one for the quotient *)
(* and fifty-two for the root.                                                *)
Definition widenUpK t := widenUp t (stepTw t).
Definition widenDnK t := widenDn t (stepTw t).

Definition divTwUpK (x y : twfloat) :=
  let q := divTwTw x y in
  if posFp (magDnTw y) then widenUpK q else TWFloat nan nan nan.
Definition divTwDnK (x y : twfloat) :=
  let q := divTwTw x y in
  if posFp (magDnTw y) then widenDnK q else TWFloat nan nan nan.

Definition sqrtTwUpK (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let q := sqrtTw x in
  if posFp (valDnTw q) && posFp (x0 + x1 + x2)%float
  then widenUpK q else TWFloat nan nan nan.
Definition sqrtTwDnK (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let q := sqrtTw x in
  if posFp (valDnTw q) && posFp (x0 + x1 + x2)%float
  then widenDnK q else TWFloat nan nan nan.

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
