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

(* Widening a triple word by a positive amount, upwards and downwards.  The   *)
(* list here is always three long, so `expF3' does it with no list at all and *)
(* `widenUpE' says that is the same answer.                                   *)
Definition widenUp t f :=
  expF3 (tw0 t) (tw1 t) (addUpFp (tw2 t) f).
Definition widenDn t f :=
  expF3 (tw0 t) (tw1 t) (addDnFp (tw2 t) (- f)).

Lemma widenUpTwE t f : widenUp t f = expUp [:: tw0 t; tw1 t; addUpFp (tw2 t) f].
Proof. by rewrite /widenUp (expF3_eq addUpFp) -/(expUpF _) expUpF_eq. Qed.

Lemma widenDnTwE t f :
  widenDn t f = expDn [:: tw0 t; tw1 t; addDnFp (tw2 t) (- f)].
Proof. by rewrite /widenDn (expF3_eq addDnFp) -/(expDnF _) expDnF_eq. Qed.

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

(* THE TWO ROUTES THAT ARE GONE.  Two earlier bounds lived here and neither  *)
(* is used: the RESIDUAL one (`divTwErr', `sqrtTwErr', `absSumUp'), which    *)
(* asked nothing of the algorithm but cost two triple-word products and two  *)
(* subtractions a call, and the SHIFT BY SO MANY ULPS (`tscale', `stepTw',    *)
(* `widenUpK'), which was a rough argument standing in for the paper's own    *)
(* theorem.  `twdiv.v' and `twsqrt.v' now carry the paper's Algorithms 14     *)
(* and 15 with `kstep' for the shift, and they define `divTwUpK' and          *)
(* `sqrtTwUpK' THEMSELVES.  Those names were declared here as well, so which  *)
(* one `tw_ops.v' got was decided by the order of its imports -- reorder them *)
(* and the quotient silently became the long-division one, still correct and  *)
(* twice as slow.  The names are gone from this file so that cannot happen.   *)

(* is two to the minus nine hundred times two to the minus a hundred and      *)
(* fifty-five, and below the line the relative error only gets smaller in     *)
(* absolute terms - so the same step serves all the way down.  Neither        *)
(* operation ever has to give up.                                            *)
Definition normLo := Eval compute in 0x1p-900%float.
Definition tabs := Eval compute in 0x1p-1050%float.

(* ===========================================================================*)
(*  What the bounds come out as                                               *)
(* ===========================================================================*)

Compute addTwUp (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute addTwDn (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute mulTwUp (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
Compute mulTwDn (toTw 1 1e-20 1e-40) (toTw 1 1e-20 1e-40).
