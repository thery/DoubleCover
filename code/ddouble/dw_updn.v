From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.
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

(* Upper and lower bounds of the three operations, whatever the rounding did. *)
Definition addUpFp a b := next_up (a + b)%float.
Definition addDnFp a b := next_down (a + b)%float.
Definition mulUpFp a b := next_up (a * b)%float.
Definition divUpFp a b := next_up (a / b)%float.
Definition divDnFp a b := next_down (a / b)%float.

(* The high word of a double word carries its value, the low word its tail.   *)
Definition dwhi d := let: DWFloat xh _ := d in xh.
Definition dwlo d := let: DWFloat _ xl := d in xl.

(* Widening a double word by a positive amount, upwards and downwards.  The   *)
(* final fastTwoSum only tidies the pair; it changes no value.                *)
Definition widenUp d f :=
  let: DWFloat zh zl := d in fastTwoSum zh (addUpFp zl f).
Definition widenDn d f :=
  let: DWFloat zh zl := d in fastTwoSum zh (addDnFp zl (- f)).

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

(* The product of two double words, together with a bound on its error.  The  *)
(* two-product is exact, so the error is the rounding of the four small       *)
(* terms plus the one term the algorithm drops, xl times yl.                  *)
Definition timesDwDwErr (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat ch cl1 := twoProd xh yh in
  let: tl1 := (xh * yl)%float in
  let: tl2 := (xl * yh)%float in
  let: cl2 := (tl1 + tl2)%float in
  let: cl3 := (cl1 + cl2)%float in
  let: e := addUpFp (mulUpFp u (addUpFp (addUpFp (abs tl1) (abs tl2))
                                        (addUpFp (abs cl2) (abs cl3))))
                    (mulUpFp (abs xl) (abs yl)) in
  (fastTwoSum ch cl3, e).

Definition mulDwUp (x y : dwfloat) :=
  let: (d, e) := timesDwDwErr x y in widenUp d e.
Definition mulDwDn (x y : dwfloat) :=
  let: (d, e) := timesDwDwErr x y in widenDn d e.

(* A double word is at least its high word made smaller by one unit in the    *)
(* last place, since the low word is at most half of one.                     *)
Definition magDnDw d := next_down (abs (dwhi d) * (1 - u))%float.

(* The quotient is not bounded by an analysis of its own algorithm but by     *)
(* its residual: whatever q is, the true quotient lies within |x - q*y|/|y|   *)
(* of it, and both are computed with the operations bounded above.            *)
Definition divDwErr (x y : dwfloat) :=
  let: q := divDwDw2 x y in
  let: rup := subDwUp x (mulDwDn q y) in
  let: rdn := subDwDn x (mulDwUp q y) in
  let: r := addUpFp (abs (dwhi rup)) (abs (dwhi rdn)) in
  (q, divUpFp r (magDnDw y)).

Definition divDwUp (x y : dwfloat) :=
  let: (d, e) := divDwErr x y in widenUp d e.
Definition divDwDn (x y : dwfloat) :=
  let: (d, e) := divDwErr x y in widenDn d e.

(* The square root is bounded the same way: from a seed of ordinary           *)
(* precision, the residual x - s*s divided by the sum of the seed and the     *)
(* true root bounds the distance between them.  That sum is not known, so a   *)
(* little less than twice the seed is used, which is below it whichever way   *)
(* the seed missed.                                                           *)
(* Sound, but only as tight as the seed: the residual is used as a width and  *)
(* not as a correction, so these two bracket the root to ordinary precision.  *)
Definition sqrtDwErr (x : dwfloat) :=
  let: DWFloat xh xl := x in
  let: s := PrimFloat.sqrt (xh + xl)%float in
  let: q := fp2dw s in
  let: rup := subDwUp x (mulDwDn q q) in
  let: rdn := subDwDn x (mulDwUp q q) in
  let: r := addUpFp (abs (dwhi rup)) (abs (dwhi rdn)) in
  (q, divUpFp r (next_down ((s + s) * (1 - u - u))%float)).

Definition sqrtDwUp (x : dwfloat) :=
  let: (d, e) := sqrtDwErr x in widenUp d e.
Definition sqrtDwDn (x : dwfloat) :=
  let: (d, e) := sqrtDwErr x in widenDn d e.

Compute addDwUp (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute plusDwDw (DWFloat 20000000000000004 (-1.75))
                 (DWFloat 20000000000000004 (-1.75)).
Compute addDwDn (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute sqrtDwUp (fp2dw 2).
Compute sqrtDwDn (fp2dw 2).
