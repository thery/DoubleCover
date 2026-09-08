From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.
From dwarith Require Import dwarith.

(* Directed rounding for double words.                                        *)
(* An interval bound must never fall on the wrong side of the exact result,   *)
(* so each operation returns its own error bound and widens by it.            *)

Implicit Type d : dwfloat.
Implicit Type f : float.

(* The unit roundoff of binary64, 2^-53.  A rounded sum differs from the      *)
(* exact one by at most u times the rounded value.                            *)
Definition u := Eval compute in (1 / 9007199254740992)%float.

(* An upper bound of a + b, whatever the rounding did.                        *)
Definition addUpFp a b := next_up (a + b)%float.

(* A lower bound of a + b.                                                    *)
Definition addDnFp a b := next_down (a + b)%float.

(* The sum of two double words, together with a bound on its error.           *)
(* The two twoSum and the two fastTwoSum are exact, so the whole error is     *)
(* the rounding of c and the rounding of w, each at most u times its result.  *)
Definition plusDwDwErr (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let: DWFloat sh sl := twoSum xh yh in
  let: DWFloat th tl := twoSum xl yl in
  let: c := (sl + th)%float in
  let: DWFloat vh vl := fastTwoSum sh c in
  let: w := (tl + vl)%float in
  let: e := (u * addUpFp (abs c) (abs w))%float in
  (fastTwoSum vh w, e).

(* Multiplying by u is exact, so only the sum of the two magnitudes needs to  *)
(* be rounded upwards.                                                        *)

(* A double word not below the exact sum of x and y.                          *)
Definition addDwUp (x y : dwfloat) :=
  let: (DWFloat zh zl, e) := plusDwDwErr x y in
  fastTwoSum zh (addUpFp zl e).

(* A double word not above the exact sum of x and y.                          *)
Definition addDwDn (x y : dwfloat) :=
  let: (DWFloat zh zl, e) := plusDwDwErr x y in
  fastTwoSum zh (addDnFp zl (- e)).

Compute addDwUp (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
Compute plusDwDw (DWFloat 20000000000000004 (-1.75))
                 (DWFloat 20000000000000004 (-1.75)).
Compute addDwDn (DWFloat 20000000000000004 (-1.75))
                (DWFloat 20000000000000004 (-1.75)).
