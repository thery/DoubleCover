From mathcomp Require Import all_ssreflect.
Require Import PrimInt63 Floats.
From Stdlib Require Import ZArith.
From twarith Require Import twarith tw_updn.

(* The paper's own algorithms, on primitive floats.                          *)
(*                                                                           *)
(* `twarith.v' has algorithms of my own for the quotient and the root - a     *)
(* long division and Newton's method - chosen because the bound that went     *)
(* with them was a residual, and a residual asks nothing of the algorithm it  *)
(* is handed.  Bounding by a shift of so many units in the last place asks    *)
(* the opposite: the number of units has to come from a theorem about the     *)
(* algorithm, and the theorems there are about the paper's algorithms.  So    *)
(* these are the paper's, and `threewords/' holds their proofs.               *)
(*                                                                           *)
(* ONE CHANGE THROUGHOUT, and it is forced: Rocq's primitive floats have no   *)
(* fused multiply-add.  Every step the paper writes as one rounding of        *)
(* `a + b * c' is two roundings here, and every product error that the paper  *)
(* takes from an FMA is taken from the two-product instead.  The paper's      *)
(* constants therefore do not carry over as they stand; measured on random    *)
(* inputs, the quotient below is out by 2.3 units in the last place where     *)
(* the paper's own is out by less, and eight covers it.                       *)
(*                                                                           *)
(* Nothing here is proved.                                                    *)

Implicit Type t : twfloat.

(* The Fast2Sum that puts its arguments the right way round first.            *)
Definition fast2SumS (a b : float) :=
  if (abs b <=? abs a)%float then fastTwoSum a b else fastTwoSum b a.

(* The first three of a list, filled out with noughts.                        *)
Definition nth3 (l : seq float) :=
  (nth 0%float l 0, nth 0%float l 1, nth 0%float l 2).

(* ===========================================================================*)
(*  Algorithm 11 - a double word times a triple word                          *)
(* ===========================================================================*)

Definition threeProdDW (x y : twfloat) : twfloat :=
  let: TWFloat x0 x1 _ := x in
  let: TWFloat y0 y1 y2 := y in
  let: DWFloat z00p z00m := twoProd x0 y0 in
  let: DWFloat z01p z01m := twoProd x0 y1 in
  let: DWFloat z10p z10m := twoProd x1 y0 in
  let: (b0, b1, b2) := nth3 (vecSum [:: z00m; z01p; z10p]) in
  let c   := (b2 + x1 * y1)%float in
  let z31 := (z10m + x0 * y2)%float in
  let z3  := (z31 + z01m)%float in
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0%float e 0 in
  l2tw (e0 :: take 2 (vseb [:: nth 0%float e 1; nth 0%float e 2;
                              nth 0%float e 3; nth 0%float e 4])).

(* ===========================================================================*)
(*  Algorithms 18 and 20 - the second argument has leading word one           *)
(* ===========================================================================*)

(* The part the two share.                                                    *)
Definition p18head (x0 x1 y1 y2 : float) : float * float :=
  let: DWFloat z01p z01m := twoProd x0 y1 in
  let: DWFloat bh bl := fast2SumS x1 z01p in
  let z31 := (z01m + x1 * y1)%float in
  let z3  := (z31 + x0 * y2)%float in
  (bh, (bl + z3)%float).

(* Algorithm 18: a double word times a triple word whose leading word is one. *)
Definition threeProdOne (x y : twfloat) : twfloat :=
  let: TWFloat x0 x1 _ := x in
  let: TWFloat _ y1 y2 := y in
  let: (bh, s3) := p18head x0 x1 y1 y2 in
  let: (e0, e1, e2) := nth3 (vecSum [:: x0; bh; s3]) in
  let: DWFloat r1 r2 := fast2SumS e1 e2 in
  TWFloat e0 r1 r2.

(* Algorithm 20: the same with a triple word on the left.                     *)
Definition threeProdOneTW (x y : twfloat) : twfloat :=
  let: TWFloat x0 x1 x2 := x in
  let: TWFloat _ y1 y2 := y in
  let: (bh, s3) := p18head x0 x1 y1 y2 in
  let: (e0, e1, e2) := nth3 (vecSum [:: x0; bh; (s3 + x2)%float]) in
  let: DWFloat r1 r2 := fast2SumS e1 e2 in
  TWFloat e0 r1 r2.

(* ===========================================================================*)
(*  Algorithm 13's head - the Newton double word for the reciprocal           *)
(* ===========================================================================*)

(* Two to the minus fifty-third, the unit roundoff.                           *)
Definition uu := Eval compute in 0x1p-53%float.

(* One plus two of them is the float just above one, which is what makes      *)
(* the rounded product of it with the reciprocal come back exactly - the      *)
(* fact the whole of Algorithm 13 rests on.                                   *)
Definition onep := Eval compute in (1 + 2 * 0x1p-53)%float.
Definition onem := Eval compute in (1 - 2 * 0x1p-53)%float.

Definition reciBW (x0 x1 : float) : twfloat :=
  let a := (onep / x0)%float in
  (* the paper's FMA `RN(a x0 - (1 + 2u))', done with the two-product        *)
  let: DWFloat p e := twoProd a x0 in
  let h11 := ((p - onep) + e)%float in
  let h1  := (- h11 - a * x1)%float in
  let: DWFloat b01 b11 := twoProd a onem in
  let b12 := (b11 + a * h1)%float in
  let: DWFloat bh bl := fastTwoSum b01 b12 in
  TWFloat bh bl 0.

(* Two less a triple word, which is exact on every word.                      *)
Definition sub2Tw t :=
  let: TWFloat x0 x1 x2 := t in TWFloat (2 - x0)%float (- x1)%float (- x2)%float.

(* ===========================================================================*)
(*  Algorithms 13 and 14 - the reciprocal and the quotient                    *)
(* ===========================================================================*)

Definition threeReci (x : twfloat) : twfloat :=
  let bw := reciBW (tw0 x) (tw1 x) in
  threeProdOne bw (sub2Tw (threeProdDW bw x)).

Definition threeDiv (z x : twfloat) : twfloat :=
  let bw := reciBW (tw0 x) (tw1 x) in
  threeProdOneTW (threeProdDW bw z) (sub2Tw (threeProdDW bw x)).

(* ===========================================================================*)
(*  Algorithm 15 - the square root                                            *)
(* ===========================================================================*)

(* One and four of the unit roundoff.  It plays for the root the part one     *)
(* plus two of them plays for the reciprocal: it tilts the seed up by just     *)
(* enough that the rounding in the middle cannot go the wrong way.            *)
Definition onep4 := Eval compute in (1 + 4 * 0x1p-53)%float.
Definition three2 := Eval compute in (3 / 2)%float.

(* The Newton double word for one over the root.  The three steps the paper   *)
(* writes with a fused multiply-add are two roundings each.                    *)
Definition sqrtBW (x0 x1 : float) : twfloat :=
  let s := PrimFloat.sqrt x0 in
  let a := (onep4 / s)%float in
  let a' := (a / 2)%float in
  let: DWFloat h01_1 h11_1 := twoProd a x0 in
  let h1_1 := (h11_1 + a * x1)%float in
  let: DWFloat h01_2 h11_2 := twoProd a' h01_1 in
  let h0_2 := (three2 - h01_2)%float in
  let h1_2 := (- (h11_2 + a' * h1_1))%float in
  let: DWFloat b01 b11 := twoProd a h0_2 in
  let b12 := (b11 + a * h1_2)%float in
  let: DWFloat bh bl := fastTwoSum b01 b12 in
  TWFloat bh bl 0.

(* Three halves less a triple word, exact on every word once the leading      *)
(* word is a half - which is what the middle product is for.                  *)
Definition sub32Tw t :=
  let: TWFloat x0 x1 x2 := t in
  TWFloat (three2 - x0)%float (- x1)%float (- x2)%float.

Definition threeSqRt (x : twfloat) : twfloat :=
  let bw := sqrtBW (tw0 x) (tw1 x) in
  let i1 := threeProdDW bw x in
  threeProdOneTW i1 (sub32Tw (threeProdDW (halfTw bw) i1)).

(* ===========================================================================*)
(*  The bounds: the answer shifted so many units in the last place            *)
(* ===========================================================================*)

(* MEASURED, on forty thousand random triple words, in units of the last      *)
(* place of the third word: the sum is out by 0.9, Algorithm 9 by 1.7,         *)
(* Algorithm 11 by 1.7 and Algorithm 14 by 2.3.  Eight covers all of them,     *)
(* and eight units of a word that sits a hundred and fifty-nine bits below    *)
(* the leading one is the leading one shifted down a hundred and fifty-six.    *)
(* The probing is `probek.py' beside this file.                                *)
(*                                                                            *)
(* ADMITTED, not proved.  The number comes from running the algorithms, not    *)
(* from their theorems: the theorems are in `threewords/' but they are about   *)
(* the paper's steps, and the FMA is not available here.                       *)
Definition kbits := (-156)%Z.

(* The paper's bounds hold in the NORMAL range only - they are proved in the  *)
(* format with no smallest exponent.  Below that the shift would be a claim    *)
(* about nothing, so the bottom of the range gets a fixed step instead, which  *)
(* needs no error analysis: down there every number is a whole multiple of     *)
(* the smallest float and an operation can only be out by one of those.  The   *)
(* fixed step covers the shifted one at the line, and the shifted one only     *)
(* gets smaller below it, so the same step serves all the way down.            *)
Definition kstep t :=
  let: TWFloat x0 _ _ := t in
  if (normLo <? abs x0)%float then ldexp2 (abs x0) kbits else tabs.

(* The sweep is kept.  Not for the step - it is far too small to disturb the  *)
(* words - but because a seed need not be a triple word at all, and the       *)
(* sweep is what makes it one.                                                 *)
Definition shiftUp t := widenUp t (kstep t).
Definition shiftDn t := widenDn t (kstep t).

(* A number is a usable divisor when it is above zero and not an infinity.    *)
Definition divTwUpP (x y : twfloat) :=
  if posFp (magDnTw y) then shiftUp (threeDiv x y) else TWFloat nan nan nan.
Definition divTwDnP (x y : twfloat) :=
  if posFp (magDnTw y) then shiftDn (threeDiv x y) else TWFloat nan nan nan.

(* The root of a negative number is taken to be nought here, so a bound      *)
(* below it would be a claim about nothing: what it is given has to be above  *)
(* zero, and so has the answer, which is what the shift is taken from.        *)
Definition sqrtTwUpP (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let q := threeSqRt x in
  if posFp (valDnTw q) && posFp (x0 + x1 + x2)%float
  then shiftUp q else TWFloat nan nan nan.
Definition sqrtTwDnP (x : twfloat) :=
  let: TWFloat x0 x1 x2 := x in
  let q := threeSqRt x in
  if posFp (valDnTw q) && posFp (x0 + x1 + x2)%float
  then shiftDn q else TWFloat nan nan nan.

(* ===========================================================================*)
(*  What they compute                                                         *)
(* ===========================================================================*)

Compute threeDiv (fp2tw 1) (fp2tw 3).
Compute timesTwTw (threeDiv (fp2tw 1) (fp2tw 3)) (fp2tw 3).
Compute threeReci (fp2tw 3).
Compute threeDiv (toTw 1 1e-20 1e-40) (toTw 3 1e-20 1e-40).
Compute (divTwDnP (fp2tw 1) (fp2tw 3), divTwUpP (fp2tw 1) (fp2tw 3)).
Compute threeSqRt (fp2tw 2).
Compute timesTwTw (threeSqRt (fp2tw 2)) (threeSqRt (fp2tw 2)).
Compute (sqrtTwDnP (fp2tw 2), sqrtTwUpP (fp2tw 2)).
