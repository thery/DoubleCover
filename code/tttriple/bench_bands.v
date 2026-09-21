From Stdlib Require Import Reals Psatz ZArith.
From Flocq Require Import Core.
From Interval Require Import Tactic.
From dwarith Require dw_unsafe.
From twarith Require tw_unsafe.

Open Scope R_scope.

(* Interval's tactic over each of the four arithmetics, on the same goals.    *)
(*                                                                            *)
(* Which arithmetic runs is decided by the tactic's dispatch, `src/Tactic.v`  *)
(* around line eighty: WITHOUT `i_prec' the tactic uses primitive floats at   *)
(* fifty-three bits, hardwired, whatever module it was built on; WITH         *)
(* `i_prec' it uses that module.  For the two word modules the number asked   *)
(* for changes nothing about the arithmetic - `PtoP' throws it away and the   *)
(* precision is fixed - but it does tell Interval's transcendental code how   *)
(* many bits to aim for.                                                      *)
(*                                                                            *)
(* NOT on the build path: native compilation overflows the stack at Qed on    *)
(* these files.  Run it by hand, and read the timings off `Time', never off   *)
(* whether the file compiled:                                                 *)
(*                                                                            *)
(*   coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_bands.v*)
(*                                                                            *)
(* Every call below is the first heavy one in its module, so none of them is  *)
(* warmed up by the one before.  For a timing to compare, run one module.     *)

Module ITdw := IntervalTactic dw_unsafe.DwFloatU.
Module ITtw := IntervalTactic tw_unsafe.TwFloatU.

(* ---------------------------------------------------------------------------*)
(*  The goals                                                                 *)
(* ---------------------------------------------------------------------------*)

(* Three brackets on pi, at forty-seven, eighty-two, a hundred and five and   *)
(* a hundred and fifty bits.  One float holds the first, a double word the    *)
(* second, and only a triple word the last two.  The tightness of the bracket *)
(* is the whole dial: nothing else about the goal changes.                    *)
Notation pi14l := 3.14159265358979.
Notation pi14h := 3.14159265358980.
Notation pi24l := 3.141592653589793238462643.
Notation pi24h := 3.141592653589793238462644.
Notation pi34l := 3.1415926535897932384626433832795.
Notation pi34h := 3.1415926535897932384626433832796.
Notation pi45l := 3.14159265358979323846264338327950288419716939.
Notation pi45h := 3.14159265358979323846264338327950288419716940.

(* The two rational approximations Interval's own testsuite bounds, from      *)
(* `testsuite/example-20220302.v' and `testsuite/example-20210218.v'.  They   *)
(* are the reason double precision is not enough there.                       *)
Notation pow2 := (Raux.bpow Zaux.radix2).
Definition p0 := 1 * pow2 (-2).
Definition p1 := 4002712888408905 * pow2 (-59).
Definition p2 := 1218985200072455 * pow2 (-66).
Definition q0 := 1 * pow2 (-1).
Definition q1 := 8006155947364787 * pow2 (-57).
Definition q2 := 4573527866750985 * pow2 (-63).

Definition f t :=
  let t2 := t * t in
  let p := p0 + t2 * (p1 + t2 * p2) in
  let q := q0 + t2 * (q1 + t2 * q2) in
  2 * ((t * p) / (q - t * p) + 1/2).

Definition g x :=
  1 + x * (4503599627370587 * powerRZ 2 (-52)
    + x * (4503599627370551 * powerRZ 2 (-53)
    + x * (6004799497195935 * powerRZ 2 (-55)
    + x * (6004799498485985 * powerRZ 2 (-57)
    + x * (2402017533563707 * powerRZ 2 (-58)
    + x * (6405354563481393 * powerRZ 2 (-62))))))) - exp x.

(* ---------------------------------------------------------------------------*)
(*  As it ships: primitive floats, fifty-three bits                           *)
(* ---------------------------------------------------------------------------*)

Module Floats.

Goal pi14l <= PI <= pi14h.
Proof. Time interval. Qed.

(* Nothing tighter than fourteen digits is within reach of one float, and     *)
(* the tactic says so: the three brackets below are all refused.               *)
Goal pi24l <= PI <= pi24h.
Proof. Fail interval. Abort.

End Floats.

(* ---------------------------------------------------------------------------*)
(*  Arbitrary-precision integers                                              *)
(* ---------------------------------------------------------------------------*)

Module Bigints.

Goal pi14l <= PI <= pi14h.
Proof. Time interval with (i_prec 60). Qed.

Goal pi24l <= PI <= pi24h.
Proof. Time interval with (i_prec 100). Qed.

Goal pi34l <= PI <= pi34h.
Proof. Time interval with (i_prec 170). Qed.

Goal pi45l <= PI <= pi45h.
Proof. Time interval with (i_prec 170). Qed.

Lemma method_error : forall t : R, Rabs t <= 0.35 ->
  Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. Time interval with (i_bisect t, i_taylor t, i_prec 80). Qed.

Lemma poly_error : forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 90). Qed.

(* The control.  Its cost is the splitting, not the arithmetic: the tactic    *)
(* cannot see that the difference is nought, so it halves the range twenty    *)
(* times over.  Whatever an arithmetic does here it does by being quick per   *)
(* operation, not by being precise.                                          *)
Lemma cancellation : forall x, (0 <= x <= 1)%R ->
  (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. Time interval with (i_bisect x, i_depth 20, i_prec 60). Qed.

End Bigints.

(* ---------------------------------------------------------------------------*)
(*  Double words                                                              *)
(* ---------------------------------------------------------------------------*)

Module DoubleWords.
Import ITdw.

Goal pi14l <= PI <= pi14h.
Proof. Time interval with (i_prec 60). Qed.

Goal pi24l <= PI <= pi24h.
Proof. Time interval with (i_prec 107). Qed.

(* A hundred and five bits is past what this format delivers - it holds a     *)
(* hundred and seven and loses five to seven of them across a whole           *)
(* evaluation - so the two tighter brackets are refused, and honestly.        *)
Goal pi34l <= PI <= pi34h.
Proof. Fail interval with (i_prec 107). Abort.

Lemma method_error : forall t : R, Rabs t <= 0.35 ->
  Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. Time interval with (i_bisect t, i_taylor t, i_prec 80). Qed.

Lemma poly_error : forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 90). Qed.

Lemma cancellation : forall x, (0 <= x <= 1)%R ->
  (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. Time interval with (i_bisect x, i_depth 20, i_prec 60). Qed.

End DoubleWords.

(* ---------------------------------------------------------------------------*)
(*  Triple words                                                              *)
(* ---------------------------------------------------------------------------*)

Module TripleWords.
Import ITtw.

Goal pi14l <= PI <= pi14h.
Proof. Time interval with (i_prec 60). Qed.

Goal pi24l <= PI <= pi24h.
Proof. Time interval with (i_prec 107). Qed.

Goal pi34l <= PI <= pi34h.
Proof. Time interval with (i_prec 159). Qed.

Goal pi45l <= PI <= pi45h.
Proof. Time interval with (i_prec 159). Qed.

Lemma poly_error : forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 90). Qed.

Lemma cancellation : forall x, (0 <= x <= 1)%R ->
  (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. Time interval with (i_bisect x, i_depth 20, i_prec 60). Qed.

(* THE GOAL THIS ARITHMETIC USED TO REFUSE.  It was not precision and it was  *)
(* not the Taylor model: it was the midpoint.  `plusTwTw' adds to nearest    *)
(* but does not sweep, so a third and a third came back as three words that  *)
(* overlap, `wellFormed' was false and the whole triple read as nothing -    *)
(* Interval then had no point to halve its range at, and every goal that     *)
(* bisects was refused.  The midpoint is now the swept sum, held between the *)
(* two ends; see `tw_ops.v'.                                                 *)
Lemma method_error : forall t : R, Rabs t <= 0.35 ->
  Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. Time interval with (i_bisect t, i_taylor t, i_prec 80). Qed.

End TripleWords.
