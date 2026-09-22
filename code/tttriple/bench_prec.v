(* ===========================================================================*)
(*  The same goals, every arithmetic at the SAME precision                    *)
(* ===========================================================================*)
(*                                                                            *)
(* `bench_bands.v' asks bignums for the precision each GOAL needs, which is   *)
(* the fair question if one is buying a proof.  It is not the fair question   *)
(* about the arithmetic: `cancellation' asks for sixty bits, and a triple     *)
(* word does a hundred and fifty-nine on every call whatever is asked.  Here  *)
(* bignums are pinned at a hundred and seven, which is what a double word     *)
(* holds, and at a hundred and fifty-nine, which is what a triple word holds, *)
(* and every goal is run at both.                                             *)
(*                                                                            *)
(* Run by hand:                                                               *)
(*                                                                            *)
(*   coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_prec.v *)

From Stdlib Require Import Reals Psatz ZArith.
From Interval Require Import Tactic.
From dwarith Require dw_unsafe.
From twarith Require tw_unsafe.

Module ITdw := IntervalTactic dw_unsafe.DwFloatU.
Module ITtw := IntervalTactic tw_unsafe.TwFloatU.

Open Scope R_scope.

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


(* Each goal is timed whether it goes through or not, so a refusal has a cost *)
(* beside it too.                                                             *)

Module B107.
Goal pi14l <= PI <= pi14h.
Proof. idtac "B107 pi14".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi24l <= PI <= pi24h.
Proof. idtac "B107 pi24".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi34l <= PI <= pi34h.
Proof. idtac "B107 pi34".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi45l <= PI <= pi45h.
Proof. idtac "B107 pi45".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal forall t : R, Rabs t <= 0.35 -> Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. idtac "B107 method_error".
Time first [interval with (i_bisect t, i_taylor t, i_prec 107); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. idtac "B107 poly_error".
Time first [interval with (i_bisect x, i_taylor x, i_prec 107); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. idtac "B107 cancellation".
Time first [interval with (i_bisect x, i_depth 20, i_prec 107); idtac "  ok"
           |idtac "  refused"]. Abort.
End B107.

Module B159.
Goal pi14l <= PI <= pi14h.
Proof. idtac "B159 pi14".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi24l <= PI <= pi24h.
Proof. idtac "B159 pi24".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi34l <= PI <= pi34h.
Proof. idtac "B159 pi34".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi45l <= PI <= pi45h.
Proof. idtac "B159 pi45".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal forall t : R, Rabs t <= 0.35 -> Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. idtac "B159 method_error".
Time first [interval with (i_bisect t, i_taylor t, i_prec 159); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. idtac "B159 poly_error".
Time first [interval with (i_bisect x, i_taylor x, i_prec 159); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. idtac "B159 cancellation".
Time first [interval with (i_bisect x, i_depth 20, i_prec 159); idtac "  ok"
           |idtac "  refused"]. Abort.
End B159.

Module DW.
Import ITdw.
Goal pi14l <= PI <= pi14h.
Proof. idtac "DW pi14".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi24l <= PI <= pi24h.
Proof. idtac "DW pi24".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi34l <= PI <= pi34h.
Proof. idtac "DW pi34".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi45l <= PI <= pi45h.
Proof. idtac "DW pi45".
Time first [interval with (i_prec 107); idtac "  ok"|idtac "  refused"]. Abort.
Goal forall t : R, Rabs t <= 0.35 -> Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. idtac "DW method_error".
Time first [interval with (i_bisect t, i_taylor t, i_prec 107); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. idtac "DW poly_error".
Time first [interval with (i_bisect x, i_taylor x, i_prec 107); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. idtac "DW cancellation".
Time first [interval with (i_bisect x, i_depth 20, i_prec 107); idtac "  ok"
           |idtac "  refused"]. Abort.
End DW.

Module TW.
Import ITtw.
Goal pi14l <= PI <= pi14h.
Proof. idtac "TW pi14".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi24l <= PI <= pi24h.
Proof. idtac "TW pi24".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi34l <= PI <= pi34h.
Proof. idtac "TW pi34".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal pi45l <= PI <= pi45h.
Proof. idtac "TW pi45".
Time first [interval with (i_prec 159); idtac "  ok"|idtac "  refused"]. Abort.
Goal forall t : R, Rabs t <= 0.35 -> Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. idtac "TW method_error".
Time first [interval with (i_bisect t, i_taylor t, i_prec 159); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. idtac "TW poly_error".
Time first [interval with (i_bisect x, i_taylor x, i_prec 159); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. idtac "TW cancellation".
Time first [interval with (i_bisect x, i_depth 20, i_prec 159); idtac "  ok"
           |idtac "  refused"]. Abort.
End TW.
