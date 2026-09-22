(* GENERATED per module by bench/run_goals.sh -- do not edit the copies. *)
From Stdlib Require Import Reals.
From Interval Require Import Tactic.
From Interval Require Import Xreal Basic Sig Float Float_full.
MODULE_IMPORT
Module IT := IntervalTactic MODULE_NAME.
Import IT.
Open Scope R_scope.

Notation pi14l := 3.14159265358979.
Notation pi14h := 3.14159265358980.
Notation pi24l := 3.141592653589793238462643.
Notation pi24h := 3.141592653589793238462644.
Notation pi34l := 3.1415926535897932384626433832795.
Notation pi34h := 3.1415926535897932384626433832796.
Notation pi45l := 3.14159265358979323846264338327950288419716939.
Notation pi45h := 3.14159265358979323846264338327950288419716940.
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

Goal pi14l <= PI <= pi14h.
idtac "pi14".
Time first [interval with (i_prec PREC); idtac "  ok" | idtac "  refused"]. Abort.
Goal pi24l <= PI <= pi24h.
idtac "pi24".
Time first [interval with (i_prec PREC); idtac "  ok" | idtac "  refused"]. Abort.
Goal pi34l <= PI <= pi34h.
idtac "pi34".
Time first [interval with (i_prec PREC); idtac "  ok" | idtac "  refused"]. Abort.
Goal pi45l <= PI <= pi45h.
idtac "pi45".
Time first [interval with (i_prec PREC); idtac "  ok" | idtac "  refused"]. Abort.
Goal forall t : R, Rabs t <= 0.35 -> Rabs ((f t - exp t) / exp t) <= 5e-18.
intros t Ht. idtac "method_error".
Time first [interval with (i_bisect t, i_taylor t, i_prec PREC); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
intros x Hx. idtac "poly_error".
Time first [interval with (i_bisect x, i_taylor x, i_prec PREC); idtac "  ok"
           |idtac "  refused"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
intros x H. idtac "cancellation".
Time first [interval with (i_bisect x, i_depth 20, i_prec PREC); idtac "  ok"
           |idtac "  refused"]. Abort.
