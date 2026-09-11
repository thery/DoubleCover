From Stdlib Require Import Reals.
From dwarith Require Import dwarith dw_ops dw_unsafe.
From Interval Require Import Tactic.

Open Scope R_scope.

(* The same goals proved twice: once by the tactic as it ships, which runs    *)
(* on arbitrary-precision integers, and once by the same tactic over          *)
(* double words.  Both are called `interval'; which one is meant is           *)
(* decided by the Import.                                                     *)
(*                                                                            *)
(* The first two come from Interval's own testsuite, where they are the       *)
(* reason double precision is not enough: a relative error of five times      *)
(* ten to the minus eighteen for a rational approximation of the              *)
(* exponential, and the error of a polynomial one.  The third is a            *)
(* difference the tactic cannot see is nought, so it splits the range         *)
(* twenty times over and the whole cost is the splitting.  The four below     *)
(* them are light, and are here only to show that they are.                   *)

Notation pow2 := (Raux.bpow Zaux.radix2).

(* A rational approximation of the exponential, from                          *)
(* testsuite/example-20220302.v.                                              *)
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

(* And a polynomial one, from testsuite/example-20210218.v, where it is       *)
(* plotted rather than bounded.                                               *)
Definition g x :=
  1 + x * (4503599627370587 * powerRZ 2 (-52)
    + x * (4503599627370551 * powerRZ 2 (-53)
    + x * (6004799497195935 * powerRZ 2 (-55)
    + x * (6004799498485985 * powerRZ 2 (-57)
    + x * (2402017533563707 * powerRZ 2 (-58)
    + x * (6405354563481393 * powerRZ 2 (-62))))))) - exp x.

Module ITdw := IntervalTactic DwFloatU.

(* ---------------------------------------------------------------------------*)
(*  As it ships: arbitrary-precision integers                                 *)
(* ---------------------------------------------------------------------------*)
Module Bigints.

Lemma method_error : forall t : R, Rabs t <= 0.35 ->
  Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. Time interval with (i_bisect t, i_taylor t, i_prec 80). Qed.

Lemma poly_error : forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 90). Qed.

Lemma cancellation : forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. Time interval with (i_bisect x, i_depth 20, i_prec 60). Qed.

Goal (3.14159265358979 <= PI <= 3.1415926535898)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (2.71828182845904 <= exp 1 <= 2.7182818284591)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (0.69314718055994 <= ln 2 <= 0.6931471805600)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal forall x, (1 <= x <= 2)%R -> (Rabs (sin x / x) <= 1)%R.
Proof. intros x Hx. Time interval with (i_bisect x, i_prec 80). Qed.

End Bigints.

(* ---------------------------------------------------------------------------*)
(*  The same, over double words                                               *)
(* ---------------------------------------------------------------------------*)
Module DoubleWords.
Import ITdw.

Lemma method_error : forall t : R, Rabs t <= 0.35 ->
  Rabs ((f t - exp t) / exp t) <= 5e-18.
Proof. intros t Ht. Time interval with (i_bisect t, i_taylor t, i_prec 80). Qed.

Lemma poly_error : forall x, -1/32 <= x <= 1/32 -> Rabs (g x) <= 1e-13.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 90). Qed.

Lemma cancellation : forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. Time interval with (i_bisect x, i_depth 20, i_prec 60). Qed.

Goal (3.14159265358979 <= PI <= 3.1415926535898)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (2.71828182845904 <= exp 1 <= 2.7182818284591)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (0.69314718055994 <= ln 2 <= 0.6931471805600)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal forall x, (1 <= x <= 2)%R -> (Rabs (sin x / x) <= 1)%R.
Proof. intros x Hx. Time interval with (i_bisect x, i_prec 80). Qed.

End DoubleWords.

(* -------------------------------------------------------------------        *)
(* What it gave, two runs on this machine, seconds:                           *)
(*                                                                            *)
(*                                        bigints         double words        *)
(*   method_error, i_prec 80             5.787  5.737     1.456  1.506        *)
(*   poly_error,   i_prec 90             0.054  0.057     0.051  0.080        *)
(*   cancellation, depth 20, prec 60    74.603 74.655    39.549 39.577        *)
(*   pi to fifteen digits                0.012  0.013     0.010  0.011        *)
(*   exp 1 to fifteen digits             0.012  0.012     0.010  0.011        *)
(*   ln 2 to fifteen digits              0.013  0.013     0.011  0.011        *)
(*   |sin x / x| <= 1, bisect            0.008  0.008     0.011  0.012        *)
(*                                                                            *)
(* Two lines say anything: the two goals that take seconds rather than        *)
(* hundredths.  method_error is about four times quicker on double words      *)
(* and cancellation about twice.  The two measure different things:           *)
(* method_error is a Taylor model at eighty bits, cancellation is the         *)
(* bisection loop run twenty deep at sixty, where the work is the splitting   *)
(* and the arithmetic on each piece is plain.  Everything below those two     *)
(* is at the level of the noise and should not be read as a result either     *)
(* way.                                                                       *)
(*                                                                            *)
(* An earlier run of this file, before method_error was in it, made exp 1     *)
(* look thirteen times quicker on double words.  That was the first heavy     *)
(* call warming something up, not arithmetic; the figures above show it       *)
(* level.  Anything measured in hundredths here is worth nothing.             *)
(*                                                                            *)
(* WHAT A CONSTANT IN A GOAL IS WORTH.                                        *)
(* The tactic builds a goal's constants with fromZ_UP and fromZ_DN, and       *)
(* ours split a whole number into its top fifty-three bits and what is        *)
(* left, so the constant enters as two words:                                 *)
(*                                                                            *)
(*   fromZ_DN tt 314159265358979323 = DWFloat 3.1415926535897933e+17 (-6)     *)
(*   fromZ_UP tt 314159265358979323 = DWFloat 3.1415926535897933e+17 (-4)     *)
(*                                                                            *)
(* - two apart on a number of that size, where a single float is out by       *)
(* about forty.  A number one float already holds is exact.  Past about       *)
(* two to the one hundred and fifth the split gives up and the one-word       *)
(* answer is used again, so a decimal of more than about thirty-one digits    *)
(* is still held to fifteen.                                                  *)
