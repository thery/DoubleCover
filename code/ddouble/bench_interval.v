From Stdlib Require Import Reals.
From dwarith Require Import dwarith dw_ops dw_unsafe.
From Interval Require Import Tactic.
From Coquelicot Require Import Coquelicot.

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
(* twenty times over and the whole cost is the splitting.  The two after      *)
(* them are the other two goals of that same testsuite file, an integral       *)
(* over a range and one out to infinity, which go through the tactic's         *)
(* integration rather than its bisection.  The four at the end are light,      *)
(* and are here only to show that they are.                                    *)

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

(* The two integrals of testsuite/example-20220302.v, the other goals of       *)
(* that file.                                                                 *)
Lemma int_range :
  Rabs (RInt (fun tau => (0.5 * ln (tau^2 + 2.25) + 4.1396 + ln PI)^2
                         / (0.25 + tau^2)) (-100000) 100000 - 226.8435) <= 2e-4.
Proof. Time integral. Qed.

Lemma int_infinite :
  Rabs (RInt_gen (fun tau =>
          (1 + (0.5 * ln (1 + 2.25/tau^2) + 4.1396 + ln PI) / ln tau)^2
          / (1 + 0.25 / tau^2) * (powerRZ tau (-2) * (ln tau)^2))
        (at_point 100000) (Rbar_locally p_infty) - 0.00317742) <= 1e-5.
Proof. Time integral. Qed.

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

(* The two integrals of testsuite/example-20220302.v, the other goals of       *)
(* that file.                                                                 *)
Lemma int_range :
  Rabs (RInt (fun tau => (0.5 * ln (tau^2 + 2.25) + 4.1396 + ln PI)^2
                         / (0.25 + tau^2)) (-100000) 100000 - 226.8435) <= 2e-4.
Proof. Time integral. Qed.

Lemma int_infinite :
  Rabs (RInt_gen (fun tau =>
          (1 + (0.5 * ln (1 + 2.25/tau^2) + 4.1396 + ln PI) / ln tau)^2
          / (1 + 0.25 / tau^2) * (powerRZ tau (-2) * (ln tau)^2))
        (at_point 100000) (Rbar_locally p_infty) - 0.00317742) <= 1e-5.
Proof. Time integral. Qed.

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
(*   method_error, i_prec 80             5.792  5.753     1.470  1.473        *)
(*   poly_error,   i_prec 90             0.057  0.060     0.048  0.048        *)
(*   cancellation, depth 20, prec 60    74.317 74.013    39.922 39.480        *)
(*   int_range,    integral              2.890  2.856     2.857  2.899        *)
(*   int_infinite, integral              0.340  0.339     0.343  0.367        *)
(*   pi to fifteen digits                0.012  0.012     0.010  0.011        *)
(*   exp 1 to fifteen digits             0.012  0.012     0.011  0.011        *)
(*   ln 2 to fifteen digits              0.013  0.013     0.011  0.012        *)
(*   |sin x / x| <= 1, bisect            0.008  0.012     0.012  0.012        *)
(*                                                                            *)
(* Three lines are worth reading and they do not agree.                       *)
(*                                                                            *)
(* method_error, a Taylor model at eighty bits, is about four times           *)
(* quicker on double words.  cancellation, the bisection loop run twenty      *)
(* deep at sixty bits, is about twice.  The two integrals are level: the      *)
(* double words neither help nor cost anything there.  So the gain is not     *)
(* a property of the arithmetic on its own - it is where the tactic spends    *)
(* its time.  Where the work is arithmetic at a precision a double word       *)
(* covers, the words win; where it is the tactic's own bookkeeping, they      *)
(* change nothing.                                                            *)
(*                                                                            *)
(* The four at the end are hundredths of a second and should not be read      *)
(* as a result either way.  An earlier run of this file, before               *)
(* method_error was in it, made exp 1 look thirteen times quicker on          *)
(* double words; that was the first heavy call warming something up, not      *)
(* arithmetic.                                                                *)
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
(*                                                                            *)
(* WHERE THESE GOALS COME FROM.                                               *)
(* Interval's sources ask for a precision above the fifty-three bits of a     *)
(* float in fourteen places.  Eleven of them are inside its own proof of      *)
(* the primitive-float exponential, in                                        *)
(* src/Interval/Float_full_primfloat.v, where each is a side condition        *)
(* standing in a context of local definitions and hypotheses, so there is     *)
(* nothing to lift out without carrying the proof around it.  The other       *)
(* three are the two testsuite files the first two goals above come from.     *)
(* The two integrals are the remaining goals of one of those files; they      *)
(* name no precision, which is why a search for one does not find them.       *)
