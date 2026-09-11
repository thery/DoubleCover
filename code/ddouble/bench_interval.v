From Stdlib Require Import Reals Psatz ZArith List Floats.
From Flocq Require Import Core PrimFloat BinarySingleNaN.
From dwarith Require Import dwarith dw_ops dw_unsafe.
From Interval Require Import Tactic.
From Coquelicot Require Import Coquelicot.

Import ListNotations.
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


(* The table of sixty-four exponentials that Interval's own primitive-float   *)
(* exponential is built on, from src/Interval/Float_full_primfloat.v.  Its    *)
(* proof checks each entry against the exponential it stands for, to within   *)
(* two to the minus fifty-three, with one interval call apiece at sixty-one   *)
(* bits - the do 64 in that file.  It is the only one of the eleven calls     *)
(* inside that proof that can be lifted out whole, because the goal it runs   *)
(* on depends on nothing but the table.                                       *)
Definition consts : list PrimFloat.float := [
  0x1.0000000000000p0%float;
  0x1.02c9a3e778061p0%float;
  0x1.059b0d3158574p0%float;
  0x1.0874518759bc8p0%float;
  0x1.0b5586cf9890fp0%float;
  0x1.0e3ec32d3d1a2p0%float;
  0x1.11301d0125b51p0%float;
  0x1.1429aaea92de0p0%float;
  0x1.172b83c7d517bp0%float;
  0x1.1a35beb6fcb75p0%float;
  0x1.1d4873168b9aap0%float;
  0x1.2063b88628cd6p0%float;
  0x1.2387a6e756238p0%float;
  0x1.26b4565e27cddp0%float;
  0x1.29e9df51fdee1p0%float;
  0x1.2d285a6e4030bp0%float;
  0x1.306fe0a31b715p0%float;
  0x1.33c08b26416ffp0%float;
  0x1.371a7373aa9cbp0%float;
  0x1.3a7db34e59ff7p0%float;
  0x1.3dea64c123422p0%float;
  0x1.4160a21f72e2ap0%float;
  0x1.44e086061892dp0%float;
  0x1.486a2b5c13cd0p0%float;
  0x1.4bfdad5362a27p0%float;
  0x1.4f9b2769d2ca7p0%float;
  0x1.5342b569d4f82p0%float;
  0x1.56f4736b527dap0%float;
  0x1.5ab07dd485429p0%float;
  0x1.5e76f15ad2148p0%float;
  0x1.6247eb03a5585p0%float;
  0x1.6623882552225p0%float;
  0x1.6a09e667f3bcdp0%float;
  0x1.6dfb23c651a2fp0%float;
  0x1.71f75e8ec5f74p0%float;
  0x1.75feb564267c9p0%float;
  0x1.7a11473eb0187p0%float;
  0x1.7e2f336cf4e62p0%float;
  0x1.82589994cce13p0%float;
  0x1.868d99b4492edp0%float;
  0x1.8ace5422aa0dbp0%float;
  0x1.8f1ae99157736p0%float;
  0x1.93737b0cdc5e5p0%float;
  0x1.97d829fde4e50p0%float;
  0x1.9c49182a3f090p0%float;
  0x1.a0c667b5de565p0%float;
  0x1.a5503b23e255dp0%float;
  0x1.a9e6b5579fdbfp0%float;
  0x1.ae89f995ad3adp0%float;
  0x1.b33a2b84f15fbp0%float;
  0x1.b7f76f2fb5e47p0%float;
  0x1.bcc1e904bc1d2p0%float;
  0x1.c199bdd85529cp0%float;
  0x1.c67f12e57d14bp0%float;
  0x1.cb720dcef9069p0%float;
  0x1.d072d4a07897cp0%float;
  0x1.d5818dcfba487p0%float;
  0x1.da9e603db3285p0%float;
  0x1.dfc97337b9b5fp0%float;
  0x1.e502ee78b3ff6p0%float;
  0x1.ea4afa2a490dap0%float;
  0x1.efa1bee615a27p0%float;
  0x1.f50765b6e4540p0%float;
  0x1.fa7c1819e90d8p0%float ].

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

Lemma exp_table : forall i, (0 <= i <= 63)%Z ->
  Rabs (SF2R Zaux.radix2 (Prim2SF (nth (Z.to_nat i) consts 0%float))
        - exp (IZR i * (Rpower.ln 2 / 64))) <= pow2 (-53).
Proof.
intros i [Hi1 Hi2].
assert (Hi: forall j, (i <= j)%Z -> i = j \/ (i <= Z.pred j)%Z) by lia.
Time do 64 (apply Hi in Hi2 ; destruct Hi2 as [->|Hi2] ;
  [cbv [consts nth Z.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Nat.add];
   cbn -[Raux.bpow]; interval with (i_prec 61) | simpl Z.pred in Hi2]).
now elim (Z.le_trans _ _ _ Hi1 Hi2).
Qed.

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

Lemma exp_table : forall i, (0 <= i <= 63)%Z ->
  Rabs (SF2R Zaux.radix2 (Prim2SF (nth (Z.to_nat i) consts 0%float))
        - exp (IZR i * (Rpower.ln 2 / 64))) <= pow2 (-53).
Proof.
intros i [Hi1 Hi2].
assert (Hi: forall j, (i <= j)%Z -> i = j \/ (i <= Z.pred j)%Z) by lia.
Time do 64 (apply Hi in Hi2 ; destruct Hi2 as [->|Hi2] ;
  [cbv [consts nth Z.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Nat.add];
   cbn -[Raux.bpow]; interval with (i_prec 61) | simpl Z.pred in Hi2]).
now elim (Z.le_trans _ _ _ Hi1 Hi2).
Qed.

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
(*   method_error, i_prec 80             6.169  5.711     1.497  1.454        *)
(*   poly_error,   i_prec 90             0.064  0.057     0.055  0.050        *)
(*   cancellation, depth 20, prec 60    74.578 74.031    39.302 39.752        *)
(*   int_range,    integral              2.826  2.876     2.919  2.869        *)
(*   int_infinite, integral              0.340  0.339     0.357  0.344        *)
(*   exp_table,    i_prec 61 x 64        3.887  3.938     3.759  3.801        *)
(*   pi to fifteen digits                0.012  0.012     0.010  0.011        *)
(*   exp 1 to fifteen digits             0.012  0.011     0.010  0.011        *)
(*   ln 2 to fifteen digits              0.013  0.014     0.011  0.012        *)
(*   |sin x / x| <= 1, bisect            0.008  0.008     0.009  0.009        *)
(*                                                                            *)
(* Six lines are heavy enough to read, and they do not agree.                 *)
(*                                                                            *)
(* method_error, a Taylor model at eighty bits, is about four times           *)
(* quicker on double words.  cancellation, the bisection loop run twenty      *)
(* deep at sixty bits, is about twice.  The other three - the two             *)
(* integrals and the table of sixty-four exponentials - are level: the        *)
(* double words neither help nor cost anything there.                         *)
(*                                                                            *)
(* So the gain is not a property of the arithmetic on its own.  It is where   *)
(* the tactic spends its time.  Where that is arithmetic at a precision a     *)
(* double word covers, the words win; where it is the tactic's own            *)
(* bookkeeping, or reducing a term, they change nothing.                      *)
(*                                                                            *)
(* The four at the end are hundredths of a second and should not be read      *)
(* as a result either way.  Nor should a goal run first in a file: an         *)
(* earlier version of this file, before method_error was in it, made exp 1    *)
(* look thirteen times quicker on double words, and that was the first        *)
(* heavy call warming something up.  exp_table timed on its own in a file     *)
(* of its own came out 5.373 against 3.851 for the same reason; the           *)
(* figures above, with five heavier goals ahead of it, are the ones to        *)
(* believe.                                                                   *)
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
(* standing in a context of local definitions and hypotheses.  Only one of    *)
(* those eleven can be lifted out whole - the do 64, which is exp_table       *)
(* above - because its goal depends on nothing but the table.  The other      *)
(* three of the fourteen are the two testsuite files the first two goals      *)
(* come from.  The two integrals are the remaining goals of one of those      *)
(* files; they name no precision, which is why a search for one does not      *)
(* find them.                                                                 *)
