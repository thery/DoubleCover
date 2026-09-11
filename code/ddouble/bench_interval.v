From Stdlib Require Import Reals.
From dwarith Require Import dwarith dw_ops dw_unsafe.
From Interval Require Import Tactic.

(* The same goals proved twice: once by the tactic as it ships, which runs    *)
(* on arbitrary-precision integers, and once by the same tactic over          *)
(* double words.  Both are called `interval'; which one is meant is           *)
(* decided by the Import.  The precision asked for is the one Interval's      *)
(* own sources use when double precision is not enough.                       *)
(*                                                                            *)
(* WHY THE GOALS ONLY ASK FOR FIFTEEN DIGITS.  The tactic builds the          *)
(* constants in a goal with `fromZ_UP` and `fromZ_DN`, and ours put the       *)
(* whole number in the high word and leave the low one empty:                 *)
(*                                                                            *)
(*   fromZ_UP tt 314159265358979323 = DWFloat 0x1.17078bfda7a84p+58 0         *)
(*                                                                            *)
(* So a constant enters at fifty-three bits however many the arithmetic       *)
(* carries, and no precision downstream can recover what the input never      *)
(* had.  Until that is fixed the comparison can only be run where fifty-      *)
(* three bits of input suffice, which is what is below.  Both sides do        *)
(* the same work; only the speed is being compared.                           *)

Module ITdw := IntervalTactic DwFloatU.

(* ---------------------------------------------------------------------------*)
(*  As it ships: arbitrary-precision integers                                 *)
(* ---------------------------------------------------------------------------*)
Module Bigints.

Goal (3.14159265358979 <= PI <= 3.1415926535898)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (2.71828182845904 <= exp 1 <= 2.7182818284591)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (0.69314718055994 <= ln 2 <= 0.6931471805600)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal forall x, (-1 <= x <= 1)%R -> (exp x - 1 - x <= 1)%R.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 80). Qed.

Goal forall x, (1 <= x <= 2)%R -> (Rabs (sin x / x) <= 1)%R.
Proof. intros x Hx. Time interval with (i_bisect x, i_prec 80). Qed.

End Bigints.

(* ---------------------------------------------------------------------------*)
(*  The same, over double words                                               *)
(* ---------------------------------------------------------------------------*)
Module DoubleWords.
Import ITdw.

Goal (3.14159265358979 <= PI <= 3.1415926535898)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (2.71828182845904 <= exp 1 <= 2.7182818284591)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal (0.69314718055994 <= ln 2 <= 0.6931471805600)%R.
Proof. Time interval with (i_prec 80). Qed.

Goal forall x, (-1 <= x <= 1)%R -> (exp x - 1 - x <= 1)%R.
Proof. intros x Hx. Time interval with (i_bisect x, i_taylor x, i_prec 80). Qed.

Goal forall x, (1 <= x <= 2)%R -> (Rabs (sin x / x) <= 1)%R.
Proof. intros x Hx. Time interval with (i_bisect x, i_prec 80). Qed.

End DoubleWords.

(* -------------------------------------------------------------------        *)
(* What it gave, two runs on this machine, seconds, i_prec 80:                *)
(*                                                                            *)
(*                                          bigints      double words         *)
(*   pi to fifteen digits                 0.023 0.023    0.013 0.013          *)
(*   exp 1 to fifteen digits              0.145 0.145    0.010 0.011          *)
(*   ln 2 to fifteen digits               0.017 0.013    0.011 0.011          *)
(*   exp x - 1 - x, bisect and taylor     0.020 0.016    0.012 0.012          *)
(*   |sin x / x| <= 1, bisect             0.008 0.008    0.009 0.008          *)
(*                                                                            *)
(* Read it carefully.  These are hundredths of a second, so the only          *)
(* figure with real daylight round it is exp 1, where the double words        *)
(* are some thirteen times quicker.  Elsewhere they are a little ahead,       *)
(* and on the last goal the two are level.                                    *)
(*                                                                            *)
(* And remember what is NOT being compared.  Both sides are asked for         *)
(* fifteen digits, which a single float nearly holds, so this measures        *)
(* the cost of the machinery and not the worth of the extra digits.  The      *)
(* comparison that would settle anything - thirty digits, where the           *)
(* bigints must work and a double word would not have to - cannot be run      *)
(* until a constant can enter with more than fifty-three bits.                *)
