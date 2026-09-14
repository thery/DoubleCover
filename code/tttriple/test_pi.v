From mathcomp Require Import all_ssreflect.
From Stdlib Require Import ZArith Floats.
From twarith Require Import twarith tw_updn tw_ops.

(* A smoke test: the arithmetic run on something worth computing.             *)
(* The first half computes pi by Machin's formula with the plain operations,  *)
(* to see how many digits three words really hold.  The second half runs the  *)
(* interface's own operations and looks at the brackets they give.            *)
(* Nothing here is proved: it is a test, not a proof, and the obligations of  *)
(* tw_ops.v are still admitted.                                              *)

(* ---------------------------------------------------------------------------*)
(*  Pi, by Machin's formula                                                   *)
(* ---------------------------------------------------------------------------*)

(* Small whole numbers as floats, one addition at a time.                     *)
Fixpoint nat2fp (n : nat) : float :=
  match n with O => 0%float | S p => (nat2fp p + 1)%float end.

(* The arc tangent series in Horner's form, which keeps every term in the     *)
(* range where a triple word is worth having:                                 *)
(*   1/k - y * (1/(k+2) - y * (1/(k+4) - ...))                                *)
Fixpoint atanH (n : nat) (y : twfloat) (k : nat) : twfloat :=
  match n with
  | O => divTwTw (fp2tw 1) (fp2tw (nat2fp k))
  | S n' =>
      plusTwTw (divTwTw (fp2tw 1) (fp2tw (nat2fp k)))
               (negTw (timesTwTw y (atanH n' y (k + 2))))
  end.

(* The arc tangent of one over a whole number.                                *)
Definition atanInv (m : nat) (terms : nat) : twfloat :=
  let x := divTwTw (fp2tw 1) (fp2tw (nat2fp m)) in
  let y := timesTwTw x x in
  timesTwTw x (atanH terms y 1).

(* Machin: pi = 16 arctan(1/5) - 4 arctan(1/239).  Three words hold about     *)
(* forty-eight digits, so the two series are taken further than for two.      *)
Definition piTw :=
  plusTwTw (timesTwTw (fp2tw 16) (atanInv 5 45))
           (negTw (timesTwTw (fp2tw 4) (atanInv 239 18))).

(* Pi to fifty digits is                                                      *)
(*   3.14159265358979323846264338327950288419716939937510                    *)
(* and the three words below add up to                                        *)
(*   3.1415926535897932384626433832795028841971693993...                      *)
Compute piTw.

(* And the machine's own pi, for comparison: sixteen digits.                  *)
Compute fp2tw 3.141592653589793.

(* ---------------------------------------------------------------------------*)
(*  The interface, and what it brackets                                       *)
(* ---------------------------------------------------------------------------*)

Import TwFloat.

(* Each pair below is a lower and an upper bound of the same number.          *)
Compute (div_DN tt (fp2tw 1) (fp2tw 3), div_UP tt (fp2tw 1) (fp2tw 3)).
Compute (div_DN tt (fp2tw 22) (fp2tw 7), div_UP tt (fp2tw 22) (fp2tw 7)).
Compute (mul_DN tt (fp2tw 3) (fp2tw 7), mul_UP tt (fp2tw 3) (fp2tw 7)).
Compute (add_DN tt piTw piTw, add_UP tt piTw piTw).
Compute (sub_DN tt piTw (fp2tw 3), sub_UP tt piTw (fp2tw 3)).

(* The root, from two Newton steps on the machine root.                       *)
Compute (sqrt_DN tt (fp2tw 2), sqrt_UP tt (fp2tw 2)).
Compute (sqrt_DN tt piTw, sqrt_UP tt piTw).

(* A whole number too large for one word enters as three: the leading word    *)
(* holds fifty-three bits of it, the next fifty-three more, and the third      *)
(* covers what is left.  A number one float holds is exact and needs no        *)
(* peeling; the two bounds are then the same triple.                           *)
Compute (fromZ_DN tt 123456789%Z, fromZ_UP tt 123456789%Z).
Compute (fromZ_DN tt 31415926535897932384%Z, fromZ_UP tt 31415926535897932384%Z).
Compute (fromZ_DN tt 314159265358979323846264338327950288419716939937510%Z,
         fromZ_UP tt 314159265358979323846264338327950288419716939937510%Z).

(* A negative number has no root here, and nought is refused too: the bound   *)
(* divides by the root it is looking for.                                     *)
Compute real (sqrt_UP tt (fp2tw (-1))).
Compute real (sqrt_UP tt (fp2tw 0)).

(* An operation that cannot answer says so, and saying so is reading as the   *)
(* whole line.  These are all false.                                          *)
Compute real (div_UP tt (fp2tw 1) (fp2tw 0)).
Compute real (mul_UP tt (fp2tw 1.7976931348623157e+308)
                        (fp2tw 1.7976931348623157e+308)).
Compute real (add_UP tt (fp2tw 1.7976931348623157e+308)
                        (fp2tw 1.7976931348623157e+308)).
