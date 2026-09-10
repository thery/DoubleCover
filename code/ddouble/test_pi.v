From Stdlib Require Import Floats.
From dwarith Require Import dwarith dw_updn dw_ops.

(* A smoke test: the arithmetic run on something worth computing.            *)
(* The first half computes pi by Machin's formula with the plain operations, *)
(* to see how many digits two words really hold.  The second half runs the   *)
(* interface's own operations, the ones with a theorem behind them, and      *)
(* looks at the brackets they give.                                          *)
(* Nothing here is proved: it is a test, not a proof.  A proved bracket for  *)
(* pi needs the module sealed, so that Interval's interval arithmetic can be *)
(* built on it - see the README.                                             *)

(* ---------------------------------------------------------------------------*)
(*  Pi, by Machin's formula                                                   *)
(* ---------------------------------------------------------------------------*)

(* Small whole numbers as floats, one addition at a time.                     *)
Fixpoint nat2fp (n : nat) : float :=
  match n with O => 0%float | S p => (nat2fp p + 1)%float end.

Definition negDw d :=
  let: DWFloat xh xl := d in DWFloat (- xh)%float (- xl)%float.

(* The arc tangent series in Horner's form, which keeps every term in the    *)
(* range where a double word is worth having:                                *)
(*   1/k - y * (1/(k+2) - y * (1/(k+4) - ...))                               *)
Fixpoint atanH (n : nat) (y : dwfloat) (k : nat) : dwfloat :=
  match n with
  | O => divDwDw2 (fp2dw 1) (fp2dw (nat2fp k))
  | S n' =>
      plusDwDw (divDwDw2 (fp2dw 1) (fp2dw (nat2fp k)))
               (negDw (timesDwDw y (atanH n' y (k + 2))))
  end.

(* The arc tangent of one over a whole number.                                *)
Definition atanInv (m : nat) (terms : nat) : dwfloat :=
  let x := divDwDw2 (fp2dw 1) (fp2dw (nat2fp m)) in
  let y := timesDwDw x x in
  timesDwDw x (atanH terms y 1).

(* Machin: pi = 16 arctan(1/5) - 4 arctan(1/239).  Thirty terms of the first *)
(* series and twelve of the second are past what two words can hold.         *)
Definition piDw :=
  plusDwDw (timesDwDw (fp2dw 16) (atanInv 5 30))
           (negDw (timesDwDw (fp2dw 4) (atanInv 239 12))).

(* Gives DWFloat 3.1415926535897931 1.2246467991473527e-16.                   *)
(* The true low word is 1.2246467991473532e-16, so this is right to about    *)
(* thirty-one digits: the arithmetic holds thirty-two, and forty operations  *)
(* of it have eaten the last one.                                            *)
Compute piDw.

(* And the machine's own pi, for comparison: sixteen digits.                  *)
Compute fp2dw 3.141592653589793.

(* ---------------------------------------------------------------------------*)
(*  The interface, and what it brackets                                       *)
(* ---------------------------------------------------------------------------*)

Import DwFloat.

(* Each pair below is a lower and an upper bound of the same number, and     *)
(* each is what add_DN_correct, div_DN_correct and their partners say it is. *)
Compute (div_DN tt (fp2dw 1) (fp2dw 3), div_UP tt (fp2dw 1) (fp2dw 3)).
Compute (div_DN tt (fp2dw 22) (fp2dw 7), div_UP tt (fp2dw 22) (fp2dw 7)).
Compute (mul_DN tt (fp2dw 3) (fp2dw 7), mul_UP tt (fp2dw 3) (fp2dw 7)).
Compute (add_DN tt piDw piDw, add_UP tt piDw piDw).
Compute (sub_DN tt piDw (fp2dw 3), sub_UP tt piDw (fp2dw 3)).

(* The root, from a Newton step on the machine root.  The true low word of    *)
(* the root of two is -9.6672933134529135e-17, which the pair below holds;    *)
(* the two are about seven times ten to the minus thirty-two apart.           *)
Compute (sqrt_DN tt (fp2dw 2), sqrt_UP tt (fp2dw 2)).
Compute (sqrt_DN tt piDw, sqrt_UP tt piDw).

(* A negative number has no root here, and nought is refused too: the         *)
(* bound divides by the root it is looking for.                               *)
Compute real (sqrt_UP tt (fp2dw (-1))).
Compute real (sqrt_UP tt (fp2dw 0)).

(* An operation that cannot answer says so, and saying so is reading as the  *)
(* whole line.  These are all false.                                         *)
Compute real (div_UP tt (fp2dw 1) (fp2dw 0)).
Compute real (mul_UP tt (fp2dw 1.7976931348623157e+308)
                        (fp2dw 1.7976931348623157e+308)).
Compute real (add_UP tt (fp2dw 1.7976931348623157e+308)
                        (fp2dw 1.7976931348623157e+308)).
