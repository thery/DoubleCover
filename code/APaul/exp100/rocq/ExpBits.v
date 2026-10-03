(** * S1: the real x of the bits xb

    [xreal xb] is the double whose bits are [xb] (Flocq's [b64_of_bits]).
    For a finite x with |x| < 1024 ([xbexp xb < be_big]), [is_x xb x]:
    the sign bit gives the sign of x and [xfix xb] = floor(|x| 2^P). *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core IEEE754.Binary IEEE754.Bits.
From Exp100 Require Import ExpConsts ExpModel.

Open Scope R_scope.

(** The double of the bits [xb]. *)
Definition xreal (xb : Z) : R := @B2R 53 1024 (b64_of_bits xb).

(** What the model reads of x: the sign, then floor(|x| 2^P). *)
Definition is_x (xb : Z) (x : R) : Prop :=
  (xsign xb = 0%Z -> 0 <= x) /\ (xsign xb <> 0%Z -> x <= 0) /\
  IZR (xfix xb) <= Rabs x * bpow radix2 P < IZR (xfix xb) + 1.

Theorem xreal_is_x xb : (0 <= xb < 2 ^ 64)%Z -> (xbexp xb < be_big)%Z ->
  is_x xb (xreal xb).
Proof.
Admitted.
