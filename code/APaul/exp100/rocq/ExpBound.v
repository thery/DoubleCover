(** * S2: the enclosure of exp x

    When [core_Z xb] returns [(y, hN)], y 2^(hN - P) is within
    D 2^(hN - P) of exp x, for every x the bits [xb] stand for
    ([is_x xb x]).  The error budget is in ../README. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From Exp100 Require Import ExpConsts ExpModel ExpBits.

Open Scope R_scope.

(** y is at least 2^P: T_j >= 2^P and the Horner value is >= C_0 = 2^P. *)
Theorem core_y_ge xb y hN : (0 <= xb < 2 ^ 64)%Z ->
  core_Z xb = inr (y, hN) -> (2 ^ P <= y)%Z.
Proof.
Admitted.

Theorem core_bound xb y hN x : (0 <= xb < 2 ^ 64)%Z ->
  core_Z xb = inr (y, hN) -> is_x xb x ->
  Rabs (exp x - IZR y * bpow radix2 (hN - P)) <=
    IZR D * bpow radix2 (hN - P).
Proof.
Admitted.
