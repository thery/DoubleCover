(** * S3: the filter

    When [decide_Z y hN] returns 0, no z within D 2^(hN - P) of
    y 2^(hN - P) is hard: z / v is at distance at least 2^-m from every
    integer, v being half an ulp of z ([vexp] of its binade), as [hard]
    of exptablekl/ExpHard.v takes it. *)

From Stdlib Require Import ZArith Reals Lia Lra.
From Flocq Require Import Core.
From ExpTableKL Require Import ExpCheck ExpHard.
From Exp100 Require Import ExpConsts ExpModel.

Open Scope R_scope.

Theorem decide_ok y hN z : decide_Z y hN = 0%Z ->
  Rabs (z - IZR y * bpow radix2 (hN - P)) <= IZR D * bpow radix2 (hN - P) ->
  forall k : Z, bp (- m) <= Rabs (z / bp (vexp (binade z)) - IZR k).
Proof.
Admitted.
