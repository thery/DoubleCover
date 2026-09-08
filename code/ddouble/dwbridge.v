From Stdlib Require Import Reals ZArith.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.

(* Primitive floats read as real numbers.                                     *)
(* The stdlib says what an operation does on bit patterns and nothing about   *)
(* its error; Flocq says the same operation is the rounded real one.  These   *)
(* are the four statements the double-word proofs need in order to speak      *)
(* about a program written with primitive floats.                             *)

(* The real number a float stands for.  An infinity or a NaN is sent to       *)
(* zero, which is why every statement below asks for finiteness.              *)
Definition D2R (x : PrimFloat.float) : R := B2R (Prim2B x).

(* A float is finite when it is neither an infinity nor a NaN.                *)
Definition Dfin (x : PrimFloat.float) := BinarySingleNaN.is_finite (Prim2B x) = true.

(* The exponent function of binary64, and its rounding: to nearest, ties to   *)
(* even.                                                                      *)
Notation Dfexp := (SpecFloat.fexp prec emax).
Notation Drnd := (round radix2 Dfexp (round_mode mode_NE)).

(* A result stays in the format when its rounding is below the largest        *)
(* exponent.  Anything else overflows, and no statement below applies.        *)
Notation Dfits r := (Rabs (Drnd r) < bpow radix2 emax)%R.

(* The rounding is the one the double-word proofs call round to nearest with  *)
(* ties to even, so their `choice` is ours.                                   *)
Lemma DrndE r : Drnd r = round radix2 Dfexp (Znearest (fun n => negb (Z.even n))) r.
Proof. by []. Qed.

(* Above the smallest normal number the bounded format rounds like the        *)
(* unbounded one.  The double-word proofs are all stated in the unbounded     *)
(* format, so this is what carries them over.                                 *)
Lemma Drnd_FLX r :
  (bpow radix2 (SpecFloat.emin prec emax + prec - 1) <= Rabs r)%R ->
  Drnd r = round radix2 (FLX_exp prec) (round_mode mode_NE) r.
Proof. by move=> rge; apply: round_FLT_FLX. Qed.

Lemma D2R_add x y :
  Dfin x -> Dfin y -> Dfits (D2R x + D2R y) ->
  D2R (x + y)%float = Drnd (D2R x + D2R y) /\ Dfin (x + y)%float.
Proof.
rewrite /Dfin /D2R => Fx Fy Hf.
rewrite add_equiv.
have := Bplus_correct _ _ Hprec Hmax mode_NE _ _ Fx Fy.
by rewrite Rlt_bool_true //; case=> -> [-> _].
Qed.

Lemma D2R_sub x y :
  Dfin x -> Dfin y -> Dfits (D2R x - D2R y) ->
  D2R (x - y)%float = Drnd (D2R x - D2R y) /\ Dfin (x - y)%float.
Proof.
rewrite /Dfin /D2R => Fx Fy Hf.
rewrite sub_equiv.
have := Bminus_correct _ _ Hprec Hmax mode_NE _ _ Fx Fy.
by rewrite Rlt_bool_true //; case=> -> [-> _].
Qed.

Lemma D2R_mul x y :
  Dfin x -> Dfin y -> Dfits (D2R x * D2R y) ->
  D2R (x * y)%float = Drnd (D2R x * D2R y) /\ Dfin (x * y)%float.
Proof.
rewrite /Dfin /D2R => Fx Fy Hf.
rewrite mul_equiv.
have := Bmult_correct _ _ Hprec Hmax mode_NE (Prim2B x) (Prim2B y).
by rewrite Rlt_bool_true //; case=> -> [-> _]; rewrite Fx Fy.
Qed.

Lemma D2R_div x y :
  Dfin x -> D2R y <> 0%R -> Dfits (D2R x / D2R y) ->
  D2R (x / y)%float = Drnd (D2R x / D2R y) /\ Dfin (x / y)%float.
Proof.
rewrite /Dfin /D2R => Fx yn0 Hf.
rewrite div_equiv.
have := Bdiv_correct _ _ Hprec Hmax mode_NE (Prim2B x) (Prim2B y) yn0.
by rewrite Rlt_bool_true //; case=> -> [-> _]; rewrite Fx.
Qed.
