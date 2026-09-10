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

(* Every primitive float is in the format: the double-word theorems all ask  *)
(* for this, of every argument.                                               *)
Lemma Dformat x : generic_format radix2 Dfexp (D2R x).
Proof. by apply: generic_format_B2R. Qed.

(* The format is FLT: the exponent is bounded below, at -1074, and not above. *)
(* Overflow is not in the exponent function at all - it is the Dfits test.    *)
Lemma DfexpE : Dfexp = FLT_exp (SpecFloat.emin prec emax) prec.
Proof. by []. Qed.

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

(* Addition and subtraction, asked the other way round.  Overflow is what     *)
(* the Dfits above rules out, and an operation that overflowed returns an     *)
(* infinity, so a finite result is itself the proof that it did not.  This    *)
(* is the form a program can test: it looks at what it just computed.         *)
Lemma Dfin_add x y :
  Dfin x -> Dfin y -> Dfin (x + y)%float ->
  D2R (x + y)%float = Drnd (D2R x + D2R y) /\ Dfits (D2R x + D2R y).
Proof.
rewrite /Dfin /D2R add_equiv => Fx Fy Fxy.
have := Bplus_correct _ _ Hprec Hmax mode_NE _ _ Fx Fy.
case: Rlt_bool_spec => [Hlt [-> _]|Hle [Hov _]]; first by [].
by move: Fxy Hov; case: Bplus.
Qed.

Lemma Dfin_sub x y :
  Dfin x -> Dfin y -> Dfin (x - y)%float ->
  D2R (x - y)%float = Drnd (D2R x - D2R y) /\ Dfits (D2R x - D2R y).
Proof.
rewrite /Dfin /D2R sub_equiv => Fx Fy Fxy.
have := Bminus_correct _ _ Hprec Hmax mode_NE _ _ Fx Fy.
case: Rlt_bool_spec => [Hlt [-> _]|Hle [Hov _]]; first by [].
by move: Fxy Hov; case: Bminus.
Qed.

(* The same question asked backwards: which arguments can have produced a     *)
(* finite result.  An operation given an infinity returns an infinity or a    *)
(* NaN, never a number, so a finite result is by itself the proof that both   *)
(* arguments were numbers.  This is what lets a program check a whole chain   *)
(* of operations by looking only at the last thing it computed.               *)
Lemma Dfin_addI a b : Dfin (a + b)%float -> Dfin a /\ Dfin b.
Proof.
rewrite /Dfin add_equiv.
by case: (Prim2B a) => [s1|s1||s1 m1 e1 H1];
   case: (Prim2B b) => [s2|s2||s2 m2 e2 H2] //=; case: (Bool.eqb s1 s2).
Qed.

Lemma Dfin_subI a b : Dfin (a - b)%float -> Dfin a /\ Dfin b.
Proof.
rewrite /Dfin sub_equiv.
by case: (Prim2B a) => [s1|s1||s1 m1 e1 H1];
   case: (Prim2B b) => [s2|s2||s2 m2 e2 H2] //=; case: (Bool.eqb s1 (negb s2)).
Qed.
