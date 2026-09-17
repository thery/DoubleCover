From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Primitive_ops.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwbridge.

(* THE SIGN OF A FLOAT, which two words and three both need to take an        *)
(* absolute value.  It is kept out of `dwbridge.v' because it is the one      *)
(* fact of its kind that needs Interval's own reading of a primitive float,   *)
(* and importing Interval there would shadow Flocq's `round', on which every  *)
(* line of the bridge rests.                                                  *)

Open Scope R_scope.

(* The sign bit of a number says which side of nought it is on.               *)
Lemma Dget_sign f : Dfin f ->
  (PrimFloat.get_sign f = true -> (D2R f <= 0)%R) /\
  (PrimFloat.get_sign f = false -> (0 <= D2R f)%R).
Proof.
move=> Ff.
have H1 : forall g, Dfin g -> PrimFloat.get_sign g = true -> (D2R g <= 0)%R.
  move=> g Fg Eg; case: (Rle_lt_dec (D2R g) 0) => // Hpos.
  have Hbg : PrimitiveFloat.BtoX (Prim2B g) = Xreal (D2R g)
    by apply: PrimitiveFloat.B2R_BtoX.
  by move: Eg; rewrite get_sign_equiv (PrimitiveFloat.Bsign_pos _ _ Hbg Hpos).
split; first exact: H1 _ Ff.
move=> E; have Fn := Dfin_opp _ Ff.
have En : PrimFloat.get_sign (- f)%float = true.
  rewrite get_sign_equiv opp_equiv Bsign_Bopp; last first.
    by move: Ff; rewrite /Dfin; case: (Prim2B f).
  by move: E; rewrite get_sign_equiv => ->.
by have := H1 _ Fn En; rewrite D2R_opp; lra.
Qed.
