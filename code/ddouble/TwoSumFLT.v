From Stdlib Require Import ZArith Reals Psatz.
From Flocq Require Import Core Plus_error Sterbenz Operations Relative Mult_error.
From mathcomp Require Import ssreflect.
From dwarith Require Import F2SumFLT.

(* Knuth's 2Sum, in the bounded format.                                       *)
(* The six-operation 2Sum is error-free with no condition on its arguments,   *)
(* and that is what makes it worth the three extra operations over            *)
(* Fast2Sum.  The proof below follows the one for the unbounded format, and   *)
(* differs in one place: halving is not exact near the bottom of the range,   *)
(* so the argument splits on whether the sum stays among the smallest         *)
(* numbers, where addition is exact anyway, or leaves them, where halving is  *)
(* exact again.                                                               *)

Open Scope R_scope.

Section TwoSumFLT.

Variable emin p : Z.
Hypothesis Hp2 : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p }.
Variable choice : Z -> bool.

Let beta := radix2.
Local Notation pow e := (bpow beta e).
Local Notation fexp := (FLT_exp emin p).
Local Notation format := (generic_format beta fexp).
Local Notation RND := (round beta fexp (Znearest choice)).

(* Below this the numbers are the evenly spaced ones and a sum of two of      *)
(* them is one of them.  Above it, halving stays in the format.               *)
Local Notation small := (pow (p + emin)).

(* Halving is exact as soon as the number is not one of the smallest.         *)
Lemma half_exact x : format x -> small <= Rabs x -> format (x * pow (-1)).
Proof.
move=> Fx xge; apply: mult_bpow_exact_FLT => //.
suff : (emin + p + 1 <= mag beta x)%Z by lia.
apply: mag_ge_bpow.
by have -> : (emin + p + 1 - 1 = p + emin)%Z by lia.
Qed.

(* Doubling is exact everywhere: the format has no top.                       *)
Lemma double_exact x : format x -> format (x * pow 1).
Proof. by move=> Fx; apply: mult_bpow_pos_exact_FLT => //; lia. Qed.

Theorem MKnuth a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  a' = s - b -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db a'E.
suff -> : db = 0.
  rewrite Rplus_0_r /da a'E.
  have -> : a - (s - b) = a + b - s by ring.
  rewrite round_generic; last by apply: generic_format_round.
  rewrite round_generic // -Ropp_minus_distr.
  by apply/generic_format_opp/Plus_error.plus_error.
rewrite /db /b' a'E.
have -> : s - (s - b) = b by ring.
rewrite !round_generic //; first by ring.
have -> : b - b = 0 by ring.
apply: generic_format_0.
Qed.

Lemma MKnuth1 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  da = a - a' -> b' = s - a' -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db daE b'E.
suff dbE : db = b - b'.
  have -> : da + db = a + b - s by lra.
  rewrite round_generic // -Ropp_minus_distr.
  by apply/generic_format_opp/Plus_error.plus_error.
rewrite /db b'E round_generic //.
rewrite -Ropp_minus_distr.
have -> : - (s - a' - b) = a' - (s - b) by lra.
apply: Plus_error.plus_error; first by apply: generic_format_round.
by apply: generic_format_opp.
Qed.

(* When the sum is exact there is nothing left to correct.                    *)
Theorem MKnuth6 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  s = a + b -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db sE.
apply: MKnuth => //; rewrite -/s sE.
have -> : a + b - b = a by lra.
by rewrite round_generic.
Qed.

(* The smallest numbers are evenly spaced, so their sums are exact and the    *)
(* whole of 2Sum has nothing to do.                                           *)
Theorem MKnuth_small a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  Rabs (a + b) <= small -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db ab_small.
apply: MKnuth6 => //; rewrite /s round_generic //.
by apply: FLT_format_plus_small => //; rewrite Z.add_comm.
Qed.

(* The first subtraction of a Fast2Sum is exact when the second argument is  *)
(* the smaller one.  This is the one piece taken from the Fast2Sum file.      *)
Lemma sma_exact_abs a b : format a -> format b -> Rabs b <= Rabs a ->
  RND (RND (a + b) - a) = RND (a + b) - a.
Proof.
move=> Fa Fb bLa.
have [->|b0] := Req_dec b 0.
  have -> : RND (a + 0) = a by rewrite Rplus_0_r round_generic.
  have -> : a - a = 0 by ring.
  by rewrite round_0.
move: (Fa); rewrite {1}/generic_format.
set Ma := Ztrunc _; set fa := Defs.Float beta _ _ => afE.
apply: (@sma_exact beta emin p choice Hp2 _ a b fa) => //.
split => //; split; first by apply: FLT_mant_le.
by rewrite /fa /= /cexp; apply/FLT_exp_monotone/mag_le_abs.
Qed.

(* When the first argument is the smaller one, the second subtraction is the *)
(* exact one and 2Sum reduces to Fast2Sum the other way round.               *)
Theorem MKnuth2 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  Rabs a <= Rabs b -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db aLb.
apply: MKnuth => //; rewrite /a' /s.
have -> : a + b = b + a by ring.
by apply: sma_exact_abs.
Qed.

(* Opposite signs, close in magnitude: the sum is exact by Sterbenz.         *)
Theorem MKnuth3 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  0 <= a -> a <= 2 * - b -> - b <= a -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db a_ge aL2b NbLa.
apply: MKnuth => //.
rewrite round_generic //.
rewrite round_generic; first by have -> : a + b - b = a by lra.
have -> : a + b = a - (- b) by lra.
by apply: sterbenz => //; [apply: generic_format_opp | lra].
Qed.

(* Opposite signs, far apart in magnitude.  This is the case that halves,    *)
(* so it is the one that asks the sum to be away from the smallest numbers.   *)
Theorem MKnuth4 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  0 < - b -> 2 * - b < a -> small <= a -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db b_neg tbLa a_big.
have a_pos : 0 < a by lra.
have taLs : / 2 * a <= s.
  have -> : / 2 * a = a * pow (-1) by rewrite -[pow (-1)]/(/2); lra.
  suff : RND (a * pow (-1)) <= s.
    rewrite round_generic //.
    by apply: half_exact => //; rewrite Rabs_pos_eq //; lra.
  by apply: round_le; rewrite -[pow (-1)]/(/2); lra.
have sLa' : s <= a'.
  suff : RND s <= a' by rewrite round_generic //; apply/generic_format_round.
  by apply: round_le; lra.
have a'Lts : a' <= 2 * s.
  have -> : 2 * s = s * pow 1 by rewrite -[pow 1]/2; lra.
  suff : a' <= RND (s * pow 1).
    by rewrite round_generic //; apply/double_exact/generic_format_round.
  by apply: round_le; rewrite -[pow 1]/2; lra.
have tsLta : 2 * s <= 2 * a.
  suff : s <= RND a by rewrite round_generic //; lra.
  by apply: round_le; lra.
apply: MKnuth1 => //; rewrite -/da -/a' => //.
  rewrite [LHS]round_generic // -Ropp_minus_distr.
  apply: generic_format_opp.
  by apply: sterbenz => //; [apply: generic_format_round | lra].
rewrite [LHS]round_generic // -Ropp_minus_distr.
apply: generic_format_opp.
apply: sterbenz => //; first by apply: generic_format_round.
  by apply: generic_format_round.
rewrite -/s; lra.
Qed.

End TwoSumFLT.
