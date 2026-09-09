From Stdlib Require Import ZArith Reals Psatz.
From Flocq Require Import Core Plus_error Sterbenz Operations Relative Mult_error.
From mathcomp Require Import ssreflect.
From dwarith Require Import F2SumFLT Imul.

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
(* Rounding to nearest reads a sign the same way on either side of zero.      *)
(* Every tie rule in use does, and the negative half of Knuth's 2Sum is the   *)
(* positive half read through that.                                           *)
Hypothesis choice_sym : forall x, choice x = negb (choice (- (x + 1))).

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

Lemma RN_sym x : RND (- x) = - RND x.
Proof.
suff : - RND (- x) = RND x by lra.
by rewrite round_N_opp Ropp_involutive /round /Znearest -choice_sym.
Qed.

(* The larger number less the rounded difference is exact.  When the two are  *)
(* close the difference itself is exact, by Sterbenz, and the rounding does   *)
(* nothing; among the smallest numbers it is exact for the other reason, that *)
(* they are evenly spaced.  Otherwise the rounded difference lies between     *)
(* half the larger and twice it, and Sterbenz applies to it instead.          *)
Lemma format_minus_minus a b : format a -> format b -> 0 <= a -> a <= b ->
  format (b - RND (b - a)).
Proof.
move=> aF bF a_ge0 aLb.
have [tbLa|aLtb] := Rle_or_lt (/ 2 * b) a.
  suff -> : b - RND (b - a) = a by [].
  rewrite round_generic; first by lra.
  rewrite -Ropp_minus_distr; apply: generic_format_opp.
  by apply: sterbenz => //; lra.
have [b_small|b_big] := Rlt_le_dec b small.
  suff -> : b - RND (b - a) = a by [].
  rewrite round_generic; first by lra.
  have -> : b - a = b + - a by lra.
  apply: FLT_format_plus_small => //; first by apply: generic_format_opp.
  by split_Rabs; lra.
rewrite -Ropp_minus_distr; apply: generic_format_opp.
apply: sterbenz => //; first by apply: generic_format_round.
split.
  have -> : b / 2 = b * pow (-1) by rewrite -[pow (-1)]/(/2); lra.
  suff : RND (b * pow (-1)) <= RND (b - a).
    rewrite round_generic //.
    by apply: half_exact => //; split_Rabs; lra.
  by apply: round_le; rewrite -[pow (-1)]/(/2); lra.
have -> : 2 * b = b * pow 1 by rewrite -[pow 1]/2; lra.
suff : RND (b - a) <= RND (b * pow 1).
  by rewrite [X in _ <= X -> _]round_generic //; apply: double_exact.
by apply: round_le; rewrite -[pow 1]/2; lra.
Qed.

(* Same signs, the smaller one second.  The second subtraction is exact by    *)
(* the lemma above, and the first is exact either by Sterbenz, when it        *)
(* overshoots, or because the sum less the larger is exact at the far end of  *)
(* the interval it falls in, and an exact difference stays exact nearer.      *)
Theorem MKnuth5 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  0 < b -> b < a -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db b_pos bLa.
have bLs : b <= s.
  suff : RND b <= s by rewrite round_generic //; lra.
  by apply: round_le; lra.
have b'E : b' = s - a'.
  rewrite /b' round_generic //.
  apply: format_minus_minus => //; first by apply: generic_format_round.
  by lra.
apply: MKnuth1 => //; rewrite -/da -/a' => //.
have a'Ls : a' <= s.
  suff : a' <= RND s by rewrite round_generic //; apply: generic_format_round.
  by apply: round_le; lra.
have sLta : s <= 2 * a.
  have -> : 2 * a = a * pow 1 by rewrite -[pow 1]/2; lra.
  suff : s <= RND (a * pow 1) by rewrite round_generic //; apply: double_exact.
  by apply: round_le; rewrite -[pow 1]/2; lra.
have [aLa'|a'La] := Rle_or_lt a a'.
  rewrite [da]round_generic // -Ropp_minus_distr.
  apply: generic_format_opp.
  by apply: sterbenz => //; [apply: generic_format_round | lra].
rewrite [LHS]round_generic //.
apply: exact_minus_interval (_ : a <= s) => //.
- by apply: generic_format_round.
- by apply: generic_format_round.
- by rewrite -b'E; apply: generic_format_round.
- have <- : RND 0 = 0 by rewrite round_generic //; apply: generic_format_0.
  by apply: round_le; lra.
- by lra.
suff : RND a <= s by rewrite round_generic //; lra.
by apply: round_le; lra.
Qed.

(* The larger of the two positive, whatever the sign of the smaller.  The     *)
(* four cases above cover it once the sum is known to leave the smallest      *)
(* numbers, which is what the opposite-sign case needs.                       *)
Theorem MKnuth7 a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  Rabs b < a -> small < Rabs (a + b) -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db bLa ab_big.
have a_gt0 : 0 < a by split_Rabs; lra.
have [b_eq0|b_neq0] := Req_dec b 0.
  by apply: MKnuth6 => //; rewrite b_eq0 Rplus_0_r round_generic.
have [b_pos|b_neg] := Rle_or_lt 0 b.
  by apply: MKnuth5 => //; split_Rabs; lra.
have [aLtb|tbLa] := Rle_or_lt a (2 * - b).
  by apply: MKnuth3 => //; split_Rabs; lra.
by apply: MKnuth4 => //; split_Rabs; lra.
Qed.

(* Knuth's 2Sum is error-free, with no condition at all on its arguments.     *)
Theorem Knuth a b : format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db.
have [ab_small|ab_big] := Rle_lt_dec (Rabs (a + b)) small.
  by apply: MKnuth_small.
have [aLb|bLa] := Rle_lt_dec (Rabs a) (Rabs b); first by apply: MKnuth2.
have [a_ge0|a_neg] := Rle_lt_dec 0 a.
  by apply: MKnuth7 => //; split_Rabs; lra.
pose s1  := RND (- a + - b).
pose a1' := RND (s1 - - b).
pose b1' := RND (s1 - a1').
pose da1 := RND (- a - a1').
pose db1 := RND (- b - b1').
have s1E : s1 = - s.
  rewrite /s1 /s (_ : - a + - b = - (a + b)); last by lra.
  by rewrite RN_sym.
have a1'E : a1' = - a'.
  rewrite /a1' /a' s1E (_ : - s - - b = - (s - b)); last by lra.
  by rewrite RN_sym.
have b1'E : b1' = - b'.
  rewrite /b1' /b' s1E a1'E (_ : - s - - a' = - (s - a')); last by lra.
  by rewrite RN_sym.
have da1E : da1 = - da.
  rewrite /da1 /da a1'E (_ : - a - - a' = - (a - a')); last by lra.
  by rewrite RN_sym.
have db1E : db1 = - db.
  rewrite /db1 /db b1'E (_ : - b - - b' = - (b - b')); last by lra.
  by rewrite RN_sym.
have -> : da + db = - (da1 + db1) by rewrite da1E db1E; lra.
rewrite RN_sym.
suff -> : RND (da1 + db1) = - a + - b - s1 by rewrite s1E; lra.
apply: MKnuth7; [by apply: generic_format_opp | by apply: generic_format_opp |
                 by split_Rabs; lra | ].
by rewrite (_ : - a + - b = - (a + b)); [rewrite Rabs_Ropp | lra].
Qed.

End TwoSumFLT.
