(* ---------------------------------------------------------------------------*)
(* The error-free transform 2Sum (paper Algorithm 2) and its properties:      *)
(* exactness, the format and half-ulp magnitude of its two words, and that    *)
(* its low word (the error) lands on the coarse input grid ([is_imul]).  A    *)
(* general round-to-nearest building block, generic over the precision [p]    *)
(* (binary64 is fixed only when instantiated ([p = 53] = binary64));                                 *)
(* built on [Uls] and imported by the triple-word development.                *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim Nonoverlap.
Require Import Fast2Sum_robust_flx.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Sec2Sum.

(* Generic over the precision [p]; [2Sum] needs [1 < p] (for Flocq's         *)
(* [TwoSum_correct]).                                                        *)
Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.

Let beta := radix2.
Local Notation pow e := (bpow beta e).

(* The [Prec_gt_0 p] instance is DERIVED from [Hp2], so lemmas depend on      *)
(* [Hp2] (which callers pass) rather than a separate unresolved instance.     *)
Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Let rnd : R -> Z := Znearest choice.
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLX_exp p)
     (FLX_exp_valid p) (FLX_exp_monotone p) choice).

(*  Basic error-free transforms                                               *)
(* ===========================================================================*)

(* Algorithm 2 of the paper: the 6-operation 2Sum.  Always exact:             *)
(*   s + e = a + b, with no assumption on the magnitudes of a and b.          *)
Definition TwoSum (a b : R) : dwR :=
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  DWR s (RND (da + db)).

(* Named projectors for the double-word record [dwR] (prelim: [DWR xh xl]),   *)
(* so a [TwoSum]/[Fast2Sum] result's components can be named without a [let]. *)
Definition dwh (d : dwR) : R := let: DWR xh _ := d in xh.
Definition dwl (d : dwR) : R := let: DWR _ xl := d in xl.

Lemma dwhE xh xl : dwh (DWR xh xl) = xh. Proof. by []. Qed.
Lemma dwlE xh xl : dwl (DWR xh xl) = xl. Proof. by []. Qed.

(* The high word of a 2Sum is the rounded sum.                                *)
Lemma TwoSum_hi a b : dwh (TwoSum a b) = RND (a + b). Proof. by []. Qed.

(* Algorithm 1 of the paper: the 3-operation Fast2Sum.  It is [TwoSum]        *)
(* without the magnitude test, so it is only error-free when the exponent of  *)
(* [b] does not exceed that of [a] ([Fast2Sum_correct_aux] of                 *)
(* Fast2Sum_robust_flx.v); ordering the arguments is the caller's job.        *)
Definition Fast2Sum (a b : R) : dwR :=
  let s := RND (a + b) in
  let z := RND (s - a) in
  DWR s (RND (b - z)).

(* The high word of a Fast2Sum is the rounded sum, as for [TwoSum].           *)
Lemma Fast2Sum_hi a b : dwh (Fast2Sum a b) = RND (a + b). Proof. by []. Qed.

Definition formatDWR (a : dwR) := let: DWR b c := a in format b /\ format c.

Lemma format_TwoSum a b : format a -> format b -> formatDWR (TwoSum a b).
Proof. by move=> Fa Fb; split; try apply: generic_format_round. Qed.

(* Both words of a Fast2Sum are rounded values, hence floats -- no hypothesis *)
(* on [a] and [b] is needed, unlike for its exactness.                        *)
Lemma format_Fast2Sum a b : formatDWR (Fast2Sum a b).
Proof. by split; apply: generic_format_round. Qed.

(* A Fast2Sum that SORTS its arguments first (one test, no extra operation).  *)
(* It is error-free unconditionally, which a bare Fast2Sum is not: whenever   *)
(* the caller cannot prove the ordering, this is the cheap fix -- cheaper     *)
(* than a 2Sum, which costs three operations more.  (Algorithm 18 of          *)
(* doc/old-triplewors.pdf needs exactly this twice; see ThreeProdOne.v.)      *)
Definition Fast2SumS (a b : R) : dwR :=
  if Rle_dec (Rabs b) (Rabs a) then Fast2Sum a b else Fast2Sum b a.

Lemma Fast2SumS_hi a b : dwh (Fast2SumS a b) = RND (a + b).
Proof.
by rewrite /Fast2SumS; case: Rle_dec => _ //=; rewrite Rplus_comm.
Qed.

Lemma format_Fast2SumS a b : formatDWR (Fast2SumS a b).
Proof. by rewrite /Fast2SumS; case: Rle_dec => Hab; apply: format_Fast2Sum. Qed.

(* The magnitude counterpart of [formatDWR]: in a 2Sum result [DWR s e]       *)
(* the error word [e] is at most half an ulp of the high word [s].            *)
Definition magnitudeDWR (a : dwR) := let: DWR s e := a in Rabs e <= ulp s / 2.

Theorem MKnuth  a b :
 format a  -> format b -> 
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

Lemma MKnuth1 a b: format a -> format b ->
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  da = a - a' -> b' = s - a' -> RND (da + db) = a + b - s.
Proof.
move=> aF bF s a' b' da db daE b'E.
suff dbE : db = b - b'.
  apply: etrans (_ : RND (a + b - s) = _); first by congr RND; lra.
  rewrite round_generic // -Ropp_minus_distr.
  by apply/generic_format_opp/Plus_error.plus_error.
rewrite /db b'E round_generic //.
rewrite -Ropp_minus_distr. 
have -> : - (s - a' - b) = a' - (s - b) by lra.
apply: Plus_error.plus_error; first by apply: generic_format_round.
by apply: generic_format_opp.
Qed.

Theorem MKnuth2 a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
 Rabs a <= Rabs b -> format a -> format b -> RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db  bLa aF bF.
apply MKnuth => //.
by rewrite [LHS]round_generic; rewrite // Rplus_comm; apply: sma_exact_abs_or0.
Qed.

Theorem MKnuth3 a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
 (0 <= a)%R ->
 (a <= 2 * - b)%R ->
 (- b <= a)%R ->
 format a ->
 format b -> RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db a_ge aL2b NbLa aF bF.
apply MKnuth => //.
rewrite round_generic //.
rewrite round_generic; first by have -> : a + b - b = a by lra.
have -> : a + b = a - (- b) by lra.
by apply: sterbenz => //; [apply: generic_format_opp | lra].
Qed.

Theorem MKnuth4 a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
 0 < - b -> 2 * - b < a ->  format a -> format b -> 
 RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db b_neg tbLa aF bF.
have taLs : / 2 * a <= s.
  have -> : / 2 * a = a * pow (-1) by rewrite -[pow (-1)]/(/2); lra.
  suff : RND (a * pow (-1)) <= s.
    rewrite round_generic //; first by apply: mult_bpow_exact_FLX.
    by apply: round_le; rewrite -[pow (-1)]/(/2); lra.
have sLa' : s <= a'.
  suff : RND s <= a' by rewrite round_generic //; apply/generic_format_round.
  by apply: round_le; lra.
have a'Lts : a' <= 2 * s.
  have -> : 2 * s = s * pow 1 by rewrite -[pow 1]/2; lra.
  suff : a' <= RND (s * pow 1).
    rewrite round_generic //.
    by apply/mult_bpow_exact_FLX/generic_format_round.
  by apply: round_le; rewrite -[pow 1]/2; lra.
have tsLta : 2 * s <= 2 * a.
  suff : s <= RND a by rewrite round_generic //; lra.
  by apply: round_le; lra.
apply: MKnuth1 => //; rewrite -/da  -/a' => //.
  rewrite [LHS]round_generic // -Ropp_minus_distr.
  apply: generic_format_opp.
  by apply: sterbenz => //; [apply: generic_format_round | lra].
rewrite [LHS]round_generic // -Ropp_minus_distr.
apply: generic_format_opp.
apply: sterbenz => //; first by apply: generic_format_round.
  by apply: generic_format_round.
rewrite -/s; lra.
Qed.

Lemma format_minus_minus a b : 
  format a -> format b -> 0 <= a -> a <= b -> format (b - RND (b - a)).
Proof.
move=> aF bF a_pos aLb.
have [tbLa|aLtb] := Rle_or_lt (/ 2 * b) a.
  suff -> : b - RND (b - a) = a by [].
  rewrite round_generic; first by lra.
  rewrite -Ropp_minus_distr.
  apply: generic_format_opp.
  by apply: sterbenz => //; lra.
rewrite -Ropp_minus_distr.
apply: generic_format_opp.
apply: sterbenz => //; first by apply: generic_format_round.
split.
  have -> : b / 2 = b * pow (-1) by rewrite -[pow (-1)]/(/2); lra.
  suff : RND (b * pow (-1)) <= RND (b - a).
    rewrite round_generic //; first by apply: mult_bpow_exact_FLX.
    by apply: round_le; rewrite -[pow (-1)]/(/2); lra.
  have -> : 2  * b = b * pow 1 by rewrite -[pow 1]/2; lra.
suff : RND (b - a) <= RND (b * pow 1).
  rewrite [X in _ <= X -> _]round_generic //.
  by apply: mult_bpow_exact_FLX.
by apply: round_le; rewrite -[pow 1]/(2); lra.
Qed.

Lemma imul_cexp_format x e : is_imul x (pow e) -> (cexp x <= e)%Z -> format x.
Proof.
move=> [k Hk] Hce.
rewrite Hk in Hce *.
apply: generic_format_F2R => _.
exact: Hce.
Qed.

(* [cexp] is monotone on the nonnegatives ([mag] is, and [FLX_exp] is).       *)
Lemma cexp_le_pos x y : 0 < x -> x <= y -> (cexp x <= cexp y)%Z.
Proof.
move=> x_gt0 xLy.
apply: FLX_exp_monotone.
apply: mag_le_abs; first by lra.
by rewrite !Rabs_pos_eq; lra.
Qed.

(* The exponent of the rightmost nonzero bit, as a plain power of two: the    *)
(* "maximal exponent" [e_a] of the informal proof.                            *)
Lemma uls_pow x : x <> 0 -> exists e, uls x = pow e.
Proof.
move=> xn0.
exists (cexp x + Z.of_nat (trZ (Ztrunc (mant x))))%Z.
by rewrite /uls; case: Req_bool_spec.
Qed.

(* Maximality of [uls]: a nonzero float is not on the grid one step COARSER   *)
(* than its rightmost nonzero bit.  (Converse of [uls_imul], via              *)
(* [is_imul_uls_ge].)                                                         *)
Lemma not_imul_uls_succ x e : format x -> x <> 0 -> uls x = pow e ->
  ~ is_imul x (pow (e + 1)).
Proof.
move=> Fx xn0 Hu Hc.
have := is_imul_uls_ge Fx xn0 Hc.
rewrite Hu => /le_bpow; lia.
Qed.

(* A float that is NOT on the [2^(e+1)] grid is representable with exponent   *)
(* [e], i.e. its canonical exponent is at most [e].  (Otherwise               *)
(* [format_imul_cexp] would put it back on the [2^(e+1)] grid.)  This is the  *)
(* step that makes the maximality of [e_a] usable below.                      *)
Lemma format_not_imul_cexp_le x e :
  format x -> ~ is_imul x (pow (e + 1)) -> (cexp x <= e)%Z.
Proof.
move=> Fx Hn.
case: (Z_le_gt_dec (cexp x) e) => // Hgt.
case: Hn.
apply: is_imul_pow_le (format_imul_cexp Fx) _.
rewrite -[Generic_fmt.cexp _ _ _]/(cexp _).
lia.
Qed.

(* ===========================================================================*)
(*  Exact subtraction on an interval                                          *)
(* ===========================================================================*)

(* If [b - a] is exact and [a <= c <= b], then [c - a] is exact.              *)
(*                                                                            *)
(* Proof (two cases, on whether [a] is expressible with [c]'s canonical       *)
(* exponent [e_c]; note [e_c <= e_b] as [cexp] is monotone).                  *)
(*  - If [a] is: then so is [c], hence so is [c - a]; and [0 < c - a <= c]    *)
(*    gives [cexp (c - a) <= e_c], so [c - a] is representable with that      *)
(*    exponent, i.e. in the format.                                           *)
(*  - Otherwise let [e_a] be [a]'s maximal exponent ([uls a = 2^e_a]).  Then  *)
(*    [e_a < e_c <= e_b], so [b] and [c] are both multiples of [2^(e_a+1)],   *)
(*    whence [b - a] and [c - a] are expressible with exponent [e_a].  By     *)
(*    maximality of [e_a], [b - a] is NOT a multiple of [2^(e_a+1)], so being *)
(*    a float it is representable with exponent [e_a] ([cexp (b-a) <= e_a]).  *)
(*    As [0 < c - a <= b - a], also [cexp (c - a) <= e_a], and [c - a] is a   *)
(*    multiple of [2^e_a]: it is in the format.                               *)
Lemma exact_minus_interval a b c :
  format a -> format b -> format c -> format (b - a) ->
  0 <= a -> a <= b -> a <= c -> c <= b -> format (c - a).
Proof.
move=> Fa Fb Fc Fba a_ge0 aLb aLc cLb.
(* Degenerate cases: [c = a] gives [0], and [a = 0] gives [c] itself.         *)
have [ca0|ca_n0] := Req_dec (c - a) 0.
  by rewrite ca0; exact: generic_format_0.
have ca_gt0 : 0 < c - a by lra.
have [a0|a_n0] := Req_dec a 0.
  by rewrite a0 Rminus_0_r.
have a_gt0 : 0 < a by lra.
have c_gt0 : 0 < c by lra.
(* [ea]: the maximal exponent of [a], i.e. [uls a = 2^ea].                    *)
have [ea Hulsa] := uls_pow a_n0.
have Hia : is_imul a (pow ea) by rewrite -Hulsa; exact: uls_imul.
have [Hcase|Hcase] := Z_le_gt_dec (cexp c) ea.
  (* Case A: [a] is expressible with [c]'s canonical exponent, hence so is    *)
  (* [c - a]; and [0 < c - a <= c] makes that exponent large enough.          *)
  have Hia' : is_imul a (pow (cexp c)) by apply: is_imul_pow_le Hia _.
  have Hic : is_imul c (pow (cexp c)) by exact: format_imul_cexp.
  apply: imul_cexp_format (is_imul_minus Hic Hia') _.
  by apply: cexp_le_pos => //; lra.
(* Case B: [ea < cexp c <= cexp b], so [b] is a multiple of [2^(ea+1)] while  *)
(* [a] is not (maximality of [ea]); hence neither is [b - a], which being a   *)
(* float is then representable with exponent [ea].                            *)
have Hcb : (cexp c <= cexp b)%Z by apply: cexp_le_pos => //; lra.
have Hib : is_imul b (pow (ea + 1)).
  apply: is_imul_pow_le (format_imul_cexp Fb) _.
  rewrite -[Generic_fmt.cexp _ _ _]/(cexp _); lia.
have Hna : ~ is_imul a (pow (ea + 1)) by apply: not_imul_uls_succ.
have Hnd : ~ is_imul (b - a) (pow (ea + 1)).
  move=> Hd; apply: Hna.
  have -> : a = b - (b - a) by lra.
  by apply: is_imul_minus.
have Hcd : (cexp (b - a) <= ea)%Z by apply: format_not_imul_cexp_le.
(* [c - a] is a multiple of [2^ea], and [0 < c - a <= b - a] transfers the    *)
(* exponent bound from [b - a].                                               *)
have Hic : is_imul c (pow ea).
  by apply: is_imul_pow_le (format_imul_cexp Fc) _;
     rewrite -[Generic_fmt.cexp _ _ _]/(cexp _); lia.
apply: imul_cexp_format (is_imul_minus Hic Hia) _.
apply: Z.le_trans Hcd.
by apply: cexp_le_pos => //; lra.
Qed.

Theorem MKnuth5 a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  0 < b -> b < a -> format a -> format b -> RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db b_pos bLa aF bF.
have bLs : b <= s.
  suff: RND b <= s by rewrite round_generic //; lra.
  by apply: round_le; lra.
have b'E : b' = s - a'.
  rewrite /b' round_generic //.
  apply: format_minus_minus => //; first by apply: generic_format_round.
  by lra.
apply: MKnuth1 => //; rewrite -/da  -/a' => //.
have a'Ls : a' <= s.
  suff : a' <= RND s by rewrite round_generic //; apply: generic_format_round.
  by apply: round_le; lra.
have sLta : s <= 2 * a.
  have -> : 2 * a = a * pow 1 by rewrite -[pow 1]/2; lra.
  suff : s <= RND (a * pow 1).
    rewrite round_generic //.
    by apply/mult_bpow_exact_FLX.
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
apply: round_le; lra.
Qed.

Theorem MKnuth6 a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  s = a + b -> format a -> format b -> RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db sE aF bF.
apply: MKnuth => //; rewrite -/s sE.
have -> : a + b - b = a by lra.
by rewrite round_generic.
Qed.

Theorem MKnuth7 a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  Rabs b < a -> format a -> format b -> RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db bLa aF bF.
have a_gt0 : 0 < a by split_Rabs; lra.
have [b_eq0|b_neg0] := Req_dec b 0.
  by apply: MKnuth6 => //; rewrite b_eq0 Rplus_0_r round_generic.
have [b_pos|b_neg] := Rle_or_lt 0 b.
  by apply: MKnuth5 => //; split_Rabs; lra.
have [aLtb|tbLa] := Rle_or_lt a (2 * - b).
  apply: MKnuth3 => //; split_Rabs; lra.
apply: MKnuth4 => //; lra.
Qed.

Theorem Knuth a b : 
  let s  := RND (a + b) in
  let a' := RND (s - b) in
  let b' := RND (s - a') in
  let da := RND (a - a') in
  let db := RND (b - b') in
  format a -> format b -> RND (da + db) = a + b - s.
Proof.
move=> s a' b' da db aF bF.
have [aLb|bLa] := Rle_or_lt (Rabs a) (Rabs b).
  by apply: MKnuth2.
have [a_pos|a_neg] := Rle_or_lt 0 a.
  by apply MKnuth7 => //; split_Rabs; lra.
pose s1 := RND (-a + -b).
pose a1' := RND (s1 - (- b)).
pose b1' := RND (s1 - a1').
pose da1 := RND (-a - a1').
pose db1 := RND (-b - b1').
have sE : s = - s1 by rewrite -RN_sym //; congr RND; lra.
have -> : da + db = - (da1 + db1).
  have a'E : a' = - a1' by rewrite -RN_sym //; congr RND; lra.
  have b'E : b' = - b1' by rewrite -RN_sym //; congr RND; lra.
  have daE : da = - da1 by rewrite -RN_sym //; congr RND; lra.
  have dbE : db = - db1 by rewrite -RN_sym //; congr RND; lra.
  by lra.
suff : RND (da1 + db1) = (- a) + (- b) - s1.
  by rewrite RN_sym // -[round _ _ _ _]/(RND _); lra.
apply: MKnuth7; first by split_Rabs; lra.
  by apply: generic_format_opp.
by apply: generic_format_opp.
Qed.

(* 2Sum is error-free: s + e = a + b.  We reuse Flocq's [TwoSum_correct]      *)
(* (the Pff bridge), instantiated with the operands SWAPPED: paper3's         *)
(* Algorithm 2 subtracts [b] first, whereas Flocq's variant subtracts its     *)
(* first argument first, so [TwoSum_correct b a] has exactly our              *)
(* intermediate values (up to commutativity of [+]).                          *)
Lemma TwoSum_correct_loc a b : format a -> format b ->
  let: DWR s e := TwoSum a b in s + e = a + b.
Proof. by move=> aF bF; rewrite /TwoSum; have := (Knuth aF bF); lra. Qed.

Lemma dwh_TwoSum_r0 eps : format eps -> dwh (TwoSum eps 0) = eps.
Proof. by move=> Feps; rewrite TwoSum_hi Rplus_0_r round_generic. Qed.

Lemma dwl_TwoSum_r0 eps : format eps -> dwl (TwoSum eps 0) = 0.
Proof.
move=> Feps.
have F0 : format 0 by apply: generic_format_0.
have Hc : dwh (TwoSum eps 0) + dwl (TwoSum eps 0) = eps + 0.
  by exact: TwoSum_correct_loc Feps F0.
by move: Hc; rewrite dwh_TwoSum_r0 //; lra.
Qed.

(* Magnitude analogue of [format_TwoSum] (Algorithm 2): the low word of a     *)
(* 2Sum is bounded by half an ulp of its high word.  Combine exactness        *)
(* [e = (a+b) - s] with the round-to-nearest bound |RN(x)-x| <= ulp(RN x)/2.*)
Lemma magnitude_TwoSum a b :
  format a -> format b -> magnitudeDWR (TwoSum a b).
Proof.
move=> Fa Fb.
have Hc := TwoSum_correct_loc Fa Fb.
move: Hc; rewrite /magnitudeDWR /TwoSum /=.
set s := RND (a + b).
set e := RND (RND (a - _) + RND (b - _)).
move=> Hc.
have He : e = a + b - s by lra.
rewrite He Rabs_minus_sym.
have /(_ p_gt_0) Hh := error_le_half_ulp_RN (a + b).
rewrite -[Znearest _]/rnd -/s in Hh.
lra.
Qed.

(* Algorithm 1 is error-free as soon as the operands are ORDERED, [|b| <= |a|]*)
(* (the test [TwoSum] performs and [Fast2Sum] does not).  In FLX no exponent  *)
(* condition is needed on top of it: [s = RN(a+b) - a] is exact               *)
(* ([sma_exact_abs_or0]) and the remaining [(a+b) - RN(a+b)] is a float       *)
(* ([Plus_error.plus_error], no underflow), so both roundings are the         *)
(* identity.                                                                  *)
Lemma Fast2Sum_correct a b :
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  let: DWR s e := Fast2Sum a b in s + e = a + b.
Proof.
move=> Fa Fb Hab.
rewrite /Fast2Sum /=.
rewrite [RND (RND (a + b) - a)]round_generic;
    last by apply: sma_exact_abs_or0.
have -> : b - (RND (a + b) - a) = - (RND (a + b) - (a + b)) by ring.
rewrite [RND (- _)]round_generic; first by ring.
by apply/generic_format_opp/Plus_error.plus_error.
Qed.

(* Magnitude analogue for Algorithm 1, as [magnitude_TwoSum] for Algorithm 2: *)
(* the low word is at most half an ulp of the high word.  This is what feeds  *)
(* the double-word predicate [2|e| <= ulp s].                                  *)
Lemma magnitude_Fast2Sum a b :
  format a -> format b -> (a <> 0 -> Rabs b <= Rabs a) ->
  magnitudeDWR (Fast2Sum a b).
Proof.
move=> Fa Fb Hab.
have Hc := Fast2Sum_correct Fa Fb Hab.
move: Hc; rewrite /magnitudeDWR /Fast2Sum /=.
set s := RND (a + b).
set e := RND (b - _).
move=> Hc.
have He : e = a + b - s by lra.
rewrite He Rabs_minus_sym.
have /(_ p_gt_0) Hh := error_le_half_ulp_RN (a + b).
rewrite -[Znearest _]/rnd -/s in Hh.
lra.
Qed.

(* The sorted Fast2Sum is error-free with NO hypothesis beyond the formats.   *)
Lemma Fast2SumS_correct a b :
  format a -> format b ->
  let: DWR s e := Fast2SumS a b in s + e = a + b.
Proof.
move=> Fa Fb; rewrite /Fast2SumS; case: Rle_dec => Hab;
  first by apply: Fast2Sum_correct.
have Hba : Rabs a <= Rabs b by lra.
have H := Fast2Sum_correct Fb Fa (fun _ => Hba).
by move: H => H /=; lra.
Qed.

(* ... and its low word is at most half an ulp of its high word.              *)
Lemma magnitude_Fast2SumS a b :
  format a -> format b -> magnitudeDWR (Fast2SumS a b).
Proof.
move=> Fa Fb; rewrite /Fast2SumS; case: Rle_dec => Hab;
  first by apply: magnitude_Fast2Sum.
have Hba : Rabs a <= Rabs b by lra.
by apply: (magnitude_Fast2Sum Fb Fa (fun _ => Hba)).
Qed.

(* The low word (error) of a 2Sum is a multiple of the coarser input grid     *)
(* [bpow (min (cexp a) (cexp b))]: [a], [b], and [RN(a+b)] all live on it, so *)
(* so does [a + b - RN(a+b)].                                                 *)
Lemma TwoSum_err_imul a b : format a -> format b ->
  is_imul (dwl (TwoSum a b)) (bpow beta (Z.min (cexp a) (cexp b))).
Proof.
move=> Fa Fb.
have Hc : dwh (TwoSum a b) + dwl (TwoSum a b) = a + b
  by exact: TwoSum_correct_loc Fa Fb.
have -> : dwl (TwoSum a b) = (a + b) - RND (a + b)
  by move: Hc; rewrite TwoSum_hi; lra.
have Hab : is_imul (a + b) (bpow beta (Z.min (cexp a) (cexp b))).
  apply: is_imul_add.
    by apply: (is_imul_pow_le _ (Z.le_min_l _ _)); apply: format_imul_cexp.
  by apply: (is_imul_pow_le _ (Z.le_min_r _ _)); apply: format_imul_cexp.
by apply: is_imul_minus => //; apply: is_imul_pow_round.
Qed.

(* The TwoSum error never exceeds the SECOND operand: [a] is itself a float   *)
(* sitting at distance [|b|] from the exact sum, so the nearest float is at   *)
(* least as close.  Draft 5.3's [i_1 <= 3] case uses it twice, to pin         *)
(* [|e_{i_1 - 1}| = |eps_{i_0}| = u] from below by [u] and above by the       *)
(* running sum.                                                               *)
Lemma TwoSum_err_le_r a b : format a -> format b ->
  Rabs (dwl (TwoSum a b)) <= Rabs b.
Proof.
move=> Fa Fb.
have Hc : dwh (TwoSum a b) + dwl (TwoSum a b) = a + b
  by exact: TwoSum_correct_loc Fa Fb.
have -> : dwl (TwoSum a b) = (a + b) - RND (a + b)
  by move: Hc; rewrite TwoSum_hi; lra.
have [_ Hnear] := round_N_pt beta fexp choice (a + b).
have Hb := Hnear a Fa.
rewrite (_ : a - (a + b) = - b) ?Rabs_Ropp in Hb; last by lra.
by rewrite Rabs_minus_sym.
Qed.

(* The TwoSum error inherits at least the [uls] of the smaller-grid operand:  *)
(* if [uls s <= uls a] then [uls s <= uls (dwl (TwoSum a s))].  Both operands *)
(* lie on the grid [bpow (cexp s + trZ (mant s))] (= [uls s]), hence so does  *)
(* the exact error [a + s - RND(a + s)]; [is_imul_uls_ge] then lifts that grid*)
(* up to the error's own [uls].  This is the separation core of Fnonoverlap.  *)
Lemma TwoSum_err_uls_ge a s : format a -> format s -> a <> 0 -> s <> 0 ->
  uls s <= uls a -> dwl (TwoSum a s) <> 0 -> uls s <= uls (dwl (TwoSum a s)).
Proof.
move=> Fa Fs an0 sn0 Hle en0.
have Hulss : uls s = bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s)))).
  by rewrite /uls; case: Req_bool_spec.
have Hulsa : uls a = bpow beta (cexp a + Z.of_nat (trZ (Ztrunc (mant a)))).
  by rewrite /uls; case: Req_bool_spec.
have HleZ : (cexp s + Z.of_nat (trZ (Ztrunc (mant s))) <=
             cexp a + Z.of_nat (trZ (Ztrunc (mant a))))%Z.
  by apply: (le_bpow beta); rewrite -Hulss -Hulsa.
have Ha : is_imul a (bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s))))).
  by apply: (is_imul_pow_le _ HleZ); rewrite -Hulsa; exact: uls_imul.
have Hs : is_imul s (bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s))))).
  by rewrite -Hulss; exact: uls_imul.
have Herr : is_imul (dwl (TwoSum a s))
              (bpow beta (cexp s + Z.of_nat (trZ (Ztrunc (mant s))))).
  have Hc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s
    by exact: TwoSum_correct_loc Fa Fs.
  have -> : dwl (TwoSum a s) = (a + s) - RND (a + s)
    by move: Hc; rewrite TwoSum_hi; lra.
  apply: is_imul_minus; first by apply: is_imul_add.
  by apply: is_imul_pow_round; apply: is_imul_add.
have Ferr : format (dwl (TwoSum a s)).
  move: (format_TwoSum Fa Fs); rewrite /formatDWR.
  by case: (TwoSum a s) => b c [].
apply: Rle_trans (is_imul_uls_ge Ferr en0 Herr).
by apply: Req_le.
Qed.

Lemma Fnonoverlap_TwoSum_err eps e l :
  format eps -> format e -> Fnonoverlap [:: eps, e & l] ->
  dwl (TwoSum eps e) <> 0 -> Fnonoverlap (dwl (TwoSum eps e) :: l).
Proof.
move=> Feps Fe Fno etn0.
have Hc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e.
  by exact: TwoSum_correct_loc Feps Fe.
have Het : RND (eps + e) + dwl (TwoSum eps e) = eps + e.
  by move: Hc; rewrite TwoSum_hi.
(* A zero operand rounds exactly, leaving [dwl = 0]; so both are nonzero.     *)
have epsn0 : eps <> 0.
  move=> eps0; apply: etn0.
  have HR : RND (eps + e) = e by rewrite eps0 Rplus_0_l; apply: round_generic.
  by lra.
have en0 : e <> 0.
  move=> e0; apply: etn0.
  have HR : RND (eps + e) = eps by rewrite e0 Rplus_0_r; apply: round_generic.
  by lra.
(* [|e| <= 1/2 uls eps] and [uls e <= |e|] give [uls e <= uls eps], so the    *)
(* error inherits at least [e]'s grid: [uls e <= uls (dwl (TwoSum eps e))].   *)
have He2 : Rabs e <= / 2 * uls eps by exact: Fnonoverlap_head2 Fno epsn0 en0.
have Hueps : uls e <= uls eps.
  have Hule : uls e <= Rabs e by apply: uls_le_abs.
  have Hu0 : 0 < uls eps by apply: uls_gt_0.
  by lra.
have Huet : uls e <= uls (dwl (TwoSum eps e)).
  by apply: (TwoSum_err_uls_ge Feps Fe epsn0 en0 Hueps).
(* The tail [l] carries over from the input (drop [eps, e]), with the running *)
(* term [e] weakened to the coarser error ([uls e <= uls (dwl ..)]).          *)
apply: Fnonoverlap_consN; first exact: etn0.
by apply: (Fnonoverlap_aux_prev Huet (Fnonoverlap_tail Fno en0)).
Qed.

(* Reusable step lemma (the [et = 0] branch): when [2Sum eps e] is exact      *)
(* ([dwl = 0], so [dwh = eps + e] merges them), prepending the merged high    *)
(* word to the tail keeps F-nonoverlap.  Needs [e <> 0] (the paper's zero-free*)
(* convention -- a zero [e] is dropped by [vsebAux_cons0] before this fires). *)
(* The tail carries over from the input directly; the only new obligation is  *)
(* the head bound [|nth l 0| <= 1/2 uls (eps + e)], which follows from        *)
(* [|nth l 0| <= 1/2 uls e] and [uls e <= uls (eps + e)]: [eps + e] is a      *)
(* nonzero float lying on [e]'s grid ([uls e]), so [is_imul_uls_ge] lifts it. *)
Lemma Fnonoverlap_TwoSum_merge eps e l :
  format eps -> format e -> e <> 0 -> dwh (TwoSum eps e) <> 0 ->
  Fnonoverlap [:: eps, e & l] ->
  dwl (TwoSum eps e) = 0 -> Fnonoverlap (dwh (TwoSum eps e) :: l).
Proof.
move=> Feps Fe en0 rn0 Fno etz.
have Hc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e.
  by exact: TwoSum_correct_loc Feps Fe.
have Hr : dwh (TwoSum eps e) = eps + e by move: Hc; rewrite etz; lra.
have Frr : format (dwh (TwoSum eps e)).
  by rewrite TwoSum_hi; apply: generic_format_round.
set r := dwh (TwoSum eps e) in Hr Frr rn0 *.
(* [uls e <= uls r]: [r = eps + e] is a nonzero float on [e]'s grid [uls e].  *)
have Hue : uls e <= uls r.
  case: (Req_dec eps 0) => [eps0|epsn0].
    by rewrite Hr eps0 Rplus_0_l; apply: Rle_refl.
  have He0 : Rabs e <= / 2 * uls eps by exact: Fnonoverlap_head2 Fno epsn0 en0.
  have Hueps : uls e <= uls eps.
    have Hu0 : 0 < uls eps by apply: uls_gt_0.
    have Hle : uls e <= Rabs e by apply: uls_le_abs.
    lra.
  have gE : uls e = pow (cexp e + trN (Ztrunc (mant e))).
    by rewrite /uls; case: Req_bool_spec.
  have gepsE : uls eps = pow (cexp eps + trN (Ztrunc (mant eps))).
    by rewrite /uls; case: Req_bool_spec.
  have HleZ : (cexp e + trN (Ztrunc (mant e)) <=
               cexp eps + trN (Ztrunc (mant eps)))%Z.
    by apply: (le_bpow beta); rewrite -gE -gepsE.
  have Hime : is_imul e (pow (cexp e + trN (Ztrunc (mant e)))).
    by rewrite -gE; exact: uls_imul.
  have Himeps : is_imul eps (pow (cexp e + trN (Ztrunc (mant e)))).
    by apply: (is_imul_pow_le _ HleZ); rewrite -gepsE; exact: uls_imul.
  have Himr : is_imul r (pow (cexp e + trN (Ztrunc (mant e)))).
    by rewrite Hr; apply: is_imul_add.
  apply: Rle_trans (is_imul_uls_ge Frr rn0 Himr).
  by rewrite gE; apply: Rle_refl.
(* Tail carries over from the input, running term [e] weakened to [r].        *)
apply: Fnonoverlap_consN; first exact: rn0.
by apply: (Fnonoverlap_aux_prev Hue (Fnonoverlap_tail Fno en0)).
Qed.


End Sec2Sum.
