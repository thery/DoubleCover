(* ---------------------------------------------------------------------------*)
(* Algorithm 13 (3Reci): the RECIPROCAL of a triple word, computed by one     *)
(* Newton-Raphson step, and its two correctness results -- the result is a    *)
(* triple word ([ThreeReci_isTW]) and the relative error bounds               *)
(* [11.5u^3 + 1465u^4] (accurate variant, [ThreeReci_error]) and              *)
(* [19u^3 + 1502u^4] (fast variant, [ThreeReciFast_error]) -- paper           *)
(* doc/paper3.pdf, Section 8 and Theorem 9 (see doc/thm9.md).  Generic over   *)
(* the precision [p] (FLX, no [emin]); needs [p >= 10].                       *)
(*                                                                            *)
(* The Newton iteration for [1/x] is [r_{n+1} = r_n (2 - r_n x)].  Algorithm  *)
(* 13 starts from [a = RN((1 + 2u)/x0)] -- NOT [RN(1/x0)] -- so that          *)
(* [RN(x0 * a) = 1 + 2u] exactly, which makes the head of                     *)
(* [2 - a * (x0 + x1)] the CONSTANT [h0 = 2 - (1 + 2u) = 1 - 2u] (a virtual   *)
(* word: no operation).  One step in double-word arithmetic gives             *)
(* [b = (b0, b1) ~ 1/x], and one step in triple-word arithmetic, through the  *)
(* DW x TW products of Algorithm 11 or Algorithm 12, gives the result.        *)
(*                                                                            *)
(* Both variants share the definition [ThreeReciAux], parameterised by the    *)
(* [3Prod_{2,3}] it calls: [ThreeReci] uses Algorithm 11 (accurate) and       *)
(* [ThreeReciFast] uses Algorithm 12 (fast).                                  *)
(*                                                                            *)
(* STATUS: COMPLETE -- Algorithm 13 is fully proved, zero admits.             *)
(* [ThreeReci_isTW] and [ThreeReciFast_isTW] are [Qed], on top of the whole   *)
(* Section 8.2 chain -- [reciB_isDW] ([b] is a double word) and               *)
(* [reciBW_x_err] ([|b x - 1| <= 34u^2 + 123u^3]) -- and of [head_one], the   *)
(* Section 8.3 property that the head limb of [3Prod_{2,3}(b, x)] is [1],     *)
(* now PROVED for both multipliers ([ThreeProdDW_head_one],                   *)
(* [ThreeProdDWFast_head_one]).  Its two steps are generic in the multiplier  *)
(* ([head_gap_gen], [head_one_gen]) and rest on the normalised head gap of    *)
(* ThreeProdDW.v / ThreeProdDWFast.v ([_head_gap_norm]) and on [head_eq_1].   *)
(* The two error bounds (Theorem 9) are PROVED too, through the assembly      *)
(* [ThreeReciAux_error] (generic in BOTH multipliers) and the specialised     *)
(* second product of ThreeProdOne.v.  Their [u^3] terms are the paper's       *)
(* ([11.5] and [19]); their [u^4] terms are ours ([1830]/[1870] instead of    *)
(* [1465]/[1502]), because the paper's [delta2 = u^3 + 260u^4] for Algorithm  *)
(* 18 does not survive an honest accounting -- see ThreeProdOne.v.            *)
(* doc/paper3.pdf gives no proof of Theorem 9 (it is in the supplementary     *)
(* material, which we do not have); the plan is recovered from                *)
(* doc/old-triplewors.pdf Section 8 -- see doc/thm9.md for the full chain.    *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import TWR.
Require Import Merge.
Require Import VecSum.
Require Import VSEB.
Require Import Thm6.
Require Import ThreeProd.
Require Import ThreeProdFast.
Require Import ThreeProdDW.
Require Import ThreeProdDWFast.
Require Import ThreeProdOne.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeReci.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 13 needs the stronger [p >= 10] of paper Section 8: it is what   *)
(* forces the leading limb of [3Prod_{2,3}(b, x)] to be exactly [1], so that  *)
(* [2 - 3Prod_{2,3}(b, x)] is exact (old paper Section 8.3, Remark 9).        *)
Hypothesis Hp10 : (10 <= p)%Z.

(* Algorithms 11 and 12, which Algorithm 13 calls, need [p >= 6].             *)
Lemma Hp6 : (6 <= p)%Z. Proof. lia. Qed.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).

(* Building blocks, with this format's [p]/[choice] hidden.                   *)
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation Fast2Sum := (Fast2Sum p choice).
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).
Local Notation tw_norm := (tw_norm p).

(* The two DW x TW products of Sections 7.1 and 7.2 (Algorithms 11 and 12).   *)
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdDWFast := (ThreeProdDWFast p choice).

(* The specialised SECOND product of Section 8.4 (Algorithm 18), shared by    *)
(* both variants: its second argument always has head [1].                    *)
Local Notation ThreeProdOne := (ThreeProdOne p choice).

(* ===========================================================================*)
(*  [2 - x] on triple words                                                   *)
(*                                                                            *)
(*  Algorithm 13 subtracts a triple word from [2] ("i <- 2 - 3Prod(b, x)").   *)
(*  Limb by limb this is [(2 - x0, -x1, -x2)]: the two low limbs are just     *)
(*  negated, and the head subtraction [2 - x0] is EXACT by Sterbenz as soon   *)
(*  as [1 <= x0 <= 2] -- in Algorithm 13 the paper proves the much stronger   *)
(*  [x0 = 1] (old paper Section 8.3), so it costs one operation and no error. *)
(*  The paper even folds it into the multiplication (its Algorithms 16-18);   *)
(*  we keep it explicit, exactly as Algorithm 13 is written.                  *)
(* ===========================================================================*)
Definition sub2TW (x : twR) : twR :=
  let: TWR x0 x1 x2 := x in TWR (2 - x0) (- x1) (- x2).

Lemma TWval_sub2TW x : TWval (sub2TW x) = 2 - TWval x.
Proof. by case: x => x0 x1 x2; rewrite /TWval /=; ring. Qed.

(* ===========================================================================*)
(*  Algorithm 13 -- 3Reci(x0, x1, x2)                                         *)
(*  (73 operations & 2 tests with Algorithm 11, 65 operations & 1 test with   *)
(*  Algorithm 12; paper Section 8).                                           *)
(*                                                                            *)
(*    a    <- RN((1 + 2u) / x0)                                               *)
(*    h11  <- RN(a x0 - (1 + 2u))          (FMA; 2Prod2_{(1+2u)}(a, x0))      *)
(*    h1   <- RN(-h11 - a x1)              (FMA)                              *)
(*    (b01, b11) <- 2Prod(a, 1 - 2u)       (1 - 2u is the virtual h0)         *)
(*    b12  <- RN(b11 + a h1)               (FMA)                              *)
(*    b    <- Fast2Sum(b01, b12)           (a DW)                             *)
(*    i    <- 2 - 3Prod_{2,3}(b, x)                                           *)
(*    y    <- 3Prod_{2,3}(b, i)                                               *)
(*                                                                            *)
(*  [h11] is the error of the product [a x0] taken with respect to [1 + 2u]:  *)
(*  since [RN(a x0) = 1 + 2u], it is exactly [a x0 - (1 + 2u)], so            *)
(*  [(1 + 2u, h11)] is an error-free transform of [a x0] and the pair         *)
(*  [h = (h0, h1) = (1 - 2u, h1)] is a double word approximating              *)
(*  [2 - a (x0 + x1)].                                                        *)
(* ===========================================================================*)
(* The six head lines, named one by one so that the bounds of Section 8.2 can *)
(* be stated and reused without unfolding the algorithm.                      *)
Definition reciA (x0 : R) : R := RND ((1 + 2 * u) / x0).

Definition reciH11 (x0 : R) : R := RND (reciA x0 * x0 - (1 + 2 * u)).

Definition reciH1 (x0 x1 : R) : R := RND (- reciH11 x0 - reciA x0 * x1).

Definition reciB01 (x0 : R) : R := (TwoProd (reciA x0) (1 - 2 * u)).1.

Definition reciB11 (x0 : R) : R := (TwoProd (reciA x0) (1 - 2 * u)).2.

Definition reciB12 (x0 x1 : R) : R :=
  RND (reciB11 x0 + reciA x0 * reciH1 x0 x1).

Definition reciB (x0 x1 : R) : dwR := Fast2Sum (reciB01 x0) (reciB12 x0 x1).

(* The Newton double word [b], packaged as a [twR] with a zero third limb --  *)
(* the shape Algorithms 11 and 12 take as their first argument.               *)
Definition reciBW (x0 x1 : R) : twR :=
  TWR (dwh (reciB x0 x1)) (dwl (reciB x0 x1)) 0.

(* The two products are kept SEPARATE: [mul1] computes [i = 2 - b x] and      *)
(* [mul2] computes [y = b i].  The paper uses a SPECIALISED [mul2] (old       *)
(* paper Algorithm 18), because [i] has head [1] and [O(u^2)] tail -- which   *)
(* is what its [11.5u^3] and its 73-operation count are for.                  *)
Definition ThreeReciAux (mul1 mul2 : twR -> twR -> twR) (x : twR) : twR :=
  let bw := reciBW (tw0 x) (tw1 x) in
  mul2 bw (sub2TW (mul1 bw x)).

(* The accurate variant: the first [3Prod_{2,3}] is Algorithm 11.             *)
Definition ThreeReci (x : twR) : twR :=
  ThreeReciAux ThreeProdDW ThreeProdOne x.

(* The fast variant: the first [3Prod_{2,3}] is Algorithm 12.                 *)
Definition ThreeReciFast (x : twR) : twR :=
  ThreeReciAux ThreeProdDWFast ThreeProdOne x.

(* ===========================================================================*)
(*  The starting point [a = RN((1 + 2u)/x0)] (paper Section 8)                *)
(*                                                                            *)
(*  [1 + 2u] is the SUCCESSOR of [1], and that is exactly what makes          *)
(*  [RN(x * RN((1 + 2u)/x)) = 1 + 2u] hold for EVERY nonzero float [x] -- the *)
(*  fact the paper calls straightforward, and which turns [h0] into the       *)
(*  constant [1 - 2u].  Scaling and sign reduce it to [1 <= x < 2], where     *)
(*  there are three cases: [x = 1] and [x = 1 + 2u] are exact, and for        *)
(*  [x >= 1 + 4u] the quotient lies in [[1/2, 1)], so it is rounded with an   *)
(*  error at most [u/2], which [x < 2] turns into a distance STRICTLY below   *)
(*  the half-ulp [u] of [1 + 2u].                                             *)
(* ===========================================================================*)
(* [p >= 10] caps [u] at [2^-10] -- the counterpart, for Algorithm 13, of the *)
(* [u <= 1/64] that the multiplication algorithms spend their [p >= 6] on.    *)
Lemma u_le_1024 : u <= / 1024.
Proof.
have -> : / 1024 = pow (-10) by rewrite /= /Z.pow_pos /=; lra.
by rewrite (u_pow p); apply: bpow_le; lia.
Qed.

Lemma format_1 : format 1.
Proof. exact: generic_format_FLX_1. Qed.

Lemma succ_1 : succ beta fexp 1 = 1 + 2 * u.
Proof.
rewrite succ_FLX_1.
have -> : (- p + 1 = 1 - p)%Z by lia.
by rewrite (pow_1mp p).
Qed.

Lemma format_1p2u : format (1 + 2 * u).
Proof. by rewrite -succ_1; apply: generic_format_succ; apply: format_1. Qed.

Lemma ulp_1p2u : ulp (1 + 2 * u) = 2 * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu4 : u <= /4 by have := u_le_1024; lra.
have Hne : 1 + 2 * u <> 0 by lra.
have Hmag : (mag beta (1 + 2 * u) = 1%Z :> Z).
  apply: (mag_unique_pos beta (1 + 2 * u) 1); split.
    have E0 : pow (1 - 1) = 1 by [].
    by rewrite E0; lra.
  have E1 : pow 1 = 2 by [].
  by rewrite E1; lra.
by rewrite ulp_neq_0 // /cexp /fexp Hmag (pow_1mp p).
Qed.

Lemma succ_1p2u : succ beta fexp (1 + 2 * u) = 1 + 4 * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
by rewrite succ_eq_pos ?ulp_1p2u; lra.
Qed.

Lemma pred_1p2u : Ulp.pred beta fexp (1 + 2 * u) = 1.
Proof. by rewrite -succ_1 pred_succ //; apply: format_1. Qed.

(* Anything strictly within the half-ulp [u] of [1 + 2u] rounds to it: the    *)
(* two midpoints are [(1 + pred) / 2 = 1 + u] and [(1 + succ) / 2 = 1 + 3u].  *)
Lemma RN_eq_1p2u t : Rabs (t - (1 + 2 * u)) < u -> RND t = 1 + 2 * u.
Proof.
move=> Ht.
have Hu0 : 0 < u by apply: u_gt_0.
have [Ht1 Ht2] := Rabs_def2 _ _ Ht.
apply: Rle_antisym.
  by apply: round_N_le_midp; [apply: format_1p2u | rewrite succ_1p2u; lra].
by apply: round_N_ge_midp; [apply: format_1p2u | rewrite pred_1p2u; lra].
Qed.

(* The normalised case [1 <= x < 2].                                          *)
Lemma round_div_1p2u_norm x :
  format x -> 1 <= x < 2 -> RND (x * RND ((1 + 2 * u) / x)) = 1 + 2 * u.
Proof.
move=> Fx [Hx1 Hx2].
have Hu0 : 0 < u by apply: u_gt_0.
have Hu4 : u <= /4 by have := u_le_1024; lra.
have F1 : format 1 by apply: format_1.
have F12u : format (1 + 2 * u) by apply: format_1p2u.
have [Hxe1 | Hxn1] := Req_dec x 1.
  rewrite Hxe1 Rmult_1_l.
  have -> : (1 + 2 * u) / 1 = 1 + 2 * u by field.
  by rewrite !round_generic.
have Hx12u : 1 + 2 * u <= x by rewrite -succ_1; apply: succ_le_lt => //; lra.
have [Hxe2 | Hxn2] := Req_dec x (1 + 2 * u).
  have -> : (1 + 2 * u) / x = 1 by rewrite Hxe2; field; lra.
  by rewrite [RND 1]round_generic // Rmult_1_r Hxe2 round_generic.
have Hx14u : 1 + 4 * u <= x by rewrite -succ_1p2u; apply: succ_le_lt => //; lra.
set v := (1 + 2 * u) / x.
have Hxn0 : x <> 0 by lra.
have Hv1 : /2 <= v.
  rewrite /v; apply: (Rmult_le_reg_r x) => //; first by lra.
  by rewrite /Rdiv Rmult_assoc Rinv_l //; lra.
have Hv2 : v < 1.
  rewrite /v; apply: (Rmult_lt_reg_r x); first by lra.
  by rewrite /Rdiv Rmult_assoc Rinv_l //; nra.
have Hvn0 : v <> 0 by lra.
have Hmagv : (mag beta v = 0%Z :> Z).
  apply: (mag_unique_pos beta v 0); split.
    have E0 : pow (0 - 1) = /2 by rewrite /= /Z.pow_pos /=; lra.
    by rewrite E0.
  have E1 : pow 0 = 1 by [].
  by rewrite E1.
have Hulpv : ulp v = u.
  by rewrite ulp_neq_0 // /cexp /fexp Hmagv (u_pow p); congr (pow _); lia.
have Herr : Rabs (RND v - v) <= /2 * ulp v by apply: error_le_half_ulp.
rewrite Hulpv in Herr.
apply: RN_eq_1p2u.
have -> : x * RND v - (1 + 2 * u) = x * (RND v - v) by rewrite /v; field.
rewrite Rabs_mult (Rabs_pos_eq x); last by lra.
have := Rabs_pos (RND v - v).
nra.
Qed.

(* The general case, by scaling to [[1, 2)] and by sign symmetry.             *)
Lemma round_div_1p2u x :
  format x -> x <> 0 -> RND (x * RND ((1 + 2 * u) / x)) = 1 + 2 * u.
Proof.
move=> Fx Hxn0.
wlog Hxpos : x Fx Hxn0 / 0 < x => [Hw|].
  have [Hpos|Hneg] := Rlt_le_dec 0 x; first by apply: Hw.
  have Hn : - x <> 0 by lra.
  have Fn : format (- x) by apply: generic_format_opp.
  have H := Hw (- x) Fn Hn ltac:(lra).
  have Hopp2 : (1 + 2 * u) / x = - ((1 + 2 * u) / - x) by field.
  rewrite Hopp2 RN_sym; last by exact: choice_sym.
  have -> : x * - RND ((1 + 2 * u) / - x) = - x * RND ((1 + 2 * u) / - x)
    by ring.
  exact: H.
(* Scale [x] into [[1, 2)]: both the division and the product commute with a  *)
(* power of two ([round_bpow_FLX]), so the normalised case suffices.          *)
set e := (mag beta x - 1)%Z.
have Hep : pow e <= x.
  have := bpow_mag_le beta x Hxn0; rewrite (Rabs_pos_eq x); last by lra.
  by rewrite /e.
have Hes : x < pow (e + 1).
  have -> : (e + 1 = mag beta x)%Z by rewrite /e; lia.
  by have := bpow_mag_gt beta x; rewrite (Rabs_pos_eq x); last by lra.
set y := x * pow (- e).
have Hpe0 : 0 < pow e by apply: bpow_gt_0.
have Hy1 : 1 <= y.
  rewrite /y bpow_opp; apply: (Rmult_le_reg_r (pow e)) => //.
  by rewrite Rmult_1_l Rmult_assoc Rinv_l; lra.
have Hy2 : y < 2.
  rewrite /y bpow_opp; apply: (Rmult_lt_reg_r (pow e)) => //.
  rewrite Rmult_assoc Rinv_l ?Rmult_1_r; last by lra.
  by move: Hes; rewrite bpow_plus; have -> : pow 1 = 2 by []; lra.
have Fy : format y by rewrite /y; apply/format_scale.
have Hxy : x = y * pow e.
  rewrite /y Rmult_assoc -bpow_plus.
  have -> : (- e + e = 0)%Z by lia.
  by have -> : pow 0 = 1 by []; rewrite Rmult_1_r.
have Hyn0 : y <> 0 by lra.
have -> : (1 + 2 * u) / x = ((1 + 2 * u) / y) * pow (- e).
  by rewrite {1}Hxy bpow_opp; field; split; lra.
rewrite round_bpow_FLX.
have -> : x * (RND ((1 + 2 * u) / y) * pow (- e)) = y * RND ((1 + 2 * u) / y).
  by rewrite {1}Hxy bpow_opp; field; lra.
by apply: round_div_1p2u_norm.
Qed.

(* ===========================================================================*)
(*  Section 8.2, first bounds: the head lines of Algorithm 13                 *)
(*                                                                            *)
(*  Everything follows from [round_div_1p2u]: [RN(x0 a) = 1 + 2u] pins the    *)
(*  product [a x0] to within half an ulp of [1 + 2u], which is [u].           *)
(* ===========================================================================*)

(* [1 - 2u], the virtual [h0], is a float: it is [(2^p - 2) * 2^-p].          *)
Lemma format_1m2u : format (1 - 2 * u).
Proof.
have Hp2p : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
have Hpp : 0 < pow p by apply: bpow_gt_0.
have -> : 1 - 2 * u = IZR (2 ^ p - 2) * pow (- p).
  by rewrite minus_IZR -Hp2p (u_pow p) bpow_opp; field; lra.
apply: (@format_mult_pow p Hp2 (2 ^ p - 2) (- p)).
have H2 : (2 <= 2 ^ p)%Z by apply: (Z.pow_le_mono_r 2 1 p); lia.
by rewrite Z.abs_eq; lia.
Qed.

(* [a x0] is within [u] of [1 + 2u] -- the whole point of dividing [1 + 2u]   *)
(* rather than [1] by [x0].                                                   *)
Lemma reciA_x0_err x0 :
  format x0 -> x0 <> 0 -> Rabs (reciA x0 * x0 - (1 + 2 * u)) <= u.
Proof.
move=> Fx0 Hx0.
have Hr : RND (x0 * reciA x0) = 1 + 2 * u by apply: round_div_1p2u.
have Herr : Rabs (RND (x0 * reciA x0) - x0 * reciA x0)
              <= /2 * ulp (RND (x0 * reciA x0)).
  by apply: error_le_half_ulp_round.
rewrite Hr ulp_1p2u in Herr.
have -> : reciA x0 * x0 - (1 + 2 * u) = - ((1 + 2 * u) - x0 * reciA x0)
  by ring.
by rewrite Rabs_Ropp; lra.
Qed.

Lemma reciA_x0_bound x0 :
  format x0 -> x0 <> 0 -> 1 + u <= reciA x0 * x0 <= 1 + 3 * u.
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have H := reciA_x0_err Fx0 Hx0.
by split_Rabs; lra.
Qed.

(* [h11] is EXACT: it is the error of the product [a x0] taken with respect   *)
(* to [1 + 2u = RN(a x0)], and a product error is a float in FLX.             *)
Lemma reciH11_exact x0 :
  format x0 -> x0 <> 0 -> reciH11 x0 = reciA x0 * x0 - (1 + 2 * u).
Proof.
move=> Fx0 Hx0.
have Fa : format (reciA x0) by apply: generic_format_round.
have Hr : RND (x0 * reciA x0) = 1 + 2 * u by apply: round_div_1p2u.
rewrite /reciH11 round_generic //.
have -> : reciA x0 * x0 - (1 + 2 * u)
        = - (RND (x0 * reciA x0) - x0 * reciA x0) by rewrite Hr; ring.
by apply/generic_format_opp/format_err_mul.
Qed.

Lemma reciH11_bound x0 : format x0 -> x0 <> 0 -> Rabs (reciH11 x0) <= u.
Proof.
by move=> Fx0 Hx0; rewrite reciH11_exact //; apply: reciA_x0_err.
Qed.

(* [|a x1| <= 2u|a x0| <= 2u(1 + 3u)]: the second limb is at most an ulp of   *)
(* the first, and [ulp x0 <= 2u|x0|].                                         *)
Lemma reciA_x1_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciA x0 * x1) <= 2 * u * (1 + 3 * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hax0 := reciA_x0_bound Fx0 Hx0.
have Hx1u : Rabs x1 <= 2 * u * Rabs x0.
  case: Hx1 => [->|Hx1]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have H := @ulp_2u p beta Hp2 x0; lra.
have -> : reciA x0 * x1 = (reciA x0 * x0) * (x1 / x0) by field.
rewrite Rabs_mult.
have Hx0p : 0 < Rabs x0 by apply: Rabs_pos_lt.
have Hd : Rabs (x1 / x0) <= 2 * u.
  rewrite /Rdiv Rabs_mult Rabs_inv.
  apply: (Rmult_le_reg_r (Rabs x0)) => //.
  rewrite Rmult_assoc Rinv_l; last by lra.
  by rewrite Rmult_1_r; lra.
have Hp : Rabs (reciA x0 * x0) <= 1 + 3 * u.
  by rewrite Rabs_pos_eq; lra.
have := Rabs_pos (x1 / x0); have := Rabs_pos (reciA x0 * x0).
by nra.
Qed.

(* The argument of the [h1] rounding.                                         *)
Lemma reciH1_arg_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (- reciH11 x0 - reciA x0 * x1) <= 3 * u + 6 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hh11 := reciH11_bound Fx0 Hx0.
have Hax1 := reciA_x1_bound Fx0 Hx0 Hx1.
have Hsum := Rabs_triang (- reciH11 x0) (- (reciA x0 * x1)).
rewrite !Rabs_Ropp in Hsum.
have -> : - reciH11 x0 - reciA x0 * x1
        = - reciH11 x0 + - (reciA x0 * x1) by ring.
by nra.
Qed.

(* [|h1| <= 3u + 10u^2] (paper Section 8.2).                                  *)
Lemma reciH1_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciH1 x0 x1) <= 3 * u + 10 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Ht := reciH1_arg_bound Fx0 Hx0 Hx1.
have Hrel :=
  @relative_error_le p beta Hp2 choice (- reciH11 x0 - reciA x0 * x1).
have Hpos := Rabs_pos (- reciH11 x0 - reciA x0 * x1).
rewrite /reciH1.
have Habs : Rabs (RND (- reciH11 x0 - reciA x0 * x1))
              <= (1 + u) * Rabs (- reciH11 x0 - reciA x0 * x1).
  by move: Hrel; split_Rabs; nra.
by nra.
Qed.

(* The rounding error of the [h1] line: [h] is that close to [2 - a(x0+x1)].  *)
Lemma reciH1_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciH1 x0 x1 - (- reciH11 x0 - reciA x0 * x1))
    <= 3 * (u * u) + 6 * (u * u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Ht := reciH1_arg_bound Fx0 Hx0 Hx1.
have Hrel :=
  @relative_error_le p beta Hp2 choice (- reciH11 x0 - reciA x0 * x1).
by rewrite /reciH1; nra.
Qed.

(* ===========================================================================*)
(*  Section 8.2: the Newton double word [b] is a DW                           *)
(*                                                                            *)
(*  [b01 = RN(a(1 - 2u))] keeps the size of [a] while [b12] is [O(u|a|)], so  *)
(*  the Fast2Sum operands are ordered and [magnitude_Fast2Sum] applies.       *)
(* ===========================================================================*)
Lemma reciB01_bound x0 :
  format x0 -> x0 <> 0 ->
  (1 - 3 * u) * Rabs (reciA x0) <= Rabs (reciB01 x0).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have Hrel := @relative_error_le p beta Hp2 choice (reciA x0 * (1 - 2 * u)).
have Hb : reciB01 x0 = RND (reciA x0 * (1 - 2 * u)) by [].
have Hm : Rabs (reciA x0 * (1 - 2 * u)) = (1 - 2 * u) * Rabs (reciA x0).
  by rewrite Rabs_mult (Rabs_pos_eq (1 - 2 * u)); lra.
rewrite Hb.
move: Hrel; rewrite Hm; split_Rabs; nra.
Qed.

Lemma reciB11_bound x0 :
  format x0 -> x0 <> 0 -> Rabs (reciB11 x0) <= u * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have Hb : reciB11 x0
        = RND (reciA x0 * (1 - 2 * u) - RND (reciA x0 * (1 - 2 * u))) by [].
have Fe : format (reciA x0 * (1 - 2 * u) - RND (reciA x0 * (1 - 2 * u))).
  have -> : reciA x0 * (1 - 2 * u) - RND (reciA x0 * (1 - 2 * u))
          = - (RND (reciA x0 * (1 - 2 * u)) - reciA x0 * (1 - 2 * u)) by ring.
  apply: generic_format_opp.
  by apply: format_err_mul; [apply: generic_format_round | apply: format_1m2u].
rewrite Hb round_generic //.
have Hrel := @relative_error_le p beta Hp2 choice (reciA x0 * (1 - 2 * u)).
have Hm : Rabs (reciA x0 * (1 - 2 * u)) = (1 - 2 * u) * Rabs (reciA x0).
  by rewrite Rabs_mult (Rabs_pos_eq (1 - 2 * u)); lra.
have -> : reciA x0 * (1 - 2 * u) - RND (reciA x0 * (1 - 2 * u))
        = - (RND (reciA x0 * (1 - 2 * u)) - reciA x0 * (1 - 2 * u)) by ring.
rewrite Rabs_Ropp.
by move: Hrel; rewrite Hm; nra.
Qed.

Lemma reciB12_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB12 x0 x1) <= 5 * u * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have Hb11 := reciB11_bound Fx0 Hx0.
have Hh1 := reciH1_bound Fx0 Hx0 Hx1.
have Hah1 : Rabs (reciA x0 * reciH1 x0 x1)
              <= (3 * u + 10 * (u * u)) * Rabs (reciA x0).
  rewrite Rabs_mult; have := Rabs_pos (reciH1 x0 x1); nra.
have Ht : Rabs (reciB11 x0 + reciA x0 * reciH1 x0 x1)
            <= (4 * u + 10 * (u * u)) * Rabs (reciA x0).
  by have := Rabs_triang (reciB11 x0) (reciA x0 * reciH1 x0 x1); nra.
have Hrel :=
  @relative_error_le p beta Hp2 choice
    (reciB11 x0 + reciA x0 * reciH1 x0 x1).
have Hpos2 := Rabs_pos (reciB11 x0 + reciA x0 * reciH1 x0 x1).
rewrite /reciB12.
have Habs : Rabs (RND (reciB11 x0 + reciA x0 * reciH1 x0 x1))
              <= (1 + u) * Rabs (reciB11 x0 + reciA x0 * reciH1 x0 x1).
  by move: Hrel; split_Rabs; nra.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
by clear -Hu0 Hu1024 Hu2 Hu3 Hpos Ht Habs Hpos2; nra.
Qed.

(* The argument of the [b12] rounding.                                        *)
Lemma reciB12_arg_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB11 x0 + reciA x0 * reciH1 x0 x1)
    <= (4 * u + 10 * (u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Hb11 := reciB11_bound Fx0 Hx0.
have Hh1 := reciH1_bound Fx0 Hx0 Hx1.
have Hah1 : Rabs (reciA x0 * reciH1 x0 x1)
              <= (3 * u + 10 * (u * u)) * Rabs (reciA x0).
  rewrite Rabs_mult; have := Rabs_pos (reciH1 x0 x1); nra.
by have := Rabs_triang (reciB11 x0) (reciA x0 * reciH1 x0 x1); nra.
Qed.

(* The rounding error of the [b12] line.                                      *)
Lemma reciB12_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB12 x0 x1 - (reciB11 x0 + reciA x0 * reciH1 x0 x1))
    <= (4 * (u * u) + 10 * (u * u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Ht := reciB12_arg_bound Fx0 Hx0 Hx1.
have Hrel :=
  @relative_error_le p beta Hp2 choice
    (reciB11 x0 + reciA x0 * reciH1 x0 x1).
by rewrite /reciB12; nra.
Qed.

(* The Fast2Sum ordering hypothesis.                                          *)
Lemma reciB12_le_B01 x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB12 x0 x1) <= Rabs (reciB01 x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have H1 := reciB12_bound Fx0 Hx0 Hx1.
have H2 := reciB01_bound Fx0 Hx0.
by nra.
Qed.

(* [b] is a double word: its two words are floats (both are roundings) and    *)
(* the low one is at most half an ulp of the high one, because the Fast2Sum   *)
(* operands are ordered.                                                      *)
Lemma reciB_isDW x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  isDW (reciBW x0 x1).
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (reciB01 x0) by apply: generic_format_round.
have F12 : format (reciB12 x0 x1) by apply: generic_format_round.
have Hord := reciB12_le_B01 Fx0 Hx0 Hx1.
have Hmag := @magnitude_Fast2Sum p Hp2 choice _ _ F01 F12 (fun _ => Hord).
have Hfor := @format_Fast2Sum p Hp2 choice (reciB01 x0) (reciB12 x0 x1).
rewrite /reciBW /reciB.
case E : (Fast2Sum (reciB01 x0) (reciB12 x0 x1)) => [s e].
rewrite E in Hmag Hfor.
rewrite /magnitudeDWR in Hmag.
case: Hfor => Fs Fe.
split => //.
by right; rewrite dwhE dwlE; lra.
Qed.

(* ===========================================================================*)
(*  Section 8.2: how well the Newton double word approximates [1/x]           *)
(*                                                                            *)
(*  Everything is stated DIMENSIONLESSLY, as [|b*x - 1| <= C]: that is        *)
(*  [|b - 1/x| <= C|1/x|], with no division to carry around.  The Newton step *)
(*  is quadratic through the identity                                         *)
(*        (a (2 - X a)) X - 1 = - (a X - 1)^2 ,                               *)
(*  so an [O(u)] starting point gives an [O(u^2)] double word.                *)
(* ===========================================================================*)

(* [b] as a real number: Fast2Sum is error-free here, so [b = b01 + b12].     *)
Lemma TWval_reciBW x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  TWval (reciBW x0 x1) = reciB01 x0 + reciB12 x0 x1.
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (reciB01 x0) by apply: generic_format_round.
have F12 : format (reciB12 x0 x1) by apply: generic_format_round.
have Hord := reciB12_le_B01 Fx0 Hx0 Hx1.
have Hc := @Fast2Sum_correct p Hp2 choice _ _ F01 F12 (fun _ => Hord).
rewrite /reciBW /TWval /reciB.
by rewrite Rplus_0_r; exact: Hc.
Qed.

(* The DW step is EXACTLY the Newton value [a(2 - X a)] plus the two          *)
(* rounding errors of the [h1] and [b12] lines: [b01 + b11 = a(1 - 2u)] and   *)
(* [h11 = a x0 - (1 + 2u)] are both exact, and                                *)
(* [(1 - 2u) + h1 = 2 - a(x0 + x1) + (h1 error)].                             *)
Lemma reciBW_newton_eq x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  TWval (reciBW x0 x1)
    = reciA x0 * (2 - (x0 + x1) * reciA x0)
      + reciA x0 * (reciH1 x0 x1 - (- reciH11 x0 - reciA x0 * x1))
      + (reciB12 x0 x1 - (reciB11 x0 + reciA x0 * reciH1 x0 x1)).
Proof.
move=> Fx0 Hx0 Hx1.
have Fa : format (reciA x0) by apply: generic_format_round.
have Hprod := TwoProd_correct Fa format_1m2u.
have [_ Hb _ _] := Hprod p_gt_0 rnd valid_rnd.
have Hb2 : reciB01 x0 + reciB11 x0 = reciA x0 * (1 - 2 * u) by exact: Hb.
have Hh11 := reciH11_exact Fx0 Hx0.
rewrite (TWval_reciBW Fx0 Hx0 Hx1) Hh11.
have -> : reciB01 x0 = reciA x0 * (1 - 2 * u) - reciB11 x0 by lra.
ring.
Qed.

Lemma reciBW_newton_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (TWval (reciBW x0 x1) - reciA x0 * (2 - (x0 + x1) * reciA x0))
    <= (7 * (u * u) + 16 * (u * u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Hh1 := reciH1_err Fx0 Hx0 Hx1.
have Hb12 := reciB12_err Fx0 Hx0 Hx1.
rewrite (reciBW_newton_eq Fx0 Hx0 Hx1).
have -> : reciA x0 * (2 - (x0 + x1) * reciA x0)
          + reciA x0 * (reciH1 x0 x1 - (- reciH11 x0 - reciA x0 * x1))
          + (reciB12 x0 x1 - (reciB11 x0 + reciA x0 * reciH1 x0 x1))
          - reciA x0 * (2 - (x0 + x1) * reciA x0)
        = reciA x0 * (reciH1 x0 x1 - (- reciH11 x0 - reciA x0 * x1))
          + (reciB12 x0 x1 - (reciB11 x0 + reciA x0 * reciH1 x0 x1)) by ring.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_mult.
by nra.
Qed.

(* [a X] is within [O(u)] of [1] -- ASYMMETRICALLY, which is what bounds      *)
(* [|2 - a X|] below [1 + u + 6u^2] rather than [1 + 5u + 6u^2].              *)
Lemma reciA_X_range x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  1 - u - 6 * (u * u) <= reciA x0 * (x0 + x1) <= 1 + 5 * u + 6 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hax0 := reciA_x0_bound Fx0 Hx0.
have Hax1 := reciA_x1_bound Fx0 Hx0 Hx1.
have -> : reciA x0 * (x0 + x1) = (reciA x0 * x0) + reciA x0 * x1 by ring.
by move: Hax1; split_Rabs; lra.
Qed.

(* [|a X - 1| <= 5u + 6u^2]: the starting point is accurate to [O(u)].        *)
Lemma reciA_X_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciA x0 * (x0 + x1) - 1) <= 5 * u + 6 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
by have := reciA_X_range Fx0 Hx0 Hx1; split_Rabs; lra.
Qed.

(* The Newton value is quadratically accurate: an identity, not an estimate.  *)
Lemma newton_id (a X : R) : (a * (2 - X * a)) * X - 1 = - (a * X - 1) ^ 2.
Proof. by ring. Qed.

(* [|b X - 1| <= 32u^2 + 112u^3] (paper: [32u^2 + 110u^3]; the extra [u^3]    *)
(* absorbs the [158u^4 + 96u^5] the squaring leaves behind).                  *)
Lemma reciB_X_err x0 x1 :
  format x0 -> 1 <= x0 < 2 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (TWval (reciBW x0 x1) * (x0 + x1) - 1)
    <= 32 * (u * u) + 112 * (u * u * u).
Proof.
move=> Fx0 [Hx0l Hx0r] Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hx0 : x0 <> 0 by lra.
have Hax0 := reciA_x0_bound Fx0 Hx0.
have HaX := reciA_X_bound Fx0 Hx0 Hx1.
have Hnew := reciBW_newton_err Fx0 Hx0 Hx1.
have Ha : Rabs (reciA x0) <= 1 + 3 * u.
  have Hap : 0 < reciA x0 by nra.
  by rewrite Rabs_pos_eq; nra.
have Hap : 0 < Rabs (reciA x0) by move: Hax0; split_Rabs; nra.
have HaXa : Rabs (reciA x0 * (x0 + x1)) <= 1 + 5 * u + 6 * (u * u).
  by move: HaX; split_Rabs; lra.
set b := TWval (reciBW x0 x1).
set a := reciA x0 in Ha Hnew HaXa HaX Hap.
set X := x0 + x1 in Hnew HaXa HaX.
(* The Newton identity turns the [O(u)] starting error into an [O(u^2)] one.  *)
have Hid : b * X - 1 = - (a * X - 1) ^ 2 + (b - a * (2 - X * a)) * X
  by rewrite /b; ring.
have HXb : Rabs ((b - a * (2 - X * a)) * X)
             <= (7 * (u * u) + 16 * (u * u * u)) * (1 + 5 * u + 6 * (u * u)).
  rewrite Rabs_mult.
  have HH : Rabs a * Rabs X = Rabs (a * X) by rewrite Rabs_mult.
  have HpX := Rabs_pos X.
  have H1 : Rabs (b - a * (2 - X * a))
              <= (7 * (u * u) + 16 * (u * u * u)) * Rabs a
    by rewrite /b; exact: Hnew.
  have Hstep : Rabs (b - a * (2 - X * a)) * Rabs X
                 <= (7 * (u * u) + 16 * (u * u * u)) * (Rabs a * Rabs X)
    by nra.
  rewrite HH in Hstep.
  have Hk : 0 <= 7 * (u * u) + 16 * (u * u * u) by nra.
  by nra.
have Hsq : (a * X - 1) ^ 2 <= (5 * u + 6 * (u * u)) ^ 2.
  have H5 : 0 <= 5 * u + 6 * (u * u) by nra.
  by clear -HaX H5; split_Rabs; nra.
have -> : x0 + x1 = X by [].
rewrite Hid.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_Ropp.
have HRsq : Rabs ((a * X - 1) ^ 2) = (a * X - 1) ^ 2
  by apply: Rabs_pos_eq; apply: pow2_ge_0.
rewrite HRsq.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
have Hu4 : u * u * u * u <= /1024 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= /1024 * (u * u * u * u) by nra.
by clear -Hu0 Hu1024 Hu2 Hu3 Hu4 Hu5 Hsq HXb; nra.
Qed.

(* [|b| <= 1 + 5u]: [b] is a Newton iterate of [1/x0] with [x0 >= 1].         *)
Lemma reciBW_bound x0 x1 :
  format x0 -> 1 <= x0 < 2 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (TWval (reciBW x0 x1)) <= 1 + 5 * u.
Proof.
move=> Fx0 [Hx0l Hx0r] Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hx0 : x0 <> 0 by lra.
have Hax0 := reciA_x0_bound Fx0 Hx0.
have HaX := reciA_X_range Fx0 Hx0 Hx1.
have Hnew := reciBW_newton_err Fx0 Hx0 Hx1.
have Ha : Rabs (reciA x0) <= 1 + 3 * u.
  have Hap : 0 < reciA x0 by nra.
  by rewrite Rabs_pos_eq; nra.
set b := TWval (reciBW x0 x1).
set a := reciA x0 in Ha Hnew HaX.
set X := x0 + x1 in Hnew HaX.
have H2 : Rabs (2 - X * a) <= 1 + u + 6 * (u * u).
  have Hc : 2 - X * a = 1 - (a * X - 1) by ring.
  by rewrite Hc; split_Rabs; lra.
have Hpa := Rabs_pos a.
have HN : Rabs (a * (2 - X * a)) <= (1 + 3 * u) * (1 + u + 6 * (u * u)).
  rewrite Rabs_mult; have := Rabs_pos (2 - X * a); nra.
have Hb : Rabs b <= Rabs (a * (2 - X * a)) + Rabs (b - a * (2 - X * a)).
  by have := Rabs_triang (a * (2 - X * a)) (b - a * (2 - X * a)); split_Rabs;
     lra.
rewrite /b in Hb.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
by clear -Hu0 Hu1024 Hu2 Hu3 Hb HN Hnew Ha Hpa; rewrite /b; nra.
Qed.

(* The full Section-8.2 bound: [|b x - 1| <= 34u^2 + 123u^3], i.e.            *)
(* [|b - 1/x| <= (34u^2 + 123u^3)|1/x|] (paper: [34u^2 + 115u^3]).  The       *)
(* third limb only contributes [|b x2| <= 2u^2(1 + 5u)].                      *)
Lemma reciB_x_err x0 x1 x2 :
  tw_norm x0 x1 x2 ->
  Rabs (TWval (reciBW x0 x1) * (x0 + x1 + x2) - 1)
    <= 34 * (u * u) + 123 * (u * u * u).
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1 Hx2] := Hn.
have HX := reciB_X_err Fx0 (conj Hx0l Hx0r) Hx1.
have Hb := reciBW_bound Fx0 (conj Hx0l Hx0r) Hx1.
have Hx2b : Rabs x2 < 2 * (u * u) by apply: (@tw_norm_x2 p Hp2 x0 x1 x2 Hn).
set b := TWval (reciBW x0 x1) in HX Hb *.
have -> : b * (x0 + x1 + x2) - 1 = (b * (x0 + x1) - 1) + b * x2 by ring.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_mult.
have := Rabs_pos b; have := Rabs_pos x2.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
by nra.
Qed.

(* ===========================================================================*)
(*  Scale and sign equivariance of the Newton double word                     *)
(*                                                                            *)
(*  [b] is a reciprocal, so it scales by [pow (-c)] when the input scales by  *)
(*  [pow c]: every line commutes with a power of two ([round_scale]), and the *)
(*  intermediate [h11], [h1] -- which approximate [a x0] and [2 - a x] -- are *)
(*  scale INVARIANT.  This is what reduces the Section 8.2 bound, proved on a *)
(*  normalised input, to an arbitrary triple word.                            *)
(* ===========================================================================*)
Lemma reciA_scale x0 c :
  x0 <> 0 -> reciA (x0 * pow c) = reciA x0 * pow (- c).
Proof.
move=> Hx0.
have Hp0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
rewrite /reciA -(round_scale p choice _ (- c)).
congr (RND _).
by rewrite bpow_opp; field; split.
Qed.

Lemma reciA_opp x0 : x0 <> 0 -> reciA (- x0) = - reciA x0.
Proof.
move=> Hx0.
rewrite /reciA.
have -> : (1 + 2 * u) / - x0 = - ((1 + 2 * u) / x0) by field.
by rewrite RN_sym.
Qed.

Lemma reciA_x0_scale x0 c :
  x0 <> 0 -> reciA (x0 * pow c) * (x0 * pow c) = reciA x0 * x0.
Proof.
move=> Hx0.
have Hp0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
by rewrite reciA_scale // bpow_opp; field.
Qed.

Lemma reciH11_scale x0 c :
  x0 <> 0 -> reciH11 (x0 * pow c) = reciH11 x0.
Proof. by move=> Hx0; rewrite /reciH11 reciA_x0_scale. Qed.

Lemma reciH11_opp x0 : x0 <> 0 -> reciH11 (- x0) = reciH11 x0.
Proof.
move=> Hx0; rewrite /reciH11 reciA_opp //.
by congr (RND _); ring.
Qed.

Lemma reciH1_scale x0 x1 c :
  x0 <> 0 -> reciH1 (x0 * pow c) (x1 * pow c) = reciH1 x0 x1.
Proof.
move=> Hx0.
have Hp0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
rewrite /reciH1 reciH11_scale // reciA_scale //.
by congr (RND _); rewrite bpow_opp; field.
Qed.

Lemma reciH1_opp x0 x1 : x0 <> 0 -> reciH1 (- x0) (- x1) = reciH1 x0 x1.
Proof.
move=> Hx0; rewrite /reciH1 reciH11_opp // reciA_opp //.
by congr (RND _); ring.
Qed.

Lemma reciB01_scale x0 c :
  x0 <> 0 -> reciB01 (x0 * pow c) = reciB01 x0 * pow (- c).
Proof.
move=> Hx0.
rewrite /reciB01 /= reciA_scale // -(round_scale p choice _ (- c)).
by congr (RND _); ring.
Qed.

Lemma reciB01_opp x0 : x0 <> 0 -> reciB01 (- x0) = - reciB01 x0.
Proof.
move=> Hx0.
rewrite /reciB01 /= reciA_opp //.
by rewrite -RN_sym //; congr (RND _); ring.
Qed.

Lemma reciB11_scale x0 c :
  x0 <> 0 -> reciB11 (x0 * pow c) = reciB11 x0 * pow (- c).
Proof.
move=> Hx0.
rewrite /reciB11 /= reciA_scale //.
have -> : reciA x0 * pow (- c) * (1 - 2 * u)
        = reciA x0 * (1 - 2 * u) * pow (- c) by ring.
rewrite (round_scale p choice).
by rewrite -Rmult_minus_distr_r (round_scale p choice).
Qed.

Lemma reciB11_opp x0 : x0 <> 0 -> reciB11 (- x0) = - reciB11 x0.
Proof.
move=> Hx0.
rewrite /reciB11 /= reciA_opp //.
have -> : - reciA x0 * (1 - 2 * u) = - (reciA x0 * (1 - 2 * u)) by ring.
rewrite RN_sym //.
have -> : - (reciA x0 * (1 - 2 * u)) - - RND (reciA x0 * (1 - 2 * u))
        = - (reciA x0 * (1 - 2 * u) - RND (reciA x0 * (1 - 2 * u))) by ring.
by rewrite RN_sym.
Qed.

Lemma reciB12_scale x0 x1 c :
  x0 <> 0 -> reciB12 (x0 * pow c) (x1 * pow c) = reciB12 x0 x1 * pow (- c).
Proof.
move=> Hx0.
rewrite /reciB12 reciB11_scale // reciA_scale // reciH1_scale //
        -(round_scale p choice _ (- c)).
by congr (RND _); ring.
Qed.

Lemma reciB12_opp x0 x1 :
  x0 <> 0 -> reciB12 (- x0) (- x1) = - reciB12 x0 x1.
Proof.
move=> Hx0.
rewrite /reciB12 reciB11_opp // reciA_opp // reciH1_opp //.
by rewrite -RN_sym //; congr (RND _); ring.
Qed.

Lemma reciBW_scale x0 x1 c :
  x0 <> 0 ->
  reciBW (x0 * pow c) (x1 * pow c) = scaleTW (- c) (reciBW x0 x1).
Proof.
move=> Hx0.
rewrite /reciBW /reciB reciB01_scale // reciB12_scale //.
rewrite /Fast2Sum /scaleTW /dwh /dwl.
have Add : forall y z : R, y * pow (- c) + z * pow (- c) = (y + z) * pow (- c)
  by move=> *; ring.
have Sub : forall y z : R, y * pow (- c) - z * pow (- c) = (y - z) * pow (- c)
  by move=> *; ring.
by rewrite !(Add, Sub, (round_scale p choice)) Rmult_0_l.
Qed.

Lemma reciBW_opp x0 x1 :
  x0 <> 0 -> reciBW (- x0) (- x1) = negTW (reciBW x0 x1).
Proof.
move=> Hx0.
rewrite /reciBW /reciB reciB01_opp // reciB12_opp //.
rewrite /Fast2Sum /negTW /dwh /dwl.
have Add : forall y z : R, - y + - z = - (y + z) by move=> *; ring.
have Sub : forall y z : R, - y - - z = - (y - z) by move=> *; ring.
by rewrite !(Add, Sub, RN_sym) // Ropp_0.
Qed.

(* The Section 8.2 bound for an ARBITRARY triple word, by normalisation.      *)
Lemma reciBW_x_err x :
  isTW x -> tw0 x <> 0 ->
  Rabs (TWval (reciBW (tw0 x) (tw1 x)) * TWval x - 1)
    <= 34 * (u * u) + 123 * (u * u * u).
Proof.
move=> Hx Hx0.
have [c _ [Hpos Hneg]] := (@isTW_normalize p Hp2 choice x Hx Hx0).
have Hpc : 0 < pow c by apply: bpow_gt_0.
case: x Hx Hx0 Hpos Hneg => x0 x1 x2 Hx Hx0 Hpos Hneg.
rewrite tw0E tw1E.
rewrite tw0E in Hx0 Hpos Hneg.
have [Hlt | Hgt] := Rdichotomy _ _ Hx0.
  have Hn := Hneg Hlt.
  rewrite /scaleTW /negTW /tw_normP in Hn.
  have Hx0n : - x0 <> 0 by lra.
  have Hb := reciB_x_err Hn.
  rewrite (reciBW_scale _ _ Hx0n) reciBW_opp // TWval_scale TWval_opp in Hb.
  have HE : - TWval (reciBW x0 x1) * pow (- c)
              * (- x0 * pow c + - x1 * pow c + - x2 * pow c)
          = TWval (reciBW x0 x1) * TWval (TWR x0 x1 x2).
    by rewrite /TWval bpow_opp; field; lra.
  by rewrite HE in Hb.
have Hn := Hpos Hgt.
rewrite /scaleTW /tw_normP in Hn.
have Hb := reciB_x_err Hn.
rewrite (reciBW_scale _ _ Hx0) TWval_scale in Hb.
have HE : TWval (reciBW x0 x1) * pow (- c)
            * (x0 * pow c + x1 * pow c + x2 * pow c)
        = TWval (reciBW x0 x1) * TWval (TWR x0 x1 x2).
  by rewrite /TWval bpow_opp; field; lra.
by rewrite HE in Hb.
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: the result is a triple-word number.                  *)
(*                                                                            *)
(*  Two ingredients, and both products are then covered by Algorithm 11's     *)
(*  (resp. Algorithm 12's) own correctness:                                   *)
(*  (i)  [b] is a double word ([reciB_isDW]);                                 *)
(*  (ii) the head limb of [3Prod_{2,3}(b, x)] is exactly [1] -- old paper     *)
(*       Section 8.3, the property that forces [p >= 10] -- so that [2 - _]   *)
(*       keeps the same [ulp] and [sub2TW] preserves [isTW].                  *)
(* ===========================================================================*)

(* [2 - t] is a triple word as soon as [t]'s head is [1]: the head stays [1], *)
(* so the two [ulp] gaps are unchanged, and the low limbs are just negated.   *)
Lemma sub2TW_isTW t : isTW t -> tw0 t = 1 -> isTW (sub2TW t).
Proof.
case: t => t0 t1 t2 [F0 F1 F2 H1 H2] /= Ht0.
rewrite Ht0.
have -> : 2 - 1 = 1 by ring.
split.
- exact: format_1.
- exact: generic_format_opp.
- exact: generic_format_opp.
- case: H1 => [->|H1]; first by left; rewrite Ropp_0.
  by right; rewrite Rabs_Ropp -Ht0.
case: H2 => [->|H2]; first by left; rewrite Ropp_0.
by right; rewrite !Rabs_Ropp ulp_opp.
Qed.

(* What Section 8.3 delivers about a [3Prod_{2,3}] whose product is close to  *)
(* [1]: its head limb is exactly [1].  Stated as a property of the multiplier *)
(* so that both variants share the assembly below.                            *)
Definition head_one (mul : twR -> twR -> twR) : Prop :=
  forall b y, isDW b -> isTW y ->
    Rabs (TWval b * TWval y - 1) <= 35 * (u * u) -> tw0 (mul b y) = 1.

(* The generic assembly: [mul1] must return a triple word and satisfy         *)
(* [head_one] (so that [2 - mul1 b x] is again a triple word); [mul2] need    *)
(* only return a triple word.                                                 *)
Lemma ThreeReciAux_isTW mul1 mul2 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> tw0 y = 1 -> isTW (mul2 b y)) ->
  head_one mul1 ->
  forall x, isTW x -> tw0 x <> 0 -> isTW (ThreeReciAux mul1 mul2 x).
Proof.
move=> Hmul Hmul2 Hhead x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1 : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HDW : isDW (reciBW (tw0 x) (tw1 x)) by apply: reciB_isDW.
have Herr := reciBW_x_err Hx Hx0.
have Herr35 : Rabs (TWval (reciBW (tw0 x) (tw1 x)) * TWval x - 1)
                <= 35 * (u * u).
  have Hu3 : u * u * u <= /1024 * (u * u) by nra.
  by clear -Hu0 Hu1024 Hu3 Herr; nra.
have Hprod := Hmul _ _ HDW Hx.
have Hhead1 := Hhead _ _ HDW Hx Herr35.
rewrite /ThreeReciAux.
apply: Hmul2 => //; first by apply: sub2TW_isTW.
by case: (mul1 _ _) Hhead1 => t0 t1 t2 /= ->; ring.
Qed.

(* ===========================================================================*)
(*  Towards Section 8.3: the two facts the head argument runs on              *)
(*                                                                            *)
(*  GENERIC, both of them -- [vecSum_head_sep] belongs in VecSum.v and        *)
(*  [head_eq_1] in Uls.v/Nonoverlap.v; they are kept here until the head      *)
(*  lemma lands, to avoid rebuilding the stack for a moving target.           *)
(* ===========================================================================*)

(* STEP 1 of the head argument, to be stated and proved in VecSum.v: the      *)
(* first TWO limbs of a VecSum output are the two words of a single 2Sum      *)
(* ([vecSum (a :: b :: l) = dwh (TwoSum a s) :: dwl (TwoSum a s) :: _] with   *)
(* [s = (vecSumAux (b :: l)).2]), so they satisfy the DOUBLE-WORD separation  *)
(* [2|e1| <= ulp e0] -- [magnitude_TwoSum] on that 2Sum, with                 *)
(* [format_vecSumAux2] for [format s].  This is strictly better than the      *)
(* P-nonoverlap [|e1| < ulp e0] of Theorem 1, and it is exactly the factor 2  *)
(* the head argument needs: the triple [(1 + 2u, -2u + 2u^2, ...)] IS         *)
(* P-nonoverlapping and sums to [1 + O(u^2)], so NO argument based on the     *)
(* output of the algorithm alone can pin its head to [1].                     *)

(* The head argument itself, as pure floating-point arithmetic: a float [e0]  *)
(* whose tail is at most HALF an ulp plus [O(u^2)], and whose total is within *)
(* [36u^2] of [1], MUST be [1].  The half-ulp is what the leading VecSum      *)
(* limbs really satisfy ([vecSum_head_sep]: [e0] and [e1] are the two words   *)
(* of ONE 2Sum); the [200u^2] slack absorbs the remaining limbs, which are    *)
(* the rounding errors of a VecSum whose entries are all [O(u)].              *)
(*                                                                            *)
(* The old paper states the tail bound as [(1 - 2^-4) uls(e0)] instead.  That *)
(* form is NOT enough: [[16; -8; -4; -2; -1]] is F-nonoverlapping and sums to *)
(* [1] with head [16], so a [uls]-only tail bound cannot pin the head -- the  *)
(* argument really needs the [ulp]-scale separation of the two leading limbs. *)
(*                                                                            *)
(* Margins: [u - 200u^2] above [1] (where [ulp e0 = 2u]) and [u/2 - 200u^2]   *)
(* below (where [ulp e0 = u]), both of which must beat [36u^2].  The binding  *)
(* one is [u/2 > 236u^2], i.e. [u < 1/472]; [p >= 10] gives [u <= 1/1024].    *)
(* The tolerance on [|v - 1|] is a PARAMETER.  Algorithm 13 needs only        *)
(* [36u^2], but Algorithm 15 arrives with [~162u^2]: there the second factor  *)
(* is [i(1) = 3Prod(b, x)], so the product is [b^2 x = (b sqrt x)^2] and the  *)
(* seed error enters SQUARED.  The head argument does not care -- it only     *)
(* needs [|v - 1|] small compared to [u], the gap from [1] to its neighbours  *)
(* being [u] below and [2u] above.  The binding constraint is the [e0 < 1]    *)
(* branch, which needs [(c + 200) u < 1/2]; [c u <= 1/4] gives it, and allows *)
(* [c] up to [256] at [p >= 10] and [512] at [p >= 11].                       *)
Lemma head_eq_1_c c e0 v :
  c * u <= / 4 ->
  format e0 -> Rabs (v - e0) <= / 2 * ulp e0 + 200 * (u * u) ->
  Rabs (v - 1) <= c * (u * u) -> e0 = 1.
Proof.
move=> Hc Fe0 Ht Habs.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hulp := @ulp_2u p beta Hp2 e0.
have Hulp0 : 0 <= ulp e0 by apply: ulp_ge_0.
(* The one fact every step below needs about [c]: [c u^2 <= u/4].  Keeping it *)
(* in this LINEAR form is what lets the [nra] calls stay scalar.              *)
have Hcu2 : c * (u * u) <= / 4 * u by nra.
(* [e0] is within [2u] of [1]: the tail is at most [u|e0| + 200u^2] (using    *)
(* [ulp e0 <= 2u|e0|]), so [|e0 - 1| <= c u^2 + 200u^2 + u |e0|].             *)
have Hd : Rabs (e0 - 1) <= c * (u * u) + (u * Rabs e0 + 200 * (u * u)).
  have H1 : Rabs (e0 - 1) <= Rabs (v - 1) + Rabs (v - e0).
    have -> : e0 - 1 = (v - 1) + - (v - e0) by ring.
    by have := Rabs_triang (v - 1) (- (v - e0)); rewrite Rabs_Ropp; lra.
  by clear -H1 Ht Habs Hulp Hulp0 Hu0; nra.
have Hinv := Rabs_triang_inv e0 1.
have Hae : Rabs e0 <= 101 / 100.
  by rewrite Rabs_R1 in Hinv; clear -Hinv Hd Hu0 Hu1024 Hcu2; nra.
have He0pos : 0 < e0.
  have Hle := Rle_abs e0.
  have Hle2 := Rabs_le_inv e0 (Rabs e0) (Rle_refl _).
  by clear -Hd Hae Hu0 Hu1024 Hcu2 Hle Hle2; split_Rabs; nra.
have Hrange : Rabs (e0 - 1) <= 2 * u
  by clear -Hd Hae Hu0 Hu1024 Hcu2; nra.
have Hlo : 1 - 2 * u <= e0 by clear -Hrange; split_Rabs; lra.
have Hhi : e0 <= 1 + 2 * u by clear -Hrange; split_Rabs; lra.
have Hu1 := @ulp_one p.
have E1 : (1 = pow 0)%R by [].
case: (Rtotal_order e0 1) => [Hlt|[//|Hgt]].
(* [e0 < 1]: then [e0 <= pred 1 = 1 - u], and [e0] lies in [[1/2, 1)] so its  *)
(* [ulp] is [u] -- the tail is at most [15/16 u] and cannot bridge the gap.   *)
- have Hpred : e0 <= 1 - u.
    have H := @pred_ge_gt beta fexp _ e0 1 Fe0 format_1 Hlt.
    have H2 := H (FLX_exp_valid p).
    move: H2; rewrite {1}E1 pred_bpow /FLX_exp -E1.
    have -> : (0 - p = - p)%Z by lia.
    by move=> /(_ p_gt_0) H3; rewrite u_pow.
  have Hulpe : ulp e0 = u.
    rewrite ulp_neq_0; last by clear -Hlo Hu0 Hu1024; lra.
    rewrite /Generic_fmt.cexp /FLX_exp u_pow.
    have Hm : (mag beta e0 = 0 :> Z)%Z.
      apply: (mag_unique_pos beta e0 0); split; last by rewrite -E1.
      have -> : (0 - 1 = -1)%Z by lia.
      have E2 : pow (-1) = /2 by [].
      by rewrite E2; clear -Hlo Hu0 Hu1024; lra.
    by rewrite Hm; congr bpow; lia.
  exfalso; rewrite Hulpe in Ht.
  have Hu2 : u * u <= /1024 * u by nra.
  by clear -Ht Habs Hpred Hu0 Hu1024 Hu2 Hcu2; split_Rabs; nra.
(* [e0 > 1]: then [e0 >= succ 1 = 1 + 2u], which the [2u] window above (in    *)
(* fact [1.93u], once [|e0| <= 1.01] is used) already excludes.               *)
have H := @succ_le_lt beta fexp _ 1 e0 format_1 Fe0 Hgt.
have H2 := H (FLX_exp_valid p).
move: H2; rewrite succ_eq_pos ?Hu1; last by lra.
move=> Hsucc; exfalso.
have {}Hsucc := Hsucc p_gt_0.
have Hu2 : u * u <= /1024 * u by nra.
by clear -Hd Hae Hsucc Hu0 Hu1024 Hu2 Hcu2 Hgt; split_Rabs; nra.
Qed.

(* Algorithm 13's instance, the one Theorems 9 and 10 use.                    *)
Lemma head_eq_1 e0 v :
  format e0 -> Rabs (v - e0) <= / 2 * ulp e0 + 200 * (u * u) ->
  Rabs (v - 1) <= 36 * (u * u) -> e0 = 1.
Proof.
apply: head_eq_1_c.
have Hu0 : 0 < u by apply: u_gt_0.
by have := u_le_1024; lra.
Qed.

(* ===========================================================================*)
(*  Section 8.3 -- the head limb of [3Prod_{2,3}(b, x)] is [1]                *)
(*                                                                            *)
(*  Old paper Section 8.3: [|e - 1| <= 35u^2] and [e] F-nonoverlapping give   *)
(*  [|e0 - e| <= (1 - 2^-4) uls(e0)], so [|e0| >= 1 + 2u] would force         *)
(*  [|e| >= 1 + 2^-3 u > 1 + 35u^2] -- excluded when [u < 1/280], i.e.        *)
(*  [p >= 9].  This is Remark 9's precision constraint.  The step needs       *)
(*  material internal to ThreeProdDW.v / ThreeProdDWFast.v -- a [uls]-based   *)
(*  bound on the tail of the product's limbs, sharper than the [ulp] one      *)
(*  [isTW] provides -- and it lives there, as [ThreeProdDW_head_gap] and its  *)
(*  [Fast] twin.  What follows here is only the transfer to the call site.    *)
(* ===========================================================================*)
(* THE INTERFACE, normalised (proved in ThreeProdDW.v as                      *)
(* [ThreeProdDW_head_gap_norm]): the leading limb of [3Prod_{2,3}(x, y)] is   *)
(* within HALF AN ULP (of itself) plus [O(u^2)] of the exact product.  The    *)
(* half-ulp is [vecSum_head_gap] on the algorithm's inner VecSum -- its two   *)
(* leading limbs are the two words of one 2Sum -- and the [O(u^2)] is the     *)
(* accumulated rounding error of the FOUR remaining entries, which are all    *)
(* [O(u)] there.  It is exactly [head_eq_1]'s hypothesis.                     *)

(* The scale/sign transfer of a head gap.  The product, the head limb and     *)
(* the [ulp] all scale by the same power of two, so the ABSOLUTE [60u^2] of   *)
(* the normalised statement becomes a RELATIVE [70u^2]; the normalised        *)
(* product bound [xy_ge] ([>= 1 - 4u]) is what converts one into the other.   *)
Lemma head_gap_scale V E c :
  1 - 4 * u <= Rabs V * pow c ->
  Rabs (V * pow c - E * pow c) <= / 2 * ulp (E * pow c) + 60 * (u * u) ->
  Rabs (V - E) <= / 2 * ulp E + 70 * (u * u) * Rabs V.
Proof.
move=> Hlo Hgap.
have Hpc : 0 < pow c by apply: bpow_gt_0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have HV := Rabs_pos V.
move: Hgap; rewrite ulp_FLX_exact_shift.
have -> : V * pow c - E * pow c = (V - E) * pow c by ring.
rewrite Rabs_mult (Rabs_pos_eq (pow c)); last by lra.
move=> Hgap.
have Hkey : 60 * (u * u) <= 70 * (u * u) * Rabs V * pow c by nra.
by apply: (Rmult_le_reg_r (pow c)) => //; nra.
Qed.

(* The interface in the general (unnormalised, signed) case, GENERIC in the   *)
(* multiplier: all a variant has to supply is the three algebraic laws its    *)
(* scale/sign WLOG already needs and its own normalised head gap.  The four   *)
(* sign combinations then reduce to the same algebra -- the product, the head *)
(* limb and the [ulp] each pick up the same power of two and at most a sign.  *)
Lemma head_gap_gen (mul : twR -> twR -> twR) :
  (forall a b X Y, mul (scaleTW a X) (scaleTW b Y) = scaleTW (a + b) (mul X Y))
  -> (forall X Y, mul (negTW X) Y = negTW (mul X Y))
  -> (forall X Y, mul X (negTW Y) = negTW (mul X Y))
  -> (forall X Y, dw_normP p X -> tw_normP p Y ->
        Rabs (TWval X * TWval Y - tw0 (mul X Y))
          <= / 2 * ulp (tw0 (mul X Y)) + 60 * (u * u))
  -> forall x y, isDW x -> isTW y -> tw0 x <> 0 -> tw0 y <> 0 ->
       Rabs (TWval x * TWval y - tw0 (mul x y))
         <= / 2 * ulp (tw0 (mul x y))
            + 70 * (u * u) * Rabs (TWval x * TWval y).
Proof.
move=> Hscale Hopp Hopp_r Hnormgap x y Hx Hy Hx0 Hy0.
have [cx _ [Hxp Hxn]] := @isDW_normalize p Hp2 choice x Hx Hx0.
have [cy _ [Hyp Hyn]] := @isTW_normalize p Hp2 choice y Hy Hy0.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
apply: (head_gap_scale (c := (cx + cy)%Z)).
  (* the normalised product is [>= 1 - 4u], whatever the signs ([xy_ge]).     *)
  have Hnorm : forall X Y, dw_normP p X -> tw_normP p Y ->
      1 - 4 * u <= Rabs (TWval X * TWval Y).
    move=> X Y; case: X => x0 x1 x2 [Nxd ->]; case: Y => y0 y1 y2 NY.
    have Nx' : tw_norm x0 x1 0 by exact: dw_norm_tw_norm Nxd.
    have Ny' : tw_norm y0 y1 y2 by exact: NY.
    by have := @xy_ge p Hp2 Hp6 x0 x1 0 y0 y1 y2 Nx' Ny'; rewrite /TWval.
  have Habs2 : forall a b : R,
      Rabs (a * pow cx * (b * pow cy)) = Rabs (a * b) * pow (cx + cy).
    move=> a b; rewrite bpow_plus.
    have -> : a * pow cx * (b * pow cy) = (a * b) * (pow cx * pow cy) by ring.
    rewrite Rabs_mult [Rabs (pow cx * pow cy)]Rabs_pos_eq //.
    by apply: Rmult_le_pos; apply: bpow_ge_0.
  case: Hxsg => Hxs; case: Hysg => Hys.
  - by have := Hnorm _ _ (Hxp Hxs) (Hyp Hys); rewrite !TWval_scale Habs2.
  - have := Hnorm _ _ (Hxp Hxs) (Hyn Hys);
      rewrite !TWval_scale !TWval_opp Habs2.
    have -> : TWval x * - TWval y = -(TWval x * TWval y) by ring.
    by rewrite Rabs_Ropp.
  - have := Hnorm _ _ (Hxn Hxs) (Hyp Hys);
      rewrite !TWval_scale !TWval_opp Habs2.
    have -> : - TWval x * TWval y = -(TWval x * TWval y) by ring.
    by rewrite Rabs_Ropp.
  have := Hnorm _ _ (Hxn Hxs) (Hyn Hys); rewrite !TWval_scale !TWval_opp Habs2.
  by have -> : - TWval x * - TWval y = TWval x * TWval y by ring.
have Hprod : forall a b : R, a * pow cx * (b * pow cy) = a * b * pow (cx + cy).
  by move=> a b; rewrite bpow_plus; ring.
case: Hxsg => Hxs; case: Hysg => Hys.
- have Hn := Hnormgap _ _ (Hxp Hxs) (Hyp Hys).
  by rewrite Hscale !TWval_scale tw0_scale Hprod in Hn.
- have Hn := Hnormgap _ _ (Hxp Hxs) (Hyn Hys).
  rewrite Hscale Hopp_r !TWval_scale !TWval_opp tw0_scale tw0_opp Hprod in Hn.
  move: Hn.
  have -> : - tw0 (mul x y) * pow (cx + cy)
          = -(tw0 (mul x y) * pow (cx + cy)) by ring.
  rewrite ulp_opp.
  have -> : TWval x * - TWval y * pow (cx + cy)
          - - (tw0 (mul x y) * pow (cx + cy))
          = -(TWval x * TWval y * pow (cx + cy)
              - tw0 (mul x y) * pow (cx + cy)) by ring.
  by rewrite Rabs_Ropp.
- have Hn := Hnormgap _ _ (Hxn Hxs) (Hyp Hys).
  rewrite Hscale Hopp !TWval_scale !TWval_opp tw0_scale tw0_opp Hprod in Hn.
  move: Hn.
  have -> : - tw0 (mul x y) * pow (cx + cy)
          = -(tw0 (mul x y) * pow (cx + cy)) by ring.
  rewrite ulp_opp.
  have -> : - TWval x * TWval y * pow (cx + cy)
          - - (tw0 (mul x y) * pow (cx + cy))
          = -(TWval x * TWval y * pow (cx + cy)
              - tw0 (mul x y) * pow (cx + cy)) by ring.
  by rewrite Rabs_Ropp.
have Hn := Hnormgap _ _ (Hxn Hxs) (Hyn Hys).
have Hxy : mul (negTW x) (negTW y) = mul x y
  by rewrite Hopp Hopp_r negTW_id.
rewrite Hscale Hxy !TWval_scale !TWval_opp tw0_scale Hprod in Hn.
move: Hn.
by have -> : - TWval x * - TWval y = TWval x * TWval y by ring.
Qed.

(* The last step, also generic: a multiplier that returns a triple word and   *)
(* has the head gap above satisfies [head_one].  The relative [70u^2] turns   *)
(* absolute here, because the product is within [35u^2] of [1].               *)
(* Same, with the tolerance a parameter -- what Algorithm 15 needs, since it  *)
(* arrives at [~162u^2] rather than [35u^2].  See [head_eq_1_c].              *)
Lemma head_one_gen_c c (mul : twR -> twR -> twR) :
  c * u <= / 4 ->
  (forall x y, isDW x -> isTW y -> isTW (mul x y)) ->
  (forall x y, isDW x -> isTW y -> tw0 x <> 0 -> tw0 y <> 0 ->
     Rabs (TWval x * TWval y - tw0 (mul x y))
       <= / 2 * ulp (tw0 (mul x y)) + 70 * (u * u) * Rabs (TWval x * TWval y)) ->
  forall b y, isDW b -> isTW y ->
    Rabs (TWval b * TWval y - 1) <= c * (u * u) -> tw0 (mul b y) = 1.
Proof.
move=> Hc HisTW Hgapgen b y Hb Hy Hprod.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hcu2 : c * (u * u) <= / 4 * u by nra.
(* A zero leading limb makes the whole factor zero, and [|0 - 1| = 1].        *)
have Hb0 : tw0 b <> 0.
  move=> H0.
  have Hz := @isTW_zero_lead p Hp2 b (isDW_isTW Hb) H0.
  move: Hprod; rewrite Hz.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  rewrite Rmult_0_l.
  have -> : (0 - 1) = -1 by ring.
  rewrite Rabs_Ropp Rabs_R1.
  by clear -Hu0 Hu1024 Hcu2; nra.
have Hy0 : tw0 y <> 0.
  move=> H0.
  have Hz := @isTW_zero_lead p Hp2 y Hy H0.
  move: Hprod; rewrite Hz.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  rewrite Rmult_0_r.
  have -> : (0 - 1) = -1 by ring.
  rewrite Rabs_Ropp Rabs_R1.
  by clear -Hu0 Hu1024 Hcu2; nra.
have Hgap := Hgapgen _ _ Hb Hy Hb0 Hy0.
have Fe0 : format (tw0 (mul b y)).
  have HTW := HisTW _ _ Hb Hy.
  by case: (mul b y) HTW => e0 e1 e2 [].
apply: (@head_eq_1_c c (tw0 (mul b y)) (TWval b * TWval y)) => //.
(* the relative [70u^2] becomes absolute: the product is within [c u^2] of    *)
(* [1], so its magnitude is at most [1 + c u^2].                              *)
have Hv : Rabs (TWval b * TWval y) <= 1 + c * (u * u).
  have := Rabs_triang_inv (TWval b * TWval y) 1.
  by rewrite Rabs_R1; clear -Hprod; lra.
have Hu2 : u * u <= /1024 * u by nra.
have Hup := Rabs_pos (TWval b * TWval y).
by clear -Hgap Hv Hu0 Hu1024 Hu2 Hcu2 Hup; nra.
Qed.

(* Algorithm 13's instance, at [35u^2].                                       *)
Lemma head_one_gen (mul : twR -> twR -> twR) :
  (forall x y, isDW x -> isTW y -> isTW (mul x y)) ->
  (forall x y, isDW x -> isTW y -> tw0 x <> 0 -> tw0 y <> 0 ->
     Rabs (TWval x * TWval y - tw0 (mul x y))
       <= / 2 * ulp (tw0 (mul x y)) + 70 * (u * u) * Rabs (TWval x * TWval y))
  -> head_one mul.
Proof.
move=> HisTW Hgapgen b y Hb Hy Hprod.
apply: (@head_one_gen_c 35 mul) => //.
have Hu0 : 0 < u by apply: u_gt_0.
by have := u_le_1024; lra.
Qed.


(* Algorithm 11: the two generic steps, instantiated.                         *)
Lemma ThreeProdDW_head_gap x y :
  ties_to_even choice -> isDW x -> isTW y -> tw0 x <> 0 -> tw0 y <> 0 ->
  Rabs (TWval x * TWval y - tw0 (ThreeProdDW x y))
    <= / 2 * ulp (tw0 (ThreeProdDW x y))
       + 70 * (u * u) * Rabs (TWval x * TWval y).
Proof.
move=> Hc; apply: head_gap_gen.
- exact: (@ThreeProdDW_scale p Hp2 choice).
- exact: (@ThreeProdDW_opp p Hp2 choice choice_sym).
- exact: (@ThreeProdDW_opp_r p Hp2 choice choice_sym).
by move=> X Y NX NY;
   apply: (@ThreeProdDW_head_gap_norm p Hp2 Hp6 choice choice_sym).
Qed.

Lemma ThreeProdDW_head_one :
  ties_to_even choice -> head_one ThreeProdDW.
Proof.
move=> Hc; apply: head_one_gen.
  by move=> X Y HX HY; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
by move=> X Y HX HY HX0 HY0; apply: ThreeProdDW_head_gap.
Qed.

(* Algorithm 12: the same two steps, at its own multiplier.                   *)
Lemma ThreeProdDWFast_head_gap x y :
  ties_to_even choice -> isDW x -> isTW y -> tw0 x <> 0 -> tw0 y <> 0 ->
  Rabs (TWval x * TWval y - tw0 (ThreeProdDWFast x y))
    <= / 2 * ulp (tw0 (ThreeProdDWFast x y))
       + 70 * (u * u) * Rabs (TWval x * TWval y).
Proof.
move=> Hc; apply: head_gap_gen.
- exact: (@ThreeProdDWFast_scale p Hp2 choice).
- exact: (@ThreeProdDWFast_opp p Hp2 choice choice_sym).
- exact: (@ThreeProdDWFast_opp_r p Hp2 choice choice_sym).
by move=> X Y NX NY;
   apply: (@ThreeProdDWFast_head_gap_norm p Hp2 Hp6 choice choice_sym).
Qed.

Lemma ThreeProdDWFast_head_one :
  ties_to_even choice -> head_one ThreeProdDWFast.
Proof.
move=> Hc; apply: head_one_gen.
  by move=> X Y HX HY;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
by move=> X Y HX HY HX0 HY0; apply: ThreeProdDWFast_head_gap.
Qed.

Lemma ThreeReci_isTW x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 -> isTW (ThreeReci x).
Proof.
move=> Hc Hx Hx0.
apply: (@ThreeReciAux_isTW ThreeProdDW ThreeProdOne) => //.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> b y Hb Hy Hy0;
     apply: (@ThreeProdOne_isTW p Hp2 Hp6 choice choice_sym).
exact: ThreeProdDW_head_one.
Qed.

Lemma ThreeReciFast_isTW x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 -> isTW (ThreeReciFast x).
Proof.
move=> Hc Hx Hx0.
apply: (@ThreeReciAux_isTW ThreeProdDWFast ThreeProdOne) => //.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> b y Hb Hy Hy0;
     apply: (@ThreeProdOne_isTW p Hp2 Hp6 choice choice_sym).
exact: ThreeProdDWFast_head_one.
Qed.

(* ===========================================================================*)
(*  Correctness, part 2: the relative error (paper Theorem 9).                *)
(*                                                                            *)
(*  Old paper Section 8.2, with [d1] the relative error of the FIRST product  *)
(*  (on general arguments -- Theorem 8, resp. Algorithm 12, as a black box)   *)
(*  and [d2] that of the SECOND one, whose second argument [i] has head [1]:  *)
(*                                                                            *)
(*    |y - 1/x| <= (d1 (1 + 71u^2) + d2 (1 + 80u^2) + 1165u^4) |1/x|          *)
(*                                                                            *)
(*  The three terms are, in order: the error of [i = 2 - 3Prod(b, x)] carried *)
(*  through the multiplication by [b]; the error of [y = 3Prod(b, i)]; and    *)
(*  the QUADRATIC Newton residue [|x| (b - 1/x)^2], which [reciBW_x_err]      *)
(*  ([|b x - 1| <= 34u^2 + 123u^3]) makes [<= 1165u^4 |1/x|].  Everything     *)
(*  here is generic in the multiplier: the two algorithms differ only in the  *)
(*  two numbers [d1] and [d2].  Whence [11.5 = 10.5 + 1] and [19 = 18 + 1].   *)
(* ===========================================================================*)

(* What the SECOND product needs, and all it needs: a sharper relative error  *)
(* for a second argument whose head is [1] and whose total is within [40u^2]  *)
(* of [1].  Nearly every error source of Theorem 8 collapses there (with      *)
(* [y0 = 1] the products [x0 y0] and [x1 y0] are EXACT and [x1 y1] is         *)
(* [O(u^3)]), which is why [d2] is one [u^3] against Theorem 8's [10.5u^3].   *)
(* The paper hides this bound inside its Algorithm 18.                        *)
Definition sharp_error (mul : twR -> twR -> twR) (d2 : R) : Prop :=
  forall b i, isDW b -> isTW i -> tw0 i = 1 ->
    Rabs (TWval i - 1) <= 40 * (u * u) ->
    Rabs (TWval (mul b i) - TWval b * TWval i)
      <= d2 * Rabs (TWval b * TWval i).

(* The Newton residue is QUADRATIC: [(b x - 1)^2 <= 1165u^4] from             *)
(* [reciBW_x_err].  The squaring leaves [1156u^4 + 8364u^5 + 15129u^6], and   *)
(* at [u <= 1/1024] that is [<= 1164.2u^4]: the [1156 -> 1165] step is all    *)
(* the room there is.  It is also all the room Theorem 9 has, since its       *)
(* [1465u^4] is [1165 (residue) + 39 (d1) + 260 (d2)] and nothing else.       *)
Lemma newton_sq_le t :
  Rabs t <= 34 * (u * u) + 123 * (u * u * u) ->
  t ^ 2 <= 1165 * (u * u * u * u).
Proof.
move=> Ht.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hp := Rabs_pos t.
have Hsq : Rabs t * Rabs t = t ^ 2.
  by rewrite -Rabs_mult Rabs_pos_eq; [ring | apply: Rle_0_sqr].
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
have Hu4 : u * u * u * u <= /1024 * (u * u * u) by nra.
by rewrite -Hsq; nra.
Qed.

(* The final arithmetic of Theorem 9, on the bare quantities: [a = |b x|],    *)
(* [c = |i|], [R0 = |1/x|] and the three error terms.  Kept apart so that the *)
(* assembly below never has to run [nra] in a large context.                  *)
Lemma reci_error_assembly a c R0 e1 e2 e3 dd1 dd2 :
  0 <= a -> a <= 1 + 35 * (u * u) ->
  0 <= c -> c <= 1 + 40 * (u * u) ->
  0 <= R0 -> 0 <= dd1 -> 0 <= dd2 ->
  e1 <= dd2 * (a * R0 * c) ->
  e2 <= a * R0 * (dd1 * a) ->
  e3 <= 1165 * (u * u * u * u) * R0 ->
  e1 + e2 + e3
    <= (dd1 * (1 + 71 * (u * u)) + dd2 * (1 + 80 * (u * u))
        + 1165 * (u * u * u * u)) * R0.
Proof.
move=> Ha0 Ha1 Hc0 Hc1 HR0 Hd10 Hd20 H1 H2 H3.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu2 : u * u <= /1024 * u by nra.
have Hac : a * c <= 1 + 80 * (u * u) by nra.
have Haa : a * a <= 1 + 71 * (u * u) by nra.
have Hd2R : 0 <= dd2 * R0 by nra.
have Hd1R : 0 <= dd1 * R0 by nra.
have K1 : dd2 * (a * R0 * c) <= dd2 * (1 + 80 * (u * u)) * R0.
  have -> : dd2 * (a * R0 * c) = (dd2 * R0) * (a * c) by ring.
  have -> : dd2 * (1 + 80 * (u * u)) * R0 = (dd2 * R0) * (1 + 80 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l.
have K2 : a * R0 * (dd1 * a) <= dd1 * (1 + 71 * (u * u)) * R0.
  have -> : a * R0 * (dd1 * a) = (dd1 * R0) * (a * a) by ring.
  have -> : dd1 * (1 + 71 * (u * u)) * R0 = (dd1 * R0) * (1 + 71 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l.
by nra.
Qed.

(* [i = 2 - 3Prod(b, x)] is within [40u^2] of [1] -- which is exactly what    *)
(* the sharp bound asks of its second argument.  Factored out of the assembly *)
(* below because Algorithm 14 needs the very same step ([doc/thm10.md], step  *)
(* 2): it is pure arithmetic on [|b x - 1| <= 35u^2] and the multiplier's own *)
(* relative error.                                                            *)
Lemma sub2_near_one B X P d1 :
  Rabs (B * X - 1) <= 35 * (u * u) ->
  Rabs (P - B * X) <= d1 * Rabs (B * X) ->
  0 <= d1 -> d1 <= u * u ->
  Rabs (2 - P - 1) <= 40 * (u * u).
Proof.
move=> H35 HP Hd10 Hd1u.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu2 : u * u <= / 1024 * u by nra.
have HBXub : Rabs (B * X) <= 1 + 35 * (u * u).
  by have := Rabs_triang_inv (B * X) 1; rewrite Rabs_R1; lra.
have Hpos := Rabs_pos (B * X).
have Hd : d1 * Rabs (B * X) <= u * u * (1 + 35 * (u * u)).
  by apply: Rmult_le_compat; lra.
have T := Rabs_triang (1 - B * X) (B * X - P).
have Hm : Rabs (1 - B * X) = Rabs (B * X - 1) by rewrite Rabs_minus_sym.
have Hm2 : Rabs (B * X - P) = Rabs (P - B * X) by rewrite Rabs_minus_sym.
have E : 2 - P - 1 = (1 - B * X) + (B * X - P) by ring.
by rewrite E; nra.
Qed.

(* THE ASSEMBLY, generic in the multiplier.  [d1] is the multiplier's own     *)
(* relative error, [d2] its sharp one; both are asked to be [<= u], which is  *)
(* far more than true ([O(u^3)]) and keeps the final arithmetic honest.       *)
Lemma ThreeReciAux_error mul1 mul2 d1 d2 :
  ties_to_even choice ->
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  head_one mul1 ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  sharp_error mul2 d2 ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  forall x, isTW x -> tw0 x <> 0 ->
    Rabs (TWval (ThreeReciAux mul1 mul2 x) - / TWval x)
      <= (d1 * (1 + 71 * (u * u)) + d2 * (1 + 80 * (u * u))
          + 1165 * (u * u * u * u)) * Rabs (/ TWval x).
Proof.
move=> Hc Hmul Hhead Herr Hsharp Hd10 Hd1u Hd20 Hd2u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1 : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
set b := reciBW (tw0 x) (tw1 x).
have HDW : isDW b by apply: reciB_isDW.
have HBX := reciBW_x_err Hx Hx0.
set B := TWval b in HBX *.
set X := TWval x in HBX *.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
have HBX35 : Rabs (B * X - 1) <= 35 * (u * u)
  by clear -HBX Hu0 Hu1024 Hu3; nra.
(* [x] itself cannot vanish: [b x] is within [35u^2] of [1].                  *)
have HX0 : X <> 0.
  move=> HX; move: HBX35; rewrite HX Rmult_0_r.
  have -> : (0 - 1) = -1 by ring.
  by rewrite Rabs_Ropp Rabs_R1; clear -Hu0 Hu1024; nra.
have Hprod1 : isTW (mul1 b x) by apply: Hmul.
have Hhead1 : tw0 (mul1 b x) = 1 by apply: Hhead.
set P := TWval (mul1 b x) in Hhead1 *.
have HP : Rabs (P - B * X) <= d1 * Rabs (B * X) by apply: Herr.
set i := sub2TW (mul1 b x).
have Hi : isTW i by apply: sub2TW_isTW.
have Hi0 : tw0 i = 1 by rewrite /i; case: (mul1 b x) Hhead1 => t0 t1 t2 /= ->;
  ring.
have HIval : TWval i = 2 - P by rewrite /i TWval_sub2TW.
have HBXub : Rabs (B * X) <= 1 + 35 * (u * u).
  have := Rabs_triang_inv (B * X) 1.
  by rewrite Rabs_R1; clear -HBX35; lra.
(* [i = 2 - 3Prod(b, x)] is within [40u^2] of [1], which is what the sharp    *)
(* bound asks of its second argument.                                         *)
have HI1 : Rabs (TWval i - 1) <= 40 * (u * u)
  by rewrite HIval; apply: (sub2_near_one HBX35 HP Hd10 Hd1u).
have Hy := Hsharp _ _ HDW Hi Hi0 HI1.
set Y := TWval (mul2 b i) in Hy *.
set I := TWval i in Hy HI1 HIval *.
rewrite -/B in Hy.
have HIub : Rabs I <= 1 + 40 * (u * u).
  by have := Rabs_triang_inv I 1; rewrite Rabs_R1; lra.
have HBabs : Rabs B = Rabs (B * X) * Rabs (/ X).
  by rewrite -Rabs_mult; congr Rabs; field.
have HR0 := Rabs_pos (/ X).
(* The Newton step: [b (2 - x b) - 1/x] is MINUS the square of [b x - 1].     *)
have Hnewton : B * (2 - X * B) - / X = - (B * X - 1) ^ 2 * / X.
  have H := newton_id B X.
  have -> : B * (2 - X * B) - / X = ((B * (2 - X * B)) * X - 1) * / X by field.
  by rewrite H.
(* ... so the total error splits into the second product's, the first one's   *)
(* carried through [b], and that quadratic residue.                           *)
have Hdecomp : Y - / X
    = (Y - B * I) + B * (X * B - P) + (B * (2 - X * B) - / X).
  by rewrite HIval; ring.
have T1 := Rabs_triang ((Y - B * I) + B * (X * B - P)) (B * (2 - X * B) - / X).
have T2 := Rabs_triang (Y - B * I) (B * (X * B - P)).
have E1 : Rabs (B * I) = Rabs (B * X) * Rabs (/ X) * Rabs I
  by rewrite Rabs_mult HBabs.
have E2 : Rabs (B * (X * B - P)) = Rabs (B * X) * Rabs (/ X) * Rabs (P - B * X).
  rewrite Rabs_mult HBabs; congr (_ * _).
  by rewrite -Rabs_Ropp; congr Rabs; ring.
have E3 : Rabs (B * (2 - X * B) - / X) = (B * X - 1) ^ 2 * Rabs (/ X).
  rewrite Hnewton Rabs_mult -Rabs_Ropp Ropp_involutive.
  by congr (_ * _); apply: Rabs_pos_eq; apply: pow2_ge_0.
have Hsq := newton_sq_le HBX.
have Hab := Rabs_pos (B * X).
have Hai := Rabs_pos I.
have Step1 : Rabs (Y - B * I) <= d2 * (Rabs (B * X) * Rabs (/ X) * Rabs I)
  by rewrite E1 in Hy.
have Step2 : Rabs (B * (X * B - P))
    <= Rabs (B * X) * Rabs (/ X) * (d1 * Rabs (B * X)).
  rewrite E2; apply: Rmult_le_compat_l; last by exact: HP.
  by apply: Rmult_le_pos.
have Step3 : Rabs (B * (2 - X * B) - / X)
    <= 1165 * (u * u * u * u) * Rabs (/ X).
  by rewrite E3; apply: Rmult_le_compat_r.
rewrite Hdecomp.
apply: Rle_trans T1 _.
have T3 : Rabs (Y - B * I + B * (X * B - P)) + Rabs (B * (2 - X * B) - / X)
    <= Rabs (Y - B * I) + Rabs (B * (X * B - P))
       + Rabs (B * (2 - X * B) - / X) by lra.
apply: Rle_trans T3 _.
by apply: (@reci_error_assembly (Rabs (B * X)) (Rabs I) (Rabs (/ X))).
Qed.

(* The sharp bound is Algorithm 18's, and it serves BOTH variants -- they     *)
(* differ only in their first product.  [ThreeProdOne_error] gives            *)
(* [u^3 + 620u^4].  The paper claims [260u^4] here; see ThreeProdOne.v for    *)
(* why the honest constant is bigger, and why only the [u^4] term moves.      *)
Lemma ThreeProdOne_sharp :
  ties_to_even choice ->
  sharp_error ThreeProdOne (u * u * u + 620 * (u * u * u * u)).
Proof.
move=> Hc b i Hb Hi Hi0 Hi1.
apply: Rle_trans
  (@ThreeProdOne_error p Hp2 Hp6 choice choice_sym b i Hc Hb Hi Hi0 Hi1) _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
have Hu0 : 0 < u by apply: u_gt_0.
by nra.
Qed.

(* Theorem 9, accurate variant.  The paper states [11.5u^3 + 1465u^4]; the    *)
(* [u^3] is exactly its, the [u^4] is ours (see [ThreeProdOne_sharp]).        *)
Lemma ThreeReci_error x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeReci x) - / TWval x) <=
     (115 / 10 * (u * u * u) + 1830 * (u * u * u * u)) *
       Rabs (/ TWval x).
Proof.
move=> Hc Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
have Hu4 : u * u * u * u <= /1024 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= /1024 * (u * u * u * u) by nra.
have Hd0 : 0 <= 105 / 10 * (u * u * u) + 39 * (u * u * u * u) by nra.
have Hdu : 105 / 10 * (u * u * u) + 39 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= u * u * u + 620 * (u * u * u * u) by nra.
have Heu : u * u * u + 620 * (u * u * u * u) <= u * u by nra.
have Hgen := @ThreeReciAux_error ThreeProdDW ThreeProdOne
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (u * u * u + 620 * (u * u * u * u)) Hc
  (fun b y Hb Hy => @ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (ThreeProdDW_head_one Hc)
  (fun b y Hb Hy => @ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (ThreeProdOne_sharp Hc)
  Hd0 Hdu He0 Heu x Hx Hx0.
rewrite /ThreeReci.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
by nra.
Qed.

(* Theorem 9, fast variant.  The paper states [19u^3 + 1502u^4].              *)
Lemma ThreeReciFast_error x :
  ties_to_even choice ->
  isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeReciFast x) - / TWval x) <=
     (19 * (u * u * u) + 1870 * (u * u * u * u)) *
       Rabs (/ TWval x).
Proof.
move=> Hc Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
have Hu4 : u * u * u * u <= /1024 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= /1024 * (u * u * u * u) by nra.
have Hd0 : 0 <= 18 * (u * u * u) + 75 * (u * u * u * u) by nra.
have Hdu : 18 * (u * u * u) + 75 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= u * u * u + 620 * (u * u * u * u) by nra.
have Heu : u * u * u + 620 * (u * u * u * u) <= u * u by nra.
have Hgen := @ThreeReciAux_error ThreeProdDWFast ThreeProdOne
  (18 * (u * u * u) + 75 * (u * u * u * u))
  (u * u * u + 620 * (u * u * u * u)) Hc
  (fun b y Hb Hy =>
     @ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (ThreeProdDWFast_head_one Hc)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (ThreeProdOne_sharp Hc)
  Hd0 Hdu He0 Heu x Hx Hx0.
rewrite /ThreeReciFast.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
by nra.
Qed.

End SecThreeReci.
