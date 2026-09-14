(* ---------------------------------------------------------------------------*)
(* Algorithm 10 (3Prod^fast_{3,3}): the FAST product of two triple-word       *)
(* numbers, and its two correctness results -- the result is a triple word    *)
(* ([ThreeProdFast_isTW]) and the relative error bound [44u^3 + 176u^4]       *)
(* ([ThreeProdFast_error]) -- paper doc/paper3.pdf, Section 6.4 (see          *)
(* doc/alg10.md).  Generic over the precision [p] (FLX, no [emin]); needs     *)
(* [p >= 6].                                                                  *)
(*                                                                            *)
(* Algorithm 10 is Algorithm 9 ([ThreeProd.v]) with the last 2Sum replaced by *)
(* a single rounding: [s3 = RN(c + z3)] is computed WITHOUT its error term    *)
(* [e4 = (c + z3) - s3], which is simply dropped.  That saves 8 operations    *)
(* and one test, at the price of one extra error source [|e4| <= 16u^3],      *)
(* whence [44u^3 = 28u^3 + 16u^3] instead of [28u^3].                         *)
(*                                                                            *)
(* STATUS: COMPLETE -- both theorems are PROVED, zero admits.  The definition *)
(* transcribes Algorithm 10 verbatim on top of [TwoProd] (Alg 3), [vecSum]    *)
(* (Alg 4) and [vsebK] (Alg 5), and both proofs re-instantiate the            *)
(* Algorithm-9 skeleton of [ThreeProd.v]:                                     *)
(*  - the head [VecSum(z00+, b0, b1, s3)] is LITERALLY Algorithm 9's inner    *)
(*    list, so [inner_head_Fnonoverlap] (the four-case [I]-set study) applies *)
(*    unchanged and no [e4] tail has to be handled;                           *)
(*  - every Section-6.1 term bound and the [eps0..eps5] error bounds are      *)
(*    reused as is, with the single extra source [eps4' = (c + z3) - s3].     *)
(* See doc/alg10.md.                                                          *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProdFast.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 10, like Algorithm 9, needs [p >= 6] (paper Section 6.4).        *)
Hypothesis Hp6 : (6 <= p)%Z.

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
Local Notation TwoSum := (TwoSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation isTW := (isTW p).

(* The paper's normalisation [1 <= x0, y0 < 2] and its triple-word packing,   *)
(* both from ThreeProd.v.                                                     *)
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

(* ===========================================================================*)
(*  Algorithm 10 -- 3Prod^fast_{3,3}(x, y)                                    *)
(*  (38 operations & 1 test; paper Section 6.4).                              *)
(*                                                                            *)
(*  The first five lines are those of Algorithm 9 ([ThreeProd]); then         *)
(*  [s3 = RN(c + z3)] replaces the 2Sum of Algorithm 9 -- its error term      *)
(*  [e4] is NOT computed -- and the final VecSum has four inputs instead of   *)
(*  five, so [(r1, r2) = VSEB(2)(e1, e2, e3)].                                *)
(*  The three [RN(_ + _ * _)] terms ([c], [z31], [z32]) are FMAs (a single    *)
(*  rounding).                                                                *)
(* ===========================================================================*)
Definition ThreeProdFast (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
  let: TWR y0 y1 y2 := y in
  let: (z00p, z00m) := TwoProd x0 y0 in
  let: (z01p, z01m) := TwoProd x0 y1 in
  let: (z10p, z10m) := TwoProd x1 y0 in
  let b := vecSum [:: z00m; z01p; z10p] in
  let b0 := nth 0 b 0 in
  let b1 := nth 0 b 1 in
  let b2 := nth 0 b 2 in
  let c   := RND (b2 + x1 * y1) in
  let z31 := RND (z10m + x0 * y2) in
  let z32 := RND (z01m + x2 * y0) in
  let z3  := RND (z31 + z32) in
  let s3  := RND (c + z3) in
  let e := vecSum [:: z00p; b0; b1; s3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* ===========================================================================*)
(*  The FLX WLOG for Algorithm 10 -- scale- and sign-equivariance and the     *)
(*  degenerate zero-factor cases, the twins of [ThreeProd_scale] /            *)
(*  [ThreeProd_opp] / [ThreeProd_opp_r] / [ThreeProd_0l] / [ThreeProd_0r].    *)
(*  Every generic ingredient ([round_scale], [vecSum_scale], [vsebK_scale],   *)
(*  [TwoProd_scale] and their [_opp] twins, [vsebAux_zeros], ...) is reused   *)
(*  from ThreeProd.v -- only these five wrappers are algorithm-specific.      *)
(* ===========================================================================*)
Lemma ThreeProdFast_scale a b x y :
  ThreeProdFast (scaleTW a x) (scaleTW b y) =
    scaleTW (a + b) (ThreeProdFast x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdFast /scaleTW.
have P1 : x1 * pow a * (y1 * pow b) = x1 * y1 * pow (a + b) by rewrite
  bpow_plus; ring.
have P2 : x0 * pow a * (y2 * pow b) = x0 * y2 * pow (a + b) by rewrite
  bpow_plus; ring.
have P3 : x2 * pow a * (y0 * pow b) = x2 * y0 * pow (a + b) by rewrite
  bpow_plus; ring.
rewrite !P1 !P2 !P3 !TwoProd_scale.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: w00m * pow (a+b); w01p * pow (a+b); w10p *
  pow (a+b)]) i = nth 0 (vecSum [:: w00m; w01p; w10p]) i * pow (a+b).
  move=> i.
  have -> : [:: w00m * pow (a+b); w01p * pow (a+b); w10p * pow (a+b)] = [seq z *
    pow (a+b) | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (t * pow (a+b) + x1 * y1 * pow (a+b)) = RND (t + x1
  * y1) * pow (a+b).
  move=> t.
  have -> : t * pow (a+b) + x1 * y1 * pow (a+b) = (t + x1 * y1) * pow (a+b) by
    ring.
  by rewrite round_scale.
have E5 : RND (RND (w10m * pow (a+b) + x0 * y2 * pow (a+b)) + RND (w01m * pow
  (a+b) + x2 * y0 * pow (a+b))) = RND (RND (w10m + x0 * y2) + RND (w01m + x2 *
  y0)) * pow (a+b).
  have -> : w10m * pow (a+b) + x0 * y2 * pow (a+b) = (w10m + x0 * y2) * pow
    (a+b) by ring.
  have -> : w01m * pow (a+b) + x2 * y0 * pow (a+b) = (w01m + x2 * y0) * pow
    (a+b) by ring.
  rewrite !round_scale.
  have -> : RND (w10m + x0 * y2) * pow (a+b) + RND (w01m + x2 * y0) * pow (a+b)
    = (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b) by ring.
  by rewrite round_scale.
rewrite !E4 !E5.
(* The extra line of Algorithm 10: [s3 = RN(c + z3)] scales as well.          *)
have E6 : RND (RND (nth 0 bb 2 + x1 * y1) * pow (a+b)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b))
        = RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b).
  have -> : RND (nth 0 bb 2 + x1 * y1) * pow (a+b)
          + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b)
          = (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b) by
    ring.
  by rewrite round_scale.
rewrite !E6.
have Ee : forall i, nth 0 (vecSum [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b);
  nth 0 bb 1 * pow (a+b); RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b)]) i
  = nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i * pow (a+b).
  move=> i.
  have -> : [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b); nth 0 bb 1 * pow
    (a+b); RND (RND (nth 0 bb 2 + x1 * y1)
       + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) * pow (a+b)]
    = [seq z * pow (a+b) | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))].
have Ev : vsebK 2 [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3
  * pow (a+b)] = [seq z * pow (a+b) | z <- vsebK 2 [::
  nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]].
  have -> : [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3 * pow
    (a+b)] = [seq z * pow (a+b) | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]]
    by [].
  by rewrite vsebK_scale.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdFast_opp x y :
  ThreeProdFast (negTW x) y = negTW (ThreeProdFast x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdFast /negTW.
have P1 : (- x1) * y1 = - (x1 * y1) by ring.
have P2 : (- x0) * y2 = - (x0 * y2) by ring.
have P3 : (- x2) * y0 = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !(@TwoProd_opp_l p choice choice_sym).
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0
  (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite (@round_opp p choice choice_sym).
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND
  (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !(@round_opp p choice choice_sym).
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0
    * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E4 !E5.
(* The extra line of Algorithm 10: [s3 = RN(c + z3)] is odd as well.          *)
have E6 : RND (- RND (nth 0 bb 2 + x1 * y1)
             + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))
        = - RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))).
  have -> : - RND (nth 0 bb 2 + x1 * y1)
          + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))
          = - (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E6.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
  - RND (RND (nth 0 bb 2 + x1 * y1)
       + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i
  = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
    - RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]
    = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]] by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] =
  [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] = [seq -
    z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]] by [].
  by rewrite (@vsebK_opp p choice choice_sym).
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdFast_opp_r x y :
  ThreeProdFast x (negTW y) = negTW (ThreeProdFast x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdFast /negTW.
have P1 : x1 * (- y1) = - (x1 * y1) by ring.
have P2 : x0 * (- y2) = - (x0 * y2) by ring.
have P3 : x2 * (- y0) = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !(@TwoProd_opp_r p choice choice_sym).
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0
  (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite (@round_opp p choice choice_sym).
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND
  (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !(@round_opp p choice choice_sym).
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0
    * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E4 !E5.
have E6 : RND (- RND (nth 0 bb 2 + x1 * y1)
             + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))
        = - RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))).
  have -> : - RND (nth 0 bb 2 + x1 * y1)
          + - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))
          = - (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))) by ring.
  by rewrite (@round_opp p choice choice_sym).
rewrite !E6.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
  - RND (RND (nth 0 bb 2 + x1 * y1)
       + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i
  = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
    - RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]
    = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))]] by [].
  by rewrite (@vecSum_opp p choice choice_sym) nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] =
  [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3] = [seq -
    z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3]] by [].
  by rewrite (@vsebK_opp p choice choice_sym).
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdFast_0l y : ThreeProdFast (TWR 0 0 0) y = TWR 0 0 0.
Proof.
case: y => y0 y1 y2.
rewrite /ThreeProdFast !TwoProd00l /=.
rewrite !Rmult_0_l !Rplus_0_r !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0] = nseq 1.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

Lemma ThreeProdFast_0r x : ThreeProdFast x (TWR 0 0 0) = TWR 0 0 0.
Proof.
case: x => x0 x1 x2.
rewrite /ThreeProdFast !TwoProd00r /=.
rewrite !Rmult_0_r !Rplus_0_l !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0] = nseq 1.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

(* ===========================================================================*)
(*  The paper's star identity for Algorithm 10, [e1 = 0] half: the head of    *)
(*  [vseb e] is [e0] and the next two limbs are those of [vseb (behead e)].   *)
(*  The Algorithm-9 twin is [vseb_head3_e1zero]; here [e] has FOUR limbs      *)
(*  (the last one is [s3 = RN(c + z3)], no [e4]).                             *)
(* ===========================================================================*)
Lemma vsebFast_head3_e1zero x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))] in
  nth 0 e 1 = 0 ->
  nth 0 (vseb e) 0 = nth 0 e 0 /\
  nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
  nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
Proof.
move=> Hc Nx Ny bb e He1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hp4 : (4 <= p)%Z by lia.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
(* Section 6.1 term bounds -- reused verbatim from ThreeProd.v (Algorithm 10  *)
(* shares every term of Algorithm 9 up to [s3]).                              *)
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z10m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny.
have Hx2y0 := @x2y0_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny.
have Hx1y1 := @x1y1_bound p x0 x1 x2 y0 y1 y2 Nx Ny.
have Hz31 := @z31_bound p Hp2 Hp6 choice _ _ _ Hz10m2 Hx0y2.
have Hz32 := @z32_bound p Hp2 Hp6 choice _ _ _ Hz01m2 Hx2y0.
have Hz3 := @z3_bound p Hp2 Hp6 choice _ _ Hz31 Hz32.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Hz00m : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic;
    first by apply: (@z00m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0));
    last by ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01p := @z01p_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny.
have Hz10p := @z10p_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq;
     apply: (@b2_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Hc8 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 8 * (u * u)
  by apply: (@c_bound p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
have Fku : forall k : Z, (Z.abs k < 2 ^ p)%Z -> format (IZR k * u)
  by move=> k Hk; rewrite u_pow; apply: format_mult_pow.
have F8u : format (8 * u) by rewrite -pow_3mp; apply: format_pow.
have Hb0 : Rabs (nth 0 bb 0) <= 10 * u.
  have Heq : nth 0 bb 0
      = RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0))).
    by rewrite /bb vecSum_nth0 vecSumAux_run_cons; congr RND; congr (_ + _).
  rewrite Heq.
  have F10 : format (10 * u) by apply: Fku; have := @two_p_ge_64 p Hp6; simpl;
    lia.
  apply: Rabs_round_le_r => //.
  have Hin : Rabs (RND (RND (x0 * y1) + RND (x1 * y0))) <= 8 * u.
    apply: Rabs_round_le_r => //.
    by have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); lra.
  by have := Rabs_triang (RND (x0 * y0 - RND (x0 * y0)))
       (RND (RND (x0 * y1) + RND (x1 * y0))); lra.
have Flbb : {in [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)],
    forall z, format z}.
  by move=> z; rewrite !inE => /orP[/eqP->|/orP[/eqP->|/eqP->]];
     apply: generic_format_round.
have Hb1 : Rabs (nth 0 bb 1) <= 8 * (u * u).
  have Hle := @vecSum_err_le_half_ulp_run p Hp2 choice choice_sym
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] 0 isT Flbb.
  move: Hle; rewrite drop0.
  have -> : (vecSumAux [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
       RND (x1 * y0)]).2 = nth 0 bb 0 by rewrite /bb vecSum_nth0.
  have -> : nth 0 (vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
       RND (x1 * y0)]) 1 = nth 0 bb 1 by rewrite /bb.
  move=> Hle.
  have Hub : ulp (nth 0 bb 0) <= 16 * (u * u).
    rewrite -pow_4m2p; apply: bound_ulp_FLX; first exact: Hp2.
    have -> : (4 - 2 * p + p = 4 - p)%Z by lia.
    have -> : pow (4 - p) = 16 * u.
      rewrite (_ : (4 - p = (3 - p) + 1)%Z); last by lia.
      rewrite bpow_plus pow_3mp.
      have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
      ring.
    by have := Hb0; lra.
  lra.
have P16 : pow (4 - p) = 16 * u.
  rewrite (_ : (4 - p = (3 - p) + 1)%Z); last by lia.
  rewrite bpow_plus pow_3mp.
  have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
  ring.
have Hulp16 : forall z, Rabs z < 16 * u -> ulp z <= 16 * (u * u).
  move=> z Hz; rewrite -pow_4m2p; apply: bound_ulp_FLX; first exact: Hp2.
  by rewrite (_ : (4 - 2 * p + p = 4 - p)%Z) ?P16 //; lia.
have Hs3 : Rabs (RND (RND (nth 0 bb 2 + x1 * y1)
    + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) <= 20 * (u * u)
  by apply: (@s3_bound p Hp2 Hp6 choice _ _ Hc8 Hz3).
set c := RND (nth 0 bb 2 + x1 * y1).
set z3v := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
       + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)).
set s3 := RND (c + z3v).
(* The running sums of the four-limb VecSum: [|s3| <= 20u^2],                 *)
(* [|RN(b1 + s3)| <= 32u^2], [|RN(b0 + ...)| <= 11u].  One step shorter than  *)
(* Algorithm 9's, whose last two inputs are [c] and [z3].                     *)
have Hr3' : Rabs ((vecSumAux [:: s3]).2) <= 20 * (u * u) by exact: Hs3.
have Hr2 : Rabs ((vecSumAux [:: nth 0 bb 1; s3]).2) <= 32 * (u * u).
  rewrite vecSumAux_run_cons.
  have F32 : format (32 * (u * u))
    by apply: (@format_imul_u2 p Hp2 32); have := @two_p_ge_64 p Hp6; lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 1) ((vecSumAux [:: s3]).2).
  move: Hb1 Hr3' Ht; nra.
have Hr1 : Rabs ((vecSumAux [:: nth 0 bb 0; nth 0 bb 1; s3]).2) <= 11 * u.
  rewrite vecSumAux_run_cons.
  have F11 : format (11 * u) by apply: Fku; have := @two_p_ge_64 p Hp6; simpl;
    lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 0) ((vecSumAux [:: nth 0 bb 1; s3]).2).
  move: Hb0 Hr2 Ht Hu0 Hu64; nra.
have He0 : 3 / 4 <= nth 0 e 0.
  rewrite /e vecSum_nth0 vecSumAux_run_cons.
  have F34 : format (3 / 4).
    have -> : 3 / 4 = IZR 3 * pow (-2) by rewrite /= /Z.pow_pos /=; lra.
    by apply: format_mult_pow; have := @two_p_ge_64 p Hp6; simpl; lia.
  apply: round_le_l => //.
  have Hz00p1 : 1 <= RND (x0 * y0)
    by apply: (@z00p_lb p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite -/c -/z3v -/s3.
  set r1 := (vecSumAux [:: nth 0 bb 0; nth 0 bb 1; s3]).2.
  set z := RND (x0 * y0).
  move: Hr1 Hz00p1; rewrite -/r1 -/z => Hr1 Hz00p1.
  have Hr1c := Rabs_le_inv _ _ Hr1.
  lra.
have HL4f : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3],
    forall z, format z}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try exact: generic_format_round; exact: Fnthbb.
have Ee : e = vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3]
  by rewrite /e -/c -/z3v -/s3.
(* Every non-head limb is [< 1/2 u]: it is [<= 1/2 ulp] of a running sum      *)
(* smaller than [16u] ([vecSum_err_le_half_ulp_run] + [Hulp16]).              *)
have Hstep : forall k : nat, (k.+1 < 4)%N ->
    Rabs ((vecSumAux
      (drop k [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3])).2) < 16 * u ->
    2 * Rabs (nth 0 e k.+1) < u.
  move=> k Hk Hrk.
  have Hle := @vecSum_err_le_half_ulp_run p Hp2 choice choice_sym
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3] k Hk HL4f.
  rewrite -Ee in Hle.
  have Hw := Hulp16 _ Hrk.
  move: Hle Hw.
  set n := Rabs (nth 0 e k.+1).
  set w := ulp _.
  move=> Hle Hw.
  move: Hle Hw Hu64 Hu0; nra.
have Hdom : forall i, (0 < i)%N -> (i < 4)%N -> 2 * Rabs (nth 0 e i) < u.
  move=> i Hi0 Hi4.
  case: i Hi0 Hi4 => [|[|[|[|i]]]] // _ _.
  - by rewrite He1 Rabs_R0; nra.
  - apply: (Hstep 1%N) => //.
    have -> : drop 1 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3]
      = [:: nth 0 bb 0; nth 0 bb 1; s3] by [].
    by move: Hr1 Hu0; lra.
  - apply: (Hstep 2%N) => //.
    have -> : drop 2 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3]
      = [:: nth 0 bb 1; s3] by [].
    by move: Hr2 Hu0 Hu64; nra.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fe : {in e, forall z, format z}
  by rewrite Ee; apply: (@format_vecSum p Hp2 choice); exact: HL4f.
have He0e : e = nth 0 e 0 :: behead e by case: (e) Hsz4 => [|a l].
have Hbeh_dom : forall x, x \in behead e -> 2 * Rabs x < u.
  move=> x xI.
  have [i Hi Hnth] : exists2 i, (i < size (behead e))%N & nth 0 (behead e) i = x
    by apply/(nthP 0).
  have Hnth' : nth 0 (behead e) i = nth 0 e i.+1 by rewrite He0e /=.
  rewrite -Hnth Hnth'.
  have Hi4 : (i.+1 < 4)%N by move: Hi; rewrite size_behead Hsz4.
  case: i Hi Hnth Hnth' Hi4 => [|i'] Hi Hnth Hnth' Hi4.
    by rewrite He1 Rabs_R0; have := u_gt_0; move=> H; nra.
  by apply: Hdom.
by apply: vseb_head3_dom => //; rewrite Hsz4.
Qed.

(* ===========================================================================*)
(*  The head VecSum of Algorithm 10 is F-nonoverlapping.  It is LITERALLY     *)
(*  Algorithm 9's inner list, so this is [inner_head_Fnonoverlap] verbatim -- *)
(*  its [s3 = dwh (TwoSum c z3)] is [RN(c + z3)] by [TwoSum_hi].  Shared by   *)
(*  [ThreeProdFast_isTW_norm] and [ThreeProdFast_error_norm] (the analogue of *)
(*  Algorithm 9's [inner_Fnonoverlap], minus the [e4] tail).                  *)
(* ===========================================================================*)
Lemma innerF_Fnonoverlap x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Fnonoverlap (vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))]).
Proof.
move=> Hc Nx Ny bb.
have H := @inner_head_Fnonoverlap p Hp2 Hp6 choice choice_sym
  x0 x1 x2 y0 y1 y2 Hc Nx Ny.
have H2 : Fnonoverlap (vecSum
  [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      dwh (TwoSum (RND (nth 0 bb 2 + x1 * y1))
           (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
               + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))))]) by exact: H.
by rewrite TwoSum_hi in H2.
Qed.

(* ===========================================================================*)
(*  The star identity [(r0, VSEB(2)) = VSEB(3)] for Algorithm 10: the output  *)
(*  is the first three limbs of [vseb e], with [e = VecSum(z00+, b0, b1, s3)] *)
(*  the pre-truncation VecSum output.  [e1 <> 0] uses [vseb_star]             *)
(*  (structural, reused from ThreeProd.v), [e1 = 0] uses                      *)
(*  [vsebFast_head3_e1zero].                                                  *)
(* ===========================================================================*)
Lemma ThreeProdFast_norm_eq x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))] in
  ThreeProdFast (TWR x0 x1 x2) (TWR y0 y1 y2) =
    TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2).
Proof.
move=> Hc Nx' Ny'.
rewrite /ThreeProdFast /TwoProd.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
          + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))].
set el := [:: nth 0 e 1; nth 0 e 2; nth 0 e 3].
have Hmatch : match vsebK 2 el with
    | [::] => TWR (nth 0 e 0) 0 0
    | [:: r1] => TWR (nth 0 e 0) r1 0
    | [:: r1, r2 & _] => TWR (nth 0 e 0) r1 r2
    end = TWR (nth 0 e 0) (nth 0 (vseb el) 0) (nth 0 (vseb el) 1).
  by rewrite /vsebK; case: (vseb el) => [|r1 [|r2 rl]].
rewrite Hmatch.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Hbeh : el = behead e.
  have gen : forall s : seq R, size s = 4%N ->
      behead s = [:: nth 0 s 1; nth 0 s 2; nth 0 s 3].
    by move=> s; case: s => [|a[|b[|c[|d[|f r]]]]].
  by rewrite /el (gen e Hsz4).
have [H0 [H1 H2]] : nth 0 (vseb e) 0 = nth 0 e 0 /\
    nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
    nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
  case: (Req_dec (nth 0 e 1) 0) => [He1|He1].
    by apply: (vsebFast_head3_e1zero Hc Nx' Ny').
  have FL4 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
              + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))],
      forall z, format z}.
    move=> z; rewrite !inE.
    move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
      try apply: generic_format_round; apply: Fnthbb.
  have Hstar := @vseb_star p Hp2 choice choice_sym _ FL4 (isT : (1 < 4)%N) He1.
  have Hs : vseb e = nth 0 e 0 :: vseb (behead e) by exact: Hstar.
  rewrite Hs; split; [exact: erefl | split; exact: erefl].
by rewrite Hbeh H0 H1 H2.
Qed.

(* ===========================================================================*)
(*  Correctness, part 1, normalised (paper WLOG [1 <= x0, y0 < 2]).  The head *)
(*  VecSum is F-nonoverlapping -- and it is LITERALLY Algorithm 9's inner     *)
(*  list, so [inner_head_Fnonoverlap] applies verbatim (its [s3] is           *)
(*  [dwh (TwoSum c z3)], which is [RN(c + z3)] by [TwoSum_hi]) -- hence       *)
(*  [vseb e] is P-nonoverlapping (Theorem 2) and its first three limbs, which *)
(*  are the output by [ThreeProdFast_norm_eq], form a triple word.            *)
(* ===========================================================================*)
Lemma ThreeProdFast_isTW_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y -> isTW (ThreeProdFast x y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 Nx.
case: y Ny => y0 y1 y2 Ny.
have Nx' : tw_norm x0 x1 x2 by exact: Nx.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
rewrite (ThreeProdFast_norm_eq Hc Nx' Ny').
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
          + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))].
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Fe : {in e, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
have Fno : Fnonoverlap e
  by rewrite /e /bb; apply: (innerF_Fnonoverlap Hc Nx' Ny').
have Pno : Pnonoverlap (vseb e).
  have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
  by have [] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
apply: Pnonoverlap_isTW3; first exact: Pno.
by apply: (@format_vseb p Hp2 choice e Fe).
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: [ThreeProdFast x y] is a triple-word number.         *)
(*                                                                            *)
(*  Paper Section 6.4: correctness is still ensured for the same reasons,     *)
(*  provided that [p >= 6].  Concretely (doc/alg10.md), the Section-6.2       *)
(*  part-1 argument of Algorithm 9 applies with LESS work:                    *)
(*  - the head [VecSum(z00+, b0, b1, s3)] is exactly the one of Algorithm 9   *)
(*    (same [z00+], [b0], [b1], and [s3 = RN(c + z3)]), so its                *)
(*    F-nonoverlapping is [ThreeProd.inner_head_Fnonoverlap] verbatim -- the  *)
(*    four-case [I]-set study of Theorem 1 does not have to be redone;        *)
(*  - the [e4] tail of Algorithm 9 is absent, so the [vecSum_split5] /        *)
(*    [Fnonoverlap_rcons] step and the [e4]-divisibility item (b) disappear;  *)
(*  - Theorem 2 ([vseb_Pnonoverlap]) then gives P-nonoverlapping of           *)
(*    [vseb (z00+, b0, b1, s3)], and the [r0 = e0] optimisation is the same   *)
(*    star identity ([vseb_star] / [vseb_head3_e1zero]).                      *)
(*  The general statement will reduce to a normalised one (paper WLOG         *)
(*  [1 <= x0, y0 < 2]) by the scale/sign equivariance of Algorithm 10, the    *)
(*  twin of [ThreeProd_scale] / [ThreeProd_opp].                              *)
(* ===========================================================================*)
Lemma ThreeProdFast_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (ThreeProdFast x y).
Proof.
move=> Hc Hx Hy.
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  rewrite (@isTW_zero_lead p Hp2 x Hx x0z) ThreeProdFast_0l.
  by exact: isTW_TWR000.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (@isTW_zero_lead p Hp2 y Hy y0z) ThreeProdFast_0r.
  by exact: isTW_TWR000.
have [cx _ [Hxp Hxn]] := @isTW_normalize p Hp2 choice x Hx x0n.
have [cy _ [Hyp Hyn]] := @isTW_normalize p Hp2 choice y Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
case: Hxsg => Hxs; case: Hysg => Hys.
- rewrite -(@isTW_scale p Hp2 choice (cx + cy)) -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxp | apply: Hyp].
- rewrite -(@isTW_opp p (ThreeProdFast x y)).
  rewrite -(@isTW_scale p Hp2 choice (cx + cy)).
  rewrite -ThreeProdFast_opp_r -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxp | apply: Hyn].
- rewrite -(@isTW_opp p (ThreeProdFast x y)).
  rewrite -(@isTW_scale p Hp2 choice (cx + cy)).
  rewrite -ThreeProdFast_opp -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxn | apply: Hyp].
- rewrite -(@isTW_scale p Hp2 choice (cx + cy)).
  have <- : ThreeProdFast (negTW x) (negTW y) = ThreeProdFast x y.
    by rewrite ThreeProdFast_opp ThreeProdFast_opp_r negTW_id.
  rewrite -ThreeProdFast_scale.
  by apply: ThreeProdFast_isTW_norm => //; [apply: Hxn | apply: Hyn].
Qed.

(* ===========================================================================*)
(*  Section 6.4 -- the error analysis.  Algorithm 10 has the SAME six error   *)
(*  sources [eps0..eps5] as Algorithm 9 (all bounds reused from ThreeProd.v)  *)
(*  plus one more, the term it drops:                                         *)
(*                                                                            *)
(*    eps4' := (c + z3) - s3,   |eps4'| <= u ufp(12u^2 + 8u^2) <= 16u^3       *)
(*                                                                            *)
(*  so the numerator becomes [44u^3 - 11.9u^4] (44 = 28 + 16) and, over       *)
(*  [x*y >= 1 - 4u], the relative error is [44u^3 + 176u^4].                  *)
(* ===========================================================================*)

Lemma pow_5m2p : pow (5 - 2 * p) = 32 * (u * u).
Proof.
rewrite (_ : (5 - 2 * p = 5 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma pow_5m3p : pow (5 - 3 * p) = 32 * (u * u * u).
Proof.
rewrite (_ : (5 - 3 * p = 5 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

(* [eps4' = (c + z3) - s3]: [<= 16u^3].  The extra source of Algorithm 10.    *)
Lemma epsp4_bound c z3 :
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (c + z3 - RND (c + z3)) <= 16 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (c + z3) < pow (5 - 2 * p).
  rewrite pow_5m2p.
  have H3 := Rabs_triang c z3.
  nra.
have Herr := @round_err_le p Hp2 choice _ _ Hw.
move: Herr; rewrite (_ : (5 - 2 * p - p = 5 - 3 * p)%Z); last by lia.
rewrite pow_5m3p; nra.
Qed.

(* Summing the SIX constant error sources: [28u^3 - 11.9u^4 + 16u^3].         *)
Lemma eps04p_sum e0 e1 e2 e3 e4 e4p :
  Rabs e0 <= 8 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  Rabs e1 <= 4 * (u * u * u) -> Rabs e2 <= 4 * (u * u * u) ->
  Rabs e3 <= 8 * (u * u * u) -> Rabs e4 <= 4 * (u * u * u) ->
  Rabs e4p <= 16 * (u * u * u) ->
  Rabs (e0 + e1 + e2 + e3 + e4 + e4p) <=
    44 * (u * u * u) - 119 / 10 * (u * u * u * u).
Proof.
move=> H0 H1 H2 H3 H4 H4p.
have T0 := Rabs_triang (e0 + e1 + e2 + e3 + e4) e4p.
have T1 := Rabs_triang (e0 + e1 + e2 + e3) e4.
have T2 := Rabs_triang (e0 + e1 + e2) e3.
have T3 := Rabs_triang (e0 + e1) e2.
have T4 := Rabs_triang e0 e1.
lra.
Qed.

(* Dividing the numerator by [|x*y| >= 1 - 4u] (the [eps5 = 0] branch).       *)
Lemma error_assembly_fast err xy :
  Rabs err <= 44 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  1 - 4 * u <= Rabs xy ->
  Rabs err <= (44 * (u * u * u) + 176 * (u * u * u * u)) * Rabs xy.
Proof.
move=> Hn Hxy.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
set B := 44 * (u * u * u) + 176 * (u * u * u * u).
have HB0 : 0 <= B by rewrite /B; nra.
apply: (Rle_trans _ (B * (1 - 4 * u))); last first.
  by apply: Rmult_le_compat_l.
apply: (Rle_trans _ _ _ Hn).
rewrite /B; nra.
Qed.

(* The error identity of Algorithm 10: the twin of [sumR_e_decomp] on the     *)
(* FOUR-limb VecSum, with the extra [eps4' = c + z3 - s3].                    *)
Lemma sumR_eF_decomp x0 x1 x2 y0 y1 y2
    z00p z00m z01p z01m z10p z10m b c z31 z32 z3 s3 :
  format x0 -> format x1 -> format y0 -> format y1 ->
  TwoProd x0 y0 = (z00p, z00m) ->
  TwoProd x0 y1 = (z01p, z01m) ->
  TwoProd x1 y0 = (z10p, z10m) ->
  b = vecSum [:: z00m; z01p; z10p] ->
  c = RND (nth 0 b 2 + x1 * y1) ->
  z31 = RND (z10m + x0 * y2) ->
  z32 = RND (z01m + x2 * y0) ->
  z3 = RND (z31 + z32) ->
  s3 = RND (c + z3) ->
  (x0 + x1 + x2) * (y0 + y1 + y2) -
    sumR (vecSum [:: z00p; nth 0 b 0; nth 0 b 1; s3]) =
    (x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
    + (z01m + x2 * y0 - z32) + (z31 + z32 - z3) + (nth 0 b 2 + x1 * y1 - c)
    + (c + z3 - s3).
Proof.
move=> Fx0 Fx1 Fy0 Fy1 HP00 HP01 HP10 Hb Hc H31 H32 H3 Hs3.
(* Algorithm 9's five-term identity, reused as is ...                         *)
have H5 := @sumR_e_decomp p Hp2 choice choice_sym x0 x1 x2 y0 y1 y2
  z00p z00m z01p z01m z10p z10m b c z31 z32 z3
  Fx0 Fx1 Fy0 Fy1 HP00 HP01 HP10 Hb Hc H31 H32 H3.
have Fz00p : format z00p.
  by have := @TwoProd_fmt1 p Hp2 choice x0 y0 Fx0 Fy0; rewrite HP00.
have Fz00m : format z00m.
  by have := @TwoProd_fmt2 p Hp2 choice x0 y0 Fx0 Fy0; rewrite HP00.
have Fz01p : format z01p.
  by have := @TwoProd_fmt1 p Hp2 choice x0 y1 Fx0 Fy1; rewrite HP01.
have Fz10p : format z10p.
  by have := @TwoProd_fmt1 p Hp2 choice x1 y0 Fx1 Fy0; rewrite HP10.
have Fb : {in b, forall z, format z}.
  rewrite Hb; apply: (@format_vecSum p Hp2 choice).
  by move=> z; rewrite !inE => /or3P[] /eqP-> //.
have Hsz : size b = 3%N by rewrite Hb size_vecSum.
have Fb0 : format (nth 0 b 0) by apply: Fb; rewrite mem_nth // Hsz.
have Fb1 : format (nth 0 b 1) by apply: Fb; rewrite mem_nth // Hsz.
have Fc : format c by rewrite Hc; apply: generic_format_round.
have Fz3 : format z3 by rewrite H3; apply: generic_format_round.
have Fs3 : format s3 by rewrite Hs3; apply: generic_format_round.
(* ... and the two VecSums are exact, so the four-limb sum differs from the   *)
(* five-limb one exactly by [eps4' = c + z3 - s3].                            *)
have Ee4 : sumR (vecSum [:: z00p; nth 0 b 0; nth 0 b 1; s3]) =
           z00p + nth 0 b 0 + nth 0 b 1 + s3.
  rewrite (@vecSum_sum p Hp2 choice choice_sym); last first.
    by move=> z; rewrite !inE =>
      /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]] //.
  by rewrite /=; ring.
have Ee5 : sumR (vecSum [:: z00p; nth 0 b 0; nth 0 b 1; c; z3]) =
           z00p + nth 0 b 0 + nth 0 b 1 + c + z3.
  rewrite (@vecSum_sum p Hp2 choice choice_sym); last first.
    by move=> z; rewrite !inE =>
      /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]] //.
  by rewrite /=; ring.
rewrite Ee4; move: H5; rewrite Ee5 => H5; lra.
Qed.

(* The [eps5 = 0] core of the [eps5 <> 0] discussion (old paper Section 6.6,  *)
(* "similarly to the previous case"): when every term is big, the leading     *)
(* terms all live on the [8u^3] grid and [|sumR e| < 5], so a fourth nonzero  *)
(* P-nonoverlapping limb would be [< 8u^3] -- impossible.  The twin of        *)
(* [eps5_zero_all_big] on the four-limb list ([s3 = RN(c + z3)] inherits the  *)
(* grid from [c] and [z3]).                                                   *)
Lemma eps5F_zero_all_big x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (c + z3)] in
  u * u <= Rabs x2 -> u * u <= Rabs y2 ->
  4 * (u * u) <= Rabs c -> 4 * (u * u) <= Rabs z3 ->
  sumR (vseb e) - sumR (vsebK 3 e) = 0.
Proof.
move=> Hc Nx Ny bb c z3 e Hx2h Hy2h Hcb Hz3b.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1o Hx2o] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r Hy1o Hy2o] := Ny.
have Hu2 : u * u = pow (- (2 * p)) by rewrite u_pow -bpow_plus; congr bpow; lia.
(* [u^2 <= |x2|] with [|x2| < ulp x1] forces [ulp x1 > u^2], hence [u <=      *)
(* |x1|]: this is why the case split is on [x2], [y2] and not on [x1], [y1].  *)
have Hderive : forall (w1 w2 : R), w2 = 0 \/ Rabs w2 < ulp w1 ->
    u * u <= Rabs w2 -> u <= Rabs w1.
  move=> w1 w2 Hw2o Hw2h.
  have Hw2n0 : w2 <> 0.
    by move=> H0; move: Hw2h; rewrite H0 Rabs_R0 => H; nra.
  have Hw2lt : Rabs w2 < ulp w1 by case: Hw2o => // H0; case: Hw2n0.
  have Hw1n0 : w1 <> 0.
    move=> H0; move: Hw2lt; rewrite H0 ulp_FLX_0 => H.
    by have := Rabs_pos w2; nra.
  have Hmagw1 : (1 - p <= mag beta w1)%Z.
    have Hulp : pow (- (2 * p)) < ulp w1 by rewrite -Hu2; lra.
    move: Hulp; rewrite ulp_neq_0 // /cexp /fexp /FLX_exp => H.
    by have := lt_bpow beta _ _ H; lia.
  apply: (Rle_trans _ (pow (mag beta w1 - 1))).
    by rewrite u_pow; apply: bpow_le; lia.
  by have := ufp_le_abs Hw1n0; rewrite /ufp.
have Hx1b : u <= Rabs x1 by apply: (Hderive x1 x2 Hx2o Hx2h).
have Hy1b : u <= Rabs y1 by apply: (Hderive y1 y2 Hy2o Hy2h).
(* Every leading term is a multiple of [8u^3 = pow (3 - 3p)] -- including     *)
(* [s3 = RN(c + z3)], which inherits the grid from [c] and [z3].              *)
pose g := (3 - 3 * p)%Z.
have Himcx : forall x : R, format x -> (g <= cexp x)%Z -> is_imul x (pow g).
  move=> x Fx Hcx.
  by apply: (is_imul_pow_le (y1 := cexp x)); [exact: format_imul_cexp | exact:
    Hcx].
have Hcexp : forall x : R, cexp x = (mag beta x - p)%Z
  by move=> x; rewrite /cexp /fexp /FLX_exp.
have Iz00p : is_imul (RND (x0 * y0)) (pow g).
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp; have Hlb : 1 <= RND (x0 * y0)
    by apply: (@z00p_lb p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  suff : (1 <= mag beta (RND (x0 * y0)))%Z by rewrite /g; lia.
  by apply: mag_ge_bpow; rewrite pow0E Rabs_pos_eq; lra.
have Fu : format u by rewrite u_pow; apply: format_pow.
have Iz00m : is_imul (RND (x0 * y0 - RND (x0 * y0))) (pow g).
  rewrite round_generic; last first.
    rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
      ring.
    by apply: generic_format_opp; exact: format_err_mul.
  apply: (is_imul_pow_le (y1 := (2 - 2 * p)%Z)); last by rewrite /g; lia.
  rewrite pow_2m2p; exact: (@z00m_imul p choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Iz01p : is_imul (RND (x0 * y1)) (pow g).
  have Hge : u <= Rabs (RND (x0 * y1)).
    apply: Rabs_round_le_l => //.
    rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
    have := Rabs_pos y1; nra.
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp /g; suff : (1 - p <= mag beta (RND (x0 * y1)))%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (1 - p - 1 = - p)%Z); last by lia.
  by rewrite -u_pow.
have Iz10p : is_imul (RND (x1 * y0)) (pow g).
  have Hge : u <= Rabs (RND (x1 * y0)).
    apply: Rabs_round_le_l => //.
    rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
    have := Rabs_pos x1; nra.
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp /g; suff : (1 - p <= mag beta (RND (x1 * y0)))%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (1 - p - 1 = - p)%Z); last by lia.
  by rewrite -u_pow.
have Ia : is_imul (RND (RND (x0 * y1) + RND (x1 * y0))) (pow g)
  by apply: is_imul_pow_round; apply: is_imul_add.
have Fz00mf : format (RND (x0 * y0 - RND (x0 * y0))) by apply:
  generic_format_round.
have Fz01pf : format (RND (x0 * y1)) by apply: generic_format_round.
have Fz10pf : format (RND (x1 * y0)) by apply: generic_format_round.
have Hbbe : bb = [:: RND (RND (x0 * y0 - RND (x0 * y0))
                         + RND (RND (x0 * y1) + RND (x1 * y0)));
    RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))
      - RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0)));
    RND (x0 * y1) + RND (x1 * y0) - RND (RND (x0 * y1) + RND (x1 * y0))]
  by rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _ Fz00mf Fz01pf Fz10pf).
have Ib0 : is_imul (nth 0 bb 0) (pow g).
  by rewrite Hbbe /=; apply: is_imul_pow_round; apply: is_imul_add;
    [exact: Iz00m | exact: Ia].
have Ib1 : is_imul (nth 0 bb 1) (pow g).
  rewrite Hbbe /=; apply: is_imul_minus.
    by apply: is_imul_add; [exact: Iz00m | exact: Ia].
  by apply: is_imul_pow_round; apply: is_imul_add; [exact: Iz00m | exact: Ia].
have Ic : is_imul c (pow g).
  apply: Himcx; first by rewrite /c; apply: generic_format_round.
  rewrite Hcexp /g; suff : (3 - 2 * p <= mag beta c)%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (3 - 2 * p - 1 = 2 - 2 * p)%Z); last by lia.
  by rewrite pow_2m2p.
have Iz3 : is_imul z3 (pow g).
  apply: Himcx; first by rewrite /z3; apply: generic_format_round.
  rewrite Hcexp /g; suff : (3 - 2 * p <= mag beta z3)%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (3 - 2 * p - 1 = 2 - 2 * p)%Z); last by lia.
  by rewrite pow_2m2p.
have Is3 : is_imul (RND (c + z3)) (pow g)
  by apply: is_imul_pow_round; apply: is_imul_add.
have Fz00pf : format (RND (x0 * y0)) by apply: generic_format_round.
have Fs3f : format (RND (c + z3)) by apply: generic_format_round.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fb0 : format (nth 0 bb 0) by apply: Fbb; rewrite /bb mem_nth //
  size_vecSum.
have Fb1 : format (nth 0 bb 1) by apply: Fbb; rewrite /bb mem_nth //
  size_vecSum.
pose l0 := [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (c + z3)].
have Feinp : {in l0, forall z, format z}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]] //.
have Ieinp : {in l0, forall z, is_imul z (pow g)}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]] //.
have Ie : {in e, forall z, is_imul z (pow g)}
  by rewrite /e; apply: vecSum_imul_forward.
have Fe : {in e, forall z, format z}
  by rewrite /e; apply: (@format_vecSum p Hp2 choice).
have Ivse : {in vseb e, forall z, is_imul z (pow g)}
  by apply: vseb_imul_forward.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fno : Fnonoverlap e
  by rewrite /e /bb; apply: (innerF_Fnonoverlap Hc Nx Ny).
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall z, format z}
  by apply: (@format_vseb p Hp2 choice e Fe).
have Hsume : sumR e = RND (x0 * y0) + nth 0 bb 0 + nth 0 bb 1 + RND (c + z3).
  rewrite /e (@vecSum_sum p Hp2 choice choice_sym); last by apply: Feinp.
  by rewrite /=; ring.
have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 (vseb e))
  by rewrite /vsebK -{1}(cat_take_drop 3 (vseb e)) sumR_cat; ring.
rewrite Hsplit.
have RNrel : forall t : R, Rabs (RND t) <= (1 + u) * Rabs t.
  move=> t; have Ht := relative_error_le beta Hp2 choice t.
  have H2 : Rabs (RND t) <= Rabs t + Rabs (RND t - t)
    by have := Rabs_triang t (RND t - t);
       rewrite (_ : t + (RND t - t) = RND t); [lra | ring].
  have := Rabs_pos t; nra.
have Hz00mb : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic;
    first by apply: (@z00m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01pb := @z01p_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny.
have Hz10pb := @z10p_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny.
have Hab : Rabs (RND (RND (x0 * y1) + RND (x1 * y0))) <= 9 * u.
  apply: (Rle_trans _ _ _ (RNrel _)).
  have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); nra.
have Hb01 : nth 0 bb 0 + nth 0 bb 1
    = RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))
  by rewrite Hbbe /=; ring.
have Hz00pu : RND (x0 * y0) < 4
  by apply: (@z00p_ub p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Hz00pl : 1 <= RND (x0 * y0)
  by apply: (@z00p_lb p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z10m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz3ub : Rabs z3 <= 12 * (u * u)
  := @z3_bound p Hp2 Hp6 choice _ _
       (@z31_bound p Hp2 Hp6 choice _ _ _ Hz10m2
          (@x0y2_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny))
       (@z32_bound p Hp2 Hp6 choice _ _ _ Hz01m2
          (@x2y0_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny)).
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Hc8 : Rabs c <= 8 * (u * u)
  := @c_bound p Hp2 Hp6 choice _ _ _ Hb2 (@x1y1_bound p x0 x1 x2 y0 y1 y2 Nx
       Ny).
have Hs3b : Rabs (RND (c + z3)) <= 20 * (u * u)
  := @s3_bound p Hp2 Hp6 choice _ _ Hc8 Hz3ub.
have Hb01b : Rabs (nth 0 bb 0 + nth 0 bb 1) <= 11 * u.
  rewrite Hb01.
  have := Rabs_triang (RND (x0 * y0 - RND (x0 * y0)))
                      (RND (RND (x0 * y1) + RND (x1 * y0))); lra.
(* [|sumR e| < 5], so [|r0| <= 5] and a fourth nonzero P-nonoverlapping limb  *)
(* would be [< 8u^3] -- yet a nonzero multiple of [8u^3].  Contradiction.     *)
have Hsum4 : Rabs (sumR e) < 5.
  rewrite Hsume.
  have -> : RND (x0 * y0) + nth 0 bb 0 + nth 0 bb 1 + RND (c + z3)
      = RND (x0 * y0) + (nth 0 bb 0 + nth 0 bb 1) + RND (c + z3) by ring.
  set S := nth 0 bb 0 + nth 0 bb 1.
  have T1 := Rabs_triang (RND (x0 * y0) + S) (RND (c + z3)).
  have T2 := Rabs_triang (RND (x0 * y0)) S.
  have Hz00pa : Rabs (RND (x0 * y0)) < 4 by rewrite Rabs_pos_eq; lra.
  have HS : Rabs S <= 11 * u by exact: Hb01b.
  clear -T1 T2 Hz00pa HS Hs3b Hu0 Hu64; nra.
have Hsvse : Rabs (sumR (vseb e)) < 5 by rewrite Hsumeq.
have Hstep : forall (i : nat) (K : Z), nth 0 (vseb e) i.+1 <> 0 ->
    (i.+1 < size (vseb e))%N -> Rabs (nth 0 (vseb e) i) < pow K ->
    Rabs (nth 0 (vseb e) i.+1) < pow (K - p).
  move=> i K Hn1 Hlt HK.
  have [Hz|Hb] := Pno i Hlt; first by case: Hn1.
  apply: (Rlt_le_trans _ _ _ Hb).
  have Hni : nth 0 (vseb e) i <> 0.
    move=> H0; move: Hb; rewrite H0 ulp_FLX_0 => Hb'.
    have := Rabs_pos (nth 0 (vseb e) i.+1); lra.
  rewrite ulp_neq_0 //; apply: bpow_le.
  rewrite Hcexp.
  suff : (mag beta (nth 0%R (vseb e) i) <= K)%Z by lia.
  by apply: mag_le_bpow.
have Hn3 : nth 0 (vseb e) 3 = 0.
  case: (Req_dec (nth 0 (vseb e) 0) 0) => [Hr0|Hr0n].
    have H1 := @nth_step_zero p Hp2 (vseb e) 0 Pno Fvse Hr0.
    have H2 := @nth_step_zero p Hp2 (vseb e) 1 Pno Fvse H1.
    exact: (@nth_step_zero p Hp2 (vseb e) 2 Pno Fvse H2).
  case: (Req_dec (nth 0 (vseb e) 3) 0) => [//|Hn3n].
  have Hn2n : nth 0 (vseb e) 2 <> 0
    by move=> H; apply: Hn3n; apply: (@nth_step_zero p Hp2 (vseb e) 2 Pno Fvse
      H).
  have Hn1n : nth 0 (vseb e) 1 <> 0
    by move=> H; apply: Hn2n; apply: (@nth_step_zero p Hp2 (vseb e) 1 Pno Fvse
      H).
  have Hsz3 : (3 < size (vseb e))%N
    by rewrite ltnNge; apply/negP => Hge; apply: Hn3n; rewrite nth_default.
  have Hsz2 : (2 < size (vseb e))%N by apply: ltn_trans Hsz3.
  have Hsz1 : (1 < size (vseb e))%N by apply: ltn_trans Hsz2.
  have Hr08 : Rabs (nth 0 (vseb e) 0) < pow 3.
    have Hlow := @sumR_ufp_lower p Hp2 (vseb e) Pno Fvse Hr0n.
    have HU := ufp_gt_0 (nth 0 (vseb e) 0).
    have Hufp8 : ufp (nth 0 (vseb e) 0) < pow 3.
      have Hp38 : pow 3 = 8 by rewrite /= /Z.pow_pos /=; lra.
      clear -Hlow Hsvse Hu0 Hu64 HU Hp38; nra.
    apply: (Rlt_le_trans _ _ _ (bpow_mag_gt beta (nth 0 (vseb e) 0))).
    apply: bpow_le.
    by move: Hufp8; rewrite /ufp => H; have := lt_bpow beta _ _ H; lia.
  have Hm1 := Hstep 0%N (3%Z) Hn1n Hsz1 Hr08.
  have Hm2 := Hstep 1%N (3 - p)%Z Hn2n Hsz2 Hm1.
  have Hm3 := Hstep 2%N (3 - p - p)%Z Hn3n Hsz3 Hm2.
  have Hge : pow g <= Rabs (nth 0 (vseb e) 3).
    apply: is_imul_pow_le_abs; last exact: Hn3n.
    by apply: Ivse; apply: mem_nth.
  have Hpg : (3 - p - p - p = g)%Z by rewrite /g; lia.
  by rewrite Hpg in Hm3; lra.
apply: (@small_head_zero p Hp2).
- exact: Pnonoverlap_drop.
- by move=> z /mem_drop; apply: Fvse.
- by rewrite nth_drop addn0.
Qed.

(* [eps5 <> 0] forces one of the four small-term cases.                       *)
Lemma eps5nzF_forces_small x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (c + z3)] in
  sumR (vseb e) - sumR (vsebK 3 e) <> 0 ->
  [\/ Rabs y2 < u * u, Rabs x2 < u * u, Rabs c < 4 * (u * u) | Rabs z3 < 4 * (u
    * u)].
Proof.
move=> Hc Nx Ny bb c z3 e HE5.
case: (Rlt_le_dec (Rabs y2) (u * u)) => Hy2; first by apply: Or41.
case: (Rlt_le_dec (Rabs x2) (u * u)) => Hx2; first by apply: Or42.
case: (Rlt_le_dec (Rabs c) (4 * (u * u))) => Hcb; first by apply: Or43.
case: (Rlt_le_dec (Rabs z3) (4 * (u * u))) => Hz3b; first by apply: Or44.
by case: HE5; apply: (eps5F_zero_all_big Hc Nx Ny).
Qed.

(* In any of the four small cases the numerator drops from [44u^3 - 11.9u^4]  *)
(* to [42u^3 - 11.9u^4]: one of [eps1..eps4] halves to [2u^3].                *)
Lemma eps5nzF_numerator x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (c + z3)] in
  [\/ Rabs y2 < u * u, Rabs x2 < u * u, Rabs c < 4 * (u * u) | Rabs z3 < 4 * (u
    * u)] ->
  Rabs ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e)
    <= 42 * (u * u * u) - 119 / 10 * (u * u * u * u).
Proof.
move=> Nx Ny bb c z3 e Hdisj.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1o Hx2o] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r Hy1o Hy2o] := Ny.
set z10m := RND (x1 * y0 - RND (x1 * y0)).
set z01m := RND (x0 * y1 - RND (x0 * y1)).
set z31 := RND (z10m + x0 * y2).
set z32 := RND (z01m + x2 * y0).
have Hz10m : Rabs z10m <= 2 * (u * u).
  rewrite /z10m round_generic;
    first by apply: (@z10m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m : Rabs z01m <= 2 * (u * u).
  rewrite /z01m round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny.
have Hx2y0 := @x2y0_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx Ny.
have Hx1y1 := @x1y1_bound p x0 x1 x2 y0 y1 y2 Nx Ny.
have Hz31 := @z31_bound p Hp2 Hp6 choice _ _ _ Hz10m Hx0y2.
have Hz32 := @z32_bound p Hp2 Hp6 choice _ _ _ Hz01m Hx2y0.
have Hz3b := @z3_bound p Hp2 Hp6 choice _ _ Hz31 Hz32.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx Ny).
have Hc8 : Rabs c <= 8 * (u * u)
  by apply: (@c_bound p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
have Hdecomp := @sumR_eF_decomp x0 x1 x2 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) z01m (RND (x1 * y0)) z10m bb c z31 z32 z3 (RND (c + z3))
  Fx0 Fx1 Fy0 Fy1 erefl erefl erefl erefl erefl erefl erefl erefl erefl.
have -> : (x0 + x1 + x2) * (y0 + y1 + y2) - sumR e
    = (x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32) + (z31 + z32 - z3)
      + (nth 0 bb 2 + x1 * y1 - c) + (c + z3 - RND (c + z3))
  by exact: Hdecomp.
have He0 := @eps0_bound p Hp2 Hp6 x0 x1 x2 y0 y1 y2 Nx Ny.
have He1 := @eps1_bound p Hp2 choice _ _ _ Hz10m Hx0y2.
have He2 := @eps2_bound p Hp2 choice _ _ _ Hz01m Hx2y0.
have He3 := @eps3_bound p Hp2 choice _ _ Hz31 Hz32.
have He4 := @eps4_bound p Hp2 choice _ _ _ Hb2 Hx1y1.
have Hep4 := @epsp4_bound c z3 Hc8 Hz3b.
have T0 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32) + (z31 + z32 - z3)
      + (nth 0 bb 2 + x1 * y1 - c)) (c + z3 - RND (c + z3)).
have T1 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32) + (z31 + z32 - z3)) (nth 0 bb 2 + x1 * y1 - c).
have T2 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32)) (z31 + z32 - z3).
have T3 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31))
      (z01m + x2 * y0 - z32).
have T4 := Rabs_triang (x1 * y2 + x2 * y1 + x2 * y2) (z10m + x0 * y2 - z31).
rewrite -/z31 in He1.
rewrite -/z32 in He2.
rewrite -/z31 -/z32 -/z3 in He3.
rewrite -/c in He4.
have Hp2m3 : pow (2 - 3 * p) = 4 * (u * u * u).
  rewrite (_ : (2 - 3 * p = 2 + - (3 * p))%Z); last by lia.
  by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
(* Reusable [Hred]: a rounded value below [4u^2] has error at most [2u^3].    *)
have Hred : forall t : R, Rabs (RND t) < 4 * (u * u) ->
    Rabs (t - RND t) <= 2 * (u * u * u).
  move=> t Hlt.
  have Herr := @error_le_half_ulp_round beta (FLX_exp p)
    (FLX_exp_valid p) (FLX_exp_monotone p) choice t.
  have Hulp : ulp (RND t) <= 4 * (u * u * u).
    case: (Req_dec (RND t) 0) => [Hz|Hn0].
      rewrite Hz ulp_FLX_0; clear -Hu0; nra.
    rewrite ulp_neq_0 //.
    apply: (Rle_trans _ (pow (2 - 3 * p))); last by rewrite Hp2m3; apply:
      Rle_refl.
    have Hmag : (mag beta (RND t) <= 2 - 2 * p)%Z.
      by apply: mag_le_bpow; [exact: Hn0 | rewrite pow_2m2p; exact: Hlt].
    apply: bpow_le.
    have Hcx : cexp (RND t) = (mag beta (RND t) - p)%Z
      by rewrite /cexp /fexp /FLX_exp.
    rewrite Hcx; lia.
  have Hpp : Prec_gt_0 p by rewrite /Prec_gt_0; lia.
  move: (Herr Hpp); rewrite Rabs_minus_sym; lra.
(* Each of the four small cases halves one [eps_i] to [2u^3]: 44 - 2 = 42.    *)
case: Hdisj => [Hy2 | Hx2 | Hcs | Hz3s].
- have He1' : Rabs (z10m + x0 * y2 - z31) <= 2 * (u * u * u).
    have Hw : Rabs (z10m + x0 * y2) < pow (2 - 2 * p).
      rewrite pow_2m2p.
      have Hxy : Rabs (x0 * y2) < 2 * (u * u).
        rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
        clear -Hx0l Hx0r Hy2 Hu0; have := Rabs_pos y2; nra.
      have H3 := Rabs_triang z10m (x0 * y2); clear -Hz10m Hxy H3; lra.
    have Herr := @round_err_le p Hp2 choice _ _ Hw.
    move: Herr; rewrite (_ : (2 - 2 * p - p = 2 - 3 * p)%Z) ?Hp2m3 -/z31;
      last by lia.
    lra.
  lra.
- have He2' : Rabs (z01m + x2 * y0 - z32) <= 2 * (u * u * u).
    have Hw : Rabs (z01m + x2 * y0) < pow (2 - 2 * p).
      rewrite pow_2m2p.
      have Hxy : Rabs (x2 * y0) < 2 * (u * u).
        rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
        clear -Hx2 Hy0l Hy0r Hu0; have := Rabs_pos x2; nra.
      have H3 := Rabs_triang z01m (x2 * y0); clear -Hz01m Hxy H3; lra.
    have Herr := @round_err_le p Hp2 choice _ _ Hw.
    move: Herr; rewrite (_ : (2 - 2 * p - p = 2 - 3 * p)%Z) ?Hp2m3 -/z32;
      last by lia.
    lra.
  lra.
- have He4' : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 2 * (u * u * u).
    by apply: (Hred (nth 0 bb 2 + x1 * y1)); rewrite -/c.
  lra.
- have He3' : Rabs (z31 + z32 - z3) <= 2 * (u * u * u).
    by apply: (Hred (z31 + z32)); rewrite -/z3.
  lra.
Qed.

(* Error assembly for the [eps5 <> 0] branch: the reduced numerator plus the  *)
(* full [eps5] still fits [44u^3 + 176u^4] (with far more [u^4] slack than    *)
(* Algorithm 9's [28u^3 + 107u^4]).                                           *)
Lemma error_assembly_eps5_fast (num s5 sm xy : R) :
  Rabs num <= 42 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  Rabs s5 <= (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * Rabs sm ->
  Rabs sm <= Rabs xy + (42 * (u * u * u) - 119 / 10 * (u * u * u * u)) ->
  1 - 4 * u <= Rabs xy ->
  Rabs (s5 + num) <= (44 * (u * u * u) + 176 * (u * u * u * u)) * Rabs xy.
Proof.
move=> Hnum Hs5 Hsm Hxy.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Ht := Rabs_triang s5 num.
have Hxy0 : 0 <= Rabs xy by apply: Rabs_pos.
have Hsm0 : 0 <= Rabs sm by apply: Rabs_pos.
have Hs5' : Rabs s5 <= (2 * (u * u * u) + 42 / 10 * (u * u * u * u))
    * (Rabs xy + (42 * (u * u * u) - 119 / 10 * (u * u * u * u))).
  apply: (Rle_trans _ _ _ Hs5); apply: Rmult_le_compat_l; [nra | exact: Hsm].
move: Ht Hnum Hs5' Hxy; set r := Rabs xy; set a := Rabs (s5 + num);
  set b := Rabs s5; set d := Rabs num.
move=> Ht Hnum Hs5' Hxy.
have Hr : (42 * (u*u*u) + 1718/10 * (u*u*u*u)) * (1 - 4*u)
    <= (42 * (u*u*u) + 1718/10 * (u*u*u*u)) * r
  by apply: Rmult_le_compat_l; [nra | lra].
have Hpoly : (2*(u*u*u) + 42/10*(u*u*u*u) + 1) * (42*(u*u*u) - 119/10*(u*u*u*u))
    <= (42*(u*u*u) + 1718/10*(u*u*u*u)) * (1 - 4*u) by clear -Hu0 Hu64; nra.
clear -Ht Hnum Hs5' Hr Hpoly; nra.
Qed.

(* The [eps5 <> 0] branch of the error bound.                                 *)
Lemma ThreeProdFast_error_eps5nz x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        RND (RND (nth 0 bb 2 + x1 * y1)
           + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))] in
  sumR (vseb e) - sumR (vsebK 3 e) <> 0 ->
  Rabs (sumR (vsebK 3 e) - (x0 + x1 + x2) * (y0 + y1 + y2)) <=
     (44 * (u * u * u) + 176 * (u * u * u * u)) *
       Rabs ((x0 + x1 + x2) * (y0 + y1 + y2)).
Proof.
move=> Hc Nx Ny bb e HE5.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Fe : {in e, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
have Fno : Fnonoverlap e
  by rewrite /e /bb; apply: (innerF_Fnonoverlap Hc Nx Ny).
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall z, format z}
  by apply: (@format_vseb p Hp2 choice e Fe).
have Hdisj := eps5nzF_forces_small Hc Nx Ny HE5.
have Hnum := eps5nzF_numerator Nx Ny Hdisj.
have Hnum2 : Rabs ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e)
    <= 42 * (u * u * u) - 119 / 10 * (u * u * u * u) by exact: Hnum.
have Hs5 := @eps5_bound p Hp2 choice e Pno Fvse (@u_le_64 p Hp6).
have Hsm : Rabs (sumR (vseb e))
    <= Rabs ((x0 + x1 + x2) * (y0 + y1 + y2))
       + (42 * (u * u * u) - 119 / 10 * (u * u * u * u)).
  rewrite Hsumeq.
  have H1 : sumR e = (x0 + x1 + x2) * (y0 + y1 + y2)
      + (sumR e - (x0 + x1 + x2) * (y0 + y1 + y2)) by ring.
  rewrite {1}H1; apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  have -> : Rabs (sumR e - (x0 + x1 + x2) * (y0 + y1 + y2))
      = Rabs ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e) by rewrite
        Rabs_minus_sym.
  move: Hnum2; lra.
have Hident : sumR (vsebK 3 e) - (x0 + x1 + x2) * (y0 + y1 + y2)
    = -((sumR (vseb e) - sumR (vsebK 3 e))
        + ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e)).
  by rewrite Hsumeq; ring.
rewrite Hident Rabs_Ropp.
apply: (@error_assembly_eps5_fast _ _ (sumR (vseb e))).
- exact: Hnum2.
- exact: Hs5.
- exact: Hsm.
- exact: (@xy_ge p Hp2 Hp6 x0 x1 x2 y0 y1 y2 Nx Ny).
Qed.

(* Section 6.4, normalised (paper WLOG [1 <= x0, y0 < 2]).                    *)
Lemma ThreeProdFast_error_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y ->
  Rabs (TWval (ThreeProdFast x y) - TWval x * TWval y) <=
     (44 * (u * u * u) + 176 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 Nx.
case: y Ny => y0 y1 y2 Ny.
have Nx' : tw_norm x0 x1 x2 by exact: Nx.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
rewrite (ThreeProdFast_norm_eq Hc Nx' Ny').
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (RND (nth 0 bb 2 + x1 * y1)
     + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
          + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))].
have HTW3 : TWval (TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2))
    = sumR (vsebK 3 e).
  rewrite /TWval /vsebK.
  case E : (vseb e) => [|v0 [|v1 [|v2 r]]] /=.
  - ring.
  - ring.
  - ring.
  - rewrite take0 /=; ring.
rewrite HTW3.
have HXY : TWval (TWR x0 x1 x2) * TWval (TWR y0 y1 y2)
    = (x0 + x1 + x2) * (y0 + y1 + y2) by rewrite /TWval.
rewrite HXY.
case: (Req_dec (sumR (vseb e) - sumR (vsebK 3 e)) 0) => [HE5z|HE5n]; last first.
  by apply: (ThreeProdFast_error_eps5nz Hc Nx' Ny' HE5n).
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny'.
have Hz10m : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z10m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx' Ny').
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx' Ny').
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx' Ny'.
have Hx2y0 := @x2y0_bound p Hp2 x0 x1 x2 y0 y1 y2 Nx' Ny'.
have Hx1y1 := @x1y1_bound p x0 x1 x2 y0 y1 y2 Nx' Ny'.
have Hz31 := @z31_bound p Hp2 Hp6 choice _ _ _ Hz10m Hx0y2.
have Hz32 := @z32_bound p Hp2 Hp6 choice _ _ _ Hz01m Hx2y0.
have Hz3 := @z3_bound p Hp2 Hp6 choice _ _ Hz31 Hz32.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq;
     apply: (@b2_bound p Hp2 choice x0 x1 x2 y0 y1 y2 Nx' Ny').
have Hc8 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 8 * (u * u)
  by apply: (@c_bound p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Fe : {in e, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
have Fno : Fnonoverlap e
  by rewrite /e /bb; apply: (innerF_Fnonoverlap Hc Nx' Ny').
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
have [_ Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Hdecomp := @sumR_eF_decomp x0 x1 x2 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) (RND (x0 * y1 - RND (x0 * y1)))
  (RND (x1 * y0)) (RND (x1 * y0 - RND (x1 * y0)))
  bb
  (RND (nth 0 bb 2 + x1 * y1))
  (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2))
  (RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))
  (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
      + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))
  (RND (RND (nth 0 bb 2 + x1 * y1)
      + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
           + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))))
  Fx0 Fx1 Fy0 Fy1 erefl erefl erefl erefl erefl erefl erefl erefl erefl.
have Hk3 : sumR (vsebK 3 e) = sumR e by rewrite -Hsumeq; lra.
rewrite Hk3.
apply: error_assembly_fast; last by apply: (@xy_ge p Hp2 Hp6 x0 x1 x2 y0 y1 y2
  Nx' Ny').
rewrite Rabs_minus_sym /e Hdecomp.
apply: eps04p_sum.
- exact: (@eps0_bound p Hp2 Hp6 x0 x1 x2 y0 y1 y2 Nx' Ny').
- exact: (@eps1_bound p Hp2 choice _ _ _ Hz10m Hx0y2).
- exact: (@eps2_bound p Hp2 choice _ _ _ Hz01m Hx2y0).
- exact: (@eps3_bound p Hp2 choice _ _ Hz31 Hz32).
- exact: (@eps4_bound p Hp2 choice _ _ _ Hb2 Hx1y1).
- exact: (@epsp4_bound _ _ Hc8 Hz3).
Qed.

(* ===========================================================================*)
(*  Correctness, part 2: relative error of [ThreeProdFast] is                 *)
(*  [<= 44u^3 + 176u^4].                                                      *)
(*                                                                            *)
(*  Paper Section 6.4 (details in doc/old-triplewors.pdf Section 6.6; see     *)
(*  doc/alg10.md).  The six error sources [eps0..eps5] of Theorem 7 are       *)
(*  unchanged, and there is ONE more, the term Algorithm 10 drops:            *)
(*                                                                            *)
(*     |eps4'| := |(c + z3) - s3| <= u ufp(c + z3) <= u ufp(12u^2 + 8u^2)     *)
(*             <= 16u^3                                                       *)
(*                                                                            *)
(*  so the numerator becomes [(28u^3 - 11.9u^4) + 16u^3 = 44u^3 - 11.9u^4],   *)
(*  and dividing by [x*y >= 1 - 4u] gives [44u^3 + 176u^4].  As for           *)
(*  Algorithm 9, the [eps5 <> 0] case is handled by showing that when all the *)
(*  other terms are big [eps5 = 0] ([ThreeProd.eps5_zero_all_big]).           *)
(* ===========================================================================*)
Lemma ThreeProdFast_error x y :
  ties_to_even choice ->
  isTW x -> isTW y ->
  Rabs (TWval (ThreeProdFast x y) - TWval x * TWval y) <=
     (44 * (u * u * u) + 176 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy.
set C := (44 * _ + _).
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  rewrite (@isTW_zero_lead p Hp2 x Hx x0z) ThreeProdFast_0l.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (@isTW_zero_lead p Hp2 y Hy y0z) ThreeProdFast_0r.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_r Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
have [cx _ [Hxp Hxn]] := @isTW_normalize p Hp2 choice x Hx x0n.
have [cy _ [Hyp Hyn]] := @isTW_normalize p Hp2 choice y Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
apply: (@error_scale_transfer (cx + cy)%Z (TWval (ThreeProdFast x y))
                              (TWval x * TWval y) C).
case: Hxsg => Hxs; case: Hysg => Hys.
- have Hn := ThreeProdFast_error_norm Hc (Hxp Hxs) (Hyp Hys).
  rewrite ThreeProdFast_scale !TWval_scale in Hn.
  rewrite (_ : TWval x * pow cx * (TWval y * pow cy) = TWval x * TWval y * pow
    (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
- have Hn := ThreeProdFast_error_norm Hc (Hxp Hxs) (Hyn Hys).
  rewrite ThreeProdFast_scale ThreeProdFast_opp_r !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : TWval x * pow cx * (- TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProdFast x y) * pow (cx + cy) - - (TWval x * TWval y *
    pow (cx + cy)) = - (TWval (ThreeProdFast x y) * pow (cx + cy) - TWval x *
    TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProdFast_error_norm Hc (Hxn Hxs) (Hyp Hys).
  rewrite ThreeProdFast_scale ThreeProdFast_opp !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : - TWval x * pow cx * (TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProdFast x y) * pow (cx + cy) - - (TWval x * TWval y *
    pow (cx + cy)) = - (TWval (ThreeProdFast x y) * pow (cx + cy) - TWval x *
    TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProdFast_error_norm Hc (Hxn Hxs) (Hyn Hys).
  have Hxy : ThreeProdFast (negTW x) (negTW y) = ThreeProdFast x y.
    by rewrite ThreeProdFast_opp ThreeProdFast_opp_r negTW_id.
  rewrite ThreeProdFast_scale Hxy !TWval_scale !TWval_opp in Hn.
  rewrite (_ : - TWval x * pow cx * (- TWval y * pow cy) = TWval x * TWval y *
    pow (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
Qed.

End SecThreeProdFast.
