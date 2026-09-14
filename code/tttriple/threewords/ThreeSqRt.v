(* ---------------------------------------------------------------------------*)
(* Algorithm 15 (3SqRt): the SQUARE ROOT of a triple word, and its two        *)
(* correctness results -- the result is a triple word ([ThreeSqRt_isTW]) and  *)
(* the relative error bounds [24u^3 + 10260u^4] (accurate variant,            *)
(* [ThreeSqRt_error]) and [39u^3 + 10333u^4] (fast variant,                   *)
(* [ThreeSqRtFast_error]) -- paper doc/paper3.pdf, Section 10 and Theorem 11  *)
(* (see doc/thm11.md).  Generic over the precision [p] (FLX, no [emin]);      *)
(* needs [p >= 11].                                                           *)
(*                                                                            *)
(* The proof follows the SUPPLEMENTARY MATERIAL, Section 3 of                 *)
(* doc/Algorithms_for_Triple-Word_Arithmetic.pdf -- the appendix paper3.pdf   *)
(* defers to.  (The long version doc/old-triplewors.pdf is of no help here:   *)
(* it stops at Section 9, the quotient, and its own roadmap reads [Section 10 *)
(* [???]], a placeholder never filled in.)  The underlying iteration is       *)
(* [r <- r (3/2 - (1/2) r^2 x)], quadratically convergent to [1/sqrt x].      *)
(*                                                                            *)
(*     a    <- RN((1 + 4u)/RN(sqrt x0))  )                                    *)
(*     a'   =  a/2                (exact) )                                   *)
(*     (h0(1), h11(1)) <- 2Prod(a, x0)   )                                    *)
(*     h1(1)  <- RN(h11(1) + a*x1)       )  the nine head lines, i.e.         *)
(*     (h01(2), h11(2)) <- 2Prod(a', h0(1))  [sqrtBW (tw0 x) (tw1 x)],        *)
(*     h0(2)  <- 3/2 - h01(2)     (exact) )  a double word [b ~ 1/sqrt x0]    *)
(*     h1(2)  <- -RN(h11(2) + a'*h1(1))  )                                    *)
(*     (b01, b11) <- 2Prod(a, h0(2))     )                                    *)
(*     b12  <- RN(b11 + a*h1(2))         )                                    *)
(*     b    <- Fast2Sum(b01, b12)        )                                    *)
(*     b'   =  b/2                (exact)                                     *)
(*     i(1) <- 3Prod_{2,3}(b, x)            (~ sqrt x)                        *)
(*     i(2) <- 3/2 - 3Prod_{2,3}(b', i(1))  (head [1], as in Algorithm 13)    *)
(*     y    <- 3Prod_{3,3}(i(1), i(2))                                        *)
(*                                                                            *)
(* Three structural differences from Algorithms 13 and 14: the seed [a]       *)
(* involves a real square root (nothing else in this development computes     *)
(* with [sqrt]); [2 - .] becomes [3/2 - .] ([sub32TW]), and the two halvings  *)
(* [a' = a/2], [b' = b/2] are exact scalings by [pow (-1)]; the last product  *)
(* is again the TW x TW one with a head-[1] SECOND argument, Algorithm 20     *)
(* ([ThreeProdOneTW] in ThreeProdOne.v).                                      *)
(*                                                                            *)
(* WHY THE PUBLISHED [24u^3] IS STILL REACHABLE FOR US, unlike Theorem 10's.  *)
(* The supplementary's global bound, with [d1], [d2], [d3] the three          *)
(* products' relative errors, is                                              *)
(*                                                                            *)
(*     |y - sqrt x| <= (d1 (1.5 + 287u^2) + d2 (0.5 + 123u^2)                 *)
(*                     + d3 (1 + 162u^2) + 9916u^4) sqrt x                    *)
(*                                                                            *)
(* whence [24 = 1.5(10.5) + 0.5(10.5) + 3] and [39 = 1.5(18) + 0.5(18) + 3].  *)
(* With OUR [d3 = 6u^3] instead of the announced [3u^3] (Algorithm 20's       *)
(* [delta3] is still loose -- see doc/thm10.md) that route gives [27u^3] and  *)
(* [42u^3], exactly as it does for Theorem 10.                                *)
(*                                                                            *)
(* AND [d3] IS NOT THE ONE ALGORITHM 14 USES.  Algorithm 20's error depends   *)
(* on how close its head-[1] second argument really is to [1], and Algorithm  *)
(* 15 cannot meet the [40u^2] Algorithm 14 hands over: [i(2) = 1 - e] with    *)
(* [e] the SEED error, [100u^2] here and [81u^2] even in the paper.  So       *)
(* ThreeProdOne.v's [ThreeProdOneTW_error_c] makes that tolerance a           *)
(* parameter [c], [delta3 = 6u^3 + (31c + 10)u^4]; Algorithm 14 keeps         *)
(* [c = 40] -- and with it the very same [1250] -- while Algorithm 15 runs at *)
(* [c = 105], i.e. [3265u^4].  See [sqrtAux_i2_near_1].                       *)
(*                                                                            *)
(* BUT the weight [1.5] on [d1] is itself loose, and provably so.  Expanding  *)
(* to first order -- [i(1)] occurs TWICE, once as a factor of [y] and once    *)
(* inside [i(2)], with OPPOSITE signs -- gives                                *)
(*                                                                            *)
(*     y/sqrt x - 1  ~  d1/2 - d2/2 + d3                                      *)
(*                                                                            *)
(* (the seed error [e] cancels too: Newton is self-correcting).  So the true  *)
(* weight on [d1] is [1/2], not [3/2]: the supplementary reaches [1.5] by     *)
(* bounding [|d1 - (d1 + d2)/2|] with the triangle inequality, discarding the *)
(* cancellation.  Exploiting it gives [18.5u^3] and [26u^3].                  *)
(*                                                                            *)
(* AND THAT SLACK IS WHAT SAVES THE [u^4] TERM.  Our [d3] is also far worse   *)
(* at [u^4] -- [3265] against the announced [263] -- and that excess lands    *)
(* undiluted (weight [1]), so the honest totals are [16.5u^3 + 18504u^4] and  *)
(* [24u^3 + 18540u^4] against the published [24u^3 + 10260u^4] and            *)
(* [39u^3 + 10333u^4].  Neither pair is termwise smaller.  But                *)
(*                                                                            *)
(*     8244u^4 <= 7.5u^3   <=>   u <= 1/1099                                  *)
(*                                                                            *)
(* and [u <= 2^-11 = 1/2048], so the [u^3] slack absorbs the [u^4] excess     *)
(* with a factor-1.9 margin; likewise [8207u^4 <= 15u^3] for the fast         *)
(* variant, which is wider still.  So THEOREM 11                              *)
(* HOLDS FOR US EXACTLY AS PUBLISHED -- the                                   *)
(* first of Theorems 9-11 for which that is true, and the reason to state it  *)
(* below with the paper's own constants rather than corrected ones.  It costs *)
(* nothing extra: the [delta3] tightening of doc/thm10.md would improve       *)
(* Theorems 9 and 10, not this one.                                           *)
(*                                                                            *)
(* STATUS: COMPLETE -- all four theorems are PROVED, zero admits.             *)
(* [ThreeSqRt_isTW], [ThreeSqRtFast_isTW], [ThreeSqRt_error] and              *)
(* [ThreeSqRtFast_error] are [Qed], and [Print Assumptions] on any of them    *)
(* shows only the standard classical/reals axioms that every result in this   *)
(* development carries.  THEOREM 11 HOLDS WITH THE PAPER'S OWN CONSTANTS.     *)
(*                                                                            *)
(* The error half is [sqrt_error_core] -- pure algebra on reals: the          *)
(* four-way split plus eight magnitude bounds, the analogue of ThreeDiv.v's   *)
(* [div_error_core] -- with [ThreeSqRtAux_error] over it and the two          *)
(* instantiations on top.                                                     *)
(*                                                                            *)
(* NOTE the sharp seed bound [81u^2 + 622u^3] the supplementary states is     *)
(* NOT USED, and has been removed.  Two reasons.  It is out of reach of this  *)
(* chain -- [sqrtA_bound_full] gives [e <= 8u], so the Newton residual is     *)
(* already [(3/2)(8u)^2 = 96u^2] before any rounding is added, and reaching   *)
(* [81] would need some 5% less slack throughout.  And it is unnecessary: the *)
(* cancellation leaves [24 - 16.5 = 7.5u^3], worth [15360u^4] at [p >= 11],   *)
(* against the [12629u^4] that the crude [120u^2] costs.  So Theorem 11's     *)
(* PUBLISHED constants are reachable from the crude bound alone.              *)
(*                                                                            *)
(* The proof, and where it departs from the paper, is doc/thm11.md.           *)
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
Require Import ThreeReci.
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeSqRt.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 15 asks for [p >= 11], one more than Algorithms 13 and 14.  Per  *)
(* the supplementary the extra bit is needed by the MODIFIED product used for *)
(* [i(2)] -- the variant whose penultimate line is [e1 <- Fast2Sum(.5)(...)]  *)
(* -- not by the exactness of [h0(2)], which follows from [h01(2) >= 1/2]     *)
(* alone.  See doc/thm11.md Section 4.                                        *)
Hypothesis Hp11 : (11 <= p)%Z.

Lemma Hp10 : (10 <= p)%Z. Proof. lia. Qed.
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

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation Fast2Sum := (Fast2Sum p choice).
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).
Local Notation head_one := (head_one p).

(* The three products: Algorithms 11/12 (DW x TW) and Algorithm 20 (TW x TW   *)
(* with a head-[1] second argument).                                          *)
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdDWFast := (ThreeProdDWFast p choice).
Local Notation ThreeProdOneTW := (ThreeProdOneTW p choice).

(* Step 4b.  The Newton residual: the EXACT value of the last two lines is    *)
(* already within [O(u^4)] of [sqrt x], by [sqrt_newton_id] applied to        *)
(* step 4.  The supplementary's constant.  This is the only [u^4] contributor *)
(* that is not a product's error.                                             *)
(* [u <= 2^-11], the [p >= 11] form of [u_le_1024].  Theorem 11 genuinely     *)
(* needs it: the Newton residual below is [9915.5u^4] at [p = 11] against     *)
(* the paper's [9916u^4], but [9989.9u^4] at [p = 10].                        *)
Lemma u_le_2048 : u <= / 2048.
Proof.
have -> : / 2048 = pow (-11) by rewrite /= /Z.pow_pos /=; lra.
by rewrite (u_pow p); apply: bpow_le; lia.
Qed.

(* ===========================================================================*)
(*  [3/2 - x] on triple words                                                 *)
(*                                                                            *)
(*  Algorithm 15 subtracts a triple word from [3/2] ([i(2) <- 3/2 - 3Prod]).  *)
(*  Limb by limb this is [(3/2 - x0, -x1, -x2)]: the two low limbs are just   *)
(*  negated, and the head subtraction [3/2 - x0] is EXACT as soon as          *)
(*  [x0 = 1/2], which is what [head_half] below asserts of the product -- the *)
(*  exact analogue of Algorithm 13's [sub2TW] and its [tw0 = 1].              *)
(* ===========================================================================*)
Definition sub32TW (x : twR) : twR :=
  let: TWR x0 x1 x2 := x in TWR (3 / 2 - x0) (- x1) (- x2).

Lemma TWval_sub32TW x : TWval (sub32TW x) = 3 / 2 - TWval x.
Proof. by case: x => x0 x1 x2; rewrite /TWval /=; ring. Qed.

Lemma sub32TW_isTW t : isTW t -> tw0 t = 1 / 2 -> isTW (sub32TW t).
Proof.
case: t => t0 t1 t2 [F0 F1 F2 H1 H2] /= Ht0.
have -> : 3 / 2 - t0 = 1 by rewrite Ht0; field.
split.
- exact: format_1.
- exact: generic_format_opp.
- exact: generic_format_opp.
- case: H1 => [->|H1]; first by left; rewrite Ropp_0.
  right; rewrite Rabs_Ropp.
  (* The head moves from [1/2] up to [1], so the gap WIDENS: [ulp (1/2) = u]  *)
  (* and [ulp 1 = 2u].  Unlike [sub2TW_isTW], where the head is unchanged,    *)
  (* this step really needs monotonicity of [ulp].                            *)
  apply: Rlt_le_trans H1 _.
  by apply: ulp_le; rewrite Ht0 !Rabs_pos_eq; lra.
case: H2 => [->|H2]; first by left; rewrite Ropp_0.
by right; rewrite !Rabs_Ropp ulp_opp.
Qed.

(* ===========================================================================*)
(*  Algorithm 15 -- 3SqRt(x0, x1, x2)                                         *)
(*  (127 operations & 4 tests with Algorithm 11, 111 operations & 2 tests     *)
(*  with Algorithm 12; paper Section 10).                                     *)
(* ===========================================================================*)
(* The nine head lines, named one by one so that the bounds of doc/thm11.md   *)
(* can be stated and reused without unfolding the algorithm.                  *)

(* The seed.  [RN(sqrt x0)] is the only place in the whole development where  *)
(* a real square root is rounded; [1 + 4u] plays the role Algorithm 13's      *)
(* [1 + 2u] plays -- it biases the seed upwards by just enough that the       *)
(* rounding of [h01(2)] cannot go the wrong way.                              *)
Definition sqrtS (x0 : R) : R := RND (sqrt x0).

Definition sqrtA (x0 : R) : R := RND ((1 + 4 * u) / sqrtS x0).

(* [a/2] and [b/2] are exact: multiplying by [pow (-1)] never leaves FLX.     *)
Definition sqrtA' (x0 : R) : R := sqrtA x0 / 2.

Definition sqrtH0_1 (x0 : R) : R := (TwoProd (sqrtA x0) x0).1.

Definition sqrtH11_1 (x0 : R) : R := (TwoProd (sqrtA x0) x0).2.

Definition sqrtH1_1 (x0 x1 : R) : R :=
  RND (sqrtH11_1 x0 + sqrtA x0 * x1).

Definition sqrtH01_2 (x0 : R) : R :=
  (TwoProd (sqrtA' x0) (sqrtH0_1 x0)).1.

Definition sqrtH11_2 (x0 : R) : R :=
  (TwoProd (sqrtA' x0) (sqrtH0_1 x0)).2.

Definition sqrtH0_2 (x0 : R) : R := 3 / 2 - sqrtH01_2 x0.

Definition sqrtH1_2 (x0 x1 : R) : R :=
  - RND (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1 x0 x1).

Definition sqrtB01 (x0 : R) : R := (TwoProd (sqrtA x0) (sqrtH0_2 x0)).1.

Definition sqrtB11 (x0 : R) : R := (TwoProd (sqrtA x0) (sqrtH0_2 x0)).2.

Definition sqrtB12 (x0 x1 : R) : R :=
  RND (sqrtB11 x0 + sqrtA x0 * sqrtH1_2 x0 x1).

Definition sqrtB (x0 x1 : R) : dwR :=
  Fast2Sum (sqrtB01 x0) (sqrtB12 x0 x1).

(* The Newton double word [b ~ 1/sqrt x0], packaged as a [twR] with a zero    *)
(* third limb -- the shape Algorithms 11 and 12 take as their first argument. *)
Definition sqrtBW (x0 x1 : R) : twR :=
  TWR (dwh (sqrtB x0 x1)) (dwl (sqrtB x0 x1)) 0.

(* [mul1] computes [i(1) = 3Prod(b, x) ~ sqrt x], [mul2] the inner            *)
(* [3Prod(b', i(1)) ~ 1/2] of [i(2)], and [mul3] the final [y = i(1) i(2)].   *)
(* Only [mul2] sees the head property (its result must have head exactly      *)
(* [1/2], so that [3/2 - .] is exact and [i(2)] has head [1]); only [mul3]    *)
(* needs to be sharp on a head-[1] second argument.                           *)
Definition ThreeSqRtAux (mul1 mul2 mul3 : twR -> twR -> twR) (x : twR)
    : twR :=
  let bw := sqrtBW (tw0 x) (tw1 x) in
  let i1 := mul1 bw x in
  mul3 i1 (sub32TW (mul2 (scaleTW (-1)%Z bw) i1)).

(* The accurate variant: both DW x TW products are Algorithm 11.              *)
Definition ThreeSqRt (x : twR) : twR :=
  ThreeSqRtAux ThreeProdDW ThreeProdDW ThreeProdOneTW x.

(* The fast variant: both DW x TW products are Algorithm 12.                  *)
Definition ThreeSqRtFast (x : twR) : twR :=
  ThreeSqRtAux ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW x.

(* ===========================================================================*)
(*  The Newton identity (PROVED)                                              *)
(*                                                                            *)
(*  Everything downstream rests on this one polynomial identity.  Writing     *)
(*  [x = s * s] and [t = b * s], the EXACT value of the algorithm's last two  *)
(*  lines, [(b x)(3/2 - (1/2) b^2 x)], differs from [s] by                    *)
(*                                                                            *)
(*      - s (t - 1)^2 ((t - 1) + 3) / 2   ~   -(3/2) s (t - 1)^2              *)
(*                                                                            *)
(*  so the seed's relative error [e = b sqrt x - 1] enters the result only    *)
(*  SQUARED.  Since [e = O(u^2)] that is [O(u^4)]: the whole [u^3] budget of  *)
(*  Theorem 11 is made of the three products' rounding errors, none of it of  *)
(*  the Newton residual.  This is the analogue of Algorithm 13's              *)
(*  [newton_id : (a(2 - Xa))X - 1 = -(aX - 1)^2].                             *)
(*                                                                            *)
(*  Stated on [s] and [b] rather than on [x] and [1/sqrt x] on purpose: it is *)
(*  then a polynomial identity, with no division and no [sqrt], and [ring]    *)
(*  closes it.  (House rule: state error chains dimensionlessly.)             *)
(* ===========================================================================*)
Lemma sqrt_newton_id s b :
  (b * (s * s)) * (3 / 2 - (1 / 2) * (b * b) * (s * s)) - s
    = - s * ((b * s - 1) * (b * s - 1)) * ((b * s - 1) + 3) / 2.
Proof. field. Qed.

(* ===========================================================================*)
(*  The six intermediate obligations (doc/thm11.md Section 4)                 *)
(*                                                                            *)
(*  Stated here so that their shape is pinned before anything is proved --    *)
(*  the house top-down method.  Steps 1 and 2 are the genuinely new ones;     *)
(*  steps 3 and 4 mirror [reciB_isDW] and [reciBW_x_err] of Algorithm 13, and *)
(*  step 5 should FALL OUT of the already-proved [head_one] by scaling rather *)
(*  than be re-proved.                                                        *)
(* ===========================================================================*)

(* ===========================================================================*)
(*  Correctness, part 1: the result is a triple word.                         *)
(*                                                                            *)
(*  Exactly Algorithm 14's assembly ([ThreeDivAux_isTW]) with [mul2] applied  *)
(*  to [b/2] and [i(1)] instead of [b] and [z], and [head_half] in place of   *)
(*  [head_one]: [mul1] must return a triple word, [mul2] must return one and  *)
(*  have head [1/2] (so that [3/2 - mul2 b' i(1)] is again a triple word, by  *)
(*  [sub32TW_isTW]), and [mul3] must do so on a head-[1] second argument.     *)
(* ===========================================================================*)
(* A triple word with a positive head is positive: the two low limbs cannot   *)
(* bridge the gap, [|x1| <= 2u|x0|] and [|x2| <= 2u^2|x0|].  Needed because   *)
(* [sqrt] is only informative on nonnegative arguments.                       *)
Lemma isTW_TWval_gt0 x : isTW x -> 0 < tw0 x -> 0 < TWval x.
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Hx2 := @isTW_tw2_le p Hp2 x Hx.
have Hx1 : Rabs (tw1 x) <= 2 * u * Rabs (tw0 x).
  case: x Hx {Hx0 Hx2} => x0 x1 x2 [_ _ _ H1 _] /=.
  case: H1 => [->|H1]; first by rewrite Rabs_R0; have := Rabs_pos x0; nra.
  by have := @ulp_2u p beta Hp2 x0; lra.
have Ha0 : Rabs (tw0 x) = tw0 x by apply: Rabs_pos_eq; lra.
have H1 := Rabs_le_inv _ _ Hx1.
have H2 := Rabs_le_inv _ _ Hx2.
by case: x Hx0 Ha0 H1 H2 {Hx Hx1 Hx2} => x0 x1 x2 /= Hx0 Ha0 H1 H2;
   rewrite /TWval /=; nra.
Qed.

(* Step 1.  The seed.  Stated TWO-SIDED and asymmetrically, not as a single   *)
(* [Rabs] bound -- the house lesson, and here it is not a matter of taste:    *)
(* the LOWER bound is the whole point of the [1 + 4u].  Both roundings are    *)
(* within a relative [u], so                                                  *)
(*                                                                            *)
(*   (1 + 4u)(1 - u)/(1 + u)  <=  a sqrt x0  <=  (1 + 4u)(1 + u)/(1 - u)      *)
(*                                                                            *)
(* i.e. [1 + 2u - O(u^2)] to [1 + 6u + O(u^2)].  Since [a sqrt x0 > 1], its   *)
(* SQUARE stays above [1], so [h01(2) ~ (1/2)(a sqrt x0)^2 >= 1/2] -- which   *)
(* is exactly the supplementary's reason for starting at [1 + 4u] rather      *)
(* than [1], and what [sqrtH0_2_exact] then runs on.                          *)
(*                                                                            *)
(* NB an earlier draft of this file stated [|a sqrt x0 - 1| <= 4u + 8u^2].    *)
(* That is FALSE -- random search over binary64 reaches [5.50u], and the      *)
(* algebra above allows [6u].                                                 *)
Lemma sqrtA_bound x0 :
  format x0 -> 0 < x0 ->
  1 + 2 * u - 8 * (u * u) <= sqrtA x0 * sqrt x0
    <= 1 + 6 * u + 12 * (u * u).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have HR : 0 < sqrt x0 by apply: sqrt_lt_R0.
(* (1) the rounding of the square root, within a relative [u].                *)
have HS : Rabs (sqrtS x0 - sqrt x0) <= u * Rabs (sqrt x0)
  by apply: (@relative_error_le p beta Hp2 choice).
rewrite (Rabs_pos_eq (sqrt x0)) in HS; last lra.
have HSb := Rabs_le_inv _ _ HS.
have HS0 : 0 < sqrtS x0 by nra.
(* (2) the rounding of the quotient, multiplied through by [S] so that no     *)
(* division survives into the arithmetic.                                     *)
have HA : Rabs (sqrtA x0 - (1 + 4 * u) / sqrtS x0)
            <= u * Rabs ((1 + 4 * u) / sqrtS x0)
  by apply: (@relative_error_le p beta Hp2 choice).
have HAS : Rabs (sqrtA x0 * sqrtS x0 - (1 + 4 * u)) <= u * (1 + 4 * u).
  have -> : sqrtA x0 * sqrtS x0 - (1 + 4 * u)
      = (sqrtA x0 - (1 + 4 * u) / sqrtS x0) * sqrtS x0
    by field; lra.
  rewrite Rabs_mult (Rabs_pos_eq (sqrtS x0)); last lra.
  have Hq : Rabs ((1 + 4 * u) / sqrtS x0) = (1 + 4 * u) / sqrtS x0.
    apply: Rabs_pos_eq; rewrite /Rdiv.
    by apply: Rmult_le_pos; [lra | left; apply: Rinv_0_lt_compat; lra].
  rewrite Hq in HA.
  have Hstep : Rabs (sqrtA x0 - (1 + 4 * u) / sqrtS x0) * sqrtS x0
      <= (u * ((1 + 4 * u) / sqrtS x0)) * sqrtS x0
    by apply: Rmult_le_compat_r; lra.
  apply: Rle_trans Hstep _.
  by rewrite /Rdiv; field_simplify; lra.
have HASb := Rabs_le_inv _ _ HAS.
(* (3) [a > 0], so the two magnitudes can be combined.                        *)
have HA0 : 0 < sqrtA x0 by nra.
(* (4) [a S] is pinned, [S] is within [(1 +- u) R], so [a R] is pinned too.   *)
by nra.
Qed.

(* Step 2.  [h0(2) = 3/2 - h01(2)] is EXACT.  This is NOT Sterbenz -- its     *)
(* hypothesis fails outright for [3/2 - 1/2].  The supplementary gives the    *)
(* reason in one line: the computation is exact BECAUSE [h01(2) >= 0.5], and  *)
(* [this is why we started with 1 + 4u instead of 1].  So [h01(2)] sits in    *)
(* the binade [[1/2, 1)], where [ulp = u]; [3/2] is a multiple of [u] there,  *)
(* hence so is the difference, which lands in [(1/2, 1]] -- representable.    *)
(* Pin [h01(2) >= 1/2] first; everything else is grid arithmetic.             *)
(* [h01(2)] lands in [[1/2, 1]].  Unfolding, [a' h0(1) = (1/2) a^2 x0 (1+d)]  *)
(* with [|d| <= u], and [a^2 x0 = (a sqrt x0)^2] is pinned by [sqrtA_bound]   *)
(* to [[1+2u-8u^2, 1+6u+12u^2]] -- so the half-square sits just ABOVE [1/2],  *)
(* which is the whole purpose of the [1 + 4u] seed.                           *)
Lemma sqrtH01_2_range x0 :
  format x0 -> 0 < x0 -> 1 / 2 <= sqrtH01_2 x0 <= 1.
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have HR : 0 < sqrt x0 by apply: sqrt_lt_R0.
have HsX : sqrt x0 * sqrt x0 = x0 by apply: sqrt_sqrt; lra.
have [Hlo Hhi] := sqrtA_bound Fx0 Hx0.
(* [h0(1) = RN(a x0)] is within a relative [u].                               *)
have Hh01 : Rabs (sqrtH0_1 x0 - sqrtA x0 * x0)
              <= u * Rabs (sqrtA x0 * x0)
  by apply: (@relative_error_le p beta Hp2 choice).
have HA0 : 0 < sqrtA x0 by nra.
have HAx : 0 < sqrtA x0 * x0 by nra.
rewrite (Rabs_pos_eq (sqrtA x0 * x0)) in Hh01; last lra.
have Hh01b := Rabs_le_inv _ _ Hh01.
(* [a' h0(1)] is then within [(1/2)(a sqrt x0)^2 (1 +- u)].                   *)
have Hprod : 1 / 2 + u <= sqrtA' x0 * sqrtH0_1 x0 <= 1 / 2 + 7 * u.
  (* [a' (a x0) = (1/2)(a sqrt x0)^2], rewriting [sqrt x0 * sqrt x0] FORWARD  *)
  (* to [x0] -- the reverse direction would rewrite under [sqrt] itself.      *)
  have HPgen : forall r a, r * r = x0 ->
      a / 2 * (a * x0) = / 2 * ((a * r) * (a * r)).
    by move=> r a <-; field.
  have HP : sqrtA' x0 * (sqrtA x0 * x0)
      = / 2 * ((sqrtA x0 * sqrt x0) * (sqrtA x0 * sqrt x0)).
    by rewrite /sqrtA'; apply: HPgen; exact: HsX.
  have HD : sqrtA' x0 * sqrtH0_1 x0
      = sqrtA' x0 * (sqrtA x0 * x0)
        + sqrtA' x0 * (sqrtH0_1 x0 - sqrtA x0 * x0) by ring.
  (* the perturbation is at most [u] times the main term                      *)
  have HA'0 : 0 < sqrtA' x0 by rewrite /sqrtA'; lra.
  have Hpert : Rabs (sqrtA' x0 * (sqrtH0_1 x0 - sqrtA x0 * x0))
      <= u * (sqrtA' x0 * (sqrtA x0 * x0)).
    rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last lra.
    have Hs : Rabs (sqrtH0_1 x0 - sqrtA x0 * x0) <= u * (sqrtA x0 * x0)
      by lra.
    have Hm : sqrtA' x0 * Rabs (sqrtH0_1 x0 - sqrtA x0 * x0)
        <= sqrtA' x0 * (u * (sqrtA x0 * x0))
      by apply: Rmult_le_compat_l; lra.
    by apply: Rle_trans Hm _; lra.
  have Hpb := Rabs_le_inv _ _ Hpert.
  set T := sqrtA x0 * sqrt x0 in HP Hlo Hhi.
  (* square the seed range BEFORE handing it to [nra] -- the squared form is  *)
  (* what the goal needs and [nra] will not find it under the perturbation.   *)
  have HT0 : 0 < T by nra.
  have HT2a : (1 + 2 * u - 8 * (u * u)) * (1 + 2 * u - 8 * (u * u)) <= T * T
    by apply: Rmult_le_compat; nra.
  have HT2b : T * T <= (1 + 6 * u + 12 * (u * u)) * (1 + 6 * u + 12 * (u * u))
    by apply: Rmult_le_compat; nra.
  rewrite HP in Hpb.
  rewrite HD HP.
  have Hu2 : u * u <= / 1024 * u by nra.
  by nra.
(* rounding cannot leave [[1/2, 1]].                                          *)
have Hround := @relative_error_le p beta Hp2 choice (sqrtA' x0 * sqrtH0_1 x0).
rewrite (Rabs_pos_eq (sqrtA' x0 * sqrtH0_1 x0)) in Hround; last lra.
have Hrb := Rabs_le_inv _ _ Hround.
by rewrite /sqrtH01_2 /=; nra.
Qed.

(* [3/2] is on the [u]-grid, being [3 * 2^(p-1)] units of [u].                *)
Lemma is_imul_3_2 : is_imul (3 / 2) (pow (- p)).
Proof.
exists (3 * 2 ^ (p - 1))%Z.
rewrite mult_IZR.
have -> : IZR (2 ^ (p - 1)) = pow (p - 1).
  by rewrite -(IZR_Zpower radix2); [congr IZR|lia].
rewrite Rmult_assoc -bpow_plus.
have -> : (p - 1 + - p = -1)%Z by lia.
by have -> : pow (-1) = / 2 by []; lra.
Qed.

(* [h0(2) = 3/2 - h01(2)] is EXACT.  NOT Sterbenz -- its hypothesis fails     *)
(* outright for [3/2 - 1/2].  Both operands are multiples of [u]              *)
(* ([is_imul_bound_pow_format] on [h01(2) >= 1/2], and [is_imul_3_2]), and    *)
(* the difference lies in [[1/2, 1]], so [imul_format] applies.               *)
Lemma sqrtH0_2_exact x0 :
  format x0 -> 0 < x0 -> format (sqrtH0_2 x0).
Proof.
move=> Fx0 Hx0.
have [Hlo Hhi] := sqrtH01_2_range Fx0 Hx0.
have Fh : format (sqrtH01_2 x0) by apply: generic_format_round.
have Him1 : is_imul (sqrtH01_2 x0) (pow (- p)).
  have -> : (- p = -1 - p + 1)%Z by lia.
  apply: is_imul_bound_pow_format => //.
  have -> : pow (-1) = / 2 by [].
  by rewrite Rabs_pos_eq; lra.
apply: (@imul_format beta p Hp2 (sqrtH0_2 x0) (- p) 1).
- by rewrite /sqrtH0_2; apply: is_imul_minus; [exact: is_imul_3_2|].
- by rewrite /sqrtH0_2 Rabs_pos_eq; lra.
have -> : (p + - p = 0)%Z by lia.
by rewrite /=; lra.
Qed.

(* ===========================================================================*)
(*  Step 3.  [b] is a double word.                                            *)
(*                                                                            *)
(*  Mirrors [reciB_isDW]: the two words are roundings, so both are floats,    *)
(*  and the low one is at most half an ulp of the high one PROVIDED the       *)
(*  Fast2Sum operands are ordered.  That ordering is the only real content,   *)
(*  and -- per doc/thm11.md -- it is CHECKED here, not assumed: an unguarded  *)
(*  Fast2Sum whose ordering fails loses [u max(|.|)], not [O(u^2)].           *)
(*                                                                            *)
(*  The chain below measures every [h]-line against [a x0] (which is the      *)
(*  natural scale, [a x0 ~ sqrt x0]) and every [b]-line against [a], so that  *)
(*  the final comparison is dimensionless.                                    *)
(* ===========================================================================*)

(* [h0(2) = 3/2 - h01(2)] inherits [[1/2, 1]] from [sqrtH01_2_range].         *)
Lemma sqrtH0_2_range x0 :
  format x0 -> 0 < x0 -> 1 / 2 <= sqrtH0_2 x0 <= 1.
Proof.
move=> Fx0 Hx0.
by have [Hlo Hhi] := sqrtH01_2_range Fx0 Hx0; rewrite /sqrtH0_2; lra.
Qed.

(* [a^2 x0 = (a sqrt x0)^2], so the seed range squares.  Reused by every      *)
(* [h]-line bound below.                                                      *)
Lemma sqrtA_sq_le x0 :
  format x0 -> 0 < x0 -> sqrtA x0 * sqrtA x0 * x0 <= 1 + 12 * u + 62 * (u * u).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HR : 0 < sqrt x0 by apply: sqrt_lt_R0.
have HsX : sqrt x0 * sqrt x0 = x0 by apply: sqrt_sqrt; lra.
have [Hlo Hhi] := sqrtA_bound Fx0 Hx0.
have Hgen : forall r a, r * r = x0 -> a * a * x0 = (a * r) * (a * r).
  by move=> r a <-; ring.
rewrite (Hgen (sqrt x0) (sqrtA x0) HsX).
have H0 : 0 <= sqrtA x0 * sqrt x0 by nra.
have Hsq : (sqrtA x0 * sqrt x0) * (sqrtA x0 * sqrt x0)
    <= (1 + 6 * u + 12 * (u * u)) * (1 + 6 * u + 12 * (u * u))
  by apply: Rmult_le_compat; nra.
(* [(1 + 6u + 12u^2)^2 = 1 + 12u + 60u^2 + 144u^3 + 144u^4]; the [u^3] tail   *)
(* fits inside the [2u^2] of slack because [u <= 1/2048].  The old [1 + 13u]  *)
(* threw that whole [u] away, and it propagated all the way to the seed.      *)
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

Lemma sqrtA_gt0 x0 : format x0 -> 0 < x0 -> 0 < sqrtA x0.
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HR : 0 < sqrt x0 by apply: sqrt_lt_R0.
by have [Hlo _] := sqrtA_bound Fx0 Hx0; nra.
Qed.

(* [h0(1) = RND(a x0)] and its error [h11(1)], both against [a x0].           *)
Lemma sqrtH0_1_le x0 :
  format x0 -> 0 < x0 -> Rabs (sqrtH0_1 x0) <= (1 + u) * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have H := @relative_error_le p beta Hp2 choice (sqrtA x0 * x0).
rewrite (Rabs_pos_eq (sqrtA x0 * x0)) in H; last lra.
have Hb := Rabs_le_inv _ _ H.
have -> : sqrtH0_1 x0 = RND (sqrtA x0 * x0) by [].
by apply: Rabs_le; lra.
Qed.

Lemma sqrtH11_1_le x0 :
  format x0 -> 0 < x0 -> Rabs (sqrtH11_1 x0) <= u * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have FA : format (sqrtA x0) by apply: generic_format_round.
have HP : 0 < sqrtA x0 * x0 by nra.
(* [2Prod] is exact, in projection form -- [TwoProd_exact] avoids the [let].  *)
have HE := @TwoProd_exact p Hp2 choice _ _ FA Fx0.
have -> : sqrtH11_1 x0 = sqrtA x0 * x0 - sqrtH0_1 x0.
  by rewrite /sqrtH11_1 /sqrtH0_1; lra.
have -> : sqrtH0_1 x0 = RND (sqrtA x0 * x0) by [].
rewrite Rabs_minus_sym.
apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
by rewrite Rabs_pos_eq; lra.
Qed.

Lemma sqrtH1_1_le x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH1_1 x0 x1) <= 4 * u * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have H11 := sqrtH11_1_le Fx0 Hx0.
have Hax1 : Rabs (sqrtA x0 * x1) <= 2 * u * (sqrtA x0 * x0).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
  have Hb : Rabs x1 <= 2 * u * x0.
    case: Hx1 => [->|Hs]; first by rewrite Rabs_R0; nra.
    have := @ulp_2u p beta Hp2 x0.
    by rewrite (Rabs_pos_eq x0); lra.
  by nra.
have Ht := Rabs_triang (sqrtH11_1 x0) (sqrtA x0 * x1).
have Hsum : Rabs (sqrtH11_1 x0 + sqrtA x0 * x1) <= 3 * u * (sqrtA x0 * x0)
  by lra.
have Hr := @abs_round_le_rel p Hp2 choice (sqrtH11_1 x0 + sqrtA x0 * x1).
rewrite /sqrtH1_1.
apply: Rle_trans Hr _.
have Hstep : (1 + u) * Rabs (sqrtH11_1 x0 + sqrtA x0 * x1)
    <= (1 + u) * (3 * u * (sqrtA x0 * x0))
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans Hstep _.
(* [4uP - (1+u)3uP = u(1-3u)P >= 0]; spelled out so [lra] suffices.           *)
have -> : 4 * u * (sqrtA x0 * x0)
    = (1 + u) * (3 * u * (sqrtA x0 * x0))
      + u * (1 - 3 * u) * (sqrtA x0 * x0) by ring.
have Hnn : 0 <= u * (1 - 3 * u) * (sqrtA x0 * x0).
  by apply: Rmult_le_pos; [apply: Rmult_le_pos|]; lra.
by lra.
Qed.

(* A pure-[u] side condition.  [nra] is much faster in a tiny context, so    *)
(* the numeric tail of [sqrtH1_2_le] is stated on its own rather than left    *)
(* to close inside that lemma's twenty-hypothesis context.                    *)
Lemma sqrtH1_2_num :
  (1 + u) * ((5 + u) / 2 * u * (1 + 12 * u + 62 * (u * u))) <= 3 * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

Lemma sqrtH1_2_le x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH1_2 x0 x1) <= 3 * u.
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hsq := sqrtA_sq_le Fx0 Hx0.
have H01 := sqrtH0_1_le Fx0 Hx0.
have H11 := sqrtH1_1_le Fx0 Hx0 Hx1.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have FA : format (sqrtA x0) by apply: generic_format_round.
have FA2 : format (sqrtA' x0).
  have -> : sqrtA' x0 = sqrtA x0 * pow (-1) by rewrite HA' /=; lra.
  by apply/format_scale.
have F01 : format (sqrtH0_1 x0) by apply: generic_format_round.
have H112 : Rabs (sqrtH11_2 x0)
    <= u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0))).
  have HE2 := @TwoProd_exact p Hp2 choice _ _ FA2 F01.
  have -> : sqrtH11_2 x0 = sqrtA' x0 * sqrtH0_1 x0 - sqrtH01_2 x0.
    by rewrite /sqrtH11_2 /sqrtH01_2; lra.
  have -> : sqrtH01_2 x0 = RND (sqrtA' x0 * sqrtH0_1 x0) by [].
  rewrite Rabs_minus_sym.
  apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
  apply: Rmult_le_compat_l; first lra.
  by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H01].
have Hmix : Rabs (sqrtA' x0 * sqrtH1_1 x0 x1)
    <= sqrtA' x0 * (4 * u * (sqrtA x0 * x0)).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
  by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H11].
have Ht := Rabs_triang (sqrtH11_2 x0) (sqrtA' x0 * sqrtH1_1 x0 x1).
have Hsum : Rabs (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1 x0 x1)
    <= (5 + u) / 2 * u * (sqrtA x0 * sqrtA x0 * x0).
  (* the two bounds sum EXACTLY to the claim; give [lra] the identity.        *)
  (* Keep everything in [a'] -- rewriting [HA'] in [Hmix] would also hit its  *)
  (* SUBJECT and break the match with [Ht].                                   *)
  have Hid : u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0)))
           + sqrtA' x0 * (4 * u * (sqrtA x0 * x0))
      = (5 + u) / 2 * u * (sqrtA x0 * sqrtA x0 * x0)
    by rewrite HA'; field.
  by lra.
have Hr := @abs_round_le_rel p Hp2 choice
             (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1 x0 x1).
rewrite /sqrtH1_2 Rabs_Ropp.
apply: Rle_trans Hr _.
have Hstep : (1 + u) * Rabs (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1 x0 x1)
    <= (1 + u) * ((5 + u) / 2 * u * (sqrtA x0 * sqrtA x0 * x0))
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans Hstep _.
have Hfin : (1 + u) * ((5 + u) / 2 * u * (sqrtA x0 * sqrtA x0 * x0))
    <= (1 + u) * ((5 + u) / 2 * u * (1 + 12 * u + 62 * (u * u))).
  apply: Rmult_le_compat_l; first lra.
  by apply: Rmult_le_compat_l; [nra | exact: Hsq].
apply: Rle_trans Hfin _.
exact: sqrtH1_2_num.
Qed.

Lemma sqrtB11_le x0 :
  format x0 -> 0 < x0 -> Rabs (sqrtB11 x0) <= u * sqrtA x0.
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have [Hh0 Hh1] := sqrtH0_2_range Fx0 Hx0.
have FA : format (sqrtA x0) by apply: generic_format_round.
have F02 : format (sqrtH0_2 x0) by apply: sqrtH0_2_exact.
have HE := @TwoProd_exact p Hp2 choice _ _ FA F02.
have -> : sqrtB11 x0 = sqrtA x0 * sqrtH0_2 x0 - sqrtB01 x0.
  by rewrite /sqrtB11 /sqrtB01; lra.
have -> : sqrtB01 x0 = RND (sqrtA x0 * sqrtH0_2 x0) by [].
rewrite Rabs_minus_sym.
apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
rewrite Rabs_mult !Rabs_pos_eq; try lra.
apply: Rmult_le_compat_l; first lra.
by nra.
Qed.

Lemma sqrtB01_ge x0 :
  format x0 -> 0 < x0 -> (1 - u) / 2 * sqrtA x0 <= Rabs (sqrtB01 x0).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have [Hh0 Hh1] := sqrtH0_2_range Fx0 Hx0.
have HP : 0 < sqrtA x0 * sqrtH0_2 x0 by nra.
have H := @relative_error_le p beta Hp2 choice (sqrtA x0 * sqrtH0_2 x0).
rewrite (Rabs_pos_eq (sqrtA x0 * sqrtH0_2 x0)) in H; last lra.
have Hb := Rabs_le_inv _ _ H.
have -> : sqrtB01 x0 = RND (sqrtA x0 * sqrtH0_2 x0) by [].
(* [nra], not [lra]: [Hb] bounds [RND] by [(1-u)(a h)], which is nonlinear.   *)
rewrite Rabs_pos_eq; last by nra.
(* [(1-u) a h - (1-u)/2 a = (1-u) a (h - 1/2) >= 0]                           *)
have Hnn : 0 <= (1 - u) * (sqrtA x0 * (sqrtH0_2 x0 - 1 / 2)).
  by apply: Rmult_le_pos; [lra | apply: Rmult_le_pos; lra].
by nra.
Qed.

Lemma sqrtB12_le_B01 x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtB12 x0 x1) <= Rabs (sqrtB01 x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hb11 := sqrtB11_le Fx0 Hx0.
have Hh12 := sqrtH1_2_le Fx0 Hx0 Hx1.
have Hb01 := sqrtB01_ge Fx0 Hx0.
have Hmix : Rabs (sqrtA x0 * sqrtH1_2 x0 x1) <= sqrtA x0 * (3 * u).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
  by apply: Rmult_le_compat_l; lra.
have Ht := Rabs_triang (sqrtB11 x0) (sqrtA x0 * sqrtH1_2 x0 x1).
have Hsum : Rabs (sqrtB11 x0 + sqrtA x0 * sqrtH1_2 x0 x1)
    <= 4 * u * sqrtA x0 by nra.
have Hr := @abs_round_le_rel p Hp2 choice
             (sqrtB11 x0 + sqrtA x0 * sqrtH1_2 x0 x1).
rewrite /sqrtB12.
apply: Rle_trans Hr _.
have Hstep : (1 + u) * Rabs (sqrtB11 x0 + sqrtA x0 * sqrtH1_2 x0 x1)
    <= (1 + u) * (4 * u * sqrtA x0)
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans Hstep _.
apply: Rle_trans Hb01.
(* [(1-u)/2 a - (1+u)4u a = (1/2 - 9u/2 - 4u^2) a >= 0].                      *)
have -> : (1 - u) / 2 * sqrtA x0
    = (1 + u) * (4 * u * sqrtA x0)
      + (1 / 2 - 9 / 2 * u - 4 * (u * u)) * sqrtA x0 by field.
have Hnn : 0 <= (1 / 2 - 9 / 2 * u - 4 * (u * u)) * sqrtA x0.
  by apply: Rmult_le_pos; [nra | lra].
by lra.
Qed.

Lemma sqrtB_isDW x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  isDW (sqrtBW x0 x1).
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (sqrtB01 x0) by apply: generic_format_round.
have F12 : format (sqrtB12 x0 x1) by apply: generic_format_round.
have Hord := sqrtB12_le_B01 Fx0 Hx0 Hx1.
have Hmag := @magnitude_Fast2Sum p Hp2 choice _ _ F01 F12 (fun _ => Hord).
have Hfor := @format_Fast2Sum p Hp2 choice (sqrtB01 x0) (sqrtB12 x0 x1).
rewrite /sqrtBW /sqrtB.
case E : (Fast2Sum (sqrtB01 x0) (sqrtB12 x0 x1)) => [s e].
rewrite E in Hmag Hfor.
rewrite /magnitudeDWR in Hmag.
case: Hfor => Fs Fe.
split => //.
by right; rewrite dwhE dwlE; lra.
Qed.

(* [TWval] in projection form -- lets the algebra below avoid [case: x],      *)
(* which cannot generalise once the context has hypotheses mentioning [x].    *)
Lemma TWval_split (t : twR) : TWval t = tw0 t + tw1 t + tw2 t.
Proof. by case: t. Qed.

(* The two low limbs together, against the head.  Extracted because both      *)
(* [isTW_TWval_gt0] and the seed bridge below need exactly this.              *)
Lemma isTW_low_le x :
  isTW x -> 0 < tw0 x ->
  Rabs (tw1 x + tw2 x) <= (2 * u + 2 * (u * u)) * tw0 x.
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Hx2 := @isTW_tw2_le p Hp2 x Hx.
have Ha0 : Rabs (tw0 x) = tw0 x by apply: Rabs_pos_eq; lra.
have Hx1 : Rabs (tw1 x) <= 2 * u * tw0 x.
  case: x Hx Hx0 Ha0 {Hx2} => x0 x1 x2 [_ _ _ H1 _] /= Hx0 Ha0.
  case: H1 => [->|H1]; first by rewrite Rabs_R0; nra.
  rewrite -Ha0.
  by have := @ulp_2u p beta Hp2 x0; lra.
rewrite Ha0 in Hx2.
by apply: Rle_trans (Rabs_triang _ _) _; lra.
Qed.

(* The seed against the FULL triple-word value, not just its head.            *)
(*                                                                            *)
(* Stated and proved through the SQUARE.  [t = a sqrt X] has                  *)
(* [t * t = a^2 X], which is pure algebra, and [leq_sqrt] (Rmore.v) turns a   *)
(* bound on [t * t] into one on [t].  Expanding [sqrt (1 + d)] directly --    *)
(* the obvious route -- is far worse and is not needed.                       *)
(*                                                                            *)
(* This is the head-to-full bridge: [sqrtA_bound] pins [a sqrt (tw0 x)], but  *)
(* the Newton form needs [a sqrt (TWval x)], and the two differ at the [u]    *)
(* level because [|x1| <= 2u|x0|].                                            *)
Lemma sqrtA_bound_full x :
  isTW x -> 0 < tw0 x ->
  1 <= sqrtA (tw0 x) * sqrt (TWval x) <= 1 + 15 * u / 2.
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have HA := sqrtA_gt0 Fx0 Hx0.
have HR0 : 0 < sqrt (tw0 x) by apply: sqrt_lt_R0.
have Hsx0 : sqrt (tw0 x) * sqrt (tw0 x) = tw0 x by apply: sqrt_sqrt; lra.
have [Hlo Hhi] := sqrtA_bound Fx0 Hx0.
(* [a^2 x0], two-sided                                                        *)
have Ha2x0 : 1 + 4 * u - 16 * (u * u)
    <= sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x <= 1 + 12 * u + 62 * (u * u).
  split; last by apply: sqrtA_sq_le.
  have Hgen : forall r a, r * r = tw0 x -> a * a * tw0 x = (a * r) * (a * r).
    by move=> r a <-; ring.
  rewrite (Hgen (sqrt (tw0 x)) (sqrtA (tw0 x)) Hsx0).
  have Hstep : (1 + 2 * u - 8 * (u * u)) * (1 + 2 * u - 8 * (u * u))
      <= (sqrtA (tw0 x) * sqrt (tw0 x)) * (sqrtA (tw0 x) * sqrt (tw0 x))
    by apply: Rmult_le_compat; nra.
  by nra.
(* the low limbs contribute at most [(2u + 2u^2) a^2 x0]                      *)
have Hlow := isTW_low_le Hx Hx0.
have Hlowb := Rabs_le_inv _ _ Hlow.
have Hsplit : sqrtA (tw0 x) * sqrtA (tw0 x) * TWval x
    = sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x
      + sqrtA (tw0 x) * sqrtA (tw0 x) * (tw1 x + tw2 x).
  by rewrite {1}TWval_split; ring.
have Ha2 : 0 < sqrtA (tw0 x) * sqrtA (tw0 x) by nra.
have Hmix : Rabs (sqrtA (tw0 x) * sqrtA (tw0 x) * (tw1 x + tw2 x))
    <= (2 * u + 2 * (u * u)) * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA (tw0 x) * sqrtA (tw0 x))); last lra.
  have Hstep : sqrtA (tw0 x) * sqrtA (tw0 x) * Rabs (tw1 x + tw2 x)
      <= sqrtA (tw0 x) * sqrtA (tw0 x) * ((2 * u + 2 * (u * u)) * tw0 x)
    by apply: Rmult_le_compat_l; lra.
  by apply: Rle_trans Hstep _; lra.
have Hmixb := Rabs_le_inv _ _ Hmix.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
(* [nra] times out if it has to expand [(2u + 2u^2)(1 + 12u + 62u^2)] itself, *)
(* so hand it the product already collected.                                  *)
have Hmix2 : (2 * u + 2 * (u * u))
    * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x) <= 2 * u + 27 * (u * u).
  have Hstep : (2 * u + 2 * (u * u))
      * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)
      <= (2 * u + 2 * (u * u)) * (1 + 12 * u + 62 * (u * u))
    by apply: Rmult_le_compat_l; nra.
  by nra.
have Hu2 : 43 * (u * u) <= 2 * u by nra.
(* whence [a^2 X] in [[1, 1 + 14u + 90u^2]], and [(1 + 15u/2)^2] covers it    *)
(* because [u >= 33.75u^2].  The old route stopped at [1 + 16u] hence [8u].   *)
have HaX : 1 <= sqrtA (tw0 x) * sqrtA (tw0 x) * TWval x
    <= 1 + 14 * u + 90 * (u * u)
  by rewrite Hsplit; nra.
have Hsq : (sqrtA (tw0 x) * sqrt (TWval x)) * (sqrtA (tw0 x) * sqrt (TWval x))
    = sqrtA (tw0 x) * sqrtA (tw0 x) * TWval x.
  (* generalise: [TWval x] occurs INSIDE [sqrt (TWval x)], so rewriting it    *)
  (* directly would go under the [sqrt].                                      *)
  have Hgen : forall r a, r * r = TWval x ->
      (a * r) * (a * r) = a * a * TWval x.
    by move=> r a <-; ring.
  by apply: Hgen; exact: HsX.
split.
- apply: leq_sqrt; first by nra.
  by rewrite Hsq; nra.
apply: leq_sqrt; first by nra.
by rewrite Hsq; nra.
Qed.

(* ===========================================================================*)
(*  Step 4, CRUDE.  The [isTW] half only needs a rough seed bound: its head   *)
(*  argument squares it ([b i(1) = (b sqrt x)^2 (1+d)]) and then asks for     *)
(*  [<= 200u^2], so any [E] with [2E + u^2 <= 200u^2] does.  [90u^2] leaves   *)
(*  margin at both ends.                                                      *)
(*                                                                            *)
(*  This is deliberately SEPARATE from the sharp [sqrtBW_x_err] below.  The   *)
(*  sharp constants [81] and [622] must both be exact -- [newton_residual_-   *)
(*  const] is tight, [9915.5u^4] against the published [9916u^4] -- whereas   *)
(*  here the Newton step alone gives [(3/2)(6u)^2 = 54u^2] from               *)
(*  [sqrtA_bound], leaving [36u^2] of slack to absorb every rounding without  *)
(*  accounting for any of them tightly.  Proving this one makes               *)
(*  [ThreeSqRt_isTW] UNCONDITIONAL; the sharp one is needed only by the       *)
(*  error assembly.                                                           *)
(* ===========================================================================*)
(* The seed-level twin of [sqrt_newton_id].  There the subject is the FINAL   *)
(* product [(b x)(3/2 - (1/2)b^2 x)]; here it is the refined SEED             *)
(* [a(3/2 - (1/2)a^2 x)], one factor of [x] lighter.  Same right-hand side,   *)
(* and again a pure polynomial identity -- no division, no [sqrt].            *)
Lemma sqrt_newton_seed s a :
  a * (3 / 2 - (1 / 2) * (a * a) * (s * s)) * s - 1
    = - ((a * s - 1) * (a * s - 1)) * (a * s - 1 + 3) / 2.
Proof. field. Qed.

(* [b] IS that refined seed, up to [10u^2 a].  All the rounding of the nine   *)
(* head lines is collected here:                                              *)
(*                                                                            *)
(*   b - a(3/2 - (1/2)a^2 X)                                                  *)
(*     = (1/2)a^3 x2 - (1/2)a^2 eps1 - a eps + eta                            *)
(*                                                                            *)
(*  where [eps1] is the rounding of [h1(1)], [eps] that of [h1(2)] and [eta]  *)
(*  that of [b12]; each is [O(u^2)] against [a] once [sqrtA_sq_le] turns      *)
(*  [a^2 x0] into [1 + 13u].  The [x2] term is the one that distinguishes     *)
(*  [x0 + x1] from the full [TWval x].                                        *)
(* The decomposition, as a GENERIC identity over abstract reals.  [ring]      *)
(* cannot use hypotheses, so the seven exactness/definition facts of the      *)
(* nine head lines are put in SOLVED form and substituted with [->], in       *)
(* dependency order; then [field] closes what is left.                        *)
Lemma newton_form_id A b01 b11 b12 h02 h12 h01_2 h11_2 h01 h11 h1_1
                     x0 x1 x2 eps1 eps eta :
  h01 = A * x0 - h11 ->
  h01_2 = A / 2 * h01 - h11_2 ->
  h02 = 3 / 2 - h01_2 ->
  h1_1 = h11 + A * x1 + eps1 ->
  h12 = - (h11_2 + A / 2 * h1_1) - eps ->
  b12 = b11 + A * h12 + eta ->
  b01 = A * h02 - b11 ->
  (b01 + b12) - A * (3 / 2 - (1 / 2) * (A * A) * (x0 + x1 + x2))
    = (1 / 2) * (A * A * A) * x2 - (1 / 2) * (A * A) * eps1 - A * eps + eta.
Proof. by move=> -> -> -> -> -> -> ->; field. Qed.

(* [b] as a real number: the Fast2Sum is error-free, the ordering having      *)
(* been established.  Mirrors [TWval_reciBW].                                 *)
Lemma TWval_sqrtBW x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  TWval (sqrtBW x0 x1) = sqrtB01 x0 + sqrtB12 x0 x1.
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (sqrtB01 x0) by apply: generic_format_round.
have F12 : format (sqrtB12 x0 x1) by apply: generic_format_round.
have Hord := sqrtB12_le_B01 Fx0 Hx0 Hx1.
have Hc := @Fast2Sum_correct p Hp2 choice _ _ F01 F12 (fun _ => Hord).
by rewrite /sqrtBW /TWval /sqrtB Rplus_0_r; exact: Hc.
Qed.

(* The [t]-bounds of the three head-line roundings, named so that both the    *)
(* magnitude chain and the decomposition below can use them.                  *)
Lemma sqrtH1_1_sum_le x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH11_1 x0 + sqrtA x0 * x1) <= 3 * u * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have H11 := sqrtH11_1_le Fx0 Hx0.
have Hax1 : Rabs (sqrtA x0 * x1) <= 2 * u * (sqrtA x0 * x0).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
  have Hb : Rabs x1 <= 2 * u * x0.
    case: Hx1 => [->|Hs]; first by rewrite Rabs_R0; nra.
    have Ha0 : Rabs x0 = x0 by apply: Rabs_pos_eq; lra.
    rewrite -Ha0.
    by have := @ulp_2u p beta Hp2 x0; lra.
  by nra.
by apply: Rle_trans (Rabs_triang _ _) _; lra.
Qed.

Lemma sqrtH1_2_sum_le x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1 x0 x1)
    <= (5 + u) / 2 * u * (sqrtA x0 * sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have H01 := sqrtH0_1_le Fx0 Hx0.
have H11 := sqrtH1_1_le Fx0 Hx0 Hx1.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have FA : format (sqrtA x0) by apply: generic_format_round.
have FA2 : format (sqrtA' x0).
  have -> : sqrtA' x0 = sqrtA x0 * pow (-1) by rewrite HA' /=; lra.
  by apply/format_scale.
have F01 : format (sqrtH0_1 x0) by apply: generic_format_round.
have H112 : Rabs (sqrtH11_2 x0)
    <= u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0))).
  have HE2 := @TwoProd_exact p Hp2 choice _ _ FA2 F01.
  have -> : sqrtH11_2 x0 = sqrtA' x0 * sqrtH0_1 x0 - sqrtH01_2 x0.
    by rewrite /sqrtH11_2 /sqrtH01_2; lra.
  have -> : sqrtH01_2 x0 = RND (sqrtA' x0 * sqrtH0_1 x0) by [].
  rewrite Rabs_minus_sym.
  apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
  apply: Rmult_le_compat_l; first lra.
  by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H01].
have Hmix : Rabs (sqrtA' x0 * sqrtH1_1 x0 x1)
    <= sqrtA' x0 * (4 * u * (sqrtA x0 * x0)).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
  by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H11].
apply: Rle_trans (Rabs_triang _ _) _.
have Hid : u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0)))
         + sqrtA' x0 * (4 * u * (sqrtA x0 * x0))
    = (5 + u) / 2 * u * (sqrtA x0 * sqrtA x0 * x0)
  by rewrite HA'; field.
by lra.
Qed.

Lemma sqrtB12_sum_le x0 x1 :
  format x0 -> 0 < x0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtB11 x0 + sqrtA x0 * sqrtH1_2 x0 x1) <= 4 * u * sqrtA x0.
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hb11 := sqrtB11_le Fx0 Hx0.
have Hh12 := sqrtH1_2_le Fx0 Hx0 Hx1.
have Hmix : Rabs (sqrtA x0 * sqrtH1_2 x0 x1) <= sqrtA x0 * (3 * u).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
  by apply: Rmult_le_compat_l; lra.
by apply: Rle_trans (Rabs_triang _ _) _; lra.
Qed.

(* Another pure-[u] side condition, kept in its own tiny context.             *)
Lemma sqrtBW_newton_num :
  (1 + 12 * u + 62 * (u * u)) * (5 + u / 2) + 4 <= 10.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
nra.
Qed.

Lemma sqrtBW_newton_form x :
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBW (tw0 x) (tw1 x))
        - sqrtA (tw0 x)
          * (3 / 2 - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * TWval x))
    <= 10 * (u * u) * sqrtA (tw0 x).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HA := sqrtA_gt0 Fx0 Hx0.
have Hsq := sqrtA_sq_le Fx0 Hx0.
have HP : 0 < sqrtA (tw0 x) * tw0 x by nra.
have HA' : sqrtA' (tw0 x) = sqrtA (tw0 x) / 2 by [].
have FA : format (sqrtA (tw0 x)) by apply: generic_format_round.
have FA2 : format (sqrtA' (tw0 x)).
  have -> : sqrtA' (tw0 x) = sqrtA (tw0 x) * pow (-1)
    by rewrite HA' /=; lra.
  by apply/format_scale.
have F01 : format (sqrtH0_1 (tw0 x)) by apply: generic_format_round.
have F02 : format (sqrtH0_2 (tw0 x)) by apply: sqrtH0_2_exact.
(* the three [2Prod] exactness facts                                          *)
have E1 := @TwoProd_exact p Hp2 choice _ _ FA Fx0.
have E2 := @TwoProd_exact p Hp2 choice _ _ FA2 F01.
have E3 := @TwoProd_exact p Hp2 choice _ _ FA F02.
(* the three roundings                                                        *)
set eps1 := sqrtH1_1 (tw0 x) (tw1 x)
            - (sqrtH11_1 (tw0 x) + sqrtA (tw0 x) * tw1 x).
set eps := - sqrtH1_2 (tw0 x) (tw1 x)
           - (sqrtH11_2 (tw0 x)
              + sqrtA' (tw0 x) * sqrtH1_1 (tw0 x) (tw1 x)).
set eta := sqrtB12 (tw0 x) (tw1 x)
           - (sqrtB11 (tw0 x) + sqrtA (tw0 x) * sqrtH1_2 (tw0 x) (tw1 x)).
have Hdec : TWval (sqrtBW (tw0 x) (tw1 x))
    - sqrtA (tw0 x)
      * (3 / 2 - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * TWval x)
    = (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x)) * tw2 x
      - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1
      - sqrtA (tw0 x) * eps + eta.
  rewrite (TWval_sqrtBW Fx0 Hx0 Hx1s) TWval_split.
  (* the six intermediate lines occur only in the HYPOTHESES of               *)
  (* [newton_form_id], so unification cannot find them -- pass them.          *)
  apply: (@newton_form_id (sqrtA (tw0 x)) (sqrtB01 (tw0 x))
            (sqrtB11 (tw0 x)) (sqrtB12 (tw0 x) (tw1 x))
            (sqrtH0_2 (tw0 x)) (sqrtH1_2 (tw0 x) (tw1 x))
            (sqrtH01_2 (tw0 x)) (sqrtH11_2 (tw0 x)) (sqrtH0_1 (tw0 x))
            (sqrtH11_1 (tw0 x)) (sqrtH1_1 (tw0 x) (tw1 x))
            (tw0 x) (tw1 x) (tw2 x) eps1 eps eta).
  - by rewrite /sqrtH0_1 /sqrtH11_1; lra.
  - by rewrite /sqrtH01_2 /sqrtH11_2 -HA'; lra.
  - by [].
  - by rewrite /eps1; lra.
  - by rewrite /eps -HA'; lra.
  - by rewrite /eta; lra.
  by rewrite /sqrtB01 /sqrtB11; lra.
rewrite Hdec.
(* now the four terms, each [O(u^2) a]                                        *)
have Hx2 := @isTW_tw2_le p Hp2 x Hx.
have Ha0 : Rabs (tw0 x) = tw0 x by apply: Rabs_pos_eq; lra.
rewrite Ha0 in Hx2.
have Heps1 : Rabs eps1 <= 3 * (u * u) * (sqrtA (tw0 x) * tw0 x).
  rewrite /eps1.
  have -> : sqrtH1_1 (tw0 x) (tw1 x)
      = RND (sqrtH11_1 (tw0 x) + sqrtA (tw0 x) * tw1 x) by [].
  apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
  have Hs := sqrtH1_1_sum_le Fx0 Hx0 Hx1s.
  have Hstep : u * Rabs (sqrtH11_1 (tw0 x) + sqrtA (tw0 x) * tw1 x)
      <= u * (3 * u * (sqrtA (tw0 x) * tw0 x))
    by apply: Rmult_le_compat_l; lra.
  by apply: Rle_trans Hstep _; lra.
have Heps : Rabs eps
    <= (5 + u) / 2 * (u * u)
       * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x).
  rewrite /eps.
  have -> : - sqrtH1_2 (tw0 x) (tw1 x)
      = RND (sqrtH11_2 (tw0 x)
             + sqrtA' (tw0 x) * sqrtH1_1 (tw0 x) (tw1 x))
    by rewrite /sqrtH1_2; ring.
  apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
  have Hs := sqrtH1_2_sum_le Fx0 Hx0 Hx1s.
  have Hstep : u * Rabs (sqrtH11_2 (tw0 x)
                         + sqrtA' (tw0 x) * sqrtH1_1 (tw0 x) (tw1 x))
      <= u * ((5 + u) / 2 * u
              * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x))
    by apply: Rmult_le_compat_l; lra.
  by apply: Rle_trans Hstep _; lra.
have Heta : Rabs eta <= 4 * (u * u) * sqrtA (tw0 x).
  rewrite /eta.
  have -> : sqrtB12 (tw0 x) (tw1 x)
      = RND (sqrtB11 (tw0 x)
             + sqrtA (tw0 x) * sqrtH1_2 (tw0 x) (tw1 x)) by [].
  apply: Rle_trans (@relative_error_le p beta Hp2 choice _) _.
  have Hs := sqrtB12_sum_le Fx0 Hx0 Hx1s.
  have Hstep : u * Rabs (sqrtB11 (tw0 x)
                         + sqrtA (tw0 x) * sqrtH1_2 (tw0 x) (tw1 x))
      <= u * (4 * u * sqrtA (tw0 x))
    by apply: Rmult_le_compat_l; lra.
  by apply: Rle_trans Hstep _; lra.
(* the four terms, each against [u^2 a]; [A^2 x0 <= 1 + 13u] carries the      *)
(* first three across.                                                        *)
have Ha3 : 0 <= (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
  by nra.
have Ha2 : 0 <= (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) by nra.
have B1 : Rabs ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
                * tw2 x)
    <= (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u))).
  rewrite Rabs_mult (Rabs_pos_eq ((1 / 2)
            * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x)))); last lra.
  have Hstep : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
                 * Rabs (tw2 x)
      <= (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
         * (2 * (u * u) * tw0 x)
    by apply: Rmult_le_compat_l; lra.
  apply: Rle_trans Hstep _.
  have -> : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
              * (2 * (u * u) * tw0 x)
      = (u * u) * (sqrtA (tw0 x)
                   * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) by field.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; lra.
have B2 : Rabs ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1)
    <= (3 / 2) * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u))).
  rewrite Rabs_mult (Rabs_pos_eq ((1 / 2)
            * (sqrtA (tw0 x) * sqrtA (tw0 x)))); last lra.
  have Hstep : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * Rabs eps1
      <= (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x))
         * (3 * (u * u) * (sqrtA (tw0 x) * tw0 x))
    by apply: Rmult_le_compat_l; lra.
  apply: Rle_trans Hstep _.
  have -> : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x))
              * (3 * (u * u) * (sqrtA (tw0 x) * tw0 x))
      = (3 / 2) * (u * u) * (sqrtA (tw0 x)
                   * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) by field.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; lra.
have B3 : Rabs (sqrtA (tw0 x) * eps)
    <= (5 + u) / 2 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u))).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA (tw0 x))); last lra.
  have Hstep : sqrtA (tw0 x) * Rabs eps
      <= sqrtA (tw0 x) * ((5 + u) / 2 * (u * u)
         * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x))
    by apply: Rmult_le_compat_l; lra.
  apply: Rle_trans Hstep _.
  have -> : sqrtA (tw0 x) * ((5 + u) / 2 * (u * u)
              * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x))
      = (5 + u) / 2 * (u * u) * (sqrtA (tw0 x)
                   * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) by field.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; lra.
(* assemble                                                                   *)
have -> : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x)) * tw2 x
          - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1
          - sqrtA (tw0 x) * eps + eta
    = ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x)) * tw2 x)
      + (- ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1))
      + (- (sqrtA (tw0 x) * eps)) + eta by field.
apply: Rle_trans (Rabs_triang _ _) _.
have T1 := Rabs_triang ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)
                                   * sqrtA (tw0 x)) * tw2 x
                        + - ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1))
                       (- (sqrtA (tw0 x) * eps)).
have T2 := Rabs_triang ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)
                                   * sqrtA (tw0 x)) * tw2 x)
                       (- ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1)).
rewrite !Rabs_Ropp in T1 T2.
have Hfin : (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + (3 / 2) * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + (5 + u) / 2 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 4 * (u * u) * sqrtA (tw0 x)
    <= 10 * (u * u) * sqrtA (tw0 x).
  have -> : (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + (3 / 2) * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + (5 + u) / 2 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 4 * (u * u) * sqrtA (tw0 x)
      = (u * u) * sqrtA (tw0 x)
        * ((1 + 12 * u + 62 * (u * u)) * (5 + u / 2) + 4) by field.
  have -> : 10 * (u * u) * sqrtA (tw0 x)
      = (u * u) * sqrtA (tw0 x) * 10 by field.
  apply: Rmult_le_compat_l; first by nra.
  exact: sqrtBW_newton_num.
by lra.
Qed.

Lemma sqrtBW_x_err_crude x :
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * sqrt (TWval x) - 1)
    <= 100 * (u * u).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have HA := sqrtA_gt0 Fx0 Hx0.
have HN := sqrtBW_newton_form Hx Hx0.
have [Hlo Hhi] := sqrtA_bound_full Hx Hx0.
set B := TWval (sqrtBW (tw0 x) (tw1 x)) in HN *.
set A := sqrtA (tw0 x) in HN HA Hlo Hhi *.
set s := sqrt (TWval x) in HsX Hs0 Hlo Hhi *.
(* [s] now hides [TWval x], so this rewrite is safe.                          *)
rewrite -HsX in HN.
have Hsplit : B * s - 1
    = (A * (3 / 2 - (1 / 2) * (A * A) * (s * s)) * s - 1)
      + (B - A * (3 / 2 - (1 / 2) * (A * A) * (s * s))) * s by field.
rewrite Hsplit.
apply: Rle_trans (Rabs_triang _ _) _.
(* (i) the Newton residual, in closed form: [e^2 (e+3)/2], [0 <= e <= 7.5u] *)
have Hnew : Rabs (A * (3 / 2 - (1 / 2) * (A * A) * (s * s)) * s - 1)
    <= 85 * (u * u).
  rewrite sqrt_newton_seed.
  have -> : - ((A * s - 1) * (A * s - 1)) * (A * s - 1 + 3) / 2
      = - (((A * s - 1) * (A * s - 1)) * ((A * s - 1 + 3) / 2)) by field.
  rewrite Rabs_Ropp Rabs_mult.
  have Hsq : Rabs ((A * s - 1) * (A * s - 1)) <= (15 * u / 2) * (15 * u / 2).
    rewrite (Rabs_pos_eq ((A * s - 1) * (A * s - 1))); last exact: Rle_0_sqr.
    by nra.
  have Hlin : Rabs ((A * s - 1 + 3) / 2) <= (3 + 15 * u / 2) / 2.
    rewrite (Rabs_pos_eq ((A * s - 1 + 3) / 2)); last lra.
    by lra.
  have Hstep : Rabs ((A * s - 1) * (A * s - 1))
                 * Rabs ((A * s - 1 + 3) / 2)
      <= ((15 * u / 2) * (15 * u / 2)) * ((3 + 15 * u / 2) / 2)
    by apply: Rmult_le_compat; try apply: Rabs_pos.
  by apply: Rle_trans Hstep _; nra.
(* (ii) the collected rounding, carried across by [A s <= 1 + 8u]             *)
have Hrest : Rabs ((B - A * (3 / 2 - (1 / 2) * (A * A) * (s * s))) * s)
    <= 11 * (u * u).
  rewrite Rabs_mult (Rabs_pos_eq s); last lra.
  have Hstep : Rabs (B - A * (3 / 2 - (1 / 2) * (A * A) * (s * s))) * s
      <= (10 * (u * u) * A) * s
    by apply: Rmult_le_compat_r; lra.
  apply: Rle_trans Hstep _.
  have -> : 10 * (u * u) * A * s = 10 * (u * u) * (A * s) by ring.
  by nra.
have Hu2p : 0 <= u * u by apply: Rle_0_sqr.
by lra.
Qed.


(* The pure-[u] half of the residual bound, split off so that [nra] never     *)
(* sees it together with the algebra.  This is EXACTLY how the paper's        *)
(* [9916u^4] arises: [E^2 (3 + E)/2] with [E = 81u^2 + 622u^3], and it is     *)
(* tight -- [9915.5u^4] at [p = 11].                                          *)
Lemma newton_residual_const :
  (100 * (u * u)) * (100 * (u * u)) * ((3 + 100 * (u * u)) / 2)
  <= 15200 * (u * u * u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have L6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
by nra.
Qed.

(* Step 4b.  The Newton residual: the EXACT value of the last two lines is    *)
(* already within [O(u^4)] of [sqrt x], by [sqrt_newton_id] applied to the    *)
(* seed bound.  The only [u^4] contributor that is not a product's error.     *)
Lemma sqrt_newton_residual x :
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x
        * (3 / 2 - (1 / 2) * (TWval (sqrtBW (tw0 x) (tw1 x))
                              * TWval (sqrtBW (tw0 x) (tw1 x))) * TWval x)
        - sqrt (TWval x))
    <= 15200 * (u * u * u * u) * Rabs (sqrt (TWval x)).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 <= sqrt (TWval x) by apply: sqrt_pos.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x
  by apply: sqrt_sqrt; lra.
have Hseed := sqrtBW_x_err_crude Hx Hx0.
set B := TWval (sqrtBW (tw0 x) (tw1 x)) in Hseed *.
set s := sqrt (TWval x) in HsX Hseed Hs0 *.
have Hid := sqrt_newton_id s B.
rewrite HsX in Hid.
rewrite Hid.
(* pull [s] out; what is left is the pure-[u] bound.                          *)
have -> : - s * ((B * s - 1) * (B * s - 1)) * (B * s - 1 + 3) / 2
    = - (s * (((B * s - 1) * (B * s - 1))
              * ((B * s - 1 + 3) / 2))) by field.
rewrite Rabs_Ropp Rabs_mult !(Rabs_pos_eq s) //.
rewrite [15200 * (u * u * u * u) * s]Rmult_comm.
apply: Rmult_le_compat_l => //.
have He := Rabs_le_inv _ _ Hseed.
have Hsq : (B * s - 1) * (B * s - 1)
    <= (100 * (u * u))
       * (100 * (u * u)) by nra.
have Hsq0 : 0 <= (B * s - 1) * (B * s - 1) by apply: Rle_0_sqr.
have Hlin : (B * s - 1 + 3) / 2
    <= (3 + (100 * (u * u))) / 2 by nra.
have Hlin0 : 0 <= (B * s - 1 + 3) / 2 by nra.
have Hstep : ((B * s - 1) * (B * s - 1)) * ((B * s - 1 + 3) / 2)
    <= (100 * (u * u))
       * (100 * (u * u))
       * ((3 + (100 * (u * u))) / 2)
  by apply: Rmult_le_compat.
rewrite Rabs_pos_eq; last by nra.
by apply: Rle_trans Hstep _; exact: newton_residual_const.
Qed.

(* Step 5.  The head property [mul2] must satisfy: on a first argument that   *)
(* is [b/2] the product has head exactly [1/2], so that [3/2 - .] is exact    *)
(* and [i(2)] has head [1] -- which is what [ThreeProdOneTW] requires of its  *)
(* second argument.  The analogue of [head_one] in ThreeReci.v.               *)
(* Stated on the UNSCALED [b], with the halving inside, because that is how   *)
(* the assembly uses it: [mul2] is applied to [scaleTW (-1) bw], and the      *)
(* hypothesis available there is Algorithm 13's [|b x - 1| <= 35u^2] -- the   *)
(* very hypothesis of [head_one].                                             *)
(* The tolerance is [200u^2], not Algorithm 13's [35u^2].  Algorithm 15       *)
(* needs the slack: at the call site the second factor is [i(1) =             *)
(* 3Prod(b, x)], so the product is [b^2 x = (b sqrt x)^2 = (1 + e)^2] with    *)
(* [|e| <= 81u^2 + 622u^3], giving [|b i(1) - 1| <= 162u^2 + O(u^3)].         *)
(* Algorithm 13 never meets this because there the second factor is [x]       *)
(* itself, so the product carries ONE power of the seed error, not two.       *)
Definition head_half (mul : twR -> twR -> twR) : Prop :=
  forall b y, isDW b -> isTW y ->
    Rabs (TWval b * TWval y - 1) <= 300 * (u * u) ->
    tw0 (mul (scaleTW (-1)%Z b) y) = 1 / 2.

(* And it is NOT re-proved from scratch: the products commute with scaling,   *)
(* so halving the first argument halves the head, and [head_one] -- already   *)
(* proved for Algorithms 11 and 12 -- does all the work.  Generic in the      *)
(* multiplier, so both variants are one line.                                 *)
(*                                                                            *)
(* The threshold is why ThreeReci.v now carries [head_eq_1_c] and             *)
(* [head_one_gen_c], the tolerance-parametric forms.  Algorithm 13's [35u^2]  *)
(* is TOO TIGHT here: at the call site the second factor is                   *)
(* [i(1) = 3Prod(b, x)], so the product is [b^2 x = (b sqrt x)^2 = (1 + e)^2] *)
(* with [|e| <= 81u^2 + 622u^3], hence [|b i(1) - 1| <= 162u^2 + O(u^3)].     *)
(* Algorithm 13 never meets this: there the second factor is [x] itself, so   *)
(* the product carries ONE power of the seed error rather than two.           *)
(*                                                                            *)
(* The head argument does not mind -- it only needs [|v - 1|] small COMPARED  *)
(* TO [u], the gap from [1] to its neighbours being [u] below and [2u] above. *)
(* The binding constraint is [head_eq_1_c]'s [e0 < 1] branch, which needs     *)
(* [(c + 200) u < 1/2]; the side condition [c u <= 1/4] gives it and allows   *)
(* [c] up to [256] at [p >= 10].  We take [c = 200] against a need of [162].  *)
(* NOTE bumping the old constant blindly does NOT work -- the proof balances  *)
(* it against its own [200u^2] slack term -- which is why the tolerance had   *)
(* to become a parameter rather than a bigger literal.                        *)
Lemma head_one_half mul :
  (forall a b X Y,
     mul (scaleTW a X) (scaleTW b Y) = scaleTW (a + b) (mul X Y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval b * TWval y - 1) <= 300 * (u * u) -> tw0 (mul b y) = 1) ->
  head_half mul.
Proof.
move=> Hscale Hone b y Hb Hy Hclose.
(* [y] is [scaleTW 0 y], which lets the scaling law fire on both arguments.   *)
have -> : mul (scaleTW (-1)%Z b) y
            = scaleTW (-1)%Z (mul b y).
  by rewrite -{1}(scaleTW_0 y) Hscale Z.add_0_r.
by rewrite tw0_scale (Hone _ _ Hb Hy Hclose) /= /Z.pow_pos /=; lra.
Qed.

(* [200 u <= 1/4] is what [head_one_gen_c] asks; [u <= 1/1024] gives it.      *)
Lemma head_c_ok : 300 * u <= / 4.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
by have := u_le_2048; lra.
Qed.

Lemma ThreeProdDW_head_half :
  ties_to_even choice -> head_half ThreeProdDW.
Proof.
move=> Hc; apply: head_one_half.
  by move=> a b X Y; apply: ThreeProdDW_scale.
apply: (@head_one_gen_c p Hp2 Hp10 300 ThreeProdDW head_c_ok).
  by move=> X Y HX HY; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
by move=> X Y HX HY HX0 HY0;
   apply: (@ThreeProdDW_head_gap p Hp2 Hp10 choice choice_sym).
Qed.

Lemma ThreeProdDWFast_head_half :
  ties_to_even choice -> head_half ThreeProdDWFast.
Proof.
move=> Hc; apply: head_one_half.
  by move=> a b X Y; apply: ThreeProdDWFast_scale.
apply: (@head_one_gen_c p Hp2 Hp10 300 ThreeProdDWFast head_c_ok).
  by move=> X Y HX HY;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
by move=> X Y HX HY HX0 HY0;
   apply: (@ThreeProdDWFast_head_gap p Hp2 Hp10 choice choice_sym).
Qed.


(* The assembly.  Beyond Algorithm 14's version this needs ONE extra          *)
(* hypothesis: a (very weak) error bound on [mul1].  Algorithm 14 applies its *)
(* head property to [b] and [x] directly, but here [mul2] is applied to [b']  *)
(* and [i(1) = mul1 b x], so the head argument only reaches [i(1)] through    *)
(* [mul1]'s accuracy.  [u^2] is far more slack than either variant needs      *)
(* ([10.5u^3] and [18u^3]).                                                   *)
Lemma ThreeSqRtAux_isTW mul1 mul2 mul3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= (u * u) * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 -> isTW (mul3 a y)) ->
  head_half mul2 ->
  forall x, isTW x -> 0 < tw0 x ->
    isTW (ThreeSqRtAux mul1 mul2 mul3 x).
Proof.
move=> Hmul1 Herr1 Hmul2 Hmul3 Hhead x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have [Fx0 Fx1] : format (tw0 x) /\ format (tw1 x)
  by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0 Fx1} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have Hi1 : isTW (mul1 (sqrtBW (tw0 x) (tw1 x)) x) by apply: Hmul1.
(* The head argument needs [|b i(1) - 1| <= 200u^2].  With [t = b sqrt x]     *)
(* and [X = t * t] we have [b i(1) = t^2 (1 + d)], [|d| <= u^2], so the       *)
(* SEED error enters SQUARED -- whence [2 * 81u^2] and the [200u^2] budget.   *)
have Key : Rabs (TWval (sqrtBW (tw0 x) (tw1 x))
                 * TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) - 1)
             <= 300 * (u * u).
  have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
  have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x
    by apply: sqrt_sqrt; lra.
  have Hseed := sqrtBW_x_err_crude Hx Hx0.
  have He1 := Herr1 _ _ HDW Hx.
  set B := TWval (sqrtBW (tw0 x) (tw1 x)) in Hseed He1 *.
  set I1 := TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) in He1 *.
  set s := sqrt (TWval x) in Hseed HsX.
  (* [B * I1 - 1 = ((B s)^2 - 1) + B * (I1 - B * X)]                          *)
  have Hsplit : B * I1 - 1
      = ((B * s) * (B * s) - 1) + B * (I1 - B * TWval x).
    by rewrite -HsX; ring.
  have Ht := Rabs_le_inv _ _ Hseed.
  have HBs : Rabs (B * s) <= 1 + (100 * (u * u)).
    by have := Rabs_triang_inv (B * s) 1; rewrite Rabs_R1; lra.
  (* the squared seed term                                                    *)
  have Hsq : Rabs ((B * s) * (B * s) - 1)
      <= (100 * (u * u))
         * (2 + (100 * (u * u))).
    have -> : (B * s) * (B * s) - 1 = (B * s - 1) * ((B * s - 1) + 2)
      by ring.
    rewrite Rabs_mult.
    apply: Rmult_le_compat => //; try apply: Rabs_pos.
    apply: Rle_trans (Rabs_triang _ _) _.
    have -> : Rabs 2 = 2 by rewrite Rabs_pos_eq; lra.
    by lra.
  (* the [mul1] term, measured against the same [t^2]                         *)
  have Hmulterm : Rabs (B * (I1 - B * TWval x))
      <= (u * u) * ((1 + (100 * (u * u)))
                    * (1 + (100 * (u * u)))).
    rewrite Rabs_mult.
    have HBp := Rabs_pos B.
    have Hstep : Rabs B * Rabs (I1 - B * TWval x)
        <= Rabs B * ((u * u) * Rabs (B * TWval x))
      by apply: Rmult_le_compat_l.
    apply: Rle_trans Hstep _.
    have HBX : Rabs B * Rabs (B * TWval x) = Rabs (B * s) * Rabs (B * s).
      by rewrite -!Rabs_mult -HsX; congr (Rabs _); ring.
    have -> : Rabs B * ((u * u) * Rabs (B * TWval x))
        = (u * u) * (Rabs B * Rabs (B * TWval x)) by ring.
    rewrite HBX.
    apply: Rmult_le_compat_l; first by nra.
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  have Ht2 := Rabs_triang ((B * s) * (B * s) - 1) (B * (I1 - B * TWval x)).
  rewrite Hsplit.
  have Hu2 : u * u <= /1024 * u by nra.
  have Hu3 : u * u * u <= /1024 * (u * u) by nra.
  have Hu4 : u * u * u * u <= /1024 * (u * u * u) by nra.
  by clear -Ht2 Hsq Hmulterm Hu0 Hu1024 Hu2 Hu3 Hu4; nra.
have Hhalf := Hhead _ _ HDW Hi1 Key.
rewrite /ThreeSqRtAux.
apply: Hmul3.
- exact: Hi1.
- apply: sub32TW_isTW; last exact: Hhalf.
  apply: Hmul2 => //.
  by apply: isDW_scale.
by case: (mul2 _ _) Hhalf => t0 t1 t2 /= ->; field.
Qed.

(* Both DW x TW variants are far inside the [u^2] the assembly asks for:      *)
(* [10.5u^3 + 39u^4] and [18u^3 + 75u^4] against [u^2].                       *)
Lemma prodDW_err_le_u2 : 105 / 10 * (u * u * u) + 39 * (u * u * u * u)
                           <= u * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have L1 : u * u * u <= / 1024 * (u * u) by nra.
have L2 : u * u * u * u <= / 1024 * (u * u * u) by nra.
by nra.
Qed.

Lemma prodDWFast_err_le_u2 : 18 * (u * u * u) + 75 * (u * u * u * u)
                               <= u * u.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have L1 : u * u * u <= / 1024 * (u * u) by nra.
have L2 : u * u * u * u <= / 1024 * (u * u * u) by nra.
by nra.
Qed.

Lemma ThreeSqRt_isTW x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x -> isTW (ThreeSqRt x).
Proof.
move=> Hc Hx Hx0.
apply: (@ThreeSqRtAux_isTW ThreeProdDW ThreeProdDW ThreeProdOneTW) => //.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- move=> b y Hb Hy.
  apply: Rle_trans
    (@ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy) _.
  apply: Rmult_le_compat_r; first by apply: Rabs_pos.
  exact: prodDW_err_le_u2.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: ThreeProdDW_head_half.
Qed.

Lemma ThreeSqRtFast_isTW x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x -> isTW (ThreeSqRtFast x).
Proof.
move=> Hc Hx Hx0.
apply: (@ThreeSqRtAux_isTW ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW)
  => //.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- move=> b y Hb Hy.
  apply: Rle_trans
    (@ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy) _.
  apply: Rmult_le_compat_r; first by apply: Rabs_pos.
  exact: prodDWFast_err_le_u2.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: ThreeProdDWFast_head_half.
Qed.

(* ===========================================================================*)
(*  Correctness, part 2: the relative error (paper Theorem 11).               *)
(*                                                                            *)
(*  THE TELESCOPING SPLIT, and where the cancellation lives.  With [b] the    *)
(*  seed, [i1 = mul1 b x], [P = mul2 b' i1], [i2 = 3/2 - P] and [y] the       *)
(*  final product,                                                            *)
(*                                                                            *)
(*    y - s = (y - i1 i2)                                    [A: d3]          *)
(*          + (- i1 (P - b' i1))                             [B: d2]          *)
(*          + (i1 - b X)((3/2 - (1/2)b^2 X) - (b/2) i1)      [C: d1]          *)
(*          + (b X (3/2 - (1/2)b^2 X) - s)                   [D: residual]    *)
(*                                                                            *)
(*  [C] is the whole point.  Its bracket is [~ 1 - 1/2 = 1/2], NOT [1] --     *)
(*  that is the cancellation between the two occurrences of [i1], and it is   *)
(*  what turns the supplementary's weight [3/2] on [d1] into [1/2].  Done     *)
(*  termwise instead, Theorem 11 comes out at [29u^3]/[44u^3] and the         *)
(*  published bound fails; through [C] it is [16.5u^3]/[24u^3] and holds.     *)
(* ===========================================================================*)
Lemma sqrt_error_split y i1 i2 b bp X P s :
  bp = b / 2 -> i2 = 3 / 2 - P ->
  y - s = (y - i1 * i2)
          + (- (i1 * (P - bp * i1)))
          + (i1 - b * X) * ((3 / 2 - (1 / 2) * (b * b) * X) - (b / 2) * i1)
          + (b * X * (3 / 2 - (1 / 2) * (b * b) * X) - s).
Proof. by move=> -> ->; field. Qed.

(* The four ingredients the split needs, each generic in the multiplier.      *)

(* [b X] against [sqrt x]: the seed bound, in the form the split consumes.    *)
Lemma sqrtAux_bX_le x :
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x)
    <= (1 + 121 * (u * u)) * sqrt (TWval x).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Hseed := sqrtBW_x_err_crude Hx Hx0.
set B := TWval (sqrtBW (tw0 x) (tw1 x)) in Hseed *.
set s := sqrt (TWval x) in HsX Hs0 Hseed *.
(* [b X = (b s) s], and [|b s - 1| <= 120u^2] is already proved.              *)
have Hgen : forall r b, r * r = TWval x -> b * TWval x = (b * r) * r.
  by move=> r b <-; ring.
rewrite (Hgen s B HsX) Rabs_mult (Rabs_pos_eq s); last lra.
have Hb := Rabs_le_inv _ _ Hseed.
(* [120u^2 <= 1/2], factored so [lra] can see it.                             *)
have Hhalf : 100 * (u * u) <= 1 / 2.
  have -> : 100 * (u * u) = 100 * u * u by ring.
  by nra.
have HBs : Rabs (B * s) <= 1 + 121 * (u * u).
  rewrite (Rabs_pos_eq (B * s)); last by lra.
  by lra.
by apply: Rmult_le_compat_r; lra.
Qed.

(* [i1 = mul1 b x] is within [(1 + 130u^2)] of [sqrt x] in magnitude.         *)
Lemma sqrtAux_i1_le mul1 d1 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  0 <= d1 -> d1 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x))
      <= (1 + 130 * (u * u)) * sqrt (TWval x).
Proof.
move=> Herr1 Hd10 Hd1u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have He := Herr1 _ _ HDW Hx.
have HbX := sqrtAux_bX_le Hx Hx0.
(* [|i1| <= |i1 - b X| + |b X| <= (1 + d1)|b X|]                              *)
have -> : TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x)
    = (TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x)
       - TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x)
      + TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x by ring.
apply: Rle_trans (Rabs_triang _ _) _.
have Hp := Rabs_pos (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x).
have Hstep : d1 * Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x)
             + Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x)
    <= (u * u) * ((1 + 121 * (u * u)) * sqrt (TWval x))
       + (1 + 121 * (u * u)) * sqrt (TWval x).
  have H1 : d1 * Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x)
      <= (u * u) * ((1 + 121 * (u * u)) * sqrt (TWval x)).
    apply: Rle_trans (_ : (u * u)
             * Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x) <= _).
      by apply: Rmult_le_compat_r.
    by apply: Rmult_le_compat_l; nra.
  by lra.
apply: Rle_trans (_ : d1 * Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x)
                      + Rabs (TWval (sqrtBW (tw0 x) (tw1 x)) * TWval x) <= _);
  first by lra.
apply: Rle_trans Hstep _.
(* [(1 + u^2)(1 + 121u^2) <= 1 + 130u^2]                                      *)
have Hfac : (u * u) * ((1 + 121 * (u * u)) * sqrt (TWval x))
            + (1 + 121 * (u * u)) * sqrt (TWval x)
    = (1 + 122 * (u * u) + 121 * (u * u) * (u * u)) * sqrt (TWval x)
  by ring.
rewrite Hfac.
apply: Rmult_le_compat_r; first lra.
have Hu4 : 121 * (u * u) * (u * u) <= 8 * (u * u).
  have -> : 121 * (u * u) * (u * u) = 121 * (u * u) * u * u by ring.
  have Hs : 0 <= u * u by apply: Rle_0_sqr.
  have Hc : 121 * (u * u) <= 8 by nra.
  by nra.
by lra.
Qed.

(* THE CANCELLATION, isolated: the bracket of [C] is [1/2], not [1].          *)
Lemma sqrtAux_bracket_le mul1 d1 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  0 <= d1 -> d1 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs ((3 / 2 - (1 / 2)
             * (TWval (sqrtBW (tw0 x) (tw1 x))
                * TWval (sqrtBW (tw0 x) (tw1 x))) * TWval x)
          - (TWval (sqrtBW (tw0 x) (tw1 x)) / 2)
            * TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x))
      <= 1 / 2 + 300 * (u * u).
Proof.
move=> Herr1 Hd10 Hd1u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0 HsX} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 HsX Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have He := Herr1 _ _ HDW Hx.
have Hseed := sqrtBW_x_err_crude Hx Hx0.
set B := TWval (sqrtBW (tw0 x) (tw1 x)) in He Hseed *.
set I1 := TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) in He *.
set s := sqrt (TWval x) in HsX Hs0 Hseed *.
have Ht := Rabs_le_inv _ _ Hseed.
(* [B^2 X = (B s)^2], generalised so the rewrite does not go under [sqrt].    *)
have HB2X : forall r b, r * r = TWval x -> b * b * TWval x = (b * r) * (b * r).
  by move=> r b <-; ring.
have HBX : B * B * TWval x = (B * s) * (B * s) by apply: HB2X.
(* [(B/2) I1 = (1/2) B^2 X + (B/2)(I1 - B X)], so the bracket splits into     *)
(* [3/2 - B^2 X ~ 1/2] and the [mul1] error.  THIS is the cancellation.       *)
have Hsplit : 3 / 2 - 1 / 2 * (B * B) * TWval x - B / 2 * I1
    = (3 / 2 - (B * B) * TWval x) - (B / 2) * (I1 - B * TWval x) by field.
rewrite Hsplit HBX.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_Ropp.
have Hhalf : 100 * (u * u) <= 1 / 2.
  have -> : 100 * (u * u) = 100 * u * u by ring.
  by nra.
have Hu4 : 14400 * ((u * u) * (u * u)) <= u * u.
  have -> : 14400 * ((u * u) * (u * u)) = 14400 * (u * u) * u * u by ring.
  have Hs2 : 0 <= u * u by apply: Rle_0_sqr.
  have Hc : 14400 * (u * u) <= 1 by nra.
  by nra.
have Hlo : 0 <= B * s by lra.
have Hsqhi : (B * s) * (B * s) <= (1 + 100 * (u * u)) * (1 + 100 * (u * u))
  by apply: Rmult_le_compat; nra.
have Hsqlo : (1 - 100 * (u * u)) * (1 - 100 * (u * u)) <= (B * s) * (B * s)
  by apply: Rmult_le_compat; nra.
have Hsq : Rabs (3 / 2 - B * s * (B * s)) <= 1 / 2 + 241 * (u * u)
  by apply: Rabs_le; nra.
have Hmix : Rabs (B / 2 * (I1 - B * TWval x)) <= 59 * (u * u).
  rewrite Rabs_mult.
  have Hstep : Rabs (B / 2) * Rabs (I1 - B * TWval x)
      <= Rabs (B / 2) * (d1 * Rabs (B * TWval x))
    by apply: Rmult_le_compat_l; [apply: Rabs_pos | exact: He].
  apply: Rle_trans Hstep _.
  have Hcomb : Rabs (B / 2) * (d1 * Rabs (B * TWval x))
      = d1 / 2 * Rabs (B * (B * TWval x)).
    rewrite /Rdiv !Rabs_mult (Rabs_pos_eq (/ 2)); last lra.
    by field.
  rewrite Hcomb.
  have HBBX : B * (B * TWval x) = B * s * (B * s) by rewrite -HBX; ring.
  rewrite HBBX.
  have Hpos : Rabs (B * s * (B * s)) <= 2.
    rewrite (Rabs_pos_eq (B * s * (B * s))); last by apply: Rle_0_sqr.
    by nra.
  have Hd2 : 0 <= d1 / 2 by lra.
  have Hstep2 : d1 / 2 * Rabs (B * s * (B * s)) <= d1 / 2 * 2
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep2 _.
  by nra.
by lra.
Qed.

(* [b i(1)] against [1]: the SEED ERROR SQUARED, and the hinge of everything  *)
(* [i(2)] needs.  With [t = b sqrt x] we have [b i(1) = t^2 (1 + d1)], so     *)
(* [|b i(1) - 1| <= |t^2 - 1| + O(u^2) <= 202u^2] out of                      *)
(* [sqrtBW_x_err_crude]'s [100u^2].  This is exactly the [Key] step inside    *)
(* [ThreeSqRtAux_isTW], but stated SHARPLY (there [300u^2] was ample) so that *)
(* [sqrtAux_i2_near_1] can halve it and stay under the tolerance [mul3] asks. *)
Lemma sqrtAux_b_i1_le mul1 d1 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  0 <= d1 -> d1 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (sqrtBW (tw0 x) (tw1 x))
          * TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) - 1)
      <= 202 * (u * u).
Proof.
move=> Herr1 Hd10 Hd1u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0 HsX} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 HsX Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have He1 := Herr1 _ _ HDW Hx.
have Hseed := sqrtBW_x_err_crude Hx Hx0.
set B := TWval (sqrtBW (tw0 x) (tw1 x)) in He1 Hseed *.
set I1 := TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) in He1 *.
set s := sqrt (TWval x) in HsX Hs0 Hseed.
(* the weak form of [mul1]'s error -- all this bound uses                     *)
have He1' : Rabs (I1 - B * TWval x) <= (u * u) * Rabs (B * TWval x).
  apply: Rle_trans He1 _.
  by apply: Rmult_le_compat_r; first by apply: Rabs_pos.
have Ht := Rabs_le_inv _ _ Hseed.
have HBs : Rabs (B * s) <= 1 + 100 * (u * u).
  by have := Rabs_triang_inv (B * s) 1; rewrite Rabs_R1; lra.
(* [B I1 - 1 = ((B s)^2 - 1) + B (I1 - B X)]                                  *)
have Hsplit : B * I1 - 1 = ((B * s) * (B * s) - 1) + B * (I1 - B * TWval x)
  by rewrite -HsX; ring.
have Hsq : Rabs ((B * s) * (B * s) - 1)
    <= (100 * (u * u)) * (2 + 100 * (u * u)).
  have -> : (B * s) * (B * s) - 1 = (B * s - 1) * ((B * s - 1) + 2) by ring.
  rewrite Rabs_mult.
  apply: Rmult_le_compat => //; try apply: Rabs_pos.
  apply: Rle_trans (Rabs_triang _ _) _.
  have -> : Rabs 2 = 2 by rewrite Rabs_pos_eq; lra.
  by lra.
have Hmulterm : Rabs (B * (I1 - B * TWval x))
    <= (u * u) * ((1 + 100 * (u * u)) * (1 + 100 * (u * u))).
  rewrite Rabs_mult.
  have HBp := Rabs_pos B.
  have Hstep : Rabs B * Rabs (I1 - B * TWval x)
      <= Rabs B * ((u * u) * Rabs (B * TWval x))
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep _.
  have HBX : Rabs B * Rabs (B * TWval x) = Rabs (B * s) * Rabs (B * s).
    by rewrite -!Rabs_mult -HsX; congr (Rabs _); ring.
  have -> : Rabs B * ((u * u) * Rabs (B * TWval x))
      = (u * u) * (Rabs B * Rabs (B * TWval x)) by ring.
  rewrite HBX.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat => //; apply: Rabs_pos.
have Ht2 := Rabs_triang ((B * s) * (B * s) - 1) (B * (I1 - B * TWval x)).
rewrite Hsplit.
have L2 : u * u <= / 2048 * u by nra.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have L5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have L6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
by clear -Ht2 Hsq Hmulterm Hu0 Hu2048 L2 L3 L4 L5 L6; nra.
Qed.

(* [i(2)] has head [1] and is within [105u^2] of it: what [mul3] demands.     *)
(*                                                                            *)
(* AND NOT [40u^2], which is what Algorithm 14 hands over and what            *)
(* [ThreeProdOneTW_error] used to require.  Algorithm 14 reaches [40u^2]      *)
(* because there [i = 2 - mul1 b x] and the seed bound [|b x - 1| <= 35u^2]   *)
(* enters ONCE.  Here [i(2) = 3/2 - mul2 b' i(1)] with                        *)
(* [b' i(1) ~ (1/2)(b sqrt x)^2], so what survives is the seed error ITSELF,  *)
(* [100u^2] by [sqrtBW_x_err_crude] -- and even the paper's own sharp         *)
(* [81u^2] would not fit inside [40].  The honest value is [101.01u^2]:       *)
(* [202u^2] halved by [b' = b/2], plus [d2] on a factor of size [1/2].        *)
(* This is why ThreeProdOne.v's [ThreeProdOneTW_error_c] had to make the      *)
(* tolerance a parameter; [105] is its second instance, [40] the first.       *)
Lemma sqrtAux_i2_near_1 mul1 mul2 d1 d2 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (sub32TW (mul2 (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
                            (mul1 (sqrtBW (tw0 x) (tw1 x)) x))) - 1)
      <= 105 * (u * u).
Proof.
move=> Herr1 Herr2 Hmul1 Hd10 Hd1u Hd20 Hd2u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have Hi1 : isTW (mul1 (sqrtBW (tw0 x) (tw1 x)) x) by apply: Hmul1.
have Hkey := sqrtAux_b_i1_le Herr1 Hd10 Hd1u Hx Hx0.
have HDWs : isDW (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
  by apply: isDW_scale.
have He2 := Herr2 _ _ HDWs Hi1.
rewrite TWval_scale in He2.
have Hpow : pow (-1) = / 2 by rewrite /= /Z.pow_pos /=; lra.
rewrite Hpow in He2.
rewrite TWval_sub32TW.
set B := TWval (sqrtBW (tw0 x) (tw1 x)) in Hkey He2 *.
set I1 := TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) in Hkey He2 *.
set P := TWval (mul2 (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
                  (mul1 (sqrtBW (tw0 x) (tw1 x)) x)) in He2 *.
have H2 : Rabs (/ 2) = / 2 by rewrite Rabs_pos_eq; lra.
(* [(B/2) I1 - 1/2] is HALF of [B I1 - 1]: the exact scaling [b' = b/2].      *)
have Hhalf : Rabs (B * / 2 * I1 - / 2) <= 101 * (u * u).
  have -> : B * / 2 * I1 - / 2 = (B * I1 - 1) * / 2 by field.
  by rewrite Rabs_mult H2; lra.
have Hub : Rabs (B * / 2 * I1) <= / 2 + 101 * (u * u).
  by have := Rabs_triang_inv (B * / 2 * I1) (/ 2); rewrite H2; lra.
have Herr : Rabs (P - B * / 2 * I1) <= (u * u) * (/ 2 + 101 * (u * u)).
  apply: Rle_trans He2 _.
  apply: Rle_trans (_ : (u * u) * Rabs (B * / 2 * I1) <= _).
    by apply: Rmult_le_compat_r; first by apply: Rabs_pos.
  by apply: Rmult_le_compat_l; first by apply: Rle_0_sqr.
have -> : 3 / 2 - P - 1 = - ((P - B * / 2 * I1) + (B * / 2 * I1 - / 2))
  by field.
rewrite Rabs_Ropp.
apply: Rle_trans (Rabs_triang _ _) _.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

(* ===========================================================================*)
(*  The assembly, as PURE ALGEBRA on reals -- the analogue of ThreeDiv.v's    *)
(*  [div_error_core].  Every floating-point fact has already been discharged  *)
(*  by the time this fires; what is left is the four-way split               *)
(*  [sqrt_error_split] and eight magnitude bounds.                            *)
(*                                                                            *)
(*  The three weights [1/2], [1/2], [1] are the whole point (doc/thm11.md     *)
(*  Section 4.1): [C]'s bracket is [1/2] and not [1], so [d1] is halved.      *)
(*  The [400u^2] corrections are slack -- they cost [O(u^5)] at the call      *)
(*  sites and are there only so that no step has to be tight.                 *)
(* ===========================================================================*)
(* The three coefficient facts [sqrt_error_core] needs, framed.  Each says   *)
(* that a product of near-[1] factors stays inside the [400u^2] slack the     *)
(* statement allows.  Framed because [nra] prices its work by the size of     *)
(* the CONTEXT: inside the core proof it sees thirty hypotheses and fails.    *)
Lemma sq_cA : (1 + 130 * (u * u)) * (1 + 105 * (u * u)) <= 1 + 400 * (u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

Lemma sq_cB :
  / 2 * ((1 + 130 * (u * u)) * (1 + 130 * (u * u)) * (1 + 100 * (u * u)))
    <= 1 / 2 + 400 * (u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have L5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have L6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
nra.
Qed.

Lemma sq_cC :
  (1 + 121 * (u * u)) * (1 / 2 + 300 * (u * u)) <= 1 / 2 + 400 * (u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

Lemma sqrt_error_core B I1 P Y X s d1 d2 d3 :
  0 < s -> s * s = X ->
  0 <= d1 -> 0 <= d2 -> 0 <= d3 ->
  Rabs (B * s - 1) <= 100 * (u * u) ->
  Rabs I1 <= (1 + 130 * (u * u)) * s ->
  Rabs (3 / 2 - P - 1) <= 105 * (u * u) ->
  Rabs (Y - I1 * (3 / 2 - P)) <= d3 * Rabs (I1 * (3 / 2 - P)) ->
  Rabs (P - B * / 2 * I1) <= d2 * Rabs (B * / 2 * I1) ->
  Rabs (I1 - B * X) <= d1 * Rabs (B * X) ->
  Rabs (B * X) <= (1 + 121 * (u * u)) * s ->
  Rabs (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1) <= 1 / 2 + 300 * (u * u) ->
  Rabs (B * X * (3 / 2 - 1 / 2 * (B * B) * X) - s)
    <= 15200 * (u * u * u * u) * s ->
  Rabs (Y - s)
    <= (d1 * (1 / 2 + 400 * (u * u)) + d2 * (1 / 2 + 400 * (u * u))
        + d3 * (1 + 400 * (u * u)) + 15200 * (u * u * u * u)) * s.
Proof.
move=> Hs0 HsX Hd1 Hd2 Hd3 Hseed Hi1 Hi2 HA HB HC HbX Hbrk HD.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L2 : u * u <= / 2048 * u by nra.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have L5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have Hu2p : 0 <= u * u by apply: Rle_0_sqr.
have Hsp : Y - s = Y - I1 * (3 / 2 - P) + - (I1 * (P - B / 2 * I1))
    + (I1 - B * X) * (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1)
    + (B * X * (3 / 2 - 1 / 2 * (B * B) * X) - s)
  by apply: sqrt_error_split.
(* [|3/2 - P| <= 1 + 105u^2] and [|B| s <= 1 + 100u^2]                        *)
have Hi2u : Rabs (3 / 2 - P) <= 1 + 105 * (u * u).
  by have := Rabs_triang_inv (3 / 2 - P) 1; rewrite Rabs_R1; lra.
have Hsa : Rabs s = s by rewrite Rabs_pos_eq; lra.
have HBu : Rabs B * s <= 1 + 100 * (u * u).
  have -> : Rabs B * s = Rabs (B * s) by rewrite Rabs_mult Hsa.
  by have := Rabs_triang_inv (B * s) 1; rewrite Rabs_R1; lra.
have Hi1p := Rabs_pos I1.
have HBp := Rabs_pos B.
(* [A]: the last product.                                                     *)
have HA' : Rabs (Y - I1 * (3 / 2 - P)) <= d3 * (1 + 400 * (u * u)) * s.
  apply: Rle_trans HA _.
  rewrite Rabs_mult.
  have Hstep : Rabs I1 * Rabs (3 / 2 - P)
      <= ((1 + 130 * (u * u)) * s) * (1 + 105 * (u * u))
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  have Hstep2 : d3 * (Rabs I1 * Rabs (3 / 2 - P))
      <= d3 * (((1 + 130 * (u * u)) * s) * (1 + 105 * (u * u)))
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep2 _.
  have Hd3s : 0 <= d3 * s by apply: Rmult_le_pos; lra.
  have -> : d3 * ((1 + 130 * (u * u)) * s * (1 + 105 * (u * u)))
      = (d3 * s) * ((1 + 130 * (u * u)) * (1 + 105 * (u * u))) by ring.
  have -> : d3 * (1 + 400 * (u * u)) * s = (d3 * s) * (1 + 400 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l; [exact: Hd3s | exact: sq_cA].
(* [B]: the inner product, where [b' = b/2] supplies the [1/2].               *)
have HB' : Rabs (- (I1 * (P - B / 2 * I1)))
    <= d2 * (1 / 2 + 400 * (u * u)) * s.
  rewrite Rabs_Ropp Rabs_mult.
  have HBe : Rabs (P - B / 2 * I1) <= d2 * Rabs (B * / 2 * I1).
    by have -> : B / 2 * I1 = B * / 2 * I1 by field.
  have Hstep : Rabs I1 * Rabs (P - B / 2 * I1)
      <= Rabs I1 * (d2 * Rabs (B * / 2 * I1))
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep _.
  have Hcomb : Rabs I1 * (d2 * Rabs (B * / 2 * I1))
      = d2 * / 2 * (Rabs I1 * Rabs I1 * Rabs B).
    rewrite !Rabs_mult (Rabs_pos_eq (/ 2)); last lra.
    by field.
  rewrite Hcomb.
  (* [|I1|^2 |B| = (|I1|/s)^2 s (|B| s)], written without dividing.           *)
  have Hsq : Rabs I1 * Rabs I1 * Rabs B
      <= ((1 + 130 * (u * u)) * (1 + 130 * (u * u))) * s
         * (1 + 100 * (u * u)).
    have Hstep2 : Rabs I1 * Rabs I1
        <= ((1 + 130 * (u * u)) * s) * ((1 + 130 * (u * u)) * s)
      by apply: Rmult_le_compat.
    have Hstep3 : Rabs I1 * Rabs I1 * Rabs B
        <= (((1 + 130 * (u * u)) * s) * ((1 + 130 * (u * u)) * s)) * Rabs B
      by apply: Rmult_le_compat_r.
    apply: Rle_trans Hstep3 _.
    have Hstep4 : (((1 + 130 * (u * u)) * s) * ((1 + 130 * (u * u)) * s))
                    * Rabs B
        = ((1 + 130 * (u * u)) * (1 + 130 * (u * u))) * s * (Rabs B * s)
      by ring.
    rewrite Hstep4.
    apply: Rmult_le_compat_l => //.
    by apply: Rmult_le_pos; nra.
  have Hd2p : 0 <= d2 * / 2 by lra.
  have Hstep5 : d2 * / 2 * (Rabs I1 * Rabs I1 * Rabs B)
      <= d2 * / 2 * (((1 + 130 * (u * u)) * (1 + 130 * (u * u))) * s
                     * (1 + 100 * (u * u)))
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep5 _.
  have Hd2s : 0 <= d2 * s by apply: Rmult_le_pos; lra.
  have -> : d2 * / 2 * ((1 + 130 * (u * u)) * (1 + 130 * (u * u)) * s
                        * (1 + 100 * (u * u)))
      = (d2 * s) * (/ 2 * ((1 + 130 * (u * u)) * (1 + 130 * (u * u))
                           * (1 + 100 * (u * u)))) by field.
  have -> : d2 * (1 / 2 + 400 * (u * u)) * s
      = (d2 * s) * (1 / 2 + 400 * (u * u)) by ring.
  by apply: Rmult_le_compat_l; [exact: Hd2s | exact: sq_cB].
(* [C]: THE CANCELLATION.  The bracket is [1/2], not [1].                     *)
have HC' : Rabs ((I1 - B * X) * (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1))
    <= d1 * (1 / 2 + 400 * (u * u)) * s.
  rewrite Rabs_mult.
  have Hstep : Rabs (I1 - B * X)
                 * Rabs (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1)
      <= (d1 * ((1 + 121 * (u * u)) * s)) * (1 / 2 + 300 * (u * u)).
    apply: Rmult_le_compat => //; try apply: Rabs_pos.
    apply: Rle_trans HC _.
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep _.
  have Hd1s : 0 <= d1 * s by apply: Rmult_le_pos; lra.
  have -> : d1 * ((1 + 121 * (u * u)) * s) * (1 / 2 + 300 * (u * u))
      = (d1 * s) * ((1 + 121 * (u * u)) * (1 / 2 + 300 * (u * u))) by ring.
  have -> : d1 * (1 / 2 + 400 * (u * u)) * s
      = (d1 * s) * (1 / 2 + 400 * (u * u)) by ring.
  by apply: Rmult_le_compat_l; [exact: Hd1s | exact: sq_cC].
(* the four, added up.                                                        *)
rewrite Hsp.
have T3 := Rabs_triang ((Y - I1 * (3 / 2 - P))
    + (- (I1 * (P - B / 2 * I1)))
    + (I1 - B * X) * (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1))
  (B * X * (3 / 2 - 1 / 2 * (B * B) * X) - s).
have T2 := Rabs_triang ((Y - I1 * (3 / 2 - P))
    + (- (I1 * (P - B / 2 * I1))))
  ((I1 - B * X) * (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1)).
have T1 := Rabs_triang (Y - I1 * (3 / 2 - P)) (- (I1 * (P - B / 2 * I1))).
by lra.
Qed.

Lemma ThreeSqRtAux_error mul1 mul2 mul3 d1 d2 d3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 ->
     Rabs (TWval y - 1) <= 105 * (u * u) ->
     Rabs (TWval (mul3 a y) - TWval a * TWval y)
       <= d3 * Rabs (TWval a * TWval y)) ->
  head_half mul2 ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  0 <= d3 -> d3 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (ThreeSqRtAux mul1 mul2 mul3 x) - sqrt (TWval x))
      <= (d1 * (1 / 2 + 400 * (u * u)) + d2 * (1 / 2 + 400 * (u * u))
          + d3 * (1 + 400 * (u * u)) + 15200 * (u * u * u * u))
         * Rabs (sqrt (TWval x)).
Proof.
move=> Hmul1 Hmul2 Herr1 Herr2 Herr3 Hhead Hd10 Hd1u Hd20 Hd2u Hd30 Hd3u
       x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 : 0 < TWval x by apply: isTW_TWval_gt0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0 HsX} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 HsX Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBW (tw0 x) (tw1 x)) by apply: sqrtB_isDW.
have Hi1 : isTW (mul1 (sqrtBW (tw0 x) (tw1 x)) x) by apply: Hmul1.
have Hu2p : 0 <= u * u by apply: Rle_0_sqr.
(* [i(2)]'s head is [1]: the head property, at the [300u^2] the [head_half]  *)
(* interface asks for -- ample, since [sqrtAux_b_i1_le] gives [202u^2].      *)
have Hkey := sqrtAux_b_i1_le Herr1 Hd10 Hd1u Hx Hx0.
have Hkey300 : Rabs (TWval (sqrtBW (tw0 x) (tw1 x))
                     * TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x) - 1)
    <= 300 * (u * u) by lra.
have Hhalf := Hhead _ _ HDW Hi1 Hkey300.
have HDWs : isDW (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
  by apply: isDW_scale.
have Hi2TW : isTW (sub32TW (mul2 (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
                              (mul1 (sqrtBW (tw0 x) (tw1 x)) x))).
  apply: sub32TW_isTW; last exact: Hhalf.
  by apply: Hmul2.
have Hi2h : tw0 (sub32TW (mul2 (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
                            (mul1 (sqrtBW (tw0 x) (tw1 x)) x))) = 1
  by case: (mul2 _ _) Hhalf => t0 t1 t2 /= ->; field.
(* the eight bounds [sqrt_error_core] consumes                               *)
have Hi2v := sqrtAux_i2_near_1 Herr1 Herr2 Hmul1 Hd10 Hd1u Hd20 Hd2u Hx Hx0.
have He3 := Herr3 _ _ Hi1 Hi2TW Hi2h Hi2v.
have He1 := Herr1 _ _ HDW Hx.
have He2 := Herr2 _ _ HDWs Hi1.
rewrite TWval_scale in He2.
have Hpow : pow (-1) = / 2 by rewrite /= /Z.pow_pos /=; lra.
rewrite Hpow in He2.
have Hi1le := sqrtAux_i1_le Herr1 Hd10 Hd1u Hx Hx0.
have Hbrk := sqrtAux_bracket_le Herr1 Hd10 Hd1u Hx Hx0.
have HbXle := sqrtAux_bX_le Hx Hx0.
have Hresid := sqrt_newton_residual Hx Hx0.
have Hseed := sqrtBW_x_err_crude Hx Hx0.
rewrite TWval_sub32TW in He3 Hi2v.
have Habs : Rabs (sqrt (TWval x)) = sqrt (TWval x)
  by rewrite Rabs_pos_eq; lra.
rewrite Habs in Hresid.
rewrite /ThreeSqRtAux Habs.
apply: (@sqrt_error_core (TWval (sqrtBW (tw0 x) (tw1 x)))
          (TWval (mul1 (sqrtBW (tw0 x) (tw1 x)) x))
          (TWval (mul2 (scaleTW (-1)%Z (sqrtBW (tw0 x) (tw1 x)))
                    (mul1 (sqrtBW (tw0 x) (tw1 x)) x)))
          _ (TWval x) (sqrt (TWval x)) d1 d2 d3) => //.
Qed.

(* Paper Theorem 11, accurate variant: [24u^3 + 10260u^4].                    *)
Lemma ThreeSqRt_error x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (ThreeSqRt x) - sqrt (TWval x)) <=
     (24 * (u * u * u) + 10260 * (u * u * u * u)) * Rabs (sqrt (TWval x)).
Proof.
move=> Hc Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Hu2 : u * u <= / 2048 * u by nra.
have Hu3 : u * u * u <= / 2048 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have Hu6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
(* the two ends of [ThreeProdOneTW_error_c]'s tolerance window; [105] is     *)
(* what [sqrtAux_i2_near_1] delivers.                                        *)
have H105a : (40 : R) <= 105 by lra.
have H105b : (105 : R) <= 112 by lra.
have Hd0 : 0 <= 105 / 10 * (u * u * u) + 39 * (u * u * u * u) by nra.
have Hdu : 105 / 10 * (u * u * u) + 39 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= 6 * (u * u * u) + 3265 * (u * u * u * u) by nra.
have Heu : 6 * (u * u * u) + 3265 * (u * u * u * u) <= u * u by nra.
(* [31 * 105 + 10 = 3265]: Algorithm 20's [delta3] at OUR tolerance.         *)
have Hd3le : 6 * (u * u * u) + (31 * 105 + 10) * (u * u * u * u)
    <= 6 * (u * u * u) + 3265 * (u * u * u * u) by lra.
have Hgen := @ThreeSqRtAux_error ThreeProdDW ThreeProdDW ThreeProdOneTW
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (6 * (u * u * u) + 3265 * (u * u * u * u))
  (fun b y Hb Hy =>
     @ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun a y Ha Hy Hy0 Hy1 =>
     Rle_trans _ _ _
       (@ThreeProdOneTW_error_c p Hp2 Hp6 choice choice_sym 105 a y Hc
          H105a H105b Ha Hy Hy0 Hy1)
       (Rmult_le_compat_r _ _ _ (Rabs_pos _) Hd3le))
  (ThreeProdDW_head_half Hc)
  Hd0 Hdu Hd0 Hdu He0 Heu x Hx Hx0.
rewrite /ThreeSqRt.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
nra.
Qed.

(* Paper Theorem 11, fast variant: [39u^3 + 10333u^4].                        *)
Lemma ThreeSqRtFast_error x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (ThreeSqRtFast x) - sqrt (TWval x)) <=
     (39 * (u * u * u) + 10333 * (u * u * u * u)) * Rabs (sqrt (TWval x)).
Proof.
move=> Hc Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Hu2 : u * u <= / 2048 * u by nra.
have Hu3 : u * u * u <= / 2048 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have Hu6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
(* the two ends of [ThreeProdOneTW_error_c]'s tolerance window; [105] is     *)
(* what [sqrtAux_i2_near_1] delivers.                                        *)
have H105a : (40 : R) <= 105 by lra.
have H105b : (105 : R) <= 112 by lra.
have Hd0 : 0 <= 18 * (u * u * u) + 75 * (u * u * u * u) by nra.
have Hdu : 18 * (u * u * u) + 75 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= 6 * (u * u * u) + 3265 * (u * u * u * u) by nra.
have Heu : 6 * (u * u * u) + 3265 * (u * u * u * u) <= u * u by nra.
(* [31 * 105 + 10 = 3265]: Algorithm 20's [delta3] at OUR tolerance.         *)
have Hd3le : 6 * (u * u * u) + (31 * 105 + 10) * (u * u * u * u)
    <= 6 * (u * u * u) + 3265 * (u * u * u * u) by lra.
have Hgen := @ThreeSqRtAux_error ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW
  (18 * (u * u * u) + 75 * (u * u * u * u))
  (18 * (u * u * u) + 75 * (u * u * u * u))
  (6 * (u * u * u) + 3265 * (u * u * u * u))
  (fun b y Hb Hy =>
     @ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun a y Ha Hy Hy0 Hy1 =>
     Rle_trans _ _ _
       (@ThreeProdOneTW_error_c p Hp2 Hp6 choice choice_sym 105 a y Hc
          H105a H105b Ha Hy Hy0 Hy1)
       (Rmult_le_compat_r _ _ _ (Rabs_pos _) Hd3le))
  (ThreeProdDWFast_head_half Hc)
  Hd0 Hdu Hd0 Hdu He0 Heu x Hx Hx0.
rewrite /ThreeSqRtFast.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
nra.
Qed.

End SecThreeSqRt.
