(* ---------------------------------------------------------------------------*)
(* Algorithm 14 (3Div): the QUOTIENT of two triple words, and its two         *)
(* correctness results -- the result is a triple word ([ThreeDiv_isTW]) and   *)
(* the relative error bounds [29u^3 + 2576u^4] (accurate variant,             *)
(* [ThreeDiv_error]) and [44u^3 + 2650u^4] (fast variant,                     *)
(* [ThreeDivFast_error]) -- paper doc/paper3.pdf, Section 10 and Theorem 10   *)
(* (see doc/thm10.md).  Generic over the precision [p] (FLX, no [emin]);      *)
(* needs [p >= 10].                                                           *)
(*                                                                            *)
(* Algorithm 14 is Algorithm 13 with the dividend folded in.  It starts from  *)
(* the SAME Newton double word [b ~ 1/x0] (the five lines of Algorithm 13,    *)
(* here [reciBW]) and then, instead of [b (2 - b x)], computes                *)
(*                                                                            *)
(*     (z b) (2 - b x)     rather than     z (b (2 - b x))                    *)
(*                                                                            *)
(* -- the old paper's Section 9 explains why: the two products [z b] and      *)
(* [2 - b x] are then INDEPENDENT (parallelisable), and the optimisations     *)
(* that the constraint [i0 = 1] allows are worth more on a TW x TW product    *)
(* than on a DW x TW one.                                                     *)
(*                                                                            *)
(*     a    <- RN((1 + 2u)/x0)          )                                     *)
(*     h11  <- RN(a*x0 - (1 + 2u))      )  the five lines of Algorithm 13,    *)
(*     h1   <- RN(-h11 - a*x1)          )  i.e. [reciBW (tw0 x) (tw1 x)]      *)
(*     (b01, b11) <- 2Prod(a, 1 - 2u)   )                                     *)
(*     b12  <- RN(b11 + a*h1)           )                                     *)
(*     b    <- Fast2Sum(b01, b12)       )                                     *)
(*     i    <- 2 - 3Prod_{2,3}(b, x)       (head [1], as in Algorithm 13)     *)
(*     a'   <- 3Prod_{2,3}(b, z)                                              *)
(*     y    <- 3Prod_{3,3}(a', i)                                             *)
(*                                                                            *)
(* The three products are parameters ([ThreeDivAux]): [mul1] and [mul2] are   *)
(* DW x TW (Algorithm 11 accurate, or Algorithm 12 fast) and [mul3] is the    *)
(* TW x TW product with a head-[1] second argument -- Algorithm 20 of the old *)
(* paper, [ThreeProdOneTW] in ThreeProdOne.v.  Whence the paper's constants   *)
(* [24 = 10.5 + 10.5 + 3] and [39 = 18 + 18 + 3] -- which the proof turns     *)
(* into [27 = 10.5 + 10.5 + 6] and [42 = 18 + 18 + 6], Algorithm 20 costing   *)
(* [6u^3] rather than the announced [3u^3] on a triple word.  It was [8u^3]   *)
(* until doc/thm10.md step 1; steps 2 and 3 would close the rest.             *)
(*                                                                            *)
(* STATUS: COMPLETE -- everything in this file is PROVED, zero admits.  The   *)
(* two error bounds rest on [ThreeProdOneTW_error] (Algorithm 20's [delta3])  *)
(* in ThreeProdOne.v, the only genuinely new bound Theorem 10 needs; the      *)
(* three steps that would tighten it further are in doc/thm10.md.             *)
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

Section SecThreeDiv.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 14 needs [p >= 10], for the same reason as Algorithm 13: it is   *)
(* what forces the leading limb of [3Prod_{2,3}(b, x)] to be exactly [1].     *)
Hypothesis Hp10 : (10 <= p)%Z.

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
Local Notation isTW := (isTW p).
Local Notation isDW := (isDW p).
Local Notation reciBW := (reciBW p choice).
Local Notation head_one := (head_one p).

(* The three products: Algorithms 11/12 (DW x TW) and Algorithm 20 (TW x TW   *)
(* with a head-[1] second argument).                                          *)
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdDWFast := (ThreeProdDWFast p choice).
Local Notation ThreeProdOneTW := (ThreeProdOneTW p choice).

(* ===========================================================================*)
(*  Algorithm 14 -- 3Div(z, x)                                                *)
(* ===========================================================================*)

(* [mul1] computes [i = 2 - b x], [mul2] computes [a = b z], [mul3] the final *)
(* [y = a i].  Only [mul1] sees the [head_one] property; only [mul3] needs to *)
(* be sharp on a head-[1] second argument.                                    *)
Definition ThreeDivAux (mul1 mul2 mul3 : twR -> twR -> twR) (z x : twR) : twR :=
  let bw := reciBW (tw0 x) (tw1 x) in
  mul3 (mul2 bw z) (sub2TW (mul1 bw x)).

(* The accurate variant: both DW x TW products are Algorithm 11.              *)
Definition ThreeDiv (z x : twR) : twR :=
  ThreeDivAux ThreeProdDW ThreeProdDW ThreeProdOneTW z x.

(* The fast variant: both DW x TW products are Algorithm 12.                  *)
Definition ThreeDivFast (z x : twR) : twR :=
  ThreeDivAux ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW z x.

(* ===========================================================================*)
(*  Correctness, part 1: the result is a triple word.                         *)
(*                                                                            *)
(*  Exactly Algorithm 13's assembly ([ThreeReciAux_isTW]) with one product    *)
(*  more: [mul1] must return a triple word and satisfy [head_one] (so that    *)
(*  [2 - mul1 b x] is again a triple word, by [sub2TW_isTW]), [mul2] must     *)
(*  return a triple word, and [mul3] must do so on a head-[1] second          *)
(*  argument.  Nothing new is needed: [reciB_isDW] and [reciBW_x_err] are     *)
(*  already proved, and [head_one] holds for Algorithms 11 and 12.            *)
(* ===========================================================================*)
Lemma ThreeDivAux_isTW mul1 mul2 mul3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 -> isTW (mul3 a y)) ->
  head_one mul1 ->
  forall z x, isTW z -> isTW x -> tw0 x <> 0 ->
    isTW (ThreeDivAux mul1 mul2 mul3 z x).
Proof.
move=> Hmul1 Hmul2 Hmul3 Hhead z x Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1 : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HDW : isDW (reciBW (tw0 x) (tw1 x))
  by apply: (@reciB_isDW p Hp2 Hp10 choice choice_sym).
have Herr := @reciBW_x_err p Hp2 Hp10 choice choice_sym x Hx Hx0.
have Herr35 : Rabs (TWval (reciBW (tw0 x) (tw1 x)) * TWval x - 1)
                <= 35 * (u * u).
  have Hu3 : u * u * u <= /1024 * (u * u) by nra.
  by clear -Hu0 Hu1024 Hu3 Herr; nra.
have Hhead1 := Hhead _ _ HDW Hx Herr35.
rewrite /ThreeDivAux.
apply: Hmul3.
- by apply: Hmul2.
- by apply: (@sub2TW_isTW p Hp2); [apply: Hmul1|].
by case: (mul1 _ _) Hhead1 => t0 t1 t2 /= ->; ring.
Qed.

Lemma ThreeDiv_isTW z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 -> isTW (ThreeDiv z x).
Proof.
move=> Hc Hz Hx Hx0.
apply: (@ThreeDivAux_isTW ThreeProdDW ThreeProdDW ThreeProdOneTW) => //.
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> b y Hb Hy; apply: (@ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: (@ThreeProdDW_head_one p Hp2 Hp10 choice choice_sym).
Qed.

Lemma ThreeDivFast_isTW z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 -> isTW (ThreeDivFast z x).
Proof.
move=> Hc Hz Hx Hx0.
apply: (@ThreeDivAux_isTW ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW) => //.
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> b y Hb Hy;
     apply: (@ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym).
- by move=> a y Ha Hy Hy0;
     apply: (@ThreeProdOneTW_isTW p Hp2 Hp6 choice choice_sym).
exact: (@ThreeProdDWFast_head_one p Hp2 Hp10 choice choice_sym).
Qed.

(* ===========================================================================*)
(*  Correctness, part 2: the relative error (paper Theorem 10).               *)
(*                                                                            *)
(*  Old paper Section 9.  With [d1] the relative error of [i = 2 - 3Prod(b,x)]*)
(*  (relative to [x b]), [d2] that of [a = 3Prod(b, z)] and [d3] that of the  *)
(*  final [y = 3Prod(a, i)]:                                                  *)
(*                                                                            *)
(*    |y - z/x| <= (d1 (1 + 71u^2) + (d2 + d3)(1 + 107u^2) + 1165u^4) |z/x|   *)
(*                                                                            *)
(*  STEPS, and what each one already has:                                     *)
(*                                                                            *)
(*  (1) [b] is a double word and [|b x - 1| <= 34u^2 + 123u^3]:               *)
(*      [reciB_isDW], [reciBW_x_err] -- PROVED (Algorithm 13).                *)
(*  (2) [i] has head [1] and [|i - 1| <= 40u^2]: [head_one] + [sub2TW_isTW],  *)
(*      the [|i - 1|] bound is inside [ThreeReciAux_error] -- PROVED, but it  *)
(*      must be FACTORED OUT of that proof to be reused here (it is the only  *)
(*      piece of Algorithm 13's assembly that is not already a lemma).        *)
(*  (3) the algebraic identity, the analogue of Algorithm 13's Newton split:  *)
(*        y - z/x = (y - a i) + (a - b z) i + z (b (2 - x b) - 1/x)           *)
(*                                     + (b z)(i - (2 - x b))                 *)
(*      whose last term is [-z (b x - 1)^2 / x] by [newton_id]; [newton_sq_le]*)
(*      bounds the square by [1165u^4] -- both PROVED.                        *)
(*  (4) the final arithmetic: [reci_error_assembly] generalised to three      *)
(*      error terms (or a fourth [assembly] lemma of the same shape).         *)
(*  (5) [d3] = [ThreeProdOneTW_error] -- the ONLY genuinely new bound.        *)
(*                                                                            *)
(*  As in Theorem 9, the [u^3] terms are [24 = 10.5 + 10.5 + 3] and           *)
(*  [39 = 18 + 18 + 3]; the [u^4] terms are stated as the paper's here and    *)
(*  will be corrected to whatever the honest accounting gives (Theorem 9's    *)
(*  [1465u^4] became [1830u^4]).  Note the [u^3] term is itself at risk this  *)
(*  time -- see the caveat on [ThreeProdOneTW_error].                         *)
(* ===========================================================================*)
(* The final arithmetic of Theorem 10, on the bare quantities: [a = |b x|],   *)
(* [c = |i|], [R0 = |z/x|] and the FOUR error terms (Theorem 9 had three --   *)
(* the extra one is the second product's, [a' = 3Prod(b, z)], whose error is  *)
(* then carried through the multiplication by [i]).  Kept apart so that the   *)
(* assembly below never has to run [nra] in a large context.                  *)
(*                                                                            *)
(* The [1 + 107u^2] the paper attaches to [d2 + d3] is generous: [a c] is     *)
(* [1 + 76u^2] and the [(1 + d2)] that [|a'| <= (1 + d2)|b z|] costs is       *)
(* another [u^2].  The [1 + 71u^2] on [d1] is [a^2], as in Theorem 9.         *)
Lemma div_error_assembly a c R0 e1 e2 e3 e4 dd1 dd2 dd3 :
  0 <= a -> a <= 1 + 35 * (u * u) ->
  0 <= c -> c <= 1 + 40 * (u * u) ->
  0 <= R0 -> 0 <= dd1 -> 0 <= dd2 -> dd2 <= u * u -> 0 <= dd3 ->
  e1 <= dd3 * ((1 + dd2) * (a * R0) * c) ->
  e2 <= dd2 * (a * R0 * c) ->
  e3 <= a * R0 * (dd1 * a) ->
  e4 <= 1165 * (u * u * u * u) * R0 ->
  e1 + e2 + e3 + e4
    <= (dd1 * (1 + 71 * (u * u)) + (dd2 + dd3) * (1 + 107 * (u * u))
        + 1165 * (u * u * u * u)) * R0.
Proof.
move=> Ha0 Ha1 Hc0 Hc1 HR0 Hd10 Hd20 Hd2u Hd30 H1 H2 H3 H4.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Hu2 : u * u <= / 1024 * u by nra.
have Hac : a * c <= 1 + 76 * (u * u) by nra.
have Hac0 : 0 <= a * c by nra.
have Haa : a * a <= 1 + 71 * (u * u) by nra.
have Hd2R : 0 <= dd2 * R0 by nra.
have Hd1R : 0 <= dd1 * R0 by nra.
have Hd3R : 0 <= dd3 * R0 by nra.
have K1 : dd3 * ((1 + dd2) * (a * R0) * c) <= dd3 * (1 + 107 * (u * u)) * R0.
  have -> : dd3 * ((1 + dd2) * (a * R0) * c)
      = (dd3 * R0) * ((1 + dd2) * (a * c))
    by ring.
  have -> : dd3 * (1 + 107 * (u * u)) * R0 = (dd3 * R0) * (1 + 107 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l => //; nra.
have K2 : dd2 * (a * R0 * c) <= dd2 * (1 + 107 * (u * u)) * R0.
  have -> : dd2 * (a * R0 * c) = (dd2 * R0) * (a * c) by ring.
  have -> : dd2 * (1 + 107 * (u * u)) * R0 = (dd2 * R0) * (1 + 107 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l => //; nra.
have K3 : a * R0 * (dd1 * a) <= dd1 * (1 + 71 * (u * u)) * R0.
  have -> : a * R0 * (dd1 * a) = (dd1 * R0) * (a * a) by ring.
  have -> : dd1 * (1 + 71 * (u * u)) * R0 = (dd1 * R0) * (1 + 71 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l.
by nra.
Qed.

(* THE CORE OF THEOREM 10, on the bare reals: [B ~ 1/X] with [reciBW]'s       *)
(* accuracy, [P] the first product ([~ B X]), [A] the second one ([~ B Z]) and*)
(* [Y] the third ([~ A (2 - P)]).  Nothing here knows about triple words -- it*)
(* is the algebraic identity                                                  *)
(*                                                                            *)
(*   Y - Z/X = (Y - A i) + (A - B Z) i + (B Z)(X B - P)                       *)
(*             + Z (B (2 - X B) - 1/X)                                        *)
(*                                                                            *)
(* (with [i = 2 - P]) whose last term is [- Z (B X - 1)^2 / X] by [newton_id],*)
(* plus the two arithmetic lemmas [sub2_near_one] and [div_error_assembly].   *)
Lemma div_error_core B X Z P A Y d1 d2 d3 :
  Rabs (B * X - 1) <= 34 * (u * u) + 123 * (u * u * u) ->
  Rabs (P - B * X) <= d1 * Rabs (B * X) ->
  Rabs (A - B * Z) <= d2 * Rabs (B * Z) ->
  Rabs (Y - A * (2 - P)) <= d3 * Rabs (A * (2 - P)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u -> 0 <= d3 ->
  Rabs (Y - Z / X)
    <= (d1 * (1 + 71 * (u * u)) + (d2 + d3) * (1 + 107 * (u * u))
        + 1165 * (u * u * u * u)) * Rabs (Z / X).
Proof.
move=> HBX HP HA HY Hd10 Hd1u Hd20 Hd2u Hd30.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Hu3 : u * u * u <= / 1024 * (u * u) by nra.
have HBX35 : Rabs (B * X - 1) <= 35 * (u * u)
  by clear -HBX Hu0 Hu1024 Hu3; nra.
(* [x] itself cannot vanish: [b x] is within [35u^2] of [1].                  *)
have HX0 : X <> 0.
  move=> HX; move: HBX35; rewrite HX Rmult_0_r.
  have -> : (0 - 1) = -1 by ring.
  by rewrite Rabs_Ropp Rabs_R1; clear -Hu0 Hu1024; nra.
set I := 2 - P in HY *.
have HI1 : Rabs (I - 1) <= 40 * (u * u)
  by apply: (@sub2_near_one p Hp10 B X P d1).
have HIub : Rabs I <= 1 + 40 * (u * u)
  by have := Rabs_triang_inv I 1; rewrite Rabs_R1; lra.
have HBXub : Rabs (B * X) <= 1 + 35 * (u * u)
  by have := Rabs_triang_inv (B * X) 1; rewrite Rabs_R1; lra.
set R0 := Rabs (Z / X).
have HR0 : 0 <= R0 by apply: Rabs_pos.
have Hab : 0 <= Rabs (B * X) by apply: Rabs_pos.
have Hai : 0 <= Rabs I by apply: Rabs_pos.
(* [|B Z| = |B X| |Z/X|]: every term is measured against the exact quotient.  *)
have HBZ : Rabs (B * Z) = Rabs (B * X) * R0.
  by rewrite /R0 -Rabs_mult; congr Rabs; field.
have HAub : Rabs A <= (1 + d2) * (Rabs (B * X) * R0).
  have T := Rabs_triang_inv A (B * Z).
  by rewrite -HBZ; nra.
have Hnewton : B * (2 - X * B) - / X = - (B * X - 1) ^ 2 * / X.
  have H := newton_id B X.
  have -> : B * (2 - X * B) - / X = ((B * (2 - X * B)) * X - 1) * / X.
    by field.
  by rewrite H.
have Hdecomp : Y - Z / X
    = (Y - A * I) + (A - B * Z) * I + (B * Z) * (X * B - P)
      + Z * (B * (2 - X * B) - / X)
  by rewrite /I; field.
have E1 : Rabs ((A - B * Z) * I) = Rabs (A - B * Z) * Rabs I
  by rewrite Rabs_mult.
have E2 : Rabs ((B * Z) * (X * B - P))
    = Rabs (B * X) * R0 * Rabs (P - B * X).
  rewrite Rabs_mult HBZ; congr (_ * _).
  by rewrite -Rabs_Ropp; congr Rabs; ring.
have E3 : Rabs (Z * (B * (2 - X * B) - / X)) = (B * X - 1) ^ 2 * R0.
  rewrite Hnewton.
  have -> : Z * (- (B * X - 1) ^ 2 * / X) = - ((B * X - 1) ^ 2 * (Z / X))
    by field.
  rewrite Rabs_Ropp Rabs_mult -/R0; congr (_ * _).
  by apply: Rabs_pos_eq; apply: pow2_ge_0.
have Step1 : Rabs (Y - A * I)
    <= d3 * ((1 + d2) * (Rabs (B * X) * R0) * Rabs I).
  apply: Rle_trans HY _.
  rewrite Rabs_mult; apply: Rmult_le_compat_l => //.
  by apply: Rmult_le_compat_r.
have Step2 : Rabs ((A - B * Z) * I) <= d2 * (Rabs (B * X) * R0 * Rabs I).
  rewrite E1.
  have -> : d2 * (Rabs (B * X) * R0 * Rabs I) = (d2 * Rabs (B * Z)) * Rabs I
    by rewrite HBZ; ring.
  by apply: Rmult_le_compat_r.
have Step3 : Rabs ((B * Z) * (X * B - P))
    <= Rabs (B * X) * R0 * (d1 * Rabs (B * X)).
  rewrite E2; apply: Rmult_le_compat_l; last by [].
  by apply: Rmult_le_pos.
have Step4 : Rabs (Z * (B * (2 - X * B) - / X))
    <= 1165 * (u * u * u * u) * R0.
  rewrite E3; apply: Rmult_le_compat_r => //.
  by apply: (@newton_sq_le p Hp10 _ HBX).
have T2 := Rabs_triang (Y - A * I + (A - B * Z) * I) ((B * Z) * (X * B - P)).
have T3 := Rabs_triang (Y - A * I) ((A - B * Z) * I).
have T1 := Rabs_triang (Y - A * I + (A - B * Z) * I + (B * Z) * (X * B - P))
                       (Z * (B * (2 - X * B) - / X)).
rewrite Hdecomp.
apply: Rle_trans T1 _.
have T4 : Rabs (Y - A * I + (A - B * Z) * I + (B * Z) * (X * B - P))
            + Rabs (Z * (B * (2 - X * B) - / X))
    <= Rabs (Y - A * I) + Rabs ((A - B * Z) * I)
       + Rabs ((B * Z) * (X * B - P)) + Rabs (Z * (B * (2 - X * B) - / X))
  by lra.
apply: Rle_trans T4 _.
by apply: (@div_error_assembly (Rabs (B * X)) (Rabs I) R0).
Qed.

Lemma ThreeDivAux_error mul1 mul2 mul3 d1 d2 d3 :
  ties_to_even choice ->
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  head_one mul1 ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 ->
     Rabs (TWval y - 1) <= 40 * (u * u) ->
     Rabs (TWval (mul3 a y) - TWval a * TWval y)
       <= d3 * Rabs (TWval a * TWval y)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  0 <= d3 -> d3 <= u * u ->
  forall z x, isTW z -> isTW x -> tw0 x <> 0 ->
    Rabs (TWval (ThreeDivAux mul1 mul2 mul3 z x) - TWval z / TWval x)
      <= (d1 * (1 + 71 * (u * u)) + (d2 + d3) * (1 + 107 * (u * u))
          + 1165 * (u * u * u * u)) * Rabs (TWval z / TWval x).
Proof.
move=> Hc Hmul1 Hmul2 Hhead Herr1 Herr2 Herr3 Hd10 Hd1u Hd20 Hd2u Hd30 Hd3u
       z x Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1 : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
rewrite /ThreeDivAux.
set b := reciBW (tw0 x) (tw1 x).
have HDW : isDW b by apply: (@reciB_isDW p Hp2 Hp10 choice choice_sym).
have HBX := @reciBW_x_err p Hp2 Hp10 choice choice_sym x Hx Hx0.
rewrite -/b in HBX.
have Hu3 : u * u * u <= / 1024 * (u * u) by nra.
have HBX35 : Rabs (TWval b * TWval x - 1) <= 35 * (u * u)
  by clear -HBX Hu0 Hu1024 Hu3; nra.
(* [i = 2 - mul1 b x] is a triple word with head [1].                         *)
have Hprod1 : isTW (mul1 b x) by apply: Hmul1.
have Hhead1 : tw0 (mul1 b x) = 1 by apply: Hhead.
set i := sub2TW (mul1 b x).
have Hi : isTW i by apply: (@sub2TW_isTW p Hp2).
have Hi0 : tw0 i = 1
  by rewrite /i; case: (mul1 b x) Hhead1 => t0 t1 t2 /= ->; ring.
have HIval : TWval i = 2 - TWval (mul1 b x) by rewrite /i TWval_sub2TW.
have HI1 : Rabs (TWval i - 1) <= 40 * (u * u).
  rewrite HIval.
  apply: (@sub2_near_one p Hp10
            (TWval b) (TWval x) (TWval (mul1 b x)) d1) => //.
  by apply: Herr1.
(* the three products, then the core.                                         *)
have Herr1' := Herr1 _ _ HDW Hx.
have Herr2' := Herr2 _ _ HDW Hz.
have Herr3' := Herr3 _ _ (Hmul2 _ _ HDW Hz) Hi Hi0 HI1.
rewrite HIval in Herr3'.
by apply: (@div_error_core (TWval b) (TWval x) (TWval z) (TWval (mul1 b x))
             (TWval (mul2 b z)) (TWval (mul3 (mul2 b z) i)) d1 d2 d3).
Qed.

(* Theorem 10, accurate variant.  The paper states [24u^3 + 1509u^4]; the     *)
(* honest bound is [29u^3 + 2576u^4].  BOTH terms move, and the [u^3] one is  *)
(* the paper's, not ours: [24 = 10.5 + 10.5 + 3] assumes Algorithm 20 costs   *)
(* [3u^3], whereas its honest cost on a TRIPLE word is [8u^3] -- see          *)
(* [ThreeProdOneTW_error].  With [delta3 = 8u^3 + 1330u^4] the assembly gives *)
(* [29u^3 + 2575.81u^4] at [p = 10], whence [2576].                           *)
Lemma ThreeDiv_error z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeDiv z x) - TWval z / TWval x) <=
     (27 * (u * u * u) + 2500 * (u * u * u * u)) *
       Rabs (TWval z / TWval x).
Proof.
move=> Hc Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Hu2 : u * u <= / 1024 * u by nra.
have Hu3 : u * u * u <= / 1024 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 1024 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 1024 * (u * u * u * u) by nra.
(* the two black boxes: [d1 = d2] is Algorithm 11's error, [d3] Algorithm     *)
(* 20's; both are far below the [u] the assembly asks for.                    *)
have Hd0 : 0 <= 105 / 10 * (u * u * u) + 39 * (u * u * u * u) by nra.
have Hdu : 105 / 10 * (u * u * u) + 39 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= 6 * (u * u * u) + 1250 * (u * u * u * u) by nra.
have Heu : 6 * (u * u * u) + 1250 * (u * u * u * u) <= u * u by nra.
have Hgen := @ThreeDivAux_error ThreeProdDW ThreeProdDW ThreeProdOneTW
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (6 * (u * u * u) + 1250 * (u * u * u * u)) Hc
  (fun b y Hb Hy => @ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy => @ThreeProdDW_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (@ThreeProdDW_head_one p Hp2 Hp10 choice choice_sym Hc)
  (fun b y Hb Hy => @ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy => @ThreeProdDW_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun a y Ha Hy Hy0 Hy1 =>
     @ThreeProdOneTW_error p Hp2 Hp6 choice choice_sym a y Hc Ha Hy Hy0 Hy1)
  Hd0 Hdu Hd0 Hdu He0 Heu z x Hz Hx Hx0.
rewrite /ThreeDiv.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
by nra.
Qed.

(* Theorem 10, fast variant.  The paper states [39u^3 + 1582u^4]; honestly    *)
(* [44u^3 + 2649.11u^4] at [p = 10], whence [2650].  Same cause: [44 =        *)
(* 18 + 18 + 8], not [39 = 18 + 18 + 3].                                      *)
Lemma ThreeDivFast_error z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeDivFast z x) - TWval z / TWval x) <=
     (42 * (u * u * u) + 2575 * (u * u * u * u)) *
       Rabs (TWval z / TWval x).
Proof.
move=> Hc Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := @u_le_1024 p Hp10.
have Hu2 : u * u <= / 1024 * u by nra.
have Hu3 : u * u * u <= / 1024 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 1024 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 1024 * (u * u * u * u) by nra.
have Hd0 : 0 <= 18 * (u * u * u) + 75 * (u * u * u * u) by nra.
have Hdu : 18 * (u * u * u) + 75 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= 6 * (u * u * u) + 1250 * (u * u * u * u) by nra.
have Heu : 6 * (u * u * u) + 1250 * (u * u * u * u) <= u * u by nra.
have Hgen := @ThreeDivAux_error ThreeProdDWFast ThreeProdDWFast ThreeProdOneTW
  (18 * (u * u * u) + 75 * (u * u * u * u))
  (18 * (u * u * u) + 75 * (u * u * u * u))
  (6 * (u * u * u) + 1250 * (u * u * u * u)) Hc
  (fun b y Hb Hy =>
     @ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_isTW p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (@ThreeProdDWFast_head_one p Hp2 Hp10 choice choice_sym Hc)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDWFast_error p Hp2 Hp6 choice choice_sym b y Hc Hb Hy)
  (fun a y Ha Hy Hy0 Hy1 =>
     @ThreeProdOneTW_error p Hp2 Hp6 choice choice_sym a y Hc Ha Hy Hy0 Hy1)
  Hd0 Hdu Hd0 Hdu He0 Heu z x Hz Hx Hx0.
rewrite /ThreeDivFast.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
by nra.
Qed.

End SecThreeDiv.
