From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From threewords Require Import TwoSum TWR VecSum ThreeProd ThreeProdDW ThreeProdOne.
From threewords Require Import ThreeSqRt.

(* THE SEED OF ALGORITHM 15, WITH NO FUSED MULTIPLY-ADD.                      *)
(*                                                                            *)
(* `twpaper.v' transcribes the paper's square root onto primitive floats, and *)
(* Rocq's primitive floats have no fused multiply-add.  Three lines of the    *)
(* paper's seed are of the form `RN(v + a * w)', one rounding; here each is    *)
(* two, `RN(v + RN(a * w))'.  This file is about those three.                 *)
(*                                                                            *)
(* THEY ARE NOT THE ONLY THREE IN ALGORITHM 15.  `ThreeProdDW' has two more   *)
(* of its own (`c' and `z31'), and so, being built the same way, does         *)
(* `ThreeProdOneTW'.  What saves the shape of the thing is that               *)
(* `ThreeSqRtAuxN_error' is GENERIC in the three products and in the `d1',    *)
(* `d2', `d3' they are out by: the seed enters through two facts and no        *)
(* others -- that it is a double word, and that `b sqrt x' is within so many  *)
(* `u^2' of one -- and the products enter only through those three numbers.   *)
(* So this file settles the seed, and the products need the same treatment    *)
(* separately: their own `d' re-derived with the extra roundings in.          *)
(*                                                                            *)
(* AND THE ROOM IS SMALL.  The seed's `100u^2' becomes `105u^2' at            *)
(* `sqrtAux_i2_near_1', and `ThreeProdOneTW_error_c' takes its tolerance as a *)
(* parameter no larger than `112'.  So what comes out below has to stay       *)
(* under about `107u^2'.                                                      *)

(* The paper's own settings, so that lemmas stated here take their arguments *)
(* the way the paper's do and its proof text reads across unchanged.          *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecSeedNoFMA.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
Hypothesis Hp11 : (11 <= p)%Z.

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
Local Notation ThreeProdDW := (ThreeProdDW p choice).
Local Notation ThreeProdOneTW := (ThreeProdOneTW p choice).
Local Notation head_half := (head_half p).

(* The two facts about one rounding that every bound below is made of.        *)
Lemma rnd_err v : Rabs (RND v - v) <= u * Rabs v.
Proof. by apply: relative_error_le. Qed.

Lemma rnd_abs v : Rabs (RND v) <= (1 + u) * Rabs v.
Proof.
have H := rnd_err v.
have T : Rabs (RND v) <= Rabs (RND v - v) + Rabs v.
  have E : RND v = RND v - v + v by ring.
  by rewrite {1}E; apply: Rabs_triang.
by lra.
Qed.

(* The paper's seed up to the first fused line, taken as it stands.           *)
Local Notation sqrtA := (sqrtA p choice).
Local Notation sqrtA' := (sqrtA' p choice).
Local Notation sqrtH0_1 := (sqrtH0_1 p choice).
Local Notation sqrtH11_1 := (sqrtH11_1 p choice).
Local Notation sqrtH01_2 := (sqrtH01_2 p choice).
Local Notation sqrtH11_2 := (sqrtH11_2 p choice).
Local Notation sqrtH0_2 := (sqrtH0_2 p choice).
Local Notation sqrtB01 := (sqrtB01 p choice).
Local Notation sqrtB11 := (sqrtB11 p choice).

(* AND THE PAPER'S LEMMAS UNDER THEIR OWN NAMES, with the precision and the   *)
(* rounding already filled in.  Inside the paper's own section those are      *)
(* section variables and every call reads `lemma Fx0 Hx0'; once the section   *)
(* closes they become arguments, and a proof copied across would have to      *)
(* pass them at every call.  Bridged here instead, once, so that the paper's  *)
(* proof text is reusable word for word.                                      *)
Local Notation u_le_2048 := (u_le_2048 Hp11).
Local Notation sqrtA_gt0 := (sqrtA_gt0 Hp2 Hp11 choice).
Local Notation sqrtA_sq_le := (sqrtA_sq_le Hp2 Hp11 choice).
Local Notation sqrtA_bound_full := (sqrtA_bound_full Hp2 Hp11 choice).
Local Notation sqrtH0_1_le := (sqrtH0_1_le Hp2 Hp11 choice).
Local Notation sqrtH11_1_le := (sqrtH11_1_le Hp2 Hp11 choice).
Local Notation sqrtB01_ge := (sqrtB01_ge Hp2 Hp11 choice).
Local Notation sqrtB11_le := (sqrtB11_le Hp2 Hp11 choice).
Local Notation sqrtH0_2_exact := (sqrtH0_2_exact Hp2 Hp11 choice).
Local Notation isTW_TWval_gt0 := (isTW_TWval_gt0 Hp2 Hp11).
Local Notation isTW_tw2_le := (isTW_tw2_le Hp2).
Local Notation TwoProd_exact := (TwoProd_exact Hp2 choice).
Local Notation Fast2Sum_correct := (Fast2Sum_correct Hp2 choice).
Local Notation format_Fast2Sum := (format_Fast2Sum Hp2 choice).
Local Notation magnitude_Fast2Sum := (magnitude_Fast2Sum Hp2 choice).
Local Notation format_scale := (format_scale Hp2 choice).
Local Notation sub32TW_isTW := (sub32TW_isTW Hp2).

(* And the three lines that differ: one rounding becomes two.                 *)
Definition sqrtH1_1n (x0 x1 : R) : R :=
  RND (sqrtH11_1 x0 + RND (sqrtA x0 * x1)).

Definition sqrtH1_2n (x0 x1 : R) : R :=
  - RND (sqrtH11_2 x0 + RND (sqrtA' x0 * sqrtH1_1n x0 x1)).

Definition sqrtB12n (x0 x1 : R) : R :=
  RND (sqrtB11 x0 + RND (sqrtA x0 * sqrtH1_2n x0 x1)).

Definition sqrtBn (x0 x1 : R) : dwR :=
  Fast2Sum (sqrtB01 x0) (sqrtB12n x0 x1).

Definition sqrtBWn (x0 x1 : R) : twR :=
  TWR (dwh (sqrtBn x0 x1)) (dwl (sqrtBn x0 x1)) 0.

(* ---------------------------------------------------------------------------*)
(*  The first fused line: `h1(1) <- RN(h11(1) + a x1)'                        *)
(* ---------------------------------------------------------------------------*)

(* The second word of a triple word is below two units of its first.          *)
Lemma tw1_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) -> Rabs x1 <= 2 * u * x0.
Proof.
move=> Fx0 Hx0 Hx1; have Hu0 : 0 < u by apply: u_gt_0.
case: Hx1 => [->|Hs]; first by rewrite Rabs_R0; nra.
have Ha0 : Rabs x0 = x0 by apply: Rabs_pos_eq; lra.
rewrite -Ha0.
by have := ulp_2u radix2 Hp2 x0; lra.
Qed.

Lemma sqrtA_x1_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtA x0 * x1) <= 2 * u * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1; have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hb := tw1_le Fx0 Hx0 Hx1.
rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
by nra.
Qed.

(* The sum the first line rounds, with the product rounded first.  One extra  *)
(* unit against the paper's `3u', and it is paid back below.                   *)
Lemma sqrtH1_1n_sum_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH11_1 x0 + RND (sqrtA x0 * x1))
    <= (3 * u + 2 * (u * u)) * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have H11 := sqrtH11_1_le Fx0 Hx0.
have Hax1 := sqrtA_x1_le Fx0 Hx0 Hx1.
have Hr1 : Rabs (RND (sqrtA x0 * x1)) <= (1 + u) * (2 * u * (sqrtA x0 * x0)).
  apply: Rle_trans (rnd_abs _) _.
  by apply: Rmult_le_compat_l; lra.
by apply: Rle_trans (Rabs_triang _ _) _; nra.
Qed.

(* So the line itself stays inside the four units the paper's own does.       *)
Lemma sqrtH1_1n_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH1_1n x0 x1) <= 4 * u * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hs := sqrtH1_1n_sum_le Fx0 Hx0 Hx1.
rewrite /sqrtH1_1n.
apply: Rle_trans (rnd_abs _) _.
apply: Rle_trans (_ : (1 + u) * ((3 * u + 2 * (u * u)) * (sqrtA x0 * x0)) <= _).
  by apply: Rmult_le_compat_l; lra.
have Hk : (1 + u) * (3 * u + 2 * (u * u)) <= 4 * u by nra.
have -> : (1 + u) * ((3 * u + 2 * (u * u)) * (sqrtA x0 * x0))
        = ((1 + u) * (3 * u + 2 * (u * u))) * (sqrtA x0 * x0) by ring.
by apply: Rmult_le_compat_r; lra.
Qed.

(* AND WHAT THE EXTRA ROUNDING COSTS.  The paper's line is out by `u' of what *)
(* it is given, so `3u^2'; ours is out by that and by the rounding of the      *)
(* product as well, so `5u^2'.  This is the first of the three places the      *)
(* missing fused multiply-add is paid for.                                     *)
Lemma eps1n_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH1_1n x0 x1 - (sqrtH11_1 x0 + sqrtA x0 * x1))
    <= 6 * (u * u) * (sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hs := sqrtH1_1n_sum_le Fx0 Hx0 Hx1.
have Hax1 := sqrtA_x1_le Fx0 Hx0 Hx1.
have E : sqrtH1_1n x0 x1 - (sqrtH11_1 x0 + sqrtA x0 * x1)
       = (RND (sqrtH11_1 x0 + RND (sqrtA x0 * x1))
          - (sqrtH11_1 x0 + RND (sqrtA x0 * x1)))
       + (RND (sqrtA x0 * x1) - sqrtA x0 * x1) by rewrite /sqrtH1_1n; ring.
rewrite E.
apply: Rle_trans (Rabs_triang _ _) _.
have A1 : Rabs (RND (sqrtH11_1 x0 + RND (sqrtA x0 * x1))
                - (sqrtH11_1 x0 + RND (sqrtA x0 * x1)))
        <= u * ((3 * u + 2 * (u * u)) * (sqrtA x0 * x0)).
  apply: Rle_trans (rnd_err _) _.
  by apply: Rmult_le_compat_l; lra.
have A2 : Rabs (RND (sqrtA x0 * x1) - sqrtA x0 * x1)
        <= u * (2 * u * (sqrtA x0 * x0)).
  apply: Rle_trans (rnd_err _) _.
  by apply: Rmult_le_compat_l; lra.
have Hk : u * (3 * u + 2 * (u * u)) + u * (2 * u) <= 6 * (u * u) by nra.
have Hid : u * ((3 * u + 2 * (u * u)) * (sqrtA x0 * x0))
         + u * (2 * u * (sqrtA x0 * x0))
         = (u * (3 * u + 2 * (u * u)) + u * (2 * u)) * (sqrtA x0 * x0) by ring.
apply: Rle_trans (_ : u * ((3 * u + 2 * (u * u)) * (sqrtA x0 * x0))
                      + u * (2 * u * (sqrtA x0 * x0)) <= _); first by lra.
rewrite Hid.
by apply: Rmult_le_compat_r; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The second fused line: `h1(2) <- -RN(h11(2) + a' h1(1))'                  *)
(* ---------------------------------------------------------------------------*)

(* [a/2] is a float: halving is a scaling by a power of two and never leaves  *)
(* the format.                                                                *)
Lemma format_sqrtA' x0 : format (sqrtA' x0).
Proof.
have -> : sqrtA' x0 = sqrtA x0 * pow (-1) by rewrite /ThreeSqRt.sqrtA' /=; lra.
apply/(format_scale); rewrite /ThreeSqRt.sqrtA.
by apply: generic_format_round.
Qed.

(* The error of the middle two-product, which the paper proves inline.        *)
Lemma sqrtH11_2_le x0 : format x0 -> 0 < x0 ->
  Rabs (sqrtH11_2 x0) <= u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0))).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have H01 := sqrtH0_1_le Fx0 Hx0.
have FA2 := format_sqrtA' x0.
have F01 : format (sqrtH0_1 x0) by apply: generic_format_round.
have HE2 := TwoProd_exact FA2 F01.
have -> : sqrtH11_2 x0 = sqrtA' x0 * sqrtH0_1 x0 - sqrtH01_2 x0.
  by rewrite /sqrtH11_2 /sqrtH01_2; lra.
have -> : sqrtH01_2 x0 = RND (sqrtA' x0 * sqrtH0_1 x0) by [].
rewrite Rabs_minus_sym.
apply: Rle_trans (rnd_err _) _.
rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
apply: Rmult_le_compat_l; first lra.
by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H01].
Qed.

(* The sum the second line rounds, with the product rounded first.            *)
Lemma sqrtH1_2n_sum_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH11_2 x0 + RND (sqrtA' x0 * sqrtH1_1n x0 x1))
    <= 5 / 2 * (1 + u) * u * (sqrtA x0 * sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have HP : 0 < sqrtA x0 * x0 by nra.
have H112 := sqrtH11_2_le Fx0 Hx0.
have H11n := sqrtH1_1n_le Fx0 Hx0 Hx1.
have Hmix : Rabs (sqrtA' x0 * sqrtH1_1n x0 x1)
          <= sqrtA' x0 * (4 * u * (sqrtA x0 * x0)).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
  by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H11n].
have Hr : Rabs (RND (sqrtA' x0 * sqrtH1_1n x0 x1))
        <= (1 + u) * (sqrtA' x0 * (4 * u * (sqrtA x0 * x0))).
  apply: Rle_trans (rnd_abs _) _.
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans (Rabs_triang _ _) _.
apply: Rle_trans (_ : u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0)))
                    + (1 + u) * (sqrtA' x0 * (4 * u * (sqrtA x0 * x0))) <= _).
  by lra.
by rewrite HA'; nra.
Qed.

(* So the second line too stays inside the paper's own three units.           *)
Lemma sqrtH1_2n_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtH1_2n x0 x1) <= 3 * u.
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hsq := sqrtA_sq_le Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hs := sqrtH1_2n_sum_le Fx0 Hx0 Hx1.
rewrite /sqrtH1_2n Rabs_Ropp.
apply: Rle_trans (rnd_abs _) _.
apply: Rle_trans
  (_ : (1 + u) * (5 / 2 * (1 + u) * u * (sqrtA x0 * sqrtA x0 * x0)) <= _).
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans
  (_ : (1 + u) * (5 / 2 * (1 + u) * u * (1 + 12 * u + 62 * (u * u))) <= _).
  apply: Rmult_le_compat_l; first lra.
  by apply: Rmult_le_compat_l; [nra | exact: Hsq].
by nra.
Qed.

(* AND WHAT THE SECOND EXTRA ROUNDING COSTS.                                  *)
Lemma epsn_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (- sqrtH1_2n x0 x1 - (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1n x0 x1))
    <= 5 * (u * u) * (sqrtA x0 * sqrtA x0 * x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have HP : 0 < sqrtA x0 * x0 by nra.
have HQ : 0 < sqrtA x0 * sqrtA x0 * x0 by nra.
have Hs := sqrtH1_2n_sum_le Fx0 Hx0 Hx1.
have H11n := sqrtH1_1n_le Fx0 Hx0 Hx1.
have Hmix : Rabs (sqrtA' x0 * sqrtH1_1n x0 x1)
          <= 2 * u * (sqrtA x0 * sqrtA x0 * x0).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA' x0)); last by rewrite HA'; lra.
  apply: Rle_trans (_ : sqrtA' x0 * (4 * u * (sqrtA x0 * x0)) <= _).
    by apply: Rmult_le_compat_l; [rewrite HA'; lra | exact: H11n].
  by rewrite HA'; nra.
have E : - sqrtH1_2n x0 x1 - (sqrtH11_2 x0 + sqrtA' x0 * sqrtH1_1n x0 x1)
       = (RND (sqrtH11_2 x0 + RND (sqrtA' x0 * sqrtH1_1n x0 x1))
          - (sqrtH11_2 x0 + RND (sqrtA' x0 * sqrtH1_1n x0 x1)))
       + (RND (sqrtA' x0 * sqrtH1_1n x0 x1) - sqrtA' x0 * sqrtH1_1n x0 x1)
  by rewrite /sqrtH1_2n; ring.
rewrite E.
apply: Rle_trans (Rabs_triang _ _) _.
have A1 : Rabs (RND (sqrtH11_2 x0 + RND (sqrtA' x0 * sqrtH1_1n x0 x1))
                - (sqrtH11_2 x0 + RND (sqrtA' x0 * sqrtH1_1n x0 x1)))
        <= u * (5 / 2 * (1 + u) * u * (sqrtA x0 * sqrtA x0 * x0)).
  apply: Rle_trans (rnd_err _) _.
  by apply: Rmult_le_compat_l; lra.
have A2 : Rabs (RND (sqrtA' x0 * sqrtH1_1n x0 x1)
                - sqrtA' x0 * sqrtH1_1n x0 x1)
        <= u * (2 * u * (sqrtA x0 * sqrtA x0 * x0)).
  apply: Rle_trans (rnd_err _) _.
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans
  (_ : u * (5 / 2 * (1 + u) * u * (sqrtA x0 * sqrtA x0 * x0))
     + u * (2 * u * (sqrtA x0 * sqrtA x0 * x0)) <= _); first by lra.
have Hk : u * (5 / 2 * (1 + u) * u) + u * (2 * u) <= 5 * (u * u) by nra.
have -> : u * (5 / 2 * (1 + u) * u * (sqrtA x0 * sqrtA x0 * x0))
        + u * (2 * u * (sqrtA x0 * sqrtA x0 * x0))
        = (u * (5 / 2 * (1 + u) * u) + u * (2 * u))
          * (sqrtA x0 * sqrtA x0 * x0) by ring.
by apply: Rmult_le_compat_r; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The third fused line: `b12 <- RN(b11 + a h1(2))'                          *)
(* ---------------------------------------------------------------------------*)

Lemma sqrtB12n_sum_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtB11 x0 + RND (sqrtA x0 * sqrtH1_2n x0 x1))
    <= (4 * u + 3 * (u * u)) * sqrtA x0.
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hb11 := sqrtB11_le Fx0 Hx0.
have Hh12 := sqrtH1_2n_le Fx0 Hx0 Hx1.
have Hmix : Rabs (sqrtA x0 * sqrtH1_2n x0 x1) <= sqrtA x0 * (3 * u).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
  by apply: Rmult_le_compat_l; lra.
have Hr : Rabs (RND (sqrtA x0 * sqrtH1_2n x0 x1))
        <= (1 + u) * (sqrtA x0 * (3 * u)).
  apply: Rle_trans (rnd_abs _) _.
  by apply: Rmult_le_compat_l; lra.
by apply: Rle_trans (Rabs_triang _ _) _; nra.
Qed.

(* The second word of the seed is no larger than the first, which is what     *)
(* Fast2Sum asks of it.                                                       *)
Lemma sqrtB12n_le_B01 x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtB12n x0 x1) <= Rabs (sqrtB01 x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hb01 := sqrtB01_ge Fx0 Hx0.
have Hs := sqrtB12n_sum_le Fx0 Hx0 Hx1.
rewrite /sqrtB12n.
apply: Rle_trans (rnd_abs _) _.
apply: Rle_trans (_ : (1 + u) * ((4 * u + 3 * (u * u)) * sqrtA x0) <= _).
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans (_ : (1 - u) / 2 * sqrtA x0 <= _); last by lra.
have -> : (1 + u) * ((4 * u + 3 * (u * u)) * sqrtA x0)
        = ((1 + u) * (4 * u + 3 * (u * u))) * sqrtA x0 by ring.
by apply: Rmult_le_compat_r; nra.
Qed.

(* AND WHAT THE THIRD EXTRA ROUNDING COSTS.                                   *)
Lemma etan_le x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (sqrtB12n x0 x1 - (sqrtB11 x0 + sqrtA x0 * sqrtH1_2n x0 x1))
    <= 8 * (u * u) * sqrtA x0.
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HA := sqrtA_gt0 Fx0 Hx0.
have Hh12 := sqrtH1_2n_le Fx0 Hx0 Hx1.
have Hs := sqrtB12n_sum_le Fx0 Hx0 Hx1.
have Hmix : Rabs (sqrtA x0 * sqrtH1_2n x0 x1) <= sqrtA x0 * (3 * u).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA x0)); last lra.
  by apply: Rmult_le_compat_l; lra.
have E : sqrtB12n x0 x1 - (sqrtB11 x0 + sqrtA x0 * sqrtH1_2n x0 x1)
       = (RND (sqrtB11 x0 + RND (sqrtA x0 * sqrtH1_2n x0 x1))
          - (sqrtB11 x0 + RND (sqrtA x0 * sqrtH1_2n x0 x1)))
       + (RND (sqrtA x0 * sqrtH1_2n x0 x1) - sqrtA x0 * sqrtH1_2n x0 x1)
  by rewrite /sqrtB12n; ring.
rewrite E.
apply: Rle_trans (Rabs_triang _ _) _.
have A1 : Rabs (RND (sqrtB11 x0 + RND (sqrtA x0 * sqrtH1_2n x0 x1))
                - (sqrtB11 x0 + RND (sqrtA x0 * sqrtH1_2n x0 x1)))
        <= u * ((4 * u + 3 * (u * u)) * sqrtA x0).
  apply: Rle_trans (rnd_err _) _.
  by apply: Rmult_le_compat_l; lra.
have A2 : Rabs (RND (sqrtA x0 * sqrtH1_2n x0 x1)
                - sqrtA x0 * sqrtH1_2n x0 x1)
        <= u * (sqrtA x0 * (3 * u)).
  apply: Rle_trans (rnd_err _) _.
  by apply: Rmult_le_compat_l; lra.
apply: Rle_trans (_ : u * ((4 * u + 3 * (u * u)) * sqrtA x0)
                    + u * (sqrtA x0 * (3 * u)) <= _); first by lra.
have -> : u * ((4 * u + 3 * (u * u)) * sqrtA x0) + u * (sqrtA x0 * (3 * u))
        = (u * (4 * u + 3 * (u * u)) + 3 * (u * u)) * sqrtA x0 by ring.
by apply: Rmult_le_compat_r; nra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The seed as a double word, and Newton's form of it                        *)
(* ---------------------------------------------------------------------------*)

(* The seed is a double word: Fast2Sum gives one as soon as its two arguments *)
(* are the right way round, which `sqrtB12n_le_B01' says.                     *)
Lemma sqrtBn_isDW x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  isDW (sqrtBWn x0 x1).
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (sqrtB01 x0).
  by rewrite /ThreeSqRt.sqrtB01 /MULTmore.TwoProd /=; apply: generic_format_round.
have F12 : format (sqrtB12n x0 x1).
  by rewrite /sqrtB12n; apply: generic_format_round.
have Hord := sqrtB12n_le_B01 Fx0 Hx0 Hx1.
have Hmag := magnitude_Fast2Sum F01 F12 (fun _ => Hord).
have Hfor := format_Fast2Sum (sqrtB01 x0) (sqrtB12n x0 x1).
rewrite /sqrtBWn /sqrtBn.
case E : (Fast2Sum (sqrtB01 x0) (sqrtB12n x0 x1)) => [s e].
rewrite E in Hmag Hfor.
rewrite /magnitudeDWR in Hmag.
case: Hfor => Fs Fe.
split => //.
by right; rewrite dwhE dwlE; lra.
Qed.

Lemma TWval_sqrtBWn x0 x1 : format x0 -> 0 < x0 ->
  (x1 = 0 \/ Rabs x1 < ulp x0) ->
  TWval (sqrtBWn x0 x1) = sqrtB01 x0 + sqrtB12n x0 x1.
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (sqrtB01 x0).
  by rewrite /ThreeSqRt.sqrtB01; apply: generic_format_round.
have F12 : format (sqrtB12n x0 x1).
  by rewrite /sqrtB12n; apply: generic_format_round.
have Hord := sqrtB12n_le_B01 Fx0 Hx0 Hx1.
have Hc := Fast2Sum_correct F01 F12 (fun _ => Hord).
by rewrite /sqrtBWn /TWval /sqrtBn Rplus_0_r; exact: Hc.
Qed.

(* Nine and eight, where the paper has five and four: the three extra          *)
(* roundings, each already paid for above.                                     *)
Lemma seed_num : 9 * (1 + 12 * u + 62 * (u * u)) + 8 <= 18.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
by nra.
Qed.

Lemma sqrtBWn_newton_form x : isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBWn (tw0 x) (tw1 x))
        - sqrtA (tw0 x)
          * (3 / 2 - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * TWval x))
    <= 18 * (u * u) * sqrtA (tw0 x).
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
have FA : format (sqrtA (tw0 x)).
  by rewrite /ThreeSqRt.sqrtA; apply: generic_format_round.
have FA2 := format_sqrtA' (tw0 x).
have F01 : format (sqrtH0_1 (tw0 x)).
  by rewrite /ThreeSqRt.sqrtH0_1 /MULTmore.TwoProd /=; apply: generic_format_round.
have F02 : format (sqrtH0_2 (tw0 x)) by apply: sqrtH0_2_exact.
have P1 := TwoProd_exact FA Fx0.
have P2 := TwoProd_exact FA2 F01.
have P3 := TwoProd_exact FA F02.
set eps1 := sqrtH1_1n (tw0 x) (tw1 x)
            - (sqrtH11_1 (tw0 x) + sqrtA (tw0 x) * tw1 x).
set eps := - sqrtH1_2n (tw0 x) (tw1 x)
           - (sqrtH11_2 (tw0 x)
              + sqrtA' (tw0 x) * sqrtH1_1n (tw0 x) (tw1 x)).
set eta := sqrtB12n (tw0 x) (tw1 x)
           - (sqrtB11 (tw0 x) + sqrtA (tw0 x) * sqrtH1_2n (tw0 x) (tw1 x)).
have Hdec : TWval (sqrtBWn (tw0 x) (tw1 x))
    - sqrtA (tw0 x)
      * (3 / 2 - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * TWval x)
    = (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x)) * tw2 x
      - (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1
      - sqrtA (tw0 x) * eps + eta.
  rewrite (TWval_sqrtBWn Fx0 Hx0 Hx1s) TWval_split.
  apply: (@newton_form_id (sqrtA (tw0 x)) (sqrtB01 (tw0 x))
            (sqrtB11 (tw0 x)) (sqrtB12n (tw0 x) (tw1 x))
            (sqrtH0_2 (tw0 x)) (sqrtH1_2n (tw0 x) (tw1 x))
            (sqrtH01_2 (tw0 x)) (sqrtH11_2 (tw0 x)) (sqrtH0_1 (tw0 x))
            (sqrtH11_1 (tw0 x)) (sqrtH1_1n (tw0 x) (tw1 x))
            (tw0 x) (tw1 x) (tw2 x) eps1 eps eta).
  - by rewrite /ThreeSqRt.sqrtH0_1 /ThreeSqRt.sqrtH11_1; lra.
  - by rewrite /ThreeSqRt.sqrtH01_2 /ThreeSqRt.sqrtH11_2 -HA'; lra.
  - by [].
  - by rewrite /eps1; lra.
  - by rewrite /eps -HA'; lra.
  - by rewrite /eta; lra.
  by rewrite /ThreeSqRt.sqrtB01 /ThreeSqRt.sqrtB11; lra.
rewrite Hdec.
have Hx2 := isTW_tw2_le Hx.
have Ha0 : Rabs (tw0 x) = tw0 x by apply: Rabs_pos_eq; lra.
rewrite Ha0 in Hx2.
have Heps1 : Rabs eps1 <= 6 * (u * u) * (sqrtA (tw0 x) * tw0 x)
  by rewrite /eps1; apply: eps1n_le.
have Heps : Rabs eps
    <= 5 * (u * u) * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)
  by rewrite /eps; apply: epsn_le.
have Heta : Rabs eta <= 8 * (u * u) * sqrtA (tw0 x)
  by rewrite /eta; apply: etan_le.
have Ha3 : 0 <= (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
  by nra.
have Ha2 : 0 <= (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) by nra.
have B1 : Rabs ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
                * tw2 x)
    <= (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u))).
  rewrite Rabs_mult (Rabs_pos_eq ((1 / 2)
            * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x)))); last lra.
  apply: Rle_trans (_ : (1 / 2)
      * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
      * (2 * (u * u) * tw0 x) <= _).
    by apply: Rmult_le_compat_l; lra.
  have -> : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x) * sqrtA (tw0 x))
              * (2 * (u * u) * tw0 x)
      = (u * u) * (sqrtA (tw0 x)
                   * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) by field.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; lra.
have B2 : Rabs ((1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x)) * eps1)
    <= 3 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u))).
  rewrite Rabs_mult (Rabs_pos_eq ((1 / 2)
            * (sqrtA (tw0 x) * sqrtA (tw0 x)))); last lra.
  apply: Rle_trans (_ : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x))
      * (6 * (u * u) * (sqrtA (tw0 x) * tw0 x)) <= _).
    by apply: Rmult_le_compat_l; lra.
  have -> : (1 / 2) * (sqrtA (tw0 x) * sqrtA (tw0 x))
              * (6 * (u * u) * (sqrtA (tw0 x) * tw0 x))
      = 3 * (u * u) * (sqrtA (tw0 x)
                   * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) by field.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; lra.
have B3 : Rabs (sqrtA (tw0 x) * eps)
    <= 5 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u))).
  rewrite Rabs_mult (Rabs_pos_eq (sqrtA (tw0 x))); last lra.
  apply: Rle_trans (_ : sqrtA (tw0 x) * (5 * (u * u)
      * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) <= _).
    by apply: Rmult_le_compat_l; lra.
  have -> : sqrtA (tw0 x) * (5 * (u * u)
              * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x))
      = 5 * (u * u) * (sqrtA (tw0 x)
                   * (sqrtA (tw0 x) * sqrtA (tw0 x) * tw0 x)) by field.
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; lra.
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
            + 3 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 5 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 8 * (u * u) * sqrtA (tw0 x)
    <= 18 * (u * u) * sqrtA (tw0 x).
  have -> : (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 3 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 5 * (u * u) * (sqrtA (tw0 x) * (1 + 12 * u + 62 * (u * u)))
            + 8 * (u * u) * sqrtA (tw0 x)
      = (u * u) * sqrtA (tw0 x)
        * (9 * (1 + 12 * u + 62 * (u * u)) + 8) by field.
  have -> : 18 * (u * u) * sqrtA (tw0 x)
      = (u * u) * sqrtA (tw0 x) * 18 by field.
  apply: Rmult_le_compat_l; first by nra.
  exact: seed_num.
by lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  And the fact the assembly actually asks for                               *)
(* ---------------------------------------------------------------------------*)

(* `b sqrt x' is within so many `u^2' of one.  Eighty-five of them are the     *)
(* NEWTON RESIDUAL, which does not move: it is `e^2 (e + 3) / 2' with          *)
(* `e = A sqrt x - 1' bounded by `15u/2', and `A' is the paper's own seed,     *)
(* untouched by the missing instruction.  The rest is the rounding collected   *)
(* above -- eleven for the paper, nineteen here.                               *)
Lemma sqrtBWn_x_err_crude x : isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * sqrt (TWval x) - 1)
    <= 104 * (u * u).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have HX0 := isTW_TWval_gt0 Hx Hx0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have HA := sqrtA_gt0 Fx0 Hx0.
have HN := sqrtBWn_newton_form Hx Hx0.
have [Hlo Hhi] := sqrtA_bound_full Hx Hx0.
set B := TWval (sqrtBWn (tw0 x) (tw1 x)) in HN *.
set A := sqrtA (tw0 x) in HN HA Hlo Hhi *.
set s := sqrt (TWval x) in HsX Hs0 Hlo Hhi *.
rewrite -HsX in HN.
have Hsplit : B * s - 1
    = (A * (3 / 2 - (1 / 2) * (A * A) * (s * s)) * s - 1)
      + (B - A * (3 / 2 - (1 / 2) * (A * A) * (s * s))) * s by field.
rewrite Hsplit.
apply: Rle_trans (Rabs_triang _ _) _.
(* (i) the Newton residual, word for word the paper's                         *)
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
(* (ii) the collected rounding, carried across by [A s <= 1 + 15u/2]          *)
have Hrest : Rabs ((B - A * (3 / 2 - (1 / 2) * (A * A) * (s * s))) * s)
    <= 19 * (u * u).
  rewrite Rabs_mult (Rabs_pos_eq s); last lra.
  have Hstep : Rabs (B - A * (3 / 2 - (1 / 2) * (A * A) * (s * s))) * s
      <= (18 * (u * u) * A) * s
    by apply: Rmult_le_compat_r; lra.
  apply: Rle_trans Hstep _.
  have -> : 18 * (u * u) * A * s = 18 * (u * u) * (A * s) by ring.
  by nra.
have Hu2p : 0 <= u * u by apply: Rle_0_sqr.
by lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The chain from the seed to the assembly                                   *)
(* ---------------------------------------------------------------------------*)
(*                                                                            *)
(*  These are the paper's own lemmas with `sqrtBW' replaced by `sqrtBWn' and  *)
(*  each constant moved by the four the seed costs.  They reach the seed      *)
(*  through `sqrtBWn_x_err_crude' and `sqrtBn_isDW' and nothing else, which   *)
(*  is why the substitution is all that is needed.                            *)

(* [b X] against [sqrt x]: 125 for the paper's 121.                           *)
Lemma sqrtAuxN_bX_le x : isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x)
    <= (1 + 125 * (u * u)) * sqrt (TWval x).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 := isTW_TWval_gt0 Hx Hx0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Hseed := sqrtBWn_x_err_crude Hx Hx0.
set B := TWval (sqrtBWn (tw0 x) (tw1 x)) in Hseed *.
set s := sqrt (TWval x) in HsX Hs0 Hseed *.
have Hgen : forall r b, r * r = TWval x -> b * TWval x = (b * r) * r.
  by move=> r b <-; ring.
rewrite (Hgen s B HsX) Rabs_mult (Rabs_pos_eq s); last lra.
have Hb := Rabs_le_inv _ _ Hseed.
have Hhalf : 104 * (u * u) <= 1 / 2.
  have -> : 104 * (u * u) = 104 * u * u by ring.
  by nra.
have HBs : Rabs (B * s) <= 1 + 125 * (u * u).
  rewrite (Rabs_pos_eq (B * s)); last by lra.
  by lra.
by apply: Rmult_le_compat_r; lra.
Qed.

(* [i1 = mul1 b x] against [sqrt x]: 134 for the paper's 130.                 *)
Lemma sqrtAuxN_i1_le mul1 d1 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  0 <= d1 -> d1 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x))
      <= (1 + 134 * (u * u)) * sqrt (TWval x).
Proof.
move=> Herr1 Hd10 Hd1u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 := isTW_TWval_gt0 Hx Hx0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBWn (tw0 x) (tw1 x)) by apply: sqrtBn_isDW.
have He := Herr1 _ _ HDW Hx.
have HbX := sqrtAuxN_bX_le Hx Hx0.
have -> : TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x)
    = (TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x)
       - TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x)
      + TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x by ring.
apply: Rle_trans (Rabs_triang _ _) _.
have Hp := Rabs_pos (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x).
have Hstep : d1 * Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x)
             + Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x)
    <= (u * u) * ((1 + 125 * (u * u)) * sqrt (TWval x))
       + (1 + 125 * (u * u)) * sqrt (TWval x).
  have H1 : d1 * Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x)
      <= (u * u) * ((1 + 125 * (u * u)) * sqrt (TWval x)).
    apply: Rle_trans (_ : (u * u)
             * Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x) <= _).
      by apply: Rmult_le_compat_r.
    by apply: Rmult_le_compat_l; nra.
  by lra.
apply: Rle_trans (_ : d1 * Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x)
                      + Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x) <= _);
  first by lra.
apply: Rle_trans Hstep _.
have Hfac : (u * u) * ((1 + 125 * (u * u)) * sqrt (TWval x))
            + (1 + 125 * (u * u)) * sqrt (TWval x)
    = (1 + 126 * (u * u) + 125 * (u * u) * (u * u)) * sqrt (TWval x)
  by ring.
rewrite Hfac.
apply: Rmult_le_compat_r; first lra.
have Hu4 : 125 * (u * u) * (u * u) <= 8 * (u * u).
  have -> : 125 * (u * u) * (u * u) = 125 * (u * u) * u * u by ring.
  have Hs : 0 <= u * u by apply: Rle_0_sqr.
  have Hc : 125 * (u * u) <= 8 by nra.
  by nra.
by lra.
Qed.

(* The cancellation: the bracket is a half, not a one.  308 for the paper's   *)
(* 300, and what consumes it has room for both.                               *)
Lemma sqrtAuxN_bracket_le mul1 d1 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  0 <= d1 -> d1 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs ((3 / 2 - (1 / 2)
             * (TWval (sqrtBWn (tw0 x) (tw1 x))
                * TWval (sqrtBWn (tw0 x) (tw1 x))) * TWval x)
          - (TWval (sqrtBWn (tw0 x) (tw1 x)) / 2)
            * TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x))
      <= 1 / 2 + 308 * (u * u).
Proof.
move=> Herr1 Hd10 Hd1u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 := isTW_TWval_gt0 Hx Hx0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0 HsX} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 HsX Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBWn (tw0 x) (tw1 x)) by apply: sqrtBn_isDW.
have He := Herr1 _ _ HDW Hx.
have Hseed := sqrtBWn_x_err_crude Hx Hx0.
set B := TWval (sqrtBWn (tw0 x) (tw1 x)) in He Hseed *.
set I1 := TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) in He *.
set s := sqrt (TWval x) in HsX Hs0 Hseed *.
have Ht := Rabs_le_inv _ _ Hseed.
have HB2X : forall r b, r * r = TWval x -> b * b * TWval x = (b * r) * (b * r).
  by move=> r b <-; ring.
have HBX : B * B * TWval x = (B * s) * (B * s) by apply: HB2X.
have Hsplit : 3 / 2 - 1 / 2 * (B * B) * TWval x - B / 2 * I1
    = (3 / 2 - (B * B) * TWval x) - (B / 2) * (I1 - B * TWval x) by field.
rewrite Hsplit HBX.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_Ropp.
have Hhalf : 104 * (u * u) <= 1 / 2.
  have -> : 104 * (u * u) = 104 * u * u by ring.
  by nra.
have Hu4 : 20000 * ((u * u) * (u * u)) <= u * u.
  have -> : 20000 * ((u * u) * (u * u)) = 20000 * (u * u) * u * u by ring.
  have Hs2 : 0 <= u * u by apply: Rle_0_sqr.
  have Hc : 20000 * (u * u) <= 1 by nra.
  by nra.
have Hlo : 0 <= B * s by lra.
have Hsqhi : (B * s) * (B * s) <= (1 + 104 * (u * u)) * (1 + 104 * (u * u))
  by apply: Rmult_le_compat; nra.
have Hsqlo : (1 - 104 * (u * u)) * (1 - 104 * (u * u)) <= (B * s) * (B * s)
  by apply: Rmult_le_compat; nra.
have Hsq : Rabs (3 / 2 - B * s * (B * s)) <= 1 / 2 + 249 * (u * u)
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

(* [b i(1)] against one: the SEED ERROR DOUBLED, 210 for the paper's 202.     *)
Lemma sqrtAuxN_b_i1_le mul1 d1 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  0 <= d1 -> d1 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (sqrtBWn (tw0 x) (tw1 x))
          * TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) - 1)
      <= 210 * (u * u).
Proof.
move=> Herr1 Hd10 Hd1u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 := isTW_TWval_gt0 Hx Hx0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have Fx0 : format (tw0 x) by case: x Hx {Hx0 HX0 Hs0 HsX} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 HX0 Hs0 HsX Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBWn (tw0 x) (tw1 x)) by apply: sqrtBn_isDW.
have He1 := Herr1 _ _ HDW Hx.
have Hseed := sqrtBWn_x_err_crude Hx Hx0.
set B := TWval (sqrtBWn (tw0 x) (tw1 x)) in He1 Hseed *.
set I1 := TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) in He1 *.
set s := sqrt (TWval x) in HsX Hs0 Hseed.
have He1' : Rabs (I1 - B * TWval x) <= (u * u) * Rabs (B * TWval x).
  apply: Rle_trans He1 _.
  by apply: Rmult_le_compat_r; first by apply: Rabs_pos.
have Ht := Rabs_le_inv _ _ Hseed.
have HBs : Rabs (B * s) <= 1 + 104 * (u * u).
  by have := Rabs_triang_inv (B * s) 1; rewrite Rabs_R1; lra.
have Hsplit : B * I1 - 1 = ((B * s) * (B * s) - 1) + B * (I1 - B * TWval x)
  by rewrite -HsX; ring.
have Hsq : Rabs ((B * s) * (B * s) - 1)
    <= (104 * (u * u)) * (2 + 104 * (u * u)).
  have -> : (B * s) * (B * s) - 1 = (B * s - 1) * ((B * s - 1) + 2) by ring.
  rewrite Rabs_mult.
  apply: Rmult_le_compat => //; try apply: Rabs_pos.
  apply: Rle_trans (Rabs_triang _ _) _.
  have -> : Rabs 2 = 2 by rewrite Rabs_pos_eq; lra.
  by lra.
have Hmulterm : Rabs (B * (I1 - B * TWval x))
    <= (u * u) * ((1 + 104 * (u * u)) * (1 + 104 * (u * u))).
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

(* AND THE NUMBER THE WHOLE THING TURNS ON.  `i(2)' has head one and is       *)
(* within `108u^2' of it, where the paper's seed reaches `105'.  What         *)
(* consumes it is `ThreeProdOneTW_error_c', whose tolerance is a parameter    *)
(* no larger than 112 -- so the four the seed costs fit, with four to spare.  *)
Lemma sqrtAuxN_i2_near_1 mul1 mul2 d1 d2 :
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (sub32TW (mul2 (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
                            (mul1 (sqrtBWn (tw0 x) (tw1 x)) x))) - 1)
      <= 108 * (u * u).
Proof.
move=> Herr1 Herr2 Hmul1 Hd10 Hd1u Hd20 Hd2u x Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HDW : isDW (sqrtBWn (tw0 x) (tw1 x)) by apply: sqrtBn_isDW.
have Hi1 : isTW (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) by apply: Hmul1.
have Hkey := sqrtAuxN_b_i1_le Herr1 Hd10 Hd1u Hx Hx0.
have HDWs : isDW (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
  by apply: isDW_scale.
have He2 := Herr2 _ _ HDWs Hi1.
rewrite TWval_scale in He2.
have Hpow : pow (-1) = / 2 by rewrite /= /Z.pow_pos /=; lra.
rewrite Hpow in He2.
rewrite TWval_sub32TW.
set B := TWval (sqrtBWn (tw0 x) (tw1 x)) in Hkey He2 *.
set I1 := TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) in Hkey He2 *.
set P := TWval (mul2 (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
                  (mul1 (sqrtBWn (tw0 x) (tw1 x)) x)) in He2 *.
have H2 : Rabs (/ 2) = / 2 by rewrite Rabs_pos_eq; lra.
have Hhalf : Rabs (B * / 2 * I1 - / 2) <= 105 * (u * u).
  have -> : B * / 2 * I1 - / 2 = (B * I1 - 1) * / 2 by field.
  by rewrite Rabs_mult H2; lra.
have Hub : Rabs (B * / 2 * I1) <= / 2 + 105 * (u * u).
  by have := Rabs_triang_inv (B * / 2 * I1) (/ 2); rewrite H2; lra.
have Herr : Rabs (P - B * / 2 * I1) <= (u * u) * (/ 2 + 105 * (u * u)).
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

(* The numeric side conditions, with our constants.  The 400 survives: it   *)
(* had ample slack and the four the seed costs do not use it up.            *)
Lemma sq_cAn : (1 + 134 * (u * u)) * (1 + 108 * (u * u)) <= 1 + 400 * (u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

Lemma sq_cBn :
  / 2 * ((1 + 134 * (u * u)) * (1 + 134 * (u * u)) * (1 + 104 * (u * u)))
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

Lemma sq_cCn :
  (1 + 125 * (u * u)) * (1 / 2 + 308 * (u * u)) <= 1 / 2 + 400 * (u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
nra.
Qed.

(* The Newton residual of the seed, 16500 for the paper's 15200.            *)
Lemma newton_residual_constN :
  (104 * (u * u)) * (104 * (u * u)) * ((3 + (104 * (u * u))) / 2)
    <= 16500 * (u * u * u * u).
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have L3 : u * u * u <= / 2048 * (u * u) by nra.
have L4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have L5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have L6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
by nra.
Qed.

Lemma sqrtN_newton_residual x :
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (sqrtBWn (tw0 x) (tw1 x)) * TWval x
        * (3 / 2 - (1 / 2) * (TWval (sqrtBWn (tw0 x) (tw1 x))
                              * TWval (sqrtBWn (tw0 x) (tw1 x))) * TWval x)
        - sqrt (TWval x))
    <= 16500 * (u * u * u * u) * Rabs (sqrt (TWval x)).
Proof.
move=> Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have HX0 := isTW_TWval_gt0 Hx Hx0.
have Hs0 : 0 <= sqrt (TWval x) by apply: sqrt_pos.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x
  by apply: sqrt_sqrt; lra.
have Hseed := sqrtBWn_x_err_crude Hx Hx0.
set B := TWval (sqrtBWn (tw0 x) (tw1 x)) in Hseed *.
set s := sqrt (TWval x) in HsX Hseed Hs0 *.
have Hid := sqrt_newton_id s B.
rewrite HsX in Hid.
rewrite Hid.
(* pull [s] out; what is left is the pure-[u] bound.                          *)
have -> : - s * ((B * s - 1) * (B * s - 1)) * (B * s - 1 + 3) / 2
    = - (s * (((B * s - 1) * (B * s - 1))
              * ((B * s - 1 + 3) / 2))) by field.
rewrite Rabs_Ropp Rabs_mult !(Rabs_pos_eq s) //.
rewrite [16500 * (u * u * u * u) * s]Rmult_comm.
apply: Rmult_le_compat_l => //.
have He := Rabs_le_inv _ _ Hseed.
have Hsq : (B * s - 1) * (B * s - 1)
    <= (104 * (u * u))
       * (104 * (u * u)) by nra.
have Hsq0 : 0 <= (B * s - 1) * (B * s - 1) by apply: Rle_0_sqr.
have Hlin : (B * s - 1 + 3) / 2
    <= (3 + (104 * (u * u))) / 2 by nra.
have Hlin0 : 0 <= (B * s - 1 + 3) / 2 by nra.
have Hstep : ((B * s - 1) * (B * s - 1)) * ((B * s - 1 + 3) / 2)
    <= (104 * (u * u))
       * (104 * (u * u))
       * ((3 + (104 * (u * u))) / 2)
  by apply: Rmult_le_compat.
rewrite Rabs_pos_eq; last by nra.
by apply: Rle_trans Hstep _; exact: newton_residual_constN.
Qed.

(* The numeric core, generic in everything but the constants.               *)
Lemma sqrtN_error_core B I1 P Y X s d1 d2 d3 :
  0 < s -> s * s = X ->
  0 <= d1 -> 0 <= d2 -> 0 <= d3 ->
  Rabs (B * s - 1) <= 104 * (u * u) ->
  Rabs I1 <= (1 + 134 * (u * u)) * s ->
  Rabs (3 / 2 - P - 1) <= 108 * (u * u) ->
  Rabs (Y - I1 * (3 / 2 - P)) <= d3 * Rabs (I1 * (3 / 2 - P)) ->
  Rabs (P - B * / 2 * I1) <= d2 * Rabs (B * / 2 * I1) ->
  Rabs (I1 - B * X) <= d1 * Rabs (B * X) ->
  Rabs (B * X) <= (1 + 125 * (u * u)) * s ->
  Rabs (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1) <= 1 / 2 + 308 * (u * u) ->
  Rabs (B * X * (3 / 2 - 1 / 2 * (B * B) * X) - s)
    <= 16500 * (u * u * u * u) * s ->
  Rabs (Y - s)
    <= (d1 * (1 / 2 + 400 * (u * u)) + d2 * (1 / 2 + 400 * (u * u))
        + d3 * (1 + 400 * (u * u)) + 16500 * (u * u * u * u)) * s.
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
have Hi2u : Rabs (3 / 2 - P) <= 1 + 108 * (u * u).
  by have := Rabs_triang_inv (3 / 2 - P) 1; rewrite Rabs_R1; lra.
have Hsa : Rabs s = s by rewrite Rabs_pos_eq; lra.
have HBu : Rabs B * s <= 1 + 104 * (u * u).
  have -> : Rabs B * s = Rabs (B * s) by rewrite Rabs_mult Hsa.
  by have := Rabs_triang_inv (B * s) 1; rewrite Rabs_R1; lra.
have Hi1p := Rabs_pos I1.
have HBp := Rabs_pos B.
(* [A]: the last product.                                                     *)
have HA' : Rabs (Y - I1 * (3 / 2 - P)) <= d3 * (1 + 400 * (u * u)) * s.
  apply: Rle_trans HA _.
  rewrite Rabs_mult.
  have Hstep : Rabs I1 * Rabs (3 / 2 - P)
      <= ((1 + 134 * (u * u)) * s) * (1 + 108 * (u * u))
    by apply: Rmult_le_compat => //; apply: Rabs_pos.
  have Hstep2 : d3 * (Rabs I1 * Rabs (3 / 2 - P))
      <= d3 * (((1 + 134 * (u * u)) * s) * (1 + 108 * (u * u)))
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep2 _.
  have Hd3s : 0 <= d3 * s by apply: Rmult_le_pos; lra.
  have -> : d3 * ((1 + 134 * (u * u)) * s * (1 + 108 * (u * u)))
      = (d3 * s) * ((1 + 134 * (u * u)) * (1 + 108 * (u * u))) by ring.
  have -> : d3 * (1 + 400 * (u * u)) * s = (d3 * s) * (1 + 400 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l; [exact: Hd3s | exact: sq_cAn].
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
      <= ((1 + 134 * (u * u)) * (1 + 134 * (u * u))) * s
         * (1 + 104 * (u * u)).
    have Hstep2 : Rabs I1 * Rabs I1
        <= ((1 + 134 * (u * u)) * s) * ((1 + 134 * (u * u)) * s)
      by apply: Rmult_le_compat.
    have Hstep3 : Rabs I1 * Rabs I1 * Rabs B
        <= (((1 + 134 * (u * u)) * s) * ((1 + 134 * (u * u)) * s)) * Rabs B
      by apply: Rmult_le_compat_r.
    apply: Rle_trans Hstep3 _.
    have Hstep4 : (((1 + 134 * (u * u)) * s) * ((1 + 134 * (u * u)) * s))
                    * Rabs B
        = ((1 + 134 * (u * u)) * (1 + 134 * (u * u))) * s * (Rabs B * s)
      by ring.
    rewrite Hstep4.
    apply: Rmult_le_compat_l => //.
    by apply: Rmult_le_pos; nra.
  have Hd2p : 0 <= d2 * / 2 by lra.
  have Hstep5 : d2 * / 2 * (Rabs I1 * Rabs I1 * Rabs B)
      <= d2 * / 2 * (((1 + 134 * (u * u)) * (1 + 134 * (u * u))) * s
                     * (1 + 104 * (u * u)))
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep5 _.
  have Hd2s : 0 <= d2 * s by apply: Rmult_le_pos; lra.
  have -> : d2 * / 2 * ((1 + 134 * (u * u)) * (1 + 134 * (u * u)) * s
                        * (1 + 104 * (u * u)))
      = (d2 * s) * (/ 2 * ((1 + 134 * (u * u)) * (1 + 134 * (u * u))
                           * (1 + 104 * (u * u)))) by field.
  have -> : d2 * (1 / 2 + 400 * (u * u)) * s
      = (d2 * s) * (1 / 2 + 400 * (u * u)) by ring.
  by apply: Rmult_le_compat_l; [exact: Hd2s | exact: sq_cBn].
(* [C]: THE CANCELLATION.  The bracket is [1/2], not [1].                     *)
have HC' : Rabs ((I1 - B * X) * (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1))
    <= d1 * (1 / 2 + 400 * (u * u)) * s.
  rewrite Rabs_mult.
  have Hstep : Rabs (I1 - B * X)
                 * Rabs (3 / 2 - 1 / 2 * (B * B) * X - B / 2 * I1)
      <= (d1 * ((1 + 125 * (u * u)) * s)) * (1 / 2 + 308 * (u * u)).
    apply: Rmult_le_compat => //; try apply: Rabs_pos.
    apply: Rle_trans HC _.
    by apply: Rmult_le_compat_l.
  apply: Rle_trans Hstep _.
  have Hd1s : 0 <= d1 * s by apply: Rmult_le_pos; lra.
  have -> : d1 * ((1 + 125 * (u * u)) * s) * (1 / 2 + 308 * (u * u))
      = (d1 * s) * ((1 + 125 * (u * u)) * (1 / 2 + 308 * (u * u))) by ring.
  have -> : d1 * (1 / 2 + 400 * (u * u)) * s
      = (d1 * s) * (1 / 2 + 400 * (u * u)) by ring.
  by apply: Rmult_le_compat_l; [exact: Hd1s | exact: sq_cCn].
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

(* WHAT IS LEFT.  `ThreeSqRtAuxN' -- Algorithm 15 with the seed above -- and  *)
(* its error, which is the paper's `ThreeSqRtAux_error' with the same         *)
(* substitution.  Everything it consumes is above; it is the last piece on    *)
(* this side.                                                                 *)

(* ---------------------------------------------------------------------------*)
(*  Algorithm 15 with the seed it can actually compute                        *)
(* ---------------------------------------------------------------------------*)

Definition ThreeSqRtAuxN (mul1 mul2 mul3 : twR -> twR -> twR) (x : twR)
    : twR :=
  let bw := sqrtBWn (tw0 x) (tw1 x) in
  let i1 := mul1 bw x in
  mul3 i1 (sub32TW (mul2 (scaleTW (-1)%Z bw) i1)).

Definition ThreeSqRtN (x : twR) : twR :=
  ThreeSqRtAuxN ThreeProdDW ThreeProdDW ThreeProdOneTW x.

Lemma ThreeSqRtAuxN_error mul1 mul2 mul3 d1 d2 d3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 ->
     Rabs (TWval y - 1) <= 108 * (u * u) ->
     Rabs (TWval (mul3 a y) - TWval a * TWval y)
       <= d3 * Rabs (TWval a * TWval y)) ->
  head_half mul2 ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  0 <= d3 -> d3 <= u * u ->
  forall x, isTW x -> 0 < tw0 x ->
    Rabs (TWval (ThreeSqRtAuxN mul1 mul2 mul3 x) - sqrt (TWval x))
      <= (d1 * (1 / 2 + 400 * (u * u)) + d2 * (1 / 2 + 400 * (u * u))
          + d3 * (1 + 400 * (u * u)) + 16500 * (u * u * u * u))
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
have HDW : isDW (sqrtBWn (tw0 x) (tw1 x)) by apply: sqrtBn_isDW.
have Hi1 : isTW (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) by apply: Hmul1.
have Hu2p : 0 <= u * u by apply: Rle_0_sqr.
(* [i(2)]'s head is [1]: the head property, at the [300u^2] the [head_half]  *)
(* interface asks for -- ample, since [sqrtAuxN_b_i1_le] gives [202u^2].      *)
have Hkey := sqrtAuxN_b_i1_le Herr1 Hd10 Hd1u Hx Hx0.
have Hkey300 : Rabs (TWval (sqrtBWn (tw0 x) (tw1 x))
                     * TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x) - 1)
    <= 300 * (u * u) by lra.
have Hhalf := Hhead _ _ HDW Hi1 Hkey300.
have HDWs : isDW (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
  by apply: isDW_scale.
have Hi2TW : isTW (sub32TW (mul2 (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
                              (mul1 (sqrtBWn (tw0 x) (tw1 x)) x))).
  apply: sub32TW_isTW; last exact: Hhalf.
  by apply: Hmul2.
have Hi2h : tw0 (sub32TW (mul2 (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
                            (mul1 (sqrtBWn (tw0 x) (tw1 x)) x))) = 1
  by case: (mul2 _ _) Hhalf => t0 t1 t2 /= ->; field.
(* the eight bounds [sqrtN_error_core] consumes                               *)
have Hi2v := sqrtAuxN_i2_near_1 Herr1 Herr2 Hmul1 Hd10 Hd1u Hd20 Hd2u Hx Hx0.
have He3 := Herr3 _ _ Hi1 Hi2TW Hi2h Hi2v.
have He1 := Herr1 _ _ HDW Hx.
have He2 := Herr2 _ _ HDWs Hi1.
rewrite TWval_scale in He2.
have Hpow : pow (-1) = / 2 by rewrite /= /Z.pow_pos /=; lra.
rewrite Hpow in He2.
have Hi1le := sqrtAuxN_i1_le Herr1 Hd10 Hd1u Hx Hx0.
have Hbrk := sqrtAuxN_bracket_le Herr1 Hd10 Hd1u Hx Hx0.
have HbXle := sqrtAuxN_bX_le Hx Hx0.
have Hresid := sqrtN_newton_residual Hx Hx0.
have Hseed := sqrtBWn_x_err_crude Hx Hx0.
rewrite TWval_sub32TW in He3 Hi2v.
have Habs : Rabs (sqrt (TWval x)) = sqrt (TWval x)
  by rewrite Rabs_pos_eq; lra.
rewrite Habs in Hresid.
rewrite /ThreeSqRtAuxN Habs.
apply: (@sqrtN_error_core (TWval (sqrtBWn (tw0 x) (tw1 x)))
          (TWval (mul1 (sqrtBWn (tw0 x) (tw1 x)) x))
          (TWval (mul2 (scaleTW (-1)%Z (sqrtBWn (tw0 x) (tw1 x)))
                    (mul1 (sqrtBWn (tw0 x) (tw1 x)) x)))
          _ (TWval x) (sqrt (TWval x)) d1 d2 d3) => //.
Qed.

Lemma ThreeSqRtN_error x :
  ties_to_even choice ->
  isTW x -> 0 < tw0 x ->
  Rabs (TWval (ThreeSqRtN x) - sqrt (TWval x)) <=
     (24 * (u * u * u) + 12000 * (u * u * u * u)) * Rabs (sqrt (TWval x)).
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
(* what [sqrtAuxN_i2_near_1] delivers.                                        *)
have H105a : (40 : R) <= 108 by lra.
have H105b : (108 : R) <= 112 by lra.
have Hd0 : 0 <= 105 / 10 * (u * u * u) + 39 * (u * u * u * u) by nra.
have Hdu : 105 / 10 * (u * u * u) + 39 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= 6 * (u * u * u) + 3358 * (u * u * u * u) by nra.
have Heu : 6 * (u * u * u) + 3358 * (u * u * u * u) <= u * u by nra.
(* [31 * 105 + 10 = 3358]: Algorithm 20's [delta3] at OUR tolerance.         *)
have Hd3le : 6 * (u * u * u) + (31 * 108 + 10) * (u * u * u * u)
    <= 6 * (u * u * u) + 3358 * (u * u * u * u) by lra.
have Hgen := @ThreeSqRtAuxN_error ThreeProdDW ThreeProdDW ThreeProdOneTW
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (105 / 10 * (u * u * u) + 39 * (u * u * u * u))
  (6 * (u * u * u) + 3358 * (u * u * u * u))
  (fun b y Hb Hy =>
     @ThreeProdDW_isTW p Hp2 (Hp6 Hp11) choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDW_isTW p Hp2 (Hp6 Hp11) choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDW_error p Hp2 (Hp6 Hp11) choice choice_sym b y Hc Hb Hy)
  (fun b y Hb Hy =>
     @ThreeProdDW_error p Hp2 (Hp6 Hp11) choice choice_sym b y Hc Hb Hy)
  (fun a y Ha Hy Hy0 Hy1 =>
     Rle_trans _ _ _
       (@ThreeProdOneTW_error_c p Hp2 (Hp6 Hp11) choice choice_sym 108 a y Hc
          H105a H105b Ha Hy Hy0 Hy1)
       (Rmult_le_compat_r _ _ _ (Rabs_pos _) Hd3le))
  (ThreeProdDW_head_half Hp2 Hp11 choice_sym Hc)
  Hd0 Hdu Hd0 Hdu He0 Heu x Hx Hx0.
rewrite /ThreeSqRtN.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
nra.
Qed.

End SecSeedNoFMA.
