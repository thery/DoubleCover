From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From threewords Require Import TwoSum TWR ThreeProd ThreeProdDW ThreeSqRt.

(* THE SEED OF ALGORITHM 15, WITH NO FUSED MULTIPLY-ADD.                      *)
(*                                                                            *)
(* `twpaper.v' transcribes the paper's square root onto primitive floats, and *)
(* Rocq's primitive floats have no fused multiply-add.  Three lines of the    *)
(* paper's seed are of the form `RN(v + a * w)', one rounding; here each is    *)
(* two, `RN(v + RN(a * w))'.  Nothing else in Algorithm 15 changes: the seed  *)
(* is the only place an FMA appears.                                          *)
(*                                                                            *)
(* WHY THAT IS THE WHOLE OF IT.  The assembly `ThreeSqRtAux_error' reaches the *)
(* seed through two facts and no others -- that it is a double word, and that *)
(* `b sqrt x' is within so many `u^2' of one.  So this file redoes those two  *)
(* for the seed without the FMA, and everything downstream is the paper's as   *)
(* it stands.                                                                 *)
(*                                                                            *)
(* AND THE ROOM IS SMALL.  The seed's `100u^2' becomes `105u^2' at            *)
(* `sqrtAux_i2_near_1', and `ThreeProdOneTW_error_c' takes its tolerance as a *)
(* parameter no larger than `112'.  So what comes out below has to stay       *)
(* under about `107u^2'.                                                      *)

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
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have Hb := tw1_le _ _ Fx0 Hx0 Hx1.
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
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have H11 := sqrtH11_1_le Hp2 Hp11 choice Fx0 Hx0.
have Hax1 := sqrtA_x1_le _ _ Fx0 Hx0 Hx1.
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
have Hu2048 := u_le_2048 Hp11.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hs := sqrtH1_1n_sum_le _ _ Fx0 Hx0 Hx1.
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
have Hu2048 := u_le_2048 Hp11.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hs := sqrtH1_1n_sum_le _ _ Fx0 Hx0 Hx1.
have Hax1 := sqrtA_x1_le _ _ Fx0 Hx0 Hx1.
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
apply/(format_scale Hp2 choice); rewrite /ThreeSqRt.sqrtA.
by apply: generic_format_round.
Qed.

(* The error of the middle two-product, which the paper proves inline.        *)
Lemma sqrtH11_2_le x0 : format x0 -> 0 < x0 ->
  Rabs (sqrtH11_2 x0) <= u * (sqrtA' x0 * ((1 + u) * (sqrtA x0 * x0))).
Proof.
move=> Fx0 Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have H01 := sqrtH0_1_le Hp2 Hp11 choice Fx0 Hx0.
have FA2 := format_sqrtA' x0.
have F01 : format (sqrtH0_1 x0) by apply: generic_format_round.
have HE2 := TwoProd_exact Hp2 choice FA2 F01.
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
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have HP : 0 < sqrtA x0 * x0 by nra.
have H112 := sqrtH11_2_le _ Fx0 Hx0.
have H11n := sqrtH1_1n_le _ _ Fx0 Hx0 Hx1.
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
have Hu2048 := u_le_2048 Hp11.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have Hsq := sqrtA_sq_le Hp2 Hp11 choice Fx0 Hx0.
have HP : 0 < sqrtA x0 * x0 by nra.
have Hs := sqrtH1_2n_sum_le _ _ Fx0 Hx0 Hx1.
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
have Hu2048 := u_le_2048 Hp11.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HA' : sqrtA' x0 = sqrtA x0 / 2 by [].
have HP : 0 < sqrtA x0 * x0 by nra.
have HQ : 0 < sqrtA x0 * sqrtA x0 * x0 by nra.
have Hs := sqrtH1_2n_sum_le _ _ Fx0 Hx0 Hx1.
have H11n := sqrtH1_1n_le _ _ Fx0 Hx0 Hx1.
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
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have Hb11 := sqrtB11_le Hp2 Hp11 choice Fx0 Hx0.
have Hh12 := sqrtH1_2n_le _ _ Fx0 Hx0 Hx1.
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
have Hu2048 := u_le_2048 Hp11.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have Hb01 := sqrtB01_ge Hp2 Hp11 choice Fx0 Hx0.
have Hs := sqrtB12n_sum_le _ _ Fx0 Hx0 Hx1.
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
have Hu2048 := u_le_2048 Hp11.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have Hh12 := sqrtH1_2n_le _ _ Fx0 Hx0 Hx1.
have Hs := sqrtB12n_sum_le _ _ Fx0 Hx0 Hx1.
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
have Hord := sqrtB12n_le_B01 _ _ Fx0 Hx0 Hx1.
have Hmag := magnitude_Fast2Sum Hp2 choice F01 F12 (fun _ => Hord).
have Hfor := format_Fast2Sum Hp2 choice (sqrtB01 x0) (sqrtB12n x0 x1).
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
have Hord := sqrtB12n_le_B01 _ _ Fx0 Hx0 Hx1.
have Hc := Fast2Sum_correct Hp2 choice F01 F12 (fun _ => Hord).
by rewrite /sqrtBWn /TWval /sqrtBn Rplus_0_r; exact: Hc.
Qed.

(* Nine and eight, where the paper has five and four: the three extra          *)
(* roundings, each already paid for above.                                     *)
Lemma seed_num : 9 * (1 + 12 * u + 62 * (u * u)) + 8 <= 18.
Proof.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048 Hp11.
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
have Hu2048 := u_le_2048 Hp11.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1s : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have Hsq := sqrtA_sq_le Hp2 Hp11 choice Fx0 Hx0.
have HP : 0 < sqrtA (tw0 x) * tw0 x by nra.
have HA' : sqrtA' (tw0 x) = sqrtA (tw0 x) / 2 by [].
have FA : format (sqrtA (tw0 x)).
  by rewrite /ThreeSqRt.sqrtA; apply: generic_format_round.
have FA2 := format_sqrtA' (tw0 x).
have F01 : format (sqrtH0_1 (tw0 x)).
  by rewrite /ThreeSqRt.sqrtH0_1 /MULTmore.TwoProd /=; apply: generic_format_round.
have F02 : format (sqrtH0_2 (tw0 x)) by apply: sqrtH0_2_exact.
have P1 := TwoProd_exact Hp2 choice FA Fx0.
have P2 := TwoProd_exact Hp2 choice FA2 F01.
have P3 := TwoProd_exact Hp2 choice FA F02.
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
  rewrite (TWval_sqrtBWn _ _ Fx0 Hx0 Hx1s) TWval_split.
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
have Hx2 := isTW_tw2_le Hp2 Hx.
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
have Hu2048 := u_le_2048 Hp11.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have HX0 := isTW_TWval_gt0 Hp2 Hp11 Hx Hx0.
have Hs0 : 0 < sqrt (TWval x) by apply: sqrt_lt_R0.
have HsX : sqrt (TWval x) * sqrt (TWval x) = TWval x by apply: sqrt_sqrt; lra.
have HA := sqrtA_gt0 Hp2 Hp11 choice Fx0 Hx0.
have HN := sqrtBWn_newton_form _ Hx Hx0.
have [Hlo Hhi] := sqrtA_bound_full Hp2 Hp11 choice Hx Hx0.
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

End SecSeedNoFMA.
