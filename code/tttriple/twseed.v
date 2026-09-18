From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From threewords Require Import TwoSum TWR ThreeProdDW ThreeSqRt.

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

End SecSeedNoFMA.
