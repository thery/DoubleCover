From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From twarith.threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From twarith.threewords Require Import TwoSum Nonoverlap TWR VecSum.
From twarith.threewords Require Import ThreeProd ThreeProdDW ThreeProdOne.
From twarith.threewords Require Import ThreeReci ThreeDiv.
From twarith Require Import twprodg twseed.

(* ALGORITHM 14 WITHOUT A FUSED MULTIPLY-ADD.                                 *)
(*                                                                            *)
(* The quotient is the reciprocal's seed and three products, and the three    *)
(* products are done: `twseed.v' has `ThreeProdDWn' and `ThreeProdOneTWn' and *)
(* what each is out by.  What is left is the seed, `reciBW', whose five lines *)
(* the paper writes with two fused multiply-adds.                             *)
(*                                                                            *)
(*     a    <- RN((1 + 2u)/x0)                                                *)
(*     h11  <- RN(a x0 - (1 + 2u))      -- a two-product on the machine,      *)
(*                                          and exact either way              *)
(*     h1   <- RN(-h11 - a x1)          -- fused                              *)
(*     (b01, b11) <- 2Prod(a, 1 - 2u)                                         *)
(*     b12  <- RN(b11 + a h1)           -- fused                              *)
(*     b    <- Fast2Sum(b01, b12)                                             *)
(*                                                                            *)
(* Split, the two cost what the root's three cost: the seed goes from `34u^2' *)
(* to `40u^2', and since the paper's `sub2_near_one' and `div_error_core'     *)
(* both have that number written into them, they are restated here with it    *)
(* as a parameter.                                                            *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecDivNoFMA.

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

Fact Hp10 : (10 <= p)%Z. Proof. lia. Qed.
Fact Hp6 : (6 <= p)%Z. Proof. lia. Qed.

(* The paper's own names, bridged once so its proof text reads unchanged.     *)
Local Notation reciA := (reciA p choice).
Local Notation reciH11 := (reciH11 p choice).
Local Notation reciB01 := (reciB01 p choice).
Local Notation reciB11 := (reciB11 p choice).
Local Notation u_le_1024 := (u_le_1024 Hp10).
Local Notation reciA_x0_bound := (reciA_x0_bound Hp2 Hp10 (choice := choice) choice_sym).
Local Notation reciA_x1_bound := (reciA_x1_bound Hp2 Hp10 (choice := choice) choice_sym).
Local Notation reciH11_bound := (reciH11_bound Hp2 Hp10 (choice := choice) choice_sym).
Local Notation reciH11_exact := (reciH11_exact Hp2 Hp10 (choice := choice) choice_sym).
Local Notation reciB01_bound := (reciB01_bound Hp2 Hp10 choice).
Local Notation reciB11_bound := (reciB11_bound Hp2 Hp10 choice).
Local Notation reciA_X_range := (reciA_X_range Hp2 Hp10 (choice := choice) choice_sym).
Local Notation reciA_X_bound := (reciA_X_bound Hp2 Hp10 (choice := choice) choice_sym).
Local Notation format_1m2u := (format_1m2u Hp2).
Local Notation reciA_scale := (reciA_scale p choice).
Local Notation reciA_opp := (reciA_opp p (choice := choice)).
Local Notation reciH11_scale := (reciH11_scale p choice).
Local Notation reciH11_opp := (reciH11_opp p (choice := choice)).
Local Notation reciB01_scale := (reciB01_scale p choice).
Local Notation reciB01_opp := (reciB01_opp p (choice := choice) choice_sym).
Local Notation reciB11_scale := (reciB11_scale p choice).
Local Notation reciB11_opp := (reciB11_opp p (choice := choice) choice_sym).
Local Notation TwoProd_correct := (MULTmore.TwoProd_correct (p := p)).
Local Notation RN_sym := (RN_sym p beta choice choice_sym).

(* The two facts about one rounding that every bound below is made of.        *)
Lemma rndd_err v : Rabs (RND v - v) <= u * Rabs v.
Proof. by apply: relative_error_le. Qed.

Lemma rndd_abs v : Rabs (RND v) <= (1 + u) * Rabs v.
Proof.
have H := rndd_err v.
have T := Rabs_triang (RND v - v) v.
have E : RND v - v + v = RND v by ring.
by rewrite E in T; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The first split line: `h1 <- RN(-h11 - a x1)'                             *)
(* ---------------------------------------------------------------------------*)

Definition reciH1n (x0 x1 : R) : R :=
  RND (- reciH11 x0 - RND (reciA x0 * x1)).

(* The inner rounding is of something under `2u', so it costs `2u^2'.         *)
Lemma reciAx1n_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (RND (reciA x0 * x1)) <= 2 * u + 9 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have H := reciA_x1_bound Fx0 Hx0 Hx1.
have Hr := rndd_abs (reciA x0 * x1).
have Hu2 : u * u <= / 1024 * u by nra.
by nra.
Qed.

Lemma reciAx1n_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (RND (reciA x0 * x1) - reciA x0 * x1) <= 3 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have H := reciA_x1_bound Fx0 Hx0 Hx1.
have Hr := rndd_err (reciA x0 * x1).
have Hu2 : u * u <= / 1024 * u by nra.
by nra.
Qed.

Lemma reciH1n_arg_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (- reciH11 x0 - RND (reciA x0 * x1)) <= 3 * u + 9 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hh11 := reciH11_bound Fx0 Hx0.
have Hax1 := reciAx1n_bound Fx0 Hx0 Hx1.
have Hsum := Rabs_triang (- reciH11 x0) (- RND (reciA x0 * x1)).
rewrite !Rabs_Ropp in Hsum.
have -> : - reciH11 x0 - RND (reciA x0 * x1)
        = - reciH11 x0 + - RND (reciA x0 * x1) by ring.
by nra.
Qed.

Lemma reciH1n_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciH1n x0 x1) <= 3 * u + 13 * (u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Ht := reciH1n_arg_bound Fx0 Hx0 Hx1.
have Hr := rndd_abs (- reciH11 x0 - RND (reciA x0 * x1)).
have Hu2 : u * u <= / 1024 * u by nra.
by rewrite /reciH1n; nra.
Qed.

(* AND WHAT THE SPLIT COSTS: six `u^2' where the paper has three.  Half of    *)
(* it is the inner rounding's own error and half is that the outer one now    *)
(* rounds a slightly larger number.                                           *)
Lemma reciH1n_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciH1n x0 x1 - (- reciH11 x0 - reciA x0 * x1))
    <= 6 * (u * u) + 10 * (u * u * u).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Ht := reciH1n_arg_bound Fx0 Hx0 Hx1.
have Hr := rndd_err (- reciH11 x0 - RND (reciA x0 * x1)).
have Hi := reciAx1n_err Fx0 Hx0 Hx1.
have E : reciH1n x0 x1 - (- reciH11 x0 - reciA x0 * x1)
       = (RND (- reciH11 x0 - RND (reciA x0 * x1))
          - (- reciH11 x0 - RND (reciA x0 * x1)))
         - (RND (reciA x0 * x1) - reciA x0 * x1) by rewrite /reciH1n; ring.
rewrite E.
have T := Rabs_triang (RND (- reciH11 x0 - RND (reciA x0 * x1))
                       - (- reciH11 x0 - RND (reciA x0 * x1)))
                      (- (RND (reciA x0 * x1) - reciA x0 * x1)).
rewrite Rabs_Ropp in T.
have E2 : RND (- reciH11 x0 - RND (reciA x0 * x1))
          - (- reciH11 x0 - RND (reciA x0 * x1))
          + - (RND (reciA x0 * x1) - reciA x0 * x1)
        = RND (- reciH11 x0 - RND (reciA x0 * x1))
          - (- reciH11 x0 - RND (reciA x0 * x1))
          - (RND (reciA x0 * x1) - reciA x0 * x1) by ring.
rewrite E2 in T.
by nra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The second: `b12 <- RN(b11 + a h1)'                                       *)
(* ---------------------------------------------------------------------------*)

Definition reciB12n (x0 x1 : R) : R :=
  RND (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1)).

Lemma reciAh1n_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (RND (reciA x0 * reciH1n x0 x1))
    <= (3 * u + 17 * (u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have Hh1 := reciH1n_bound Fx0 Hx0 Hx1.
have Hm : Rabs (reciA x0 * reciH1n x0 x1)
            <= (3 * u + 13 * (u * u)) * Rabs (reciA x0).
  rewrite Rabs_mult; have := Rabs_pos (reciH1n x0 x1); nra.
have Hr := rndd_abs (reciA x0 * reciH1n x0 x1).
have Hstep : (1 + u) * Rabs (reciA x0 * reciH1n x0 x1)
             <= (1 + u) * ((3 * u + 13 * (u * u)) * Rabs (reciA x0)).
  by apply: Rmult_le_compat_l; lra.
have Hfin : (1 + u) * ((3 * u + 13 * (u * u)) * Rabs (reciA x0))
            <= (3 * u + 17 * (u * u)) * Rabs (reciA x0).
  have -> : (1 + u) * ((3 * u + 13 * (u * u)) * Rabs (reciA x0))
          = (3 * u + 16 * (u * u) + 13 * (u * u * u)) * Rabs (reciA x0)
    by ring.
  by apply: Rmult_le_compat_r => //; nra.
lra.
Qed.

Lemma reciAh1n_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (RND (reciA x0 * reciH1n x0 x1) - reciA x0 * reciH1n x0 x1)
    <= (3 * (u * u) + 13 * (u * u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Hh1 := reciH1n_bound Fx0 Hx0 Hx1.
have Hm : Rabs (reciA x0 * reciH1n x0 x1)
            <= (3 * u + 13 * (u * u)) * Rabs (reciA x0).
  rewrite Rabs_mult; have := Rabs_pos (reciH1n x0 x1); nra.
have Hr := rndd_err (reciA x0 * reciH1n x0 x1).
by nra.
Qed.

Lemma reciB12n_arg_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1))
    <= (4 * u + 17 * (u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Hb11 := reciB11_bound Fx0 Hx0.
have Hah1 := reciAh1n_bound Fx0 Hx0 Hx1.
by have := Rabs_triang (reciB11 x0) (RND (reciA x0 * reciH1n x0 x1)); nra.
Qed.

Lemma reciB12n_bound x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB12n x0 x1) <= 5 * u * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have Ht := reciB12n_arg_bound Fx0 Hx0 Hx1.
have Hr := rndd_abs (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1)).
have Hstep : (1 + u) * Rabs (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1))
             <= (1 + u) * ((4 * u + 17 * (u * u)) * Rabs (reciA x0)).
  by apply: Rmult_le_compat_l; lra.
have Hfin : (1 + u) * ((4 * u + 17 * (u * u)) * Rabs (reciA x0))
            <= 5 * u * Rabs (reciA x0).
  have -> : (1 + u) * ((4 * u + 17 * (u * u)) * Rabs (reciA x0))
          = (4 * u + 21 * (u * u) + 17 * (u * u * u)) * Rabs (reciA x0)
    by ring.
  by apply: Rmult_le_compat_r => //; nra.
by rewrite /reciB12n; lra.
Qed.

Lemma reciB12n_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB12n x0 x1 - (reciB11 x0 + reciA x0 * reciH1n x0 x1))
    <= (7 * (u * u) + 30 * (u * u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Ht := reciB12n_arg_bound Fx0 Hx0 Hx1.
have Hr := rndd_err (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1)).
have Hi := reciAh1n_err Fx0 Hx0 Hx1.
have E : reciB12n x0 x1 - (reciB11 x0 + reciA x0 * reciH1n x0 x1)
       = (RND (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1))
          - (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1)))
         + (RND (reciA x0 * reciH1n x0 x1) - reciA x0 * reciH1n x0 x1)
  by rewrite /reciB12n; ring.
rewrite E.
have T := Rabs_triang (RND (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1))
                       - (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1)))
                      (RND (reciA x0 * reciH1n x0 x1)
                       - reciA x0 * reciH1n x0 x1).
by nra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The seed, and that it is a double word                                    *)
(* ---------------------------------------------------------------------------*)

Definition reciBn (x0 x1 : R) : dwR := Fast2Sum (reciB01 x0) (reciB12n x0 x1).

Definition reciBWn (x0 x1 : R) : twR :=
  TWR (dwh (reciBn x0 x1)) (dwl (reciBn x0 x1)) 0.

Lemma reciB12n_le_B01 x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (reciB12n x0 x1) <= Rabs (reciB01 x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hpos := Rabs_pos (reciA x0).
have H1 := reciB12n_bound Fx0 Hx0 Hx1.
have H2 := reciB01_bound Fx0 Hx0.
by nra.
Qed.

Lemma reciBn_isDW x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  isDW (reciBWn x0 x1).
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (reciB01 x0) by apply: generic_format_round.
have F12 : format (reciB12n x0 x1) by apply: generic_format_round.
have Hord := reciB12n_le_B01 Fx0 Hx0 Hx1.
have Hmag := @magnitude_Fast2Sum p Hp2 choice _ _ F01 F12 (fun _ => Hord).
have Hfor := @format_Fast2Sum p Hp2 choice (reciB01 x0) (reciB12n x0 x1).
rewrite /reciBWn /reciBn.
case E : (Fast2Sum (reciB01 x0) (reciB12n x0 x1)) => [s e].
rewrite E in Hmag Hfor.
rewrite /magnitudeDWR in Hmag.
case: Hfor => Fs Fe.
split => //.
by right; rewrite dwhE dwlE; lra.
Qed.

Lemma TWval_reciBWn x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  TWval (reciBWn x0 x1) = reciB01 x0 + reciB12n x0 x1.
Proof.
move=> Fx0 Hx0 Hx1.
have F01 : format (reciB01 x0) by apply: generic_format_round.
have F12 : format (reciB12n x0 x1) by apply: generic_format_round.
have Hord := reciB12n_le_B01 Fx0 Hx0 Hx1.
have Hc := @Fast2Sum_correct p Hp2 choice _ _ F01 F12 (fun _ => Hord).
rewrite /reciBWn /TWval /reciBn.
by rewrite Rplus_0_r; exact: Hc.
Qed.


(* ---------------------------------------------------------------------------*)
(*  How well the split seed approximates one over x                           *)
(* ---------------------------------------------------------------------------*)

Lemma reciBWn_newton_eq x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  TWval (reciBWn x0 x1)
    = reciA x0 * (2 - (x0 + x1) * reciA x0)
      + reciA x0 * (reciH1n x0 x1 - (- reciH11 x0 - reciA x0 * x1))
      + (reciB12n x0 x1 - (reciB11 x0 + reciA x0 * reciH1n x0 x1)).
Proof.
move=> Fx0 Hx0 Hx1.
have Fa : format (reciA x0) by apply: generic_format_round.
have Hprod := TwoProd_correct Fa format_1m2u.
have [_ Hb _ _] := Hprod p_gt_0 rnd valid_rnd.
have Hb2 : reciB01 x0 + reciB11 x0 = reciA x0 * (1 - 2 * u) by exact: Hb.
have Hh11 := reciH11_exact Fx0 Hx0.
rewrite (TWval_reciBWn Fx0 Hx0 Hx1) Hh11.
have -> : reciB01 x0 = reciA x0 * (1 - 2 * u) - reciB11 x0 by lra.
ring.
Qed.

(* THIRTEEN `u^2' WHERE THE PAPER HAS SEVEN, which is the two split lines     *)
(* and nothing else: six from the first and seven from the second.            *)
Lemma reciBWn_newton_err x0 x1 :
  format x0 -> x0 <> 0 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (TWval (reciBWn x0 x1) - reciA x0 * (2 - (x0 + x1) * reciA x0))
    <= (13 * (u * u) + 40 * (u * u * u)) * Rabs (reciA x0).
Proof.
move=> Fx0 Hx0 Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpos := Rabs_pos (reciA x0).
have Hh1 := reciH1n_err Fx0 Hx0 Hx1.
have Hb12 := reciB12n_err Fx0 Hx0 Hx1.
rewrite (reciBWn_newton_eq Fx0 Hx0 Hx1).
have -> : reciA x0 * (2 - (x0 + x1) * reciA x0)
          + reciA x0 * (reciH1n x0 x1 - (- reciH11 x0 - reciA x0 * x1))
          + (reciB12n x0 x1 - (reciB11 x0 + reciA x0 * reciH1n x0 x1))
          - reciA x0 * (2 - (x0 + x1) * reciA x0)
        = reciA x0 * (reciH1n x0 x1 - (- reciH11 x0 - reciA x0 * x1))
          + (reciB12n x0 x1 - (reciB11 x0 + reciA x0 * reciH1n x0 x1)) by ring.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_mult.
by nra.
Qed.

(* `38u^2' for the paper's `32u^2'.  The square of the starting error does    *)
(* not move -- it is `a' alone, which is unchanged -- and all six of the      *)
(* extra `u^2' are the seed's.                                                *)
Lemma reciB_X_errn x0 x1 :
  format x0 -> 1 <= x0 < 2 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (TWval (reciBWn x0 x1) * (x0 + x1) - 1)
    <= 38 * (u * u) + 180 * (u * u * u).
Proof.
move=> Fx0 [Hx0l Hx0r] Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hx0 : x0 <> 0 by lra.
have Hax0 := reciA_x0_bound Fx0 Hx0.
have HaX := reciA_X_bound Fx0 Hx0 Hx1.
have Hnew := reciBWn_newton_err Fx0 Hx0 Hx1.
have Ha : Rabs (reciA x0) <= 1 + 3 * u.
  have Hap : 0 < reciA x0 by nra.
  by rewrite Rabs_pos_eq; nra.
have Hap : 0 < Rabs (reciA x0) by move: Hax0; split_Rabs; nra.
have HaXa : Rabs (reciA x0 * (x0 + x1)) <= 1 + 5 * u + 6 * (u * u).
  by move: HaX; split_Rabs; lra.
set b := TWval (reciBWn x0 x1).
set a := reciA x0 in Ha Hnew HaXa HaX Hap.
set X := x0 + x1 in Hnew HaXa HaX.
have Hid : b * X - 1 = - (a * X - 1) ^ 2 + (b - a * (2 - X * a)) * X
  by rewrite /b; ring.
have HXb : Rabs ((b - a * (2 - X * a)) * X)
             <= (13 * (u * u) + 40 * (u * u * u)) * (1 + 5 * u + 6 * (u * u)).
  rewrite Rabs_mult.
  have HH : Rabs a * Rabs X = Rabs (a * X) by rewrite Rabs_mult.
  have HpX := Rabs_pos X.
  have H1 : Rabs (b - a * (2 - X * a))
              <= (13 * (u * u) + 40 * (u * u * u)) * Rabs a
    by rewrite /b; exact: Hnew.
  have Hstep : Rabs (b - a * (2 - X * a)) * Rabs X
                 <= (13 * (u * u) + 40 * (u * u * u)) * (Rabs a * Rabs X)
    by nra.
  rewrite HH in Hstep.
  have Hk : 0 <= 13 * (u * u) + 40 * (u * u * u) by nra.
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

Lemma reciBWn_bound x0 x1 :
  format x0 -> 1 <= x0 < 2 -> (x1 = 0 \/ Rabs x1 < ulp x0) ->
  Rabs (TWval (reciBWn x0 x1)) <= 1 + 5 * u.
Proof.
move=> Fx0 [Hx0l Hx0r] Hx1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hx0 : x0 <> 0 by lra.
have Hax0 := reciA_x0_bound Fx0 Hx0.
have HaX := reciA_X_range Fx0 Hx0 Hx1.
have Hnew := reciBWn_newton_err Fx0 Hx0 Hx1.
have Ha : Rabs (reciA x0) <= 1 + 3 * u.
  have Hap : 0 < reciA x0 by nra.
  by rewrite Rabs_pos_eq; nra.
set b := TWval (reciBWn x0 x1).
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

Lemma reciB_x_errn x0 x1 x2 :
  tw_norm p x0 x1 x2 ->
  Rabs (TWval (reciBWn x0 x1) * (x0 + x1 + x2) - 1)
    <= 40 * (u * u) + 200 * (u * u * u).
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1 Hx2] := Hn.
have HX := reciB_X_errn Fx0 (conj Hx0l Hx0r) Hx1.
have Hb := reciBWn_bound Fx0 (conj Hx0l Hx0r) Hx1.
have Hx2b : Rabs x2 < 2 * (u * u) by apply: (@tw_norm_x2 p Hp2 x0 x1 x2 Hn).
set b := TWval (reciBWn x0 x1) in HX Hb *.
have -> : b * (x0 + x1 + x2) - 1 = (b * (x0 + x1) - 1) + b * x2 by ring.
apply: Rle_trans (Rabs_triang _ _) _.
rewrite Rabs_mult.
have := Rabs_pos b; have := Rabs_pos x2.
have Hu2 : u * u <= /1024 * u by nra.
have Hu3 : u * u * u <= /1024 * (u * u) by nra.
by nra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Scale and sign, so the bound holds of any triple word                     *)
(* ---------------------------------------------------------------------------*)

Lemma reciH1n_scale x0 x1 c :
  x0 <> 0 -> reciH1n (x0 * pow c) (x1 * pow c) = reciH1n x0 x1.
Proof.
move=> Hx0.
have Hp0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
rewrite /reciH1n reciH11_scale // reciA_scale //.
have -> : reciA x0 * pow (- c) * (x1 * pow c) = reciA x0 * x1
  by rewrite bpow_opp; field.
by [].
Qed.

Lemma reciH1n_opp x0 x1 : x0 <> 0 -> reciH1n (- x0) (- x1) = reciH1n x0 x1.
Proof.
move=> Hx0; rewrite /reciH1n reciH11_opp // reciA_opp //.
have -> : - reciA x0 * - x1 = reciA x0 * x1 by ring.
by [].
Qed.

Lemma reciB12n_scale x0 x1 c :
  x0 <> 0 -> reciB12n (x0 * pow c) (x1 * pow c) = reciB12n x0 x1 * pow (- c).
Proof.
move=> Hx0.
rewrite /reciB12n reciB11_scale // reciA_scale // reciH1n_scale //.
have -> : reciA x0 * pow (- c) * reciH1n x0 x1
        = reciA x0 * reciH1n x0 x1 * pow (- c) by ring.
rewrite (round_scale p choice).
rewrite -Rmult_plus_distr_r.
by rewrite (round_scale p choice).
Qed.

Lemma reciB12n_opp x0 x1 :
  x0 <> 0 -> reciB12n (- x0) (- x1) = - reciB12n x0 x1.
Proof.
move=> Hx0.
rewrite /reciB12n reciB11_opp // reciA_opp // reciH1n_opp //.
have -> : - reciA x0 * reciH1n x0 x1 = - (reciA x0 * reciH1n x0 x1) by ring.
rewrite RN_sym //.
have -> : - reciB11 x0 + - RND (reciA x0 * reciH1n x0 x1)
        = - (reciB11 x0 + RND (reciA x0 * reciH1n x0 x1)) by ring.
by rewrite RN_sym.
Qed.

Lemma reciBWn_scale x0 x1 c :
  x0 <> 0 ->
  reciBWn (x0 * pow c) (x1 * pow c) = scaleTW (- c) (reciBWn x0 x1).
Proof.
move=> Hx0.
rewrite /reciBWn /reciBn reciB01_scale // reciB12n_scale //.
rewrite /Fast2Sum /scaleTW /dwh /dwl.
have Add : forall y z : R, y * pow (- c) + z * pow (- c) = (y + z) * pow (- c)
  by move=> *; ring.
have Sub : forall y z : R, y * pow (- c) - z * pow (- c) = (y - z) * pow (- c)
  by move=> *; ring.
by rewrite !(Add, Sub, (round_scale p choice)) Rmult_0_l.
Qed.

Lemma reciBWn_opp x0 x1 :
  x0 <> 0 -> reciBWn (- x0) (- x1) = negTW (reciBWn x0 x1).
Proof.
move=> Hx0.
rewrite /reciBWn /reciBn reciB01_opp // reciB12n_opp //.
rewrite /Fast2Sum /negTW /dwh /dwl.
have Add : forall y z : R, - y + - z = - (y + z) by move=> *; ring.
have Sub : forall y z : R, - y - - z = - (y - z) by move=> *; ring.
by rewrite !(Add, Sub, RN_sym) // Ropp_0.
Qed.

Lemma reciBWn_x_err x :
  isTW x -> tw0 x <> 0 ->
  Rabs (TWval (reciBWn (tw0 x) (tw1 x)) * TWval x - 1)
    <= 40 * (u * u) + 200 * (u * u * u).
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
  have Hb := reciB_x_errn Hn.
  rewrite (reciBWn_scale _ _ Hx0n) reciBWn_opp // TWval_scale TWval_opp in Hb.
  have HE : - TWval (reciBWn x0 x1) * pow (- c)
              * (- x0 * pow c + - x1 * pow c + - x2 * pow c)
          = TWval (reciBWn x0 x1) * TWval (TWR x0 x1 x2).
    by rewrite /TWval bpow_opp; field; lra.
  by rewrite HE in Hb.
have Hn := Hpos Hgt.
rewrite /scaleTW /tw_normP in Hn.
have Hb := reciB_x_errn Hn.
rewrite (reciBWn_scale _ _ Hx0) TWval_scale in Hb.
have HE : TWval (reciBWn x0 x1) * pow (- c)
            * (x0 * pow c + x1 * pow c + x2 * pow c)
        = TWval (reciBWn x0 x1) * TWval (TWR x0 x1 x2).
  by rewrite /TWval bpow_opp; field; lra.
by rewrite HE in Hb.
Qed.

End SecDivNoFMA.
