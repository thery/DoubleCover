From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From twarith.threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From twarith.threewords Require Import TwoSum Nonoverlap TWR VecSum.
From twarith.threewords Require Import ThreeProd ThreeProdDW ThreeProdOne.
From twarith.threewords Require Import ThreeReci ThreeDiv ThreeSqRt.
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
Local Notation u_le_2048 := (u_le_2048 Hp11).
Local Notation sub2TW_isTW := (sub2TW_isTW Hp2).
Local Notation head_one_gen_c := (head_one_gen_c Hp2 Hp10).
Local Notation ThreeProdDWn := (ThreeProdDWn p choice).
Local Notation ThreeProdOneTWn := (ThreeProdOneTWn p choice).
Local Notation ThreeProdDWn_isTW := (ThreeProdDWn_isTW Hp2 Hp11 choice_sym).
Local Notation ThreeProdDWn_error := (ThreeProdDWn_error Hp2 Hp11 choice_sym).
Local Notation ThreeProdDWn_head_gap := (ThreeProdDWn_head_gap Hp2 Hp11 choice_sym).
Local Notation ThreeProdOneTWn_error_c := (ThreeProdOneTWn_error_c Hp2 Hp11 choice_sym).

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


(* ---------------------------------------------------------------------------*)
(*  The assembly, with the seed's number a parameter                          *)
(* ---------------------------------------------------------------------------*)

(* The paper writes its own `34' and `35' into `sub2_near_one',               *)
(* `newton_sq_le' and `div_error_assembly'.  Ours is `40', so the three are   *)
(* restated with it; nothing else about them changes.                         *)
Lemma newton_sq_len t :
  Rabs t <= 40 * (u * u) + 200 * (u * u * u) ->
  t ^ 2 <= 1700 * (u * u * u * u).
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

Lemma sub2_near_onen B X P d1 :
  Rabs (B * X - 1) <= 41 * (u * u) ->
  Rabs (P - B * X) <= d1 * Rabs (B * X) ->
  0 <= d1 -> d1 <= u * u ->
  Rabs (2 - P - 1) <= 43 * (u * u).
Proof.
move=> H41 HP Hd10 Hd1u.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu2 : u * u <= / 1024 * u by nra.
have HBXub : Rabs (B * X) <= 1 + 41 * (u * u).
  by have := Rabs_triang_inv (B * X) 1; rewrite Rabs_R1; lra.
have Hpos := Rabs_pos (B * X).
have Hd : d1 * Rabs (B * X) <= u * u * (1 + 41 * (u * u)).
  by apply: Rmult_le_compat; lra.
have T := Rabs_triang (1 - B * X) (B * X - P).
have Hm : Rabs (1 - B * X) = Rabs (B * X - 1) by rewrite Rabs_minus_sym.
have Hm2 : Rabs (B * X - P) = Rabs (P - B * X) by rewrite Rabs_minus_sym.
have E : 2 - P - 1 = (1 - B * X) + (B * X - P) by ring.
by rewrite E; nra.
Qed.

Lemma div_error_assemblyn a c R0 e1 e2 e3 e4 dd1 dd2 dd3 :
  0 <= a -> a <= 1 + 41 * (u * u) ->
  0 <= c -> c <= 1 + 43 * (u * u) ->
  0 <= R0 -> 0 <= dd1 -> 0 <= dd2 -> dd2 <= u * u -> 0 <= dd3 ->
  e1 <= dd3 * ((1 + dd2) * (a * R0) * c) ->
  e2 <= dd2 * (a * R0 * c) ->
  e3 <= a * R0 * (dd1 * a) ->
  e4 <= 1700 * (u * u * u * u) * R0 ->
  e1 + e2 + e3 + e4
    <= (dd1 * (1 + 83 * (u * u)) + (dd2 + dd3) * (1 + 90 * (u * u))
        + 1700 * (u * u * u * u)) * R0.
Proof.
move=> Ha0 Ha1 Hc0 Hc1 HR0 Hd10 Hd20 Hd2u Hd30 H1 H2 H3 H4.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu2 : u * u <= / 1024 * u by nra.
have Hac : a * c <= 1 + 85 * (u * u) by nra.
have Hac0 : 0 <= a * c by nra.
have Haa : a * a <= 1 + 83 * (u * u) by nra.
have Hd2R : 0 <= dd2 * R0 by nra.
have Hd1R : 0 <= dd1 * R0 by nra.
have Hd3R : 0 <= dd3 * R0 by nra.
have K1 : dd3 * ((1 + dd2) * (a * R0) * c) <= dd3 * (1 + 90 * (u * u)) * R0.
  have -> : dd3 * ((1 + dd2) * (a * R0) * c)
      = (dd3 * R0) * ((1 + dd2) * (a * c))
    by ring.
  have -> : dd3 * (1 + 90 * (u * u)) * R0 = (dd3 * R0) * (1 + 90 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l => //; nra.
have K2 : dd2 * (a * R0 * c) <= dd2 * (1 + 90 * (u * u)) * R0.
  have -> : dd2 * (a * R0 * c) = (dd2 * R0) * (a * c) by ring.
  have -> : dd2 * (1 + 90 * (u * u)) * R0 = (dd2 * R0) * (1 + 90 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l => //; nra.
have K3 : a * R0 * (dd1 * a) <= dd1 * (1 + 83 * (u * u)) * R0.
  have -> : a * R0 * (dd1 * a) = (dd1 * R0) * (a * a) by ring.
  have -> : dd1 * (1 + 83 * (u * u)) * R0 = (dd1 * R0) * (1 + 83 * (u * u))
    by ring.
  by apply: Rmult_le_compat_l.
by nra.
Qed.

(* The core of Theorem 10, on the bare reals, with the seed's number handed   *)
(* in.  Nothing here knows about triple words: it is the algebraic identity   *)
(*                                                                            *)
(*   Y - Z/X = (Y - A i) + (A - B Z) i + (B Z)(X B - P) + Z (B (2 - X B) - 1/X)*)
(*                                                                            *)
(* with `i = 2 - P', whose last term is `- Z (B X - 1)^2 / X'.                *)
Lemma div_error_coren B X Z P A Y d1 d2 d3 :
  Rabs (B * X - 1) <= 40 * (u * u) + 200 * (u * u * u) ->
  Rabs (P - B * X) <= d1 * Rabs (B * X) ->
  Rabs (A - B * Z) <= d2 * Rabs (B * Z) ->
  Rabs (Y - A * (2 - P)) <= d3 * Rabs (A * (2 - P)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u -> 0 <= d3 ->
  Rabs (Y - Z / X)
    <= (d1 * (1 + 83 * (u * u)) + (d2 + d3) * (1 + 90 * (u * u))
        + 1700 * (u * u * u * u)) * Rabs (Z / X).
Proof.
move=> HBX HP HA HY Hd10 Hd1u Hd20 Hd2u Hd30.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Hu3 : u * u * u <= / 1024 * (u * u) by nra.
have HBX41 : Rabs (B * X - 1) <= 41 * (u * u)
  by clear -HBX Hu0 Hu1024 Hu3; nra.
have HX0 : X <> 0.
  move=> HX; move: HBX41; rewrite HX Rmult_0_r.
  have -> : (0 - 1) = -1 by ring.
  by rewrite Rabs_Ropp Rabs_R1; clear -Hu0 Hu1024; nra.
set I := 2 - P in HY *.
have HI1 : Rabs (I - 1) <= 43 * (u * u)
  by apply: (sub2_near_onen (B := B) (X := X) (P := P) (d1 := d1)).
have HIub : Rabs I <= 1 + 43 * (u * u)
  by have := Rabs_triang_inv I 1; rewrite Rabs_R1; lra.
have HBXub : Rabs (B * X) <= 1 + 41 * (u * u)
  by have := Rabs_triang_inv (B * X) 1; rewrite Rabs_R1; lra.
set R0 := Rabs (Z / X).
have HR0 : 0 <= R0 by apply: Rabs_pos.
have Hab : 0 <= Rabs (B * X) by apply: Rabs_pos.
have Hai : 0 <= Rabs I by apply: Rabs_pos.
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
    <= 1700 * (u * u * u * u) * R0.
  rewrite E3; apply: Rmult_le_compat_r => //.
  by apply: newton_sq_len.
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
by apply: (div_error_assemblyn (a := Rabs (B * X)) (c := Rabs I) (R0 := R0)).
Qed.


(* ---------------------------------------------------------------------------*)
(*  Algorithm 14, with nothing fused anywhere                                 *)
(* ---------------------------------------------------------------------------*)

Definition ThreeDivAuxN (mul1 mul2 mul3 : twR -> twR -> twR) (z x : twR)
    : twR :=
  let bw := reciBWn (tw0 x) (tw1 x) in
  mul3 (mul2 bw z) (sub2TW (mul1 bw x)).

Definition ThreeDivN (z x : twR) : twR :=
  ThreeDivAuxN ThreeProdDWn ThreeProdDWn ThreeProdOneTWn z x.

(* The paper's assembly, with its own `35' and `40' become `41' and `43'.     *)
Lemma ThreeDivAuxN_error mul1 mul2 mul3 d1 d2 d3 :
  (forall b y, isDW b -> isTW y -> isTW (mul1 b y)) ->
  (forall b y, isDW b -> isTW y -> isTW (mul2 b y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval b * TWval y - 1) <= 41 * (u * u) -> tw0 (mul1 b y) = 1) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul1 b y) - TWval b * TWval y)
       <= d1 * Rabs (TWval b * TWval y)) ->
  (forall b y, isDW b -> isTW y ->
     Rabs (TWval (mul2 b y) - TWval b * TWval y)
       <= d2 * Rabs (TWval b * TWval y)) ->
  (forall a y, isTW a -> isTW y -> tw0 y = 1 ->
     Rabs (TWval y - 1) <= 43 * (u * u) ->
     Rabs (TWval (mul3 a y) - TWval a * TWval y)
       <= d3 * Rabs (TWval a * TWval y)) ->
  0 <= d1 -> d1 <= u * u -> 0 <= d2 -> d2 <= u * u ->
  0 <= d3 -> d3 <= u * u ->
  forall z x, isTW z -> isTW x -> tw0 x <> 0 ->
    Rabs (TWval (ThreeDivAuxN mul1 mul2 mul3 z x) - TWval z / TWval x)
      <= (d1 * (1 + 83 * (u * u)) + (d2 + d3) * (1 + 90 * (u * u))
          + 1700 * (u * u * u * u)) * Rabs (TWval z / TWval x).
Proof.
move=> Hmul1 Hmul2 Hhead Herr1 Herr2 Herr3 Hd10 Hd1u Hd20 Hd2u Hd30 Hd3u
       z x Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu1024 := u_le_1024.
have Fx0 : format (tw0 x) by case: x Hx {Hx0} => x0 x1 x2 [].
have Hx1 : tw1 x = 0 \/ Rabs (tw1 x) < ulp (tw0 x)
  by case: x Hx {Hx0 Fx0} => x0 x1 x2 [].
rewrite /ThreeDivAuxN.
set b := reciBWn (tw0 x) (tw1 x).
have HDW : isDW b by apply: reciBn_isDW.
have HBX := reciBWn_x_err Hx Hx0.
rewrite -/b in HBX.
have Hu3 : u * u * u <= / 1024 * (u * u) by nra.
have HBX41 : Rabs (TWval b * TWval x - 1) <= 41 * (u * u)
  by clear -HBX Hu0 Hu1024 Hu3; nra.
have Hprod1 : isTW (mul1 b x) by apply: Hmul1.
have Hhead1 : tw0 (mul1 b x) = 1 by apply: Hhead.
set i := sub2TW (mul1 b x).
have Hi : isTW i by apply: (sub2TW_isTW Hprod1).
have Hi0 : tw0 i = 1
  by rewrite /i; case: (mul1 b x) Hhead1 => t0 t1 t2 /= ->; ring.
have HIval : TWval i = 2 - TWval (mul1 b x) by rewrite /i TWval_sub2TW.
have HI1 : Rabs (TWval i - 1) <= 43 * (u * u).
  rewrite HIval.
  apply: (sub2_near_onen (B := TWval b) (X := TWval x)
            (P := TWval (mul1 b x)) (d1 := d1)) => //.
  by apply: Herr1.
have Herr1' := Herr1 _ _ HDW Hx.
have Herr2' := Herr2 _ _ HDW Hz.
have Herr3' := Herr3 _ _ (Hmul2 _ _ HDW Hz) Hi Hi0 HI1.
rewrite HIval in Herr3'.
by apply: (div_error_coren (B := TWval b) (X := TWval x) (Z := TWval z)
             (P := TWval (mul1 b x)) (A := TWval (mul2 b z))
             (Y := TWval (mul3 (mul2 b z) i)) (d1 := d1) (d2 := d2)
             (d3 := d3)).
Qed.

(* AND WHAT THE QUOTIENT COMES TO: 56u^3 for the paper's 29.                  *)
(*                                                                            *)
(* Twenty-five of it is each of the two double-word products, which the       *)
(* quotient does NOT halve -- unlike the root, which does -- and six is       *)
(* Algorithm 20, unchanged.  The paper's 29 is 10.5 + 10.5 + 8 at its own     *)
(* `d1'; ours is 25 + 25 + 6 at the naive one.                                *)
Lemma ThreeDivN_error z x :
  ties_to_even choice ->
  isTW z -> isTW x -> tw0 x <> 0 ->
  Rabs (TWval (ThreeDivN z x) - TWval z / TWval x)
    <= (56 * (u * u * u) + 5000 * (u * u * u * u))
       * Rabs (TWval z / TWval x).
Proof.
move=> Hc Hz Hx Hx0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu2048 := u_le_2048.
have Hu2 : u * u <= / 2048 * u by nra.
have Hu3 : u * u * u <= / 2048 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 2048 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 2048 * (u * u * u * u) by nra.
have Hu6 : u * u * u * u * u * u <= / 2048 * (u * u * u * u * u) by nra.
have H43a : (0 : R) <= 43 by lra.
have H43b : (43 : R) <= 112 by lra.
have Hd0 : 0 <= 25 * (u * u * u) + 200 * (u * u * u * u) by nra.
have Hdu : 25 * (u * u * u) + 200 * (u * u * u * u) <= u * u by nra.
have He0 : 0 <= 6 * (u * u * u) + 2180 * (u * u * u * u) by nra.
have Heu : 6 * (u * u * u) + 2180 * (u * u * u * u) <= u * u by nra.
(* [50 * 43 + 30 = 2180]: Algorithm 20's [delta3] at OUR tolerance.           *)
have Hd3le : 6 * (u * u * u) + (50 * 43 + 30) * (u * u * u * u)
    <= 6 * (u * u * u) + 2180 * (u * u * u * u) by lra.
have Hcu : (41 : R) * u <= / 4 by nra.
have Hhead : forall b y, isDW b -> isTW y ->
    Rabs (TWval b * TWval y - 1) <= 41 * (u * u) ->
    tw0 (ThreeProdDWn b y) = 1.
  apply: (head_one_gen_c Hcu).
  - by move=> X Y HX HY; apply: ThreeProdDWn_isTW.
  by move=> X Y HX HY HX0 HY0; apply: ThreeProdDWn_head_gap.
have Hgen := @ThreeDivAuxN_error ThreeProdDWn ThreeProdDWn ThreeProdOneTWn
  (25 * (u * u * u) + 200 * (u * u * u * u))
  (25 * (u * u * u) + 200 * (u * u * u * u))
  (6 * (u * u * u) + 2180 * (u * u * u * u))
  (fun b y Hb Hy => ThreeProdDWn_isTW Hb Hy)
  (fun b y Hb Hy => ThreeProdDWn_isTW Hb Hy)
  Hhead
  (fun b y Hb Hy => ThreeProdDWn_error Hc Hb Hy)
  (fun b y Hb Hy => ThreeProdDWn_error Hc Hb Hy)
  (fun a y Ha Hy Hy0 Hy1 =>
     Rle_trans _ _ _
       (ThreeProdOneTWn_error_c Hc H43a H43b Ha Hy Hy0 Hy1)
       (Rmult_le_compat_r _ _ _ (Rabs_pos _) Hd3le))
  Hd0 Hdu Hd0 Hdu He0 Heu z x Hz Hx Hx0.
rewrite /ThreeDivN.
apply: Rle_trans Hgen _.
apply: Rmult_le_compat_r; first by apply: Rabs_pos.
nra.
Qed.

End SecDivNoFMA.
