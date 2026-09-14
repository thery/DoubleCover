(* Counterexample: vecSum_Thm6 as currently stated (Fnonoverlap of the raw    *)
(* VecSum output) is FALSE.  Input [15;15;15/16;15/16] at p=4 satisfies        *)
(* sorted_mag + pairwise_ulp + size<=6 + normal + ties-to-even, yet            *)
(* VecSum = [32;-1;7/8;0], which is NOT F-nonoverlapping (|7/8| > 1/2 uls(-1)   *)
(* = 1/2).  The paper's real Theorem 6 concludes P-nonoverlap of VSEB(VecSum),  *)
(* a strictly weaker statement.                                                *)
From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import VecSum.

Open Scope R_scope.

Definition p : Z := 4.
Definition choice (z : Z) : bool := negb (Z.even z).

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation rnd := (Znearest choice).
Local Notation RND := (round beta fexp rnd).

Lemma Hp2 : (1 < p)%Z. Proof. by []. Qed.
Instance p_gt_0 : Prec_gt_0 p. Proof. by []. Qed.
Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

(* the input list *)
Definition l : seq R := [:: 15; 15; 15/16; 15/16].

Local Notation TwoSum := (TwoSum p choice).
Local Notation vecSum := (VecSum.vecSum p choice).
Local Notation vecSumAux := (VecSum.vecSumAux p choice).
Local Notation Fnonoverlap := (Nonoverlap.Fnonoverlap p).
Local Notation uls := (Uls.uls p).

Lemma choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Proof.
move=> x; rewrite /choice; congr negb.
have -> : (- (x + 1) = - x - 1)%Z by lia.
by rewrite Z.even_sub Z.even_opp /=; case: Z.even.
Qed.

(* format facts *)
Lemma Ffloat (m e : Z) : (Z.abs m < 2 ^ p)%Z ->
  format (IZR m * pow e).
Proof.
move=> Hm; apply: generic_format_FLX.
by exists (Float beta m e); rewrite /F2R //=.
Qed.

Lemma Ffloat' (v : R) (m e : Z) : v = IZR m * pow e ->
  (Z.abs m < 2 ^ p)%Z -> format v.
Proof. by move=> ->; apply: Ffloat. Qed.

Lemma F15 : format 15.
Proof. by apply: (Ffloat' _ 15 0); rewrite /= ?Rmult_1_r. Qed.

Lemma F15_16 : format (15 / 16).
Proof. apply: (Ffloat' _ 15 (-4)); [rewrite /= /Z.pow_pos /=; lra | ]; by []. Qed.

Lemma F15_8 : format (15 / 8).
Proof. apply: (Ffloat' _ 15 (-3)); [rewrite /= /Z.pow_pos /=; lra | ]; by []. Qed.

Lemma F7_8 : format (7 / 8).
Proof. apply: (Ffloat' _ 7 (-3)); [rewrite /= /Z.pow_pos /=; lra | ]; by []. Qed.

Lemma F16 : format 16.
Proof. apply: (Ffloat' _ 1 4); [rewrite /= /Z.pow_pos /=; lra | ]; by []. Qed.

Lemma F32 : format 32.
Proof. apply: (Ffloat' _ 1 5); [rewrite /= /Z.pow_pos /=; lra | ]; by []. Qed.

Lemma Fm1 : format (-1).
Proof.
apply: generic_format_opp; apply: (Ffloat' _ 1 0); rewrite /= ?Rmult_1_r; by [].
Qed.

Lemma RND_15_8 : RND (15 / 8) = 15 / 8.
Proof. by apply: round_generic; apply: F15_8. Qed.

(* 15 + 15/8 = 135/8 = 16.875 rounds to 16 (nearest float; 18 is farther). *)
Lemma RND_16875 : RND (15 + 15 / 8) = 16.
Proof.
have V := FLX_exp_valid p.
have E16 : (16 = pow 4) by rewrite /= /Z.pow_pos /=; lra.
have E18 : (18 = 9 * pow 1) by rewrite /= /Z.pow_pos /=; lra.
have Vd := V p_gt_0.
have U16 : ulp beta fexp 16 = 2.
  rewrite E16 ulp_bpow /FLX_exp /=.
  by rewrite /= /Z.pow_pos /=; lra.
have Hd : round beta fexp Zfloor (15 + 15 / 8) = 16.
  apply: round_DN_eq => //; first exact: F16.
  rewrite succ_eq_pos; last by lra.
  rewrite U16; lra.
have F18 : format 18 by rewrite E18; apply: (Ffloat 9 1).
have Hu : round beta fexp Zceil (15 + 15 / 8) = 18.
  have -> : (15 + 15 / 8 = 16 + 7 / 8) by lra.
  rewrite (@round_UP_plus_eps beta fexp Vd 16 F16 (7/8)); last first.
    rewrite Rle_bool_true; last by lra.
    rewrite U16; lra.
  rewrite succ_eq_pos; last by lra.
  rewrite U16; lra.
rewrite (@round_N_eq_DN beta fexp Vd choice (15 + 15/8)); first by rewrite Hd.
rewrite Hd Hu; lra.
Qed.

(* 15 + 16 = 31 is the exact midpoint of [30,32]; ties-to-even -> 32. *)
Lemma RND_31 : RND (15 + 16) = 32.
Proof.
have V := FLX_exp_valid p.
have Vd := V p_gt_0.
have E30 : (30 = 15 * pow 1) by rewrite /= /Z.pow_pos /=; lra.
have F30 : format 30 by rewrite E30; apply: (Ffloat 15 1).
have U30 : ulp beta fexp 30 = 2.
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /FLX_exp.
  have Hm30 : (mag beta 30 = 5%Z :> Z)
    by apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
  by rewrite Hm30 /p /= /Z.pow_pos /=; lra.
have Hd : round beta fexp Zfloor (15 + 16) = 30.
  apply: round_DN_eq => //.
  rewrite succ_eq_pos; last by lra.
  rewrite U30; lra.
have Hu : round beta fexp Zceil (15 + 16) = 32.
  have -> : (15 + 16 = 30 + 1) by lra.
  rewrite (@round_UP_plus_eps beta fexp Vd 30 F30 1); last first.
    rewrite Rle_bool_true; last by lra.
    rewrite U30; lra.
  rewrite succ_eq_pos; last by lra.
  rewrite U30; lra.
rewrite (@round_N_middle beta fexp choice (15 + 16)); last by rewrite Hd Hu; lra.
rewrite Hd Hu.
have Hm31 : (mag beta (15 + 16) = 5%Z :> Z)
  by apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
have Hsm : scaled_mantissa beta fexp (15 + 16) = 31 / 2.
  rewrite /scaled_mantissa /cexp Hm31 /FLX_exp /p //.
  rewrite /= /Z.pow_pos /=; lra.
rewrite Hsm.
have Hzf : Zfloor (31 / 2) = 15%Z.
  apply: Zfloor_imp; rewrite (_ : (15 + 1)%Z = 16%Z) //= /Z.pow_pos /=; lra.
by rewrite Hzf /choice /=.
Qed.

(* Any 2Sum with format operands is fully determined by its rounded sum. *)
Lemma TwoSum_eq a b : format a -> format b ->
  TwoSum a b = DWR (RND (a + b)) (a + b - RND (a + b)).
Proof.
move=> Fa Fb.
have Hc := TwoSum_correct_loc Hp2 choice_sym Fa Fb.
rewrite {1}/TwoSum.TwoSum; congr DWR; lra.
Qed.

(* ===========================================================================*)
(*  THE COUNTEREXAMPLE.                                                       *)
(*                                                                            *)
(*  [l] satisfies every hypothesis of Theorem 6 -- its entries are floats,    *)
(*  magnitude-sorted and pairwise-ulp separated, [size l <= 6], and the       *)
(*  rounding is ties-to-even -- yet [vecSum l = [32; -1; 7/8; 0]], whose      *)
(*  third entry overflows the F-nonoverlap budget of the second:              *)
(*  [|7/8| > 1/2 uls(-1) = 1/2].  So the raw VecSum output is NOT             *)
(*  F-nonoverlapping, and Theorem 6 CANNOT be strengthened to say it is.      *)
(*  What the paper (and [Thm6.v]) proves is the P-nonoverlap of [vseb] OF     *)
(*  that output -- VSEB repairs exactly this overlap.                         *)
(* ===========================================================================*)
Lemma vecSum_l : vecSum l = [:: 32; -1; 7/8; 0].
Proof.
have E2 : vecSumAux [:: 15/16; 15/16] = ([:: 0], 15/8).
  rewrite /vecSumAux (TwoSum_eq _ _ F15_16 F15_16).
  have -> : (15/16 + 15/16 = 15/8) by lra.
  by rewrite RND_15_8; congr (_, _); congr cons; lra.
have E3 : vecSumAux [:: 15; 15/16; 15/16] = ([:: 7/8; 0], 16).
  rewrite VecSum.vecSumAux_cons E2 (TwoSum_eq _ _ F15 F15_8) RND_16875.
  by congr (_, _); congr cons; lra.
rewrite /VecSum.vecSum /l VecSum.vecSumAux_cons E3 (TwoSum_eq _ _ F15 F16)
        RND_31.
by congr cons; congr cons; lra.
Qed.

Lemma not_Fnonoverlap_vecSum_l : ~ Fnonoverlap (vecSum l).
Proof.
have H32 : (32 != 0 :> R) by apply/eqP; lra.
have Hm1 : (-1 != 0 :> R) by apply/eqP; lra.
have H78 : (7/8 != 0 :> R) by apply/eqP; lra.
have H0 : (0 != 0 :> R) = false by apply/eqP.
rewrite vecSum_l /Nonoverlap.Fnonoverlap /= H32 Hm1 H78 H0.
move=> [_ [H _]].
have Hu : uls (-1) <= Rabs (-1) by apply: Uls.uls_le_abs Fm1 _; lra.
have H78' : (7/8 : R) <> 0 by lra.
have Hv := H H78'.
have Hne : is_left (Req_EM_T (-1) 0) = false by case: Req_EM_T => // He; lra.
move: Hv; rewrite Hne => Hv'.
by move: Hu Hv'; split_Rabs; lra.
Qed.
