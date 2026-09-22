From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
From twarith.threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From twarith.threewords Require Import Uls TwoSum Nonoverlap TWR Merge VecSum.
From twarith.threewords Require Import VSEB Thm6 ThreeProd.

(* ALGORITHM 9'S STRUCTURE, TAKEN OFF ITS TWO FUSED LINES.                    *)
(*                                                                            *)
(* Section 6.2 of the paper settles the shape of the inner `VecSum' -- that   *)
(* it is F-nonoverlapping, that `VSEB' emits its leading limb unchanged --    *)
(* and `ThreeProd.v' proves all of it for the particular `c' and `z3' that    *)
(* Algorithm 9 computes.  Read again, the argument never asks what `c' and    *)
(* `z3' are.  It asks four things: that both are in the format, that `c' is   *)
(* under `8u^2' and `z3' under `12u^2', and that their sum's leading half is  *)
(* no bigger than fifteen `ulp' of the larger middle word.  Everything else   *)
(* is about `z00+', `b0', `b1', which no missing multiply-add touches.        *)
(*                                                                            *)
(* So this file is the paper's own proof text with `c' and `z3' made          *)
(* variables and those four facts made hypotheses.  Algorithm 9 satisfies     *)
(* them; so does the version with the two fused lines split in two, which is  *)
(* what `twseed.v' needs and why the file exists.                             *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecProdGen.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
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

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).
Local Notation TwoSum := (TwoSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation vseb := (vseb p choice).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation tw_norm := (tw_norm p).

(* The paper's own lemmas, bridged once so its proof text reads unchanged.    *)
Local Notation u_le_64 := (u_le_64 Hp6).
Local Notation two_p_ge_64 := (two_p_ge_64 Hp6).
Local Notation format_imul_u2 := (format_imul_u2 Hp2).
Local Notation vecSum3 := (vecSum3 Hp2 (choice := choice) choice_sym).
Local Notation s3_bound := (s3_bound Hp2 Hp6 choice).
Local Notation z00p_lb := (z00p_lb Hp2 choice).
Local Notation z00m_imul := (z00m_imul (p := p) choice).
Local Notation z00m_bound := (z00m_bound Hp2 choice).
Local Notation z01p_bound := (z01p_bound Hp2 choice).
Local Notation z10p_bound := (z10p_bound Hp2 choice).
Local Notation b2_bound := (b2_bound Hp2 choice).
Local Notation half_ulp_div_RN_add := (half_ulp_div_RN_add Hp2 choice).
Local Notation e4_le_half_ulp := (e4_le_half_ulp Hp2 choice_sym).
Local Notation mag_le_of_le_15ulp := (mag_le_of_le_15ulp (p := p)).
Local Notation b01_imul_half_ulp := (b01_imul_half_ulp Hp2 choice_sym).
Local Notation vseb_head3_dom := (vseb_head3_dom Hp2 Hp6 (choice := choice)).
Local Notation vecSumAux_run_cons := (vecSumAux_run_cons p choice).
Local Notation vecSum_split5 := (vecSum_split5 p choice).
Local Notation z3_bound := (z3_bound Hp2 Hp6 choice).
Local Notation z10m_bound := (z10m_bound Hp2 choice).
Local Notation z01m_bound := (z01m_bound Hp2 choice).
Local Notation x1y1_bound := (x1y1_bound (p := p)).
Local Notation x0y2_bound := (x0y2_bound Hp2).
Local Notation x2y0_bound := (x2y0_bound Hp2).
Local Notation tw_normP := (tw_normP p).
Local Notation isTW := (isTW p).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation vseb_star := (vseb_star Hp2 choice_sym).
Local Notation size_vecSum := (size_vecSum p choice).
Local Notation isTW_scale := (isTW_scale Hp2 choice).
Local Notation isTW_opp := (isTW_opp p).
Local Notation isTW_normalize := (isTW_normalize Hp2 choice).
Local Notation isTW_zero_lead := (isTW_zero_lead Hp2).
Local Notation isTW_TWR000 := (isTW_TWR000 p).
Local Notation err_mul_le_ulp := (err_mul_le_ulp Hp2 choice).
Local Notation u_abs_le_ulp := (u_abs_le_ulp Hp2).
Local Notation tw_norm_x1 := (tw_norm_x1 (p := p)).
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation vsebK := (vsebK p choice).
Local Notation round_scale := (round_scale p choice).
Local Notation round_opp := (round_opp p choice_sym).
Local Notation TwoProd_scale := (TwoProd_scale p choice).
Local Notation TwoProd_opp_l := (TwoProd_opp_l p choice_sym).
Local Notation TwoProd_opp_r := (TwoProd_opp_r p choice_sym).
Local Notation vecSum_scale := (vecSum_scale p choice).
Local Notation vecSum_opp := (vecSum_opp p choice_sym).
Local Notation vsebK_scale := (vsebK_scale p choice).
Local Notation vsebK_opp := (vsebK_opp p choice_sym).
Local Notation vsebAux_zeros := (vsebAux_zeros p choice).
Local Notation TwoProd00l := (TwoProd00l p choice).
Local Notation TwoProd00r := (TwoProd00r p choice).

Local Notation Fnonoverlap_vecSum_filter :=
  (Fnonoverlap_vecSum_filter Hp2 choice_sym).

Lemma s3_le_16max_g x1 y1 c z3 :
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  Rabs (dwh (TwoSum c z3)) <= 16 * Rmax (ulp x1) (ulp y1).
Proof.
move=> H.
have H0 : 0 <= Rmax (ulp x1) (ulp y1)
  by apply: (Rle_trans _ _ _ (ulp_ge_0 beta fexp x1)); apply: Rmax_l.
lra.
Qed.

Lemma s3_ulp_op_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let s3 := dwh (TwoSum c z3) in
  s3 <> 0 ->
  2 * ulp s3 <= ulp (RND (x1 * y0)) \/ 2 * ulp s3 <= ulp (RND (x0 * y1)).
Proof.
move=> Nx Ny H15 s3 Hs3n0.
have Hmax : Rabs s3 <= 16 * Rmax (ulp x1) (ulp y1) := s3_le_16max_g H15.
have Hulps3 : ulp s3 = pow (cexp s3) by apply: ulp_neq_0.
have V : Valid_exp fexp by apply: FLX_exp_valid.
have Mono : Monotone_exp fexp by apply: FLX_exp_monotone.
have [[Fx0 Fx1 Fx2] Hx0l Hx0h _ _] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0h _ _] := Ny.
have key : forall w z : R, format w -> w <> 0 -> 1 <= z ->
    Rabs s3 <= 16 * ulp w -> 2 * ulp s3 <= ulp (RND (w * z)).
  move=> w z Fw wn0 z1 Hs3w.
  have Hz1 : 1 <= Rabs z by rewrite Rabs_pos_eq; lra.
  have Hwz : Rabs w <= Rabs (RND (w * z)).
    apply: Rabs_round_le_l; first exact: generic_format_abs.
    by rewrite Rabs_mult; move: (Rabs_pos w) Hz1; nra.
  have Hwzn0 : RND (w * z) <> 0.
    by move=> H0; move: Hwz; rewrite H0 Rabs_R0; have := Rabs_pos_lt _ wn0; lra.
  have Hmagw : (mag beta w <= mag beta (RND (w * z)))%Z.
    rewrite -(mag_abs beta w) -(mag_abs beta (RND (w * z))).
    by apply: mag_le => //; apply: Rabs_pos_lt.
  have Hmags3 : (mag beta s3 <= mag beta w - p + 5)%Z.
    apply: mag_le_bpow => //.
    apply: (Rle_lt_trans _ _ _ Hs3w).
    rewrite (ulp_neq_0 _ _ _ wn0) /cexp /fexp /FLX_exp.
    have -> : 16 * pow (mag beta w - p) = pow (mag beta w - p + 4).
      by rewrite bpow_plus (_ : pow 4 = 16); [ring | rewrite /= /Z.pow_pos /=;
        lra].
    by apply: bpow_lt; lia.
  rewrite Hulps3 (ulp_neq_0 _ _ _ Hwzn0).
  have -> : 2 * pow (cexp s3) = pow (cexp s3 + 1)
    by rewrite bpow_plus (_ : pow 1 = 2); [ring | rewrite /= /Z.pow_pos /=;
      lra].
  apply: bpow_le.
  move: Hmags3 Hmagw; rewrite /cexp /fexp /FLX_exp; lia.
case: (Rle_dec (ulp y1) (ulp x1)) => [Hle|Hgt].
- left.
  have Hx1n0 : x1 <> 0.
    move=> H0; apply: Hs3n0.
    have Hy1u : ulp y1 = 0 by
      move: Hle; rewrite H0 ulp_FLX_0; have := ulp_ge_0 beta fexp y1; lra.
    move: Hmax; rewrite H0 ulp_FLX_0 Hy1u Rmax_left; last by lra.
    by rewrite Rmult_0_r => H; split_Rabs; lra.
  have Hmx : Rabs s3 <= 16 * ulp x1 by move: Hmax; rewrite (Rmax_left _ _ Hle).
  exact: (key x1 y0 Fx1 Hx1n0 Hy0l Hmx).
- right.
  have Hgt' : ulp x1 <= ulp y1 by lra.
  have Hy1n0 : y1 <> 0.
    move=> H0; apply: Hs3n0.
    have Hx1u : ulp x1 = 0 by
      move: Hgt'; rewrite H0 ulp_FLX_0; have := ulp_ge_0 beta fexp x1; lra.
    move: Hmax; rewrite H0 ulp_FLX_0 Hx1u Rmax_right; last by lra.
    by rewrite Rmult_0_r => H; split_Rabs; lra.
  have Hmx : Rabs s3 <= 16 * ulp y1 by move: Hmax; rewrite (Rmax_right _ _
    Hgt').
  rewrite (Rmult_comm x0 y1).
  exact: (key y1 x0 Fy1 Hy1n0 Hx0l Hmx).
Qed.

Lemma a_imul_ulp_s3_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let s3 := dwh (TwoSum c z3) in
  s3 <> 0 ->
  is_imul (RND (RND (x0 * y1) + RND (x1 * y0))) (ulp s3).
Proof.
move=> Nx Ny H15 s3 Hs3n0.
have Fz01p : format (RND (x0 * y1)) by apply: generic_format_round.
have Fz10p : format (RND (x1 * y0)) by apply: generic_format_round.
have Hulps3 : ulp s3 = pow (cexp s3) by apply: ulp_neq_0.
have Hulps3pos : 0 < ulp s3 by rewrite Hulps3; apply: bpow_gt_0.
have Hhalf : forall z : R, z <> 0 -> / 2 * ulp z = pow (cexp z - 1).
  move=> z zn0; rewrite ulp_neq_0 // (_ : (cexp z - 1 = (-1) + cexp z)%Z);
    last by lia.
  by rewrite bpow_plus (_ : pow (-1) = / 2); [ring | rewrite /= /Z.pow_pos /=;
    lra].
have Hcexp : forall z, z <> 0 -> 2 * ulp s3 <= ulp z ->
    (cexp s3 <= cexp z - 1)%Z.
  move=> z zn0 Hz; suff : (cexp s3 + 1 <= cexp z)%Z by lia.
  apply: (le_bpow beta); rewrite bpow_plus.
  have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
  by move: Hz; rewrite Hulps3 (ulp_neq_0 _ _ _ zn0); lra.
have [Hop | Hop] := s3_ulp_op_g Nx Ny H15 Hs3n0.
- have Hop' : 2 * ulp s3 <= ulp (RND (x1 * y0)) := Hop.
  have Hz10n0 : RND (x1 * y0) <> 0.
    by move=> H0; move: Hop' Hulps3pos; rewrite H0 ulp_FLX_0; lra.
  rewrite (Rplus_comm (RND (x0 * y1)) (RND (x1 * y0))) Hulps3.
  apply: (is_imul_pow_le (y1 := (cexp (RND (x1 * y0)) - 1)%Z));
    last exact: (Hcexp _ Hz10n0 Hop').
  rewrite -(Hhalf _ Hz10n0); exact: half_ulp_div_RN_add.
- have Hop' : 2 * ulp s3 <= ulp (RND (x0 * y1)) := Hop.
  have Hz01n0 : RND (x0 * y1) <> 0.
    by move=> H0; move: Hop' Hulps3pos; rewrite H0 ulp_FLX_0; lra.
  rewrite Hulps3.
  apply: (is_imul_pow_le (y1 := (cexp (RND (x0 * y1)) - 1)%Z));
    last exact: (Hcexp _ Hz01n0 Hop').
  rewrite -(Hhalf _ Hz01n0); exact: half_ulp_div_RN_add.
Qed.

Lemma inner_inputs_imul_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let s3 := dwh (TwoSum c z3) in
  s3 <> 0 ->
  [/\ is_imul (RND (x0 * y0)) (ulp s3),
      is_imul (nth 0 bb 0) (ulp s3) & is_imul (nth 0 bb 1) (ulp s3)].
Proof.
move=> Nx Ny Hc8 Hz3b H15 bb s3 Hs3n0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Hs3E : s3 = RND (c + z3) by rewrite /s3 TwoSum_hi.
have Hs3_20 : Rabs s3 <= 20 * (u * u) by rewrite Hs3E; apply: s3_bound.
have P32 : pow (5 - 2 * p) = 32 * (u * u).
  rewrite (_ : (5 - 2 * p = (4 - 2 * p) + 1)%Z); last by lia.
  rewrite bpow_plus pow_4m2p.
  have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
  ring.
have Hmagle : (mag beta s3 <= 5 - 2 * p)%Z.
  apply: mag_le_bpow => //; rewrite P32; move: Hs3_20 Hu0; nra.
have Hgle : (cexp s3 <= 5 - 3 * p)%Z by rewrite /cexp /FLX_exp; lia.
have Hulps3 : ulp s3 = pow (cexp s3) by apply: ulp_neq_0.
have Fz00p : format (RND (x0 * y0)) by apply: generic_format_round.
have Hz00p1 : 1 <= RND (x0 * y0) by apply: (z00p_lb Nx Ny).
have Hmagge : (1 <= mag beta (RND (x0 * y0)))%Z.
  apply: mag_ge_bpow; rewrite pow0E; move: Hz00p1; split_Rabs; lra.
have Hz00p : is_imul (RND (x0 * y0)) (ulp s3).
  rewrite Hulps3.
  apply: (is_imul_pow_le (y1 := cexp (RND (x0 * y0)))); last first.
    have Ecx1 : (cexp s3 = mag beta s3 - p)%Z by rewrite /cexp /fexp /FLX_exp.
    have Ecx2 : (cexp (RND (x0 * y0)) = mag beta (RND (x0 * y0)) - p)%Z
      by rewrite /cexp /fexp /FLX_exp.
    rewrite Ecx1 Ecx2; lia.
  exact: (format_imul_cexp Fz00p).
have Hz00m : is_imul (RND (x0 * y0 - RND (x0 * y0))) (ulp s3).
  rewrite Hulps3 round_generic; last first.
    rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
      ring.
    by apply: generic_format_opp; exact: format_err_mul.
  apply: (is_imul_pow_le (y1 := (2 - 2 * p)%Z)); last by lia.
  rewrite pow_2m2p; exact: (z00m_imul Nx Ny).
have Fz00mf : format (RND (x0 * y0 - RND (x0 * y0))) by apply:
  generic_format_round.
have Fz01pf : format (RND (x0 * y1)) by apply: generic_format_round.
have Fz10pf : format (RND (x1 * y0)) by apply: generic_format_round.
have Hbbeq : bb = [:: RND (RND (x0 * y0 - RND (x0 * y0))
                         + RND (RND (x0 * y1) + RND (x1 * y0)));
    RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))
      - RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0)));
    RND (x0 * y1) + RND (x1 * y0) - RND (RND (x0 * y1) + RND (x1 * y0))]
  by rewrite /bb (vecSum3 Fz00mf Fz01pf Fz10pf).
have Ha := a_imul_ulp_s3_g Nx Ny H15 Hs3n0.
move: Hz00m Ha; rewrite Hulps3 => Hz00m Ha.
split.
- by move: Hz00p; rewrite Hulps3.
- rewrite Hbbeq /=.
  by apply: is_imul_pow_round; apply: is_imul_add; [exact: Hz00m | exact: Ha].
- rewrite Hbbeq /=.
  apply: is_imul_minus.
    by apply: is_imul_add; [exact: Hz00m | exact: Ha].
  by apply: is_imul_pow_round; apply: is_imul_add; [exact: Hz00m | exact: Ha].
Qed.

Lemma e4_dominates_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  format c -> format z3 ->
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  forall x,
    x \in vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        dwh (TwoSum c z3) ] ->
    x <> 0 ->
    Rabs (dwl (TwoSum c z3))
      <= / 2 * uls x.
Proof.
move=> Nx Ny Fc Fz3 Hc8 Hz3b H15 bb x xI xn0.
have [Fs3 Fe4] := @format_TwoSum p Hp2 choice c z3 Fc Fz3.
case: (Req_dec (dwl (TwoSum c z3)) 0) => [He4|He4].
  by rewrite He4 Rabs_R0; apply: Rmult_le_pos; [lra | apply: uls_ge_0].
have Hs3n0 : dwh (TwoSum c z3) <> 0.
  move=> Hs3; apply: He4.
  have Hhi := TwoSum_hi p choice c z3.
  have Hsum := TwoSum_correct_loc Hp2 choice_sym Fc Fz3.
  have Hd : RND (dwl (TwoSum c z3)) = 0.
    have Hrn0 : RND (c + z3) = 0 by rewrite -Hhi.
    have HsumF : dwh (TwoSum c z3) + dwl (TwoSum c z3) = c + z3 by exact: Hsum.
    have Hdwl : dwl (TwoSum c z3) = c + z3 by move: HsumF; rewrite Hs3; lra.
    by rewrite Hdwl.
  have Fe4' : format (dwl (TwoSum c z3)) by exact: Fe4.
  by rewrite -(round_generic _ _ _ _ Fe4').
have [Hz Hb0 Hb1] := inner_inputs_imul_g Nx Ny Hc8 Hz3b H15 Hs3n0.
have Fs3n0 := ulp_neq_0 beta fexp _ Hs3n0.
have Hf4 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; dwh (TwoSum c z3)],
    forall z, format z}.
  move=> z; rewrite !inE => /or4P[/eqP->|/eqP->|/eqP->|/eqP->];
    try apply: generic_format_round; exact: Fs3.
have Hm4 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; dwh (TwoSum c z3)],
    forall z, is_imul z (pow (cexp (dwh (TwoSum c z3))))}.
  move=> z; rewrite !inE => /or4P[/eqP->|/eqP->|/eqP->|/eqP->].
  - by rewrite -Fs3n0; exact: Hz.
  - by rewrite -Fs3n0; exact: Hb0.
  - by rewrite -Fs3n0; exact: Hb1.
  - exact: (format_imul_cexp Fs3).
have Himx : is_imul x (ulp (dwh (TwoSum c z3))).
  rewrite Fs3n0.
  exact: (@vecSum_imul_forward p Hp2 choice choice_sym _ _ Hf4 Hm4 x xI).
have Fx : format x by apply: (@format_vecSum p Hp2 choice _ Hf4 x xI).
have Hulsx : ulp (dwh (TwoSum c z3)) <= uls x.
  rewrite Fs3n0; apply: is_imul_uls_ge => //.
  by move: Himx; rewrite Fs3n0.
have He4le := e4_le_half_ulp Fc Fz3.
lra.
Qed.

Lemma s3_div_facts_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let s3 := dwh (TwoSum c z3) in
  s3 <> 0 ->
  exists w : R, [/\ w <> 0,
     4 * ulp s3 <= ulp w,
     ufp s3 <= 8 * ulp w,
     is_imul (nth 0 bb 0) (/ 2 * ulp w) & is_imul (nth 0 bb 1) (/ 2 * ulp w)].
Proof.
move=> Nx Ny H15 bb s3 Hs3n0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hmax : Rabs s3 <= 15 * Rmax (ulp x1) (ulp y1) := H15.
have magfacts : forall w : R, w <> 0 -> Rabs s3 <= 15 * ulp w ->
    4 * ulp s3 <= ulp w /\ ufp s3 <= 8 * ulp w.
  move=> w wn0 Hw.
  have Hmg : (mag beta s3 <= mag beta w - p + 4)%Z
    by apply: (mag_le_of_le_15ulp wn0 Hs3n0 Hw).
  have Hcs3 : ulp s3 = pow (mag beta s3 - p)
    by rewrite ulp_neq_0 // /cexp /fexp /FLX_exp.
  have Hcw : ulp w = pow (mag beta w - p)
    by rewrite ulp_neq_0 // /cexp /fexp /FLX_exp.
  split.
  - rewrite Hcs3 Hcw.
    have -> : 4 * pow (mag beta s3 - p) = pow (mag beta s3 - p + 2)
      by rewrite bpow_plus (_ : pow 2 = 4); [ring | rewrite /= /Z.pow_pos /=;
        lra].
    by apply: bpow_le; lia.
  rewrite /ufp Hcw.
  have -> : 8 * pow (mag beta w - p) = pow (mag beta w - p + 3)
    by rewrite bpow_plus (_ : pow 3 = 8); [ring | rewrite /= /Z.pow_pos /=;
      lra].
  by apply: bpow_le; lia.
case: (Rle_dec (ulp y1) (ulp x1)) => [Hle|Hgt].
- have Hx1n0 : x1 <> 0.
    move=> H0; apply: Hs3n0.
    have Hy1u : ulp y1 = 0
      by move: Hle; rewrite H0 ulp_FLX_0; have := ulp_ge_0 beta fexp y1; lra.
    move: Hmax; rewrite H0 ulp_FLX_0 Hy1u Rmax_left; last by lra.
    by rewrite Rmult_0_r => H; split_Rabs; lra.
  have Hmx : Rabs s3 <= 15 * ulp x1 by move: Hmax; rewrite (Rmax_left _ _ Hle).
  have [H4 Hufp] := magfacts x1 Hx1n0 Hmx.
  have [Hb0 Hb1] := b01_imul_half_ulp Nx Ny (or_introl (erefl x1)) Hx1n0.
  by exists x1; split.
have Hgt' : ulp x1 <= ulp y1 by lra.
have Hy1n0 : y1 <> 0.
  move=> H0; apply: Hs3n0.
  have Hx1u : ulp x1 = 0
    by move: Hgt'; rewrite H0 ulp_FLX_0; have := ulp_ge_0 beta fexp x1; lra.
  move: Hmax; rewrite H0 ulp_FLX_0 Hx1u Rmax_right; last by lra.
  by rewrite Rmult_0_r => H; split_Rabs; lra.
have Hmy : Rabs s3 <= 15 * ulp y1 by move: Hmax; rewrite (Rmax_right _ _ Hgt').
have [H4 Hufp] := magfacts y1 Hy1n0 Hmy.
have [Hb0 Hb1] := b01_imul_half_ulp Nx Ny (or_intror (erefl y1)) Hy1n0.
by exists y1; split.
Qed.

Lemma inner_head_Fnonoverlap_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  format c -> format z3 ->
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Fnonoverlap (vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        dwh (TwoSum c z3)]).
Proof.
move=> Nx Ny Fc Fz3 Hc8 Hz3b H15 bb.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
set z00p := RND (x0 * y0).
set b0 := nth 0 bb 0.
set b1 := nth 0 bb 1.
set s3 := dwh (TwoSum c z3).
have [Fs3 Fe4] := @format_TwoSum p Hp2 choice c z3 Fc Fz3.
have Fz00p : format z00p by apply: generic_format_round.
have Fbb : {in bb, forall z : R, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fb0 : format b0 by apply: Fbb; rewrite /b0 /bb mem_nth // size_vecSum.
have Fb1 : format b1 by apply: Fbb; rewrite /b1 /bb mem_nth // size_vecSum.
have Fs3' : format s3 by rewrite /s3 (TwoSum_hi p choice).
have Hz00p1 : 1 <= z00p by apply: (z00p_lb Nx Ny).
have z00pn0 : z00p <> 0 by lra.
apply: Fnonoverlap_vecSum_filter.
  by move=> z; rewrite !inE => /or4P[/eqP->|/eqP->|/eqP->|/eqP->].
apply: (@vecSum_Fnonoverlap_sep).
exact: Hp2.
exact: choice_sym.
have Hufp : forall x : R, x <> 0 -> ufp x = pow (p - 1) * ulp x.
  move=> x xn0; rewrite /ufp ulp_neq_0 // /cexp /fexp /FLX_exp -bpow_plus.
  by congr bpow; lia.
have Hhw : forall x : R, x <> 0 -> / 2 * ulp x = pow (cexp x - 1).
  move=> x xn0; rewrite ulp_neq_0 // (_ : / 2 = pow (-1));
    last by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -bpow_plus; congr bpow; lia.
have Hufpz00p : 1 <= ufp z00p.
  rewrite /ufp -(pow0E beta); apply: bpow_le.
  suff : (1 <= mag beta z00p)%Z by lia.
  by apply: mag_ge_bpow; rewrite pow0E Rabs_pos_eq; lra.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1o Hx2o] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r Hy1o Hy2o] := Ny.
have Hs3_20 : Rabs s3 <= 20 * (u * u)
  by rewrite /s3 (TwoSum_hi p choice); apply: (s3_bound Hc8 Hz3b).
have RNrel : forall t : R, Rabs (RND t) <= (1 + u) * Rabs t.
  move=> t; have Ht := relative_error_le beta Hp2 choice t.
  have H2 : Rabs (RND t) <= Rabs t + Rabs (RND t - t)
    by have := Rabs_triang t (RND t - t);
       rewrite (_ : t + (RND t - t) = RND t); [lra | ring].
  have := Rabs_pos t; nra.
have Hz01pb := z01p_bound Nx Ny.
have Hz10pb := z10p_bound Nx Ny.
have Hz00mb : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic; first by apply: (z00m_bound Nx Ny).
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hav9 : Rabs (RND (RND (x0 * y1) + RND (x1 * y0))) <= 9 * u.
  apply: (Rle_trans _ _ _ (RNrel _)).
  have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); nra.
have Hb0e : b0 = RND (RND (x0 * y0 - RND (x0 * y0))
                      + RND (RND (x0 * y1) + RND (x1 * y0))).
  by rewrite /b0 /bb (vecSum3 (generic_format_round _ _ _ _)
    (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)).
have Hb0lt1 : Rabs b0 < 1.
  rewrite Hb0e; apply: (Rle_lt_trans _ _ _ (RNrel _)).
  set A := RND (x0 * y0 - RND (x0 * y0)).
  set B := RND (RND (x0 * y1) + RND (x1 * y0)).
  have Ht := Rabs_triang A B.
  have HA : Rabs A <= 2 * u by exact: Hz00mb.
  have HB : Rabs B <= 9 * u by exact: Hav9.
  have Hr : Rabs (A + B) <= 11 * u by lra.
  clear -Hr Hu0 Hu64; have Hrp := Rabs_pos (A + B); nra.
have Hz00mF : format (RND (x0 * y0 - RND (x0 * y0)))
  by apply: generic_format_round.
have HavF : format (RND (RND (x0 * y1) + RND (x1 * y0)))
  by apply: generic_format_round.
have Hb1e' : b1 = RND (x0 * y0 - RND (x0 * y0))
      + RND (RND (x0 * y1) + RND (x1 * y0))
    - RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))).
  by rewrite /b1 /bb (vecSum3 (generic_format_round _ _ _ _)
    (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)).
have Hb1half : Rabs b1 <= / 2 * ulp b0.
  move: (@magnitude_TwoSum p Hp2 choice choice_sym _ _ Hz00mF HavF)
        (TwoSum_correct_loc Hp2 choice_sym Hz00mF HavF)
        (TwoSum_hi p choice (RND (x0 * y0 - RND (x0 * y0)))
          (RND (RND (x0 * y1) + RND (x1 * y0)))).
  case: (TwoSum _ _) => sh sl; rewrite /magnitudeDWR /dwh /dwl => Hmag Hsum Hhi.
  have Hb0sh : b0 = sh by rewrite Hb0e -Hhi.
  have Hb1sl : b1 = sl by rewrite Hb1e' -Hhi; lra.
  rewrite Hb0sh Hb1sl; move: Hmag; lra.
have Hulpufp : forall x : R, x <> 0 -> ulp x <= ufp x.
  by move=> x xn0; rewrite /ufp ulp_neq_0 // /cexp /fexp /FLX_exp;
    apply: bpow_le; lia.
have HC1 : b0 <> 0 -> 2 * ufp b0 <= ufp z00p.
  move=> b0n0.
  have Hmb : (mag beta b0 <= 0)%Z by apply: mag_le_bpow => //; rewrite pow0E.
  have Hub : ufp b0 <= / 2.
    rewrite /ufp (_ : / 2 = pow (-1)); last by rewrite /= /Z.pow_pos /=; lra.
    by apply: bpow_le; lia.
  lra.
have HC2 : b0 <> 0 -> b1 <> 0 -> 2 * ufp b1 <= ufp b0.
  move=> b0n0 b1n0.
  have Hub1 : ufp b1 <= / 2 * ulp b0
    by apply: (Rle_trans _ _ _ (ufp_le_abs b1n0)); exact: Hb1half.
  have := Hulpufp b0 b0n0; lra.
have HC3 : s3 <> 0 -> 2 * ufp s3 <= ufp z00p.
  move=> s3n0.
  have Hub : ufp s3 <= 20 * (u * u)
    by apply: (Rle_trans _ _ _ (ufp_le_abs s3n0)); exact: Hs3_20.
  have H40 : 40 * (u * u) <= 1 by clear -Hu0 Hu64; nra.
  lra.
have HM4 : s3 <> 0 -> 4 * ufp s3 <= ufp z00p.
  move=> s3n0.
  have Hub : ufp s3 <= 20 * (u * u)
    by apply: (Rle_trans _ _ _ (ufp_le_abs s3n0)); exact: Hs3_20.
  have H80 : 80 * (u * u) <= 1 by clear -Hu0 Hu64; nra.
  lra.
have Hs3on : s3 <> 0 ->
  [/\ (b0 <> 0 -> ufp s3 <= pow (p - 2) * uls b0),
      (b1 <> 0 -> ufp s3 <= pow (p - 2) * uls b1) &
      (b0 <> 0 -> b1 <> 0 -> 4 * ufp s3 <= ufp b0)].
  move=> s3n0.
  have [w [wn0 H4w Hufpw Hb0im Hb1im]] := s3_div_facts_g Nx Ny H15 s3n0.
  have Hwpow : / 2 * ulp w = pow (cexp w - 1) := Hhw w wn0.
  have Hp1 : pow (p - 1) = 2 * pow (p - 2).
    rewrite (_ : (p - 1 = (p - 2) + 1)%Z); last by lia.
    by rewrite bpow_plus (_ : pow 1 = 2); [ring | rewrite /= /Z.pow_pos /=;
      lra].
  have Hufps3 : ufp s3 = pow (p - 1) * ulp s3 := Hufp s3 s3n0.
  have Hp20 : 0 <= pow (p - 2) by apply: bpow_ge_0.
  split.
  - move=> b0n0.
    have Hulsb0 : / 2 * ulp w <= uls b0.
      rewrite Hwpow; apply: (is_imul_uls_ge Fb0 b0n0).
      by move: Hb0im; rewrite Hwpow.
    have H4s : 4 * ulp s3 <= ulp w by exact: H4w.
    rewrite Hufps3 Hp1; clear -H4s Hulsb0 Hp20; nra.
  - move=> b1n0.
    have Hulsb1 : / 2 * ulp w <= uls b1.
      rewrite Hwpow; apply: (is_imul_uls_ge Fb1 b1n0).
      by move: Hb1im; rewrite Hwpow.
    have H4s : 4 * ulp s3 <= ulp w by exact: H4w.
    rewrite Hufps3 Hp1; clear -H4s Hulsb1 Hp20; nra.
  move=> b0n0 b1n0.
  have Hufps38 : ufp s3 <= 8 * ulp w by exact: Hufpw.
  have Hufpb1lo : / 2 * ulp w <= ufp b1.
    have Hb1ge : / 2 * ulp w <= Rabs b1.
      rewrite Hwpow; apply: (is_imul_pow_le_abs _ b1n0).
      by move: Hb1im; rewrite Hwpow.
    have Hmagb1 : (cexp w <= mag beta b1)%Z.
      by apply: mag_ge_bpow; rewrite -Hwpow.
    rewrite /ufp Hwpow; apply: bpow_le; move: Hmagb1; lia.
  have Hufpb1hi : ufp b1 <= / 2 * ulp b0
    by apply: (Rle_trans _ _ _ (ufp_le_abs b1n0)); exact: Hb1half.
  have H32 : 32 * ulp b0 <= ufp b0.
    rewrite /ufp ulp_neq_0 // /cexp /fexp /FLX_exp.
    have -> : 32 * pow (mag beta b0 - p) = pow (mag beta b0 - p + 5)
      by rewrite bpow_plus (_ : pow 5 = 32); [ring | rewrite /= /Z.pow_pos /=;
        lra].
    by apply: bpow_le; lia.
  have Hulpw0 : 0 <= ulp w by apply: ulp_ge_0.
  clear -Hufps38 Hufpb1lo Hufpb1hi H32 Hulpw0; lra.
have Hb01 : b0 = 0 -> b1 = 0.
  move=> b00; move: Hb1half; rewrite b00 ulp_FLX_0 Rmult_0_r => H.
  clear -H; apply: Rabs_eq_R0; have := Rabs_pos b1; lra.
have Cor1_empty : forall l : seq R, {in l, forall z : R, format z} ->
    (forall i, (i < size l)%N -> nth 0 l i <> 0) ->
    (forall i, (i.+1 < size l)%N -> 2 * ufp (nth 0 l i.+1) <= ufp (nth 0 l i))
      ->
    Cor1_hyp p l.
  move=> l Fl Hnz Hdec; split; [exact: Fl | exact: Hnz |].
  exists (fun=> false); split => // i Hi _.
  exact: Hdec.
have Cor1_I1 : forall a b d : R,
    format a -> format b -> format d -> a <> 0 -> b <> 0 -> d <> 0 ->
    2 * ufp b <= ufp a -> ufp d <= pow (p - 2) * uls b -> 4 * ufp d <= ufp a ->
    Cor1_hyp p [:: a; b; d].
  move=> a b d Fa Fb Fd an0 bn0 dn0 H1 H2 H3; split.
  - by move=> z; rewrite !inE => /or3P[/eqP->|/eqP->|/eqP->].
  - by move=> [|[|[|i]]] //= _.
  exists (fun i => i == 1%N); split.
  - by move=> [|[|i]] //= _.
  - by move=> [|[|i]].
  - by move=> [|[|[|i]]] //= _ _.
  - by move=> [|[|i]] //= _.
  by move=> [|[|i]] //= _.
have Cor1_I2 : forall a b cc d : R,
    format a -> format b -> format cc -> format d ->
    a <> 0 -> b <> 0 -> cc <> 0 -> d <> 0 ->
    2 * ufp b <= ufp a -> 2 * ufp cc <= ufp b ->
    ufp d <= pow (p - 2) * uls cc -> 4 * ufp d <= ufp b ->
    Cor1_hyp p [:: a; b; cc; d].
  move=> a b cc d Fa Fb Fcc Fd an0 bn0 ccn0 dn0 H1 H2 H3 H4; split.
  - by move=> z; rewrite !inE => /or4P[/eqP->|/eqP->|/eqP->|/eqP->].
  - by move=> [|[|[|[|i]]]] //= _.
  exists (fun i => i == 2%N); split.
  - by move=> [|[|[|i]]] //= _.
  - by move=> [|[|[|i]]].
  - by move=> [|[|[|[|i]]]] //= _ _.
  - by move=> [|[|[|i]]] //= _.
  by move=> [|[|[|i]]] //= _.
have Hfz : [seq x <- [:: z00p; b0; b1; s3] | x != 0 :> R]
    = z00p :: [seq x <- [:: b0; b1; s3] | x != 0 :> R]
  by rewrite /= ifT //; apply/eqP.
rewrite Hfz.
case: (Req_dec b0 0) => [b00|b0n0].
- have b10 := Hb01 b00.
  have -> : [seq x <- [:: b0; b1; s3] | x != 0 :> R]
      = [seq x <- [:: s3] | x != 0 :> R] by rewrite /= b00 b10 !eqxx.
  case: (Req_dec s3 0) => [s30|s3n0].
  + rewrite /= s30 eqxx /=.
    apply: Cor1_empty.
    * by move=> z; rewrite inE => /eqP->.
    * by move=> [|i] //= _.
    * by move=> [|i] //=.
  + rewrite /= ifT; last by apply/eqP.
    apply: Cor1_empty.
    * by move=> z; rewrite !inE => /orP[/eqP->|/eqP->].
    * by move=> [|[|i]] //= _.
    * by move=> [|i] //= _; exact: HC3 s3n0.
have -> : [seq x <- [:: b0; b1; s3] | x != 0 :> R]
    = b0 :: [seq x <- [:: b1; s3] | x != 0 :> R]
  by rewrite /= ifT //; apply/eqP.
case: (Req_dec b1 0) => [b10|b1n0].
- have -> : [seq x <- [:: b1; s3] | x != 0 :> R] = [seq x <- [:: s3] | x != 0 :>
  R]
    by rewrite /= b10 eqxx.
  case: (Req_dec s3 0) => [s30|s3n0].
  + rewrite /= s30 eqxx /=.
    apply: Cor1_empty.
    * by move=> z; rewrite !inE => /orP[/eqP->|/eqP->].
    * by move=> [|[|i]] //= _.
    * by move=> [|i] //= _; exact: HC1 b0n0.
  + rewrite /= ifT; last by apply/eqP.
    apply: Cor1_I1 => //; [exact: HC1 b0n0 | | exact: HM4 s3n0].
    by have [M3 _ _] := Hs3on s3n0; apply: M3.
have -> : [seq x <- [:: b1; s3] | x != 0 :> R] = b1 :: [seq x <- [:: s3] | x !=
  0 :> R]
  by rewrite /= ifT //; apply/eqP.
case: (Req_dec s3 0) => [s30|s3n0].
- rewrite /= s30 eqxx /=.
  apply: Cor1_empty.
  + by move=> z; rewrite !inE => /or3P[/eqP->|/eqP->|/eqP->].
  + by move=> [|[|[|i]]] //= _.
  + by move=> [|[|i]] //= _; [exact: HC1 b0n0 | exact: HC2 b0n0 b1n0].
- rewrite /= ifT; last by apply/eqP.
  apply: Cor1_I2 => //;
    [exact: HC1 b0n0 | exact: HC2 b0n0 b1n0
    | by have [_ M5 _] := Hs3on s3n0; apply: M5
    | by have [_ _ M6] := Hs3on s3n0; apply: M6].
Qed.

Lemma inner_Fnonoverlap_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  format c -> format z3 ->
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (dwh (TwoSum c z3)) <= 15 * Rmax (ulp x1) (ulp y1) ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Fnonoverlap (vecSum
    [:: RND (x0 * y0);
        nth 0 bb 0;
        nth 0 bb 1;
        c;
        z3]).
Proof.
move=> Nx Ny Fc Fz3 Hc8 Hz3b H15 bb.
rewrite (vecSum_split5 (RND (x0 * y0)) (nth 0 bb 0) (nth 0 bb 1) c z3).
rewrite cats1.
apply: Fnonoverlap_rcons.
  by apply: (inner_head_Fnonoverlap_g Nx Ny Fc Fz3 Hc8 Hz3b H15).
by apply: (e4_dominates_g Nx Ny Fc Fz3 Hc8 Hz3b H15).
Qed.

Lemma vseb_head3_e1zero_g x0 x1 x2 y0 y1 y2 c z3 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  format c -> format z3 ->
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0);
        nth 0 bb 0;
        nth 0 bb 1;
        c;
        z3] in
  nth 0 e 1 = 0 ->
  nth 0 (vseb e) 0 = nth 0 e 0 /\
  nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
  nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
Proof.
move=> Nx Ny Fc Fz3 Hc8 Hz3b bb e He1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have Hp4 : (4 <= p)%Z by lia.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Hz00m : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic; first by apply: (z00m_bound Nx Ny).
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01p := z01p_bound Nx Ny.
have Hz10p := z10p_bound Nx Ny.
have Fku : forall k : Z, (Z.abs k < 2 ^ p)%Z -> format (IZR k * u)
  by move=> k Hk; rewrite u_pow; apply: format_mult_pow.
have F8u : format (8 * u) by rewrite -pow_3mp; apply: format_pow.
have Hb0 : Rabs (nth 0 bb 0) <= 10 * u.
  have Heq : nth 0 bb 0
      = RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0))).
    by rewrite /bb vecSum_nth0 vecSumAux_run_cons; congr RND; congr (_ + _).
  rewrite Heq.
  have F10 : format (10 * u) by apply: Fku; have := two_p_ge_64; simpl; lia.
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
have Hr3 : Rabs (RND (c
    + z3)) <= 20 * (u * u)
  by apply: s3_bound.
have Hr3' : Rabs ((vecSumAux [:: c; z3]).2) <= 20 * (u * u).
  by rewrite vecSumAux_run_cons.
have Hr2 : Rabs ((vecSumAux [:: nth 0 bb 1; c; z3]).2) <= 32 * (u * u).
  rewrite vecSumAux_run_cons.
  have F32 : format (32 * (u * u))
    by apply: (format_imul_u2 (k := 32)); have := two_p_ge_64; lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 1) ((vecSumAux [:: c; z3]).2).
  move: Hb1 Hr3' Ht; nra.
have Hr1 : Rabs ((vecSumAux [:: nth 0 bb 0; nth 0 bb 1; c; z3]).2) <= 11 * u.
  rewrite vecSumAux_run_cons.
  have F11 : format (11 * u) by apply: Fku; have := two_p_ge_64; simpl; lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 0) ((vecSumAux [:: nth 0 bb 1; c; z3]).2).
  move: Hb0 Hr2 Ht Hu0 Hu64; nra.
have He0 : 3 / 4 <= nth 0 e 0.
  rewrite /e vecSum_nth0 vecSumAux_run_cons.
  have F34 : format (3 / 4).
    have -> : 3 / 4 = IZR 3 * pow (-2) by rewrite /= /Z.pow_pos /=; lra.
    by apply: format_mult_pow; have := two_p_ge_64; simpl; lia.
  apply: round_le_l => //.
  have Hz00p1 : 1 <= RND (x0 * y0) by apply: (z00p_lb Nx Ny).
  set r1 := (vecSumAux [:: nth 0 bb 0; nth 0 bb 1; c; z3]).2.
  set z := RND (x0 * y0).
  move: Hr1 Hz00p1; rewrite -/r1 -/z => Hr1 Hz00p1.
  have Hr1c := Rabs_le_inv _ _ Hr1.
  lra.
have HL5f : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3],
    forall z, format z}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
    first [exact: generic_format_round | exact: Fnthbb | assumption].
have Ee : e = vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3]
  by rewrite /e.
have Hstep : forall k : nat, (k.+1 < 5)%N ->
    Rabs ((vecSumAux
      (drop k [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3])).2) < 16 * u
        ->
    2 * Rabs (nth 0 e k.+1) < u.
  move=> k Hk Hrk.
  have Hle := @vecSum_err_le_half_ulp_run p Hp2 choice choice_sym
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3] k Hk HL5f.
  rewrite -Ee in Hle.
  have Hw := Hulp16 _ Hrk.
  move: Hle Hw.
  set n := Rabs (nth 0 e k.+1).
  set w := ulp _.
  move=> Hle Hw.
  move: Hle Hw Hu64 Hu0; nra.
have Hdom : forall i, (0 < i)%N -> (i < 5)%N -> 2 * Rabs (nth 0 e i) < u.
  move=> i Hi0 Hi5.
  case: i Hi0 Hi5 => [|[|[|[|[|i]]]]] // _ _.
  - by rewrite He1 Rabs_R0; nra.
  - apply: (Hstep 1%N) => //.
    have -> : drop 1 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3]
      = [:: nth 0 bb 0; nth 0 bb 1; c; z3] by [].
    by move: Hr1 Hu0; lra.
  - apply: (Hstep 2%N) => //.
    have -> : drop 2 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3]
      = [:: nth 0 bb 1; c; z3] by [].
    by move: Hr2 Hu0 Hu64; nra.
  - apply: (Hstep 3%N) => //.
    have -> : drop 3 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3]
      = [:: c; z3] by [].
    by move: Hr3' Hu0 Hu64; nra.
have Hsz5 : size e = 5%N by rewrite /e size_vecSum.
have Fe : {in e, forall z, format z}
  by rewrite Ee; apply: (@format_vecSum p Hp2 choice); exact: HL5f.
have He0e : e = nth 0 e 0 :: behead e by case: (e) Hsz5 => [|a l].
have Hbeh_dom : forall x, x \in behead e -> 2 * Rabs x < u.
  move=> x xI.
  have [i Hi Hnth] : exists2 i, (i < size (behead e))%N & nth 0 (behead e) i = x
    by apply/(nthP 0).
  have Hnth' : nth 0 (behead e) i = nth 0 e i.+1 by rewrite He0e /=.
  rewrite -Hnth Hnth'.
  have Hi5 : (i.+1 < 5)%N by move: Hi; rewrite size_behead Hsz5.
  case: i Hi Hnth Hnth' Hi5 => [|i'] Hi Hnth Hnth' Hi5.
    by rewrite He1 Rabs_R0; have := u_gt_0; move=> H; nra.
  by apply: Hdom.
by apply: vseb_head3_dom => //; rewrite Hsz5.
Qed.



(* The fifteen does not move: the two new roundings cost `(1 + u)' apiece,  *)
(* and the paper's constant comes out at `14.74' where it came out at `14'. *)
Lemma s3n_le_15max x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (dwh (TwoSum (RND (nth 0 (vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)]) 2
      + RND (x1 * y1)))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
               + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0))))))
    <= 15 * Rmax (ulp x1) (ulp y1).
Proof.
move=> Nx Ny.
rewrite (TwoSum_hi p choice).
set z00m := RND (x0 * y0 - RND (x0 * y0)).
set z01p := RND (x0 * y1).
set z10p := RND (x1 * y0).
set b2 := nth 0 (vecSum [:: z00m; z01p; z10p]) 2.
set c := RND (b2 + RND (x1 * y1)).
set z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
               + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0))).
set M := Rmax (ulp x1) (ulp y1).
have Hu0 : 0 < u by apply: u_gt_0.
have HMx : ulp x1 <= M by apply: Rmax_l.
have HMy : ulp y1 <= M by apply: Rmax_r.
have HM0 : 0 <= M by apply: (Rle_trans _ _ _ (ulp_ge_0 beta fexp x1)).
have Hule : u <= / 64.
  rewrite u_pow; have -> : (/64 = pow (-6)) by rewrite /= /Z.pow_pos /=; lra.
  by apply: bpow_le; lia.
have RNrel : forall t : R, Rabs (RND t) <= (1 + u) * Rabs t.
  move=> t; have Ht := relative_error_le beta Hp2 choice t.
  have H2 : Rabs (RND t) <= Rabs t + Rabs (RND t - t).
    by have := Rabs_triang t (RND t - t);
       rewrite (_ : t + (RND t - t) = RND t); [lra | ring].
  have := Rabs_pos t; nra.
have [[Fx0 Fx1 Fx2] Hx0l Hx0h _ Hx2opt] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0h _ Hy2opt] := Ny.
have Hx0b : Rabs x0 <= 2 by rewrite Rabs_pos_eq; lra.
have Hy0b : Rabs y0 <= 2 by rewrite Rabs_pos_eq; lra.
have Hx2b : Rabs x2 <= M.
  have Hle : Rabs x2 <= ulp x1
    by case: Hx2opt => [->|H]; [rewrite Rabs_R0; apply: ulp_ge_0 | lra].
  lra.
have Hy2b : Rabs y2 <= M.
  have Hle : Rabs y2 <= ulp y1
    by case: Hy2opt => [->|H]; [rewrite Rabs_R0; apply: ulp_ge_0 | lra].
  lra.
have Ee1 : RND (x1 * y0 - RND (x1 * y0)) = x1 * y0 - RND (x1 * y0).
  apply: round_generic.
  rewrite (_ : x1 * y0 - RND (x1 * y0) = - (RND (x1 * y0) - x1 * y0)); last
    ring.
  by apply: generic_format_opp; apply: format_err_mul.
have HT1 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * M.
  rewrite Ee1.
  by apply: (Rle_trans _ _ _ (err_mul_le_ulp x1 Hy0b)); lra.
have Ee3 : RND (x0 * y1 - RND (x0 * y1)) = x0 * y1 - RND (x0 * y1).
  apply: round_generic.
  rewrite (_ : x0 * y1 - RND (x0 * y1) = - (RND (x0 * y1) - x0 * y1)); last
    ring.
  by apply: generic_format_opp; apply: format_err_mul.
have HT3 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * M.
  rewrite Ee3 (Rmult_comm x0 y1).
  by apply: (Rle_trans _ _ _ (err_mul_le_ulp y1 Hx0b)); lra.
have HT2 : Rabs (x0 * y2) <= 2 * M.
  rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
  have := Rabs_pos y2; nra.
have HT4 : Rabs (x2 * y0) <= 2 * M.
  rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
  have := Rabs_pos x2; nra.
have HT5 : Rabs (x1 * y1) <= 2 * M.
  have Hy1 := tw_norm_x1 Ny.
  have Hux1 := u_abs_le_ulp x1.
  rewrite Rabs_mult.
  have Hx1p := Rabs_pos x1.
  have Hstep : Rabs x1 * Rabs y1 <= Rabs x1 * (2 * u).
    by apply: Rmult_le_compat_l; [exact: Hx1p | lra].
  nra.
have Fz00m : format z00m by apply: generic_format_round.
have Fz01p : format z01p by apply: generic_format_round.
have Fz10p : format z10p by apply: generic_format_round.
have Hb2e : b2 = z01p + z10p - RND (z01p + z10p).
  by rewrite /b2 (vecSum3 Fz00m Fz01p Fz10p).
have Hz01 : Rabs z01p <= 2 * (1 + u) * Rabs y1.
  rewrite /z01p.
  apply: (Rle_trans _ _ _ (RNrel _)).
  rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
  rewrite (_ : 2 * (1 + u) * Rabs y1 = (1 + u) * (2 * Rabs y1)); last ring.
  apply: Rmult_le_compat_l; first lra.
  by apply: Rmult_le_compat_r; [apply: Rabs_pos | lra].
have Hz10 : Rabs z10p <= 2 * (1 + u) * Rabs x1.
  rewrite /z10p.
  apply: (Rle_trans _ _ _ (RNrel _)).
  rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
  rewrite (_ : 2 * (1 + u) * Rabs x1 = (1 + u) * (2 * Rabs x1)); last ring.
  apply: Rmult_le_compat_l; first lra.
  rewrite Rmult_comm.
  by apply: Rmult_le_compat_r; [apply: Rabs_pos | lra].
have Hb2 : Rabs b2 <= 4 * (1 + u) * M.
  rewrite Hb2e Rabs_minus_sym.
  have Hbe1 : Rabs (RND (z01p + z10p) - (z01p + z10p)) <= u * Rabs (z01p +
    z10p).
    by have [H1 H2] := error_bound_ulp_u beta Hp2 choice (z01p + z10p); lra.
  apply: (Rle_trans _ _ _ Hbe1).
  have Ht := Rabs_triang z01p z10p.
  have Hux1 := u_abs_le_ulp x1.
  have Huy1 := u_abs_le_ulp y1.
  have Hx1p := Rabs_pos x1; have Hy1p := Rabs_pos y1.
  have Hsum : Rabs (z01p + z10p) <= 2 * (1 + u) * (Rabs x1 + Rabs y1) by nra.
  have Hup : 0 <= u by lra.
  have Hstep : u * Rabs (z01p + z10p) <=
               2 * (1 + u) * (u * Rabs x1 + u * Rabs y1).
    have H := Rmult_le_compat_l u _ _ Hup Hsum.
    have Heq : u * (2 * (1 + u) * (Rabs x1 + Rabs y1))
             = 2 * (1 + u) * (u * Rabs x1 + u * Rabs y1) by ring.
    lra.
  have H1u : 0 < 1 + u by lra.
  nra.
have Hx1y1r : Rabs (RND (x1 * y1)) <= (1 + u) * (2 * M).
  apply: (Rle_trans _ _ _ (RNrel _)); nra.
have Hcb : Rabs c <= (1 + u) * (4 * (1 + u) * M + (1 + u) * (2 * M)).
  rewrite /c.
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang b2 (RND (x1 * y1)); lra.
have Hx0y2r : Rabs (RND (x0 * y2)) <= (1 + u) * (2 * M).
  apply: (Rle_trans _ _ _ (RNrel _)); nra.
have HA : Rabs (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2)))
          <= (1 + u) * (2 * M + (1 + u) * (2 * M)).
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang (RND (x1 * y0 - RND (x1 * y0))) (RND (x0 * y2)); lra.
have Hx2y0r : Rabs (RND (x2 * y0)) <= (1 + u) * (2 * M).
  apply: (Rle_trans _ _ _ (RNrel _)); nra.
have HB : Rabs (RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0)))
          <= (1 + u) * (2 * M + (1 + u) * (2 * M)).
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang (RND (x0 * y1 - RND (x0 * y1))) (RND (x2 * y0)); lra.
have Hzb : Rabs z3 <= (1 + u) * ((1 + u) * (2 * M + (1 + u) * (2 * M))
                                 + (1 + u) * (2 * M + (1 + u) * (2 * M))).
  rewrite /z3.
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2)))
                      (RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0))); lra.
apply: (Rle_trans _ _ _ (RNrel _)).
apply: (Rle_trans _ ((1 + u) * (Rabs c + Rabs z3))).
  apply: Rmult_le_compat_l; first lra.
  exact: Rabs_triang.
apply: (Rle_trans _ ((1 + u) * ((1 + u) * (4 * (1 + u) * M + (1 + u) * (2 * M))
    + (1 + u) * ((1 + u) * (2 * M + (1 + u) * (2 * M))
               + (1 + u) * (2 * M + (1 + u) * (2 * M)))))).
  apply: Rmult_le_compat_l; first lra.
  by have := Hcb; have := Hzb; lra.
have Heq : (1 + u) * ((1 + u) * (4 * (1 + u) * M + (1 + u) * (2 * M))
    + (1 + u) * ((1 + u) * (2 * M + (1 + u) * (2 * M))
               + (1 + u) * (2 * M + (1 + u) * (2 * M))))
    = M * ((1 + u) * ((1 + u) * (4 * (1 + u) + (1 + u) * 2)
      + (1 + u) * ((1 + u) * (2 + (1 + u) * 2)
                 + (1 + u) * (2 + (1 + u) * 2)))) by ring.
rewrite Heq.
have HK : (1 + u) * ((1 + u) * (4 * (1 + u) + (1 + u) * 2)
      + (1 + u) * ((1 + u) * (2 + (1 + u) * 2)
                 + (1 + u) * (2 + (1 + u) * 2))) <= 15 by nra.
have := HM0; nra.
Qed.

(* Symmetric [<= 16] corollary of the tighter [s3_le_15max]; kept for the     *)
(* [s3_ulp_op] magnitude argument (the strict [< 16] margin is only needed    *)
(* for the [I]-set divisibility of [inner_head_Fnonoverlap]).                 *)

(* ===========================================================================*)
(*  ALGORITHM 9 WITHOUT THE FUSED MULTIPLY-ADD.                               *)
(*                                                                            *)
(*  The paper's `c', `z31' and `z32' are `RN(v + a w)', one rounding each.    *)
(*  Rocq's primitive floats have no such instruction, so each is two here.    *)
(*  Everything else is Algorithm 9 unchanged.                                 *)
(* ===========================================================================*)
Definition ThreeProdn (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
  let: TWR y0 y1 y2 := y in
  let: (z00p, z00m) := TwoProd x0 y0 in
  let: (z01p, z01m) := TwoProd x0 y1 in
  let: (z10p, z10m) := TwoProd x1 y0 in
  let b := vecSum [:: z00m; z01p; z10p] in
  let b0 := nth 0 b 0 in
  let b1 := nth 0 b 1 in
  let b2 := nth 0 b 2 in
  let c   := RND (b2 + RND (x1 * y1)) in
  let z31 := RND (z10m + RND (x0 * y2)) in
  let z32 := RND (z01m + RND (x2 * y0)) in
  let z3  := RND (z31 + z32) in
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* Scale-equivariance, the paper's proof with one more [round_scale] a line.  *)
Lemma ThreeProdn_scale a b x y :
  ThreeProdn (scaleTW a x) (scaleTW b y) = scaleTW (a + b) (ThreeProdn x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdn /scaleTW.
have P1 : x1 * pow a * (y1 * pow b) = x1 * y1 * pow (a + b)
  by rewrite bpow_plus; ring.
have P2 : x0 * pow a * (y2 * pow b) = x0 * y2 * pow (a + b)
  by rewrite bpow_plus; ring.
have P3 : x2 * pow a * (y0 * pow b) = x2 * y0 * pow (a + b)
  by rewrite bpow_plus; ring.
rewrite !P1 !P2 !P3 !TwoProd_scale.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: w00m * pow (a+b); w01p * pow (a+b);
    w10p * pow (a+b)]) i = nth 0 (vecSum [:: w00m; w01p; w10p]) i * pow (a+b).
  move=> i.
  have -> : [:: w00m * pow (a+b); w01p * pow (a+b); w10p * pow (a+b)]
    = [seq z * pow (a+b) | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (t * pow (a+b) + RND (x1 * y1 * pow (a+b)))
    = RND (t + RND (x1 * y1)) * pow (a+b).
  move=> t.
  rewrite round_scale.
  have -> : t * pow (a+b) + RND (x1 * y1) * pow (a+b)
    = (t + RND (x1 * y1)) * pow (a+b) by ring.
  by rewrite round_scale.
have E5 : RND (RND (w10m * pow (a+b) + RND (x0 * y2 * pow (a+b)))
             + RND (w01m * pow (a+b) + RND (x2 * y0 * pow (a+b))))
    = RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))
      * pow (a+b).
  rewrite !round_scale.
  have -> : w10m * pow (a+b) + RND (x0 * y2) * pow (a+b)
    = (w10m + RND (x0 * y2)) * pow (a+b) by ring.
  have -> : w01m * pow (a+b) + RND (x2 * y0) * pow (a+b)
    = (w01m + RND (x2 * y0)) * pow (a+b) by ring.
  rewrite !round_scale.
  have -> : RND (w10m + RND (x0 * y2)) * pow (a+b)
            + RND (w01m + RND (x2 * y0)) * pow (a+b)
    = (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0))) * pow (a+b)
    by ring.
  by rewrite round_scale.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b);
    nth 0 bb 1 * pow (a+b); RND (nth 0 bb 2 + RND (x1 * y1)) * pow (a+b);
    RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))
      * pow (a+b)]) i
  = nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + RND (x1 * y1));
      RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]) i
    * pow (a+b).
  move=> i.
  have -> : [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b);
      nth 0 bb 1 * pow (a+b); RND (nth 0 bb 2 + RND (x1 * y1)) * pow (a+b);
      RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))
        * pow (a+b)]
    = [seq z * pow (a+b) | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (nth 0 bb 2 + RND (x1 * y1));
        RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + RND (x1 * y1));
  RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))].
have Ev : vsebK 2 [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b);
    nth 0 ee 3 * pow (a+b); nth 0 ee 4 * pow (a+b)]
  = [seq z * pow (a+b) | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3;
      nth 0 ee 4]].
  have -> : [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b);
      nth 0 ee 3 * pow (a+b); nth 0 ee 4 * pow (a+b)]
    = [seq z * pow (a+b) | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3;
        nth 0 ee 4]] by [].
  by rewrite vsebK_scale.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdn_opp x y : ThreeProdn (negTW x) y = negTW (ThreeProdn x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdn /negTW.
have P1 : (- x1) * y1 = - (x1 * y1) by ring.
have P2 : (- x0) * y2 = - (x0 * y2) by ring.
have P3 : (- x2) * y0 = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !round_opp !TwoProd_opp_l.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i
    = - nth 0 (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - RND (x1 * y1))
    = - RND (t + RND (x1 * y1)).
  move=> t.
  have -> : - t + - RND (x1 * y1) = - (t + RND (x1 * y1)) by ring.
  by rewrite round_opp.
have E5 : RND (RND (- w10m + - RND (x0 * y2)) + RND (- w01m + - RND (x2 * y0)))
    = - RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0))).
  have -> : - w10m + - RND (x0 * y2) = - (w10m + RND (x0 * y2)) by ring.
  have -> : - w01m + - RND (x2 * y0) = - (w01m + RND (x2 * y0)) by ring.
  rewrite !round_opp.
  have -> : - RND (w10m + RND (x0 * y2)) + - RND (w01m + RND (x2 * y0))
    = - (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0))) by ring.
  by rewrite round_opp.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
    - RND (nth 0 bb 2 + RND (x1 * y1));
    - RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]) i
  = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + RND (x1 * y1));
      RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
      - RND (nth 0 bb 2 + RND (x1 * y1));
      - RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]
    = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (nth 0 bb 2 + RND (x1 * y1));
        RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + RND (x1 * y1));
  RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4]
  = [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3;
      nth 0 ee 4]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4]
    = [seq - z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]]
    by [].
  by rewrite vsebK_opp.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdn_opp_r x y : ThreeProdn x (negTW y) = negTW (ThreeProdn x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdn /negTW.
have P1 : x1 * (- y1) = - (x1 * y1) by ring.
have P2 : x0 * (- y2) = - (x0 * y2) by ring.
have P3 : x2 * (- y0) = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !round_opp !TwoProd_opp_r.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i
    = - nth 0 (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - RND (x1 * y1))
    = - RND (t + RND (x1 * y1)).
  move=> t.
  have -> : - t + - RND (x1 * y1) = - (t + RND (x1 * y1)) by ring.
  by rewrite round_opp.
have E5 : RND (RND (- w10m + - RND (x0 * y2)) + RND (- w01m + - RND (x2 * y0)))
    = - RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0))).
  have -> : - w10m + - RND (x0 * y2) = - (w10m + RND (x0 * y2)) by ring.
  have -> : - w01m + - RND (x2 * y0) = - (w01m + RND (x2 * y0)) by ring.
  rewrite !round_opp.
  have -> : - RND (w10m + RND (x0 * y2)) + - RND (w01m + RND (x2 * y0))
    = - (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0))) by ring.
  by rewrite round_opp.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
    - RND (nth 0 bb 2 + RND (x1 * y1));
    - RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]) i
  = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + RND (x1 * y1));
      RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1;
      - RND (nth 0 bb 2 + RND (x1 * y1));
      - RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]
    = [seq - z | z <- [:: w00p; nth 0 bb 0; nth 0 bb 1;
        RND (nth 0 bb 2 + RND (x1 * y1));
        RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + RND (x1 * y1));
  RND (RND (w10m + RND (x0 * y2)) + RND (w01m + RND (x2 * y0)))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4]
  = [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3;
      nth 0 ee 4]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4]
    = [seq - z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]]
    by [].
  by rewrite vsebK_opp.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

Lemma ThreeProdn_0l y : ThreeProdn (TWR 0 0 0) y = TWR 0 0 0.
Proof.
case: y => y0 y1 y2.
rewrite /ThreeProdn !TwoProd00l /=.
rewrite !Rmult_0_l !Rplus_0_r !round_0.
do 50! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0; 0] = nseq 2.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

Lemma ThreeProdn_0r x : ThreeProdn x (TWR 0 0 0) = TWR 0 0 0.
Proof.
case: x => x0 x1 x2.
rewrite /ThreeProdn !TwoProd00r /=.
rewrite !Rmult_0_r !Rplus_0_l !round_0.
do 50! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0; 0] = nseq 2.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.


(* The two split lines cost nothing in size: the inner rounding lands on a    *)
(* bound that is itself in the format, so it cannot overshoot it.             *)
Lemma cn_bound b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 4 * (u * u) ->
  Rabs (RND (b2 + RND (x1 * y1))) <= 8 * (u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have F4 : format (4 * (u * u))
  by apply: (format_imul_u2 (k := 4)); have := two_p_ge_64; lia.
have F8 : format (8 * (u * u))
  by apply: (format_imul_u2 (k := 8)); have := two_p_ge_64; lia.
have H2' : Rabs (RND (x1 * y1)) <= 4 * (u * u)
  by apply: Rabs_round_le_r => //; lra.
apply: Rabs_round_le_r => //.
by have := Rabs_triang b2 (RND (x1 * y1)); lra.
Qed.

Lemma z31n_bound z10m x0 y2 :
  Rabs z10m <= 2 * (u * u) -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (RND (z10m + RND (x0 * y2))) <= 6 * (u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have F4 : format (4 * (u * u))
  by apply: (format_imul_u2 (k := 4)); have := two_p_ge_64; lia.
have F6 : format (6 * (u * u))
  by apply: (format_imul_u2 (k := 6)); have := two_p_ge_64; lia.
have H2' : Rabs (RND (x0 * y2)) <= 4 * (u * u)
  by apply: Rabs_round_le_r => //; lra.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z10m (RND (x0 * y2)); lra.
Qed.

Lemma z32n_bound z01m x2 y0 :
  Rabs z01m <= 2 * (u * u) -> Rabs (x2 * y0) < 4 * (u * u) ->
  Rabs (RND (z01m + RND (x2 * y0))) <= 6 * (u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have F4 : format (4 * (u * u))
  by apply: (format_imul_u2 (k := 4)); have := two_p_ge_64; lia.
have F6 : format (6 * (u * u))
  by apply: (format_imul_u2 (k := 6)); have := two_p_ge_64; lia.
have H2' : Rabs (RND (x2 * y0)) <= 4 * (u * u)
  by apply: Rabs_round_le_r => //; lra.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z01m (RND (x2 * y0)); lra.
Qed.

Lemma z10m_bound2 x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
Proof.
move=> Nx Ny.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
rewrite round_generic; first by apply: (z10m_bound Nx Ny).
rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
  last by ring.
by apply: generic_format_opp; exact: format_err_mul.
Qed.

Lemma z01m_bound2 x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
Proof.
move=> Nx Ny.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
rewrite round_generic; first by apply: (z01m_bound Nx Ny).
rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
  last by ring.
by apply: generic_format_opp; exact: format_err_mul.
Qed.

(* The four things the generic chain asks of `c' and `z3', in one place.      *)
Lemma cz3n_facts x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + RND (x1 * y1)) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
               + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0))) in
  [/\ format c, format z3, Rabs c <= 8 * (u * u) & Rabs z3 <= 12 * (u * u)].
Proof.
move=> Nx Ny bb c z3.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx Ny).
split; try apply: generic_format_round.
  by apply: cn_bound => //; apply: (x1y1_bound Nx Ny).
apply: z3_bound.
  by apply: z31n_bound; [apply: (z10m_bound2 Nx Ny) | apply: (x0y2_bound Nx Ny)].
by apply: z32n_bound; [apply: (z01m_bound2 Nx Ny) | apply: (x2y0_bound Nx Ny)].
Qed.

Lemma ThreeProdn_norm_eq x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + RND (x1 * y1));
        RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
           + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0)))] in
  ThreeProdn (TWR x0 x1 x2) (TWR y0 y1 y2) =
    TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2).
Proof.
move=> Nx' Ny'.
have [Fc Fz3 Hc8 Hz3b] := cz3n_facts Nx' Ny'.
rewrite /ThreeProdn /TwoProd.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + RND (x1 * y1));
  RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
           + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0)))].
set el := [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4].
have Hmatch : match vsebK 2 el with
    | [::] => TWR (nth 0 e 0) 0 0
    | [:: r1] => TWR (nth 0 e 0) r1 0
    | [:: r1, r2 & _] => TWR (nth 0 e 0) r1 r2
    end = TWR (nth 0 e 0) (nth 0 (vseb el) 0) (nth 0 (vseb el) 1).
  by rewrite /vsebK; case: (vseb el) => [|r1 [|r2 rl]].
rewrite Hmatch.
have Hsz5 : size e = 5%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Hbeh : el = behead e.
  have gen : forall s : seq R, size s = 5%N ->
      behead s = [:: nth 0 s 1; nth 0 s 2; nth 0 s 3; nth 0 s 4].
    by move=> s; case: s => [|a[|b[|c[|d[|f[|g r]]]]]].
  by rewrite /el (gen e Hsz5).
have [H0 [H1 H2]] : nth 0 (vseb e) 0 = nth 0 e 0 /\
    nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
    nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
  case: (Req_dec (nth 0 e 1) 0) => [He1|He1].
    by apply: (vseb_head3_e1zero_g Nx' Ny' Fc Fz3 Hc8 Hz3b).
  have FL5 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + RND (x1 * y1));
      RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
           + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0)))],
      forall z, format z}.
    move=> z; rewrite !inE.
    move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
      try apply: generic_format_round; apply: Fnthbb.
  have Hstar := vseb_star FL5 (isT : (1 < 5)%N) He1.
  have Hs : vseb e = nth 0 e 0 :: vseb (behead e) by exact: Hstar.
  rewrite Hs; split; [exact: erefl | split; exact: erefl].
by rewrite Hbeh H0 H1 H2.
Qed.

Lemma ThreeProdn_isTW_norm x y :
  tw_normP x -> tw_normP y -> isTW (ThreeProdn x y).
Proof.
move=> Nx Ny.
case: x Nx => x0 x1 x2 Nx.
case: y Ny => y0 y1 y2 Ny.
have Nx' : tw_norm x0 x1 x2 by exact: Nx.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
have [Fc Fz3 Hc8 Hz3b] := cz3n_facts Nx' Ny'.
rewrite (ThreeProdn_norm_eq Nx' Ny').
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + RND (x1 * y1));
  RND (RND (RND (x1 * y0 - RND (x1 * y0)) + RND (x0 * y2))
           + RND (RND (x0 * y1 - RND (x0 * y1)) + RND (x2 * y0)))].
have Hsz5 : size e = 5%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Fe : {in e, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
    try apply: generic_format_round; apply: Fnthbb.
have Fno : Fnonoverlap e
  by rewrite /e /bb;
     apply: (inner_Fnonoverlap_g Nx' Ny' Fc Fz3 Hc8 Hz3b (s3n_le_15max Nx' Ny')).
have Pno : Pnonoverlap (vseb e).
  have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
  by have [] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
apply: Pnonoverlap_isTW3; first exact: Pno.
by apply: (@format_vseb p Hp2 choice e Fe).
Qed.

Lemma ThreeProdn_isTW x y : isTW x -> isTW y -> isTW (ThreeProdn x y).
Proof.
move=> Hx Hy.
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  by rewrite (isTW_zero_lead Hx x0z) ThreeProdn_0l; exact: isTW_TWR000.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  by rewrite (isTW_zero_lead Hy y0z) ThreeProdn_0r; exact: isTW_TWR000.
have [cx _ [Hxp Hxn]] := isTW_normalize Hx x0n.
have [cy _ [Hyp Hyn]] := isTW_normalize Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
case: Hxsg => Hxs; case: Hysg => Hys.
- rewrite -(isTW_scale (cx + cy)) -ThreeProdn_scale.
  by apply: ThreeProdn_isTW_norm => //; [apply: Hxp | apply: Hyp].
- rewrite -(isTW_opp (ThreeProdn x y)) -(isTW_scale (cx + cy)).
  rewrite -ThreeProdn_opp_r -ThreeProdn_scale.
  by apply: ThreeProdn_isTW_norm => //; [apply: Hxp | apply: Hyn].
- rewrite -(isTW_opp (ThreeProdn x y)) -(isTW_scale (cx + cy)).
  rewrite -ThreeProdn_opp -ThreeProdn_scale.
  by apply: ThreeProdn_isTW_norm => //; [apply: Hxn | apply: Hyp].
- rewrite -(isTW_scale (cx + cy)).
  have <- : ThreeProdn (negTW x) (negTW y) = ThreeProdn x y.
    by rewrite ThreeProdn_opp ThreeProdn_opp_r negTW_id.
  rewrite -ThreeProdn_scale.
  by apply: ThreeProdn_isTW_norm => //; [apply: Hxn | apply: Hyn].
Qed.

End SecProdGen.
