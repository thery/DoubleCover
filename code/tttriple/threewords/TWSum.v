(* ---------------------------------------------------------------------------*)
(* Algorithm 8 (TWSum): the sum of two triple-word numbers, and its two main  *)
(* correctness results -- the result is a triple word ([TWSum_isTW]) and the  *)
(* relative error bound ([TWSum_error]).  Generic over the precision [p] and  *)
(* over the precision [p] alone -- FLX, no [emin] (binary64 is fixed only in *)
(* [TwoSum], [Nonoverlap], [TWR], [Merge], [VecSum] and [VSEB].               *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecTWSum.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* The correctness of triple-word addition needs enough precision (paper      *)
(* Section 5: [p >= 4] for Theorem 6, [p >= 6] for the Theorem-3 truncation   *)
(* and [size < p + 1] for six merged terms).  [p >= 6] covers all of them;    *)
(* binary64 ([p = 53]) satisfies it; the development is generic in [p].                          *)
Hypothesis Hp6 : (6 <= p)%Z.

(* [Thm6.v] is stated for [4 <= p]; here [6 <= p].                           *)
Fact Hp4 : (4 <= p)%Z. Proof. by lia. Qed.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).
Local Notation uE := (@uE p).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation RU := (round beta fexp Zceil).
Local Notation RD := (round beta fexp Zfloor).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).
Local Notation error_le_half_ulp_RN :=
  (@error_le_half_ulp_round beta (FLX_exp p)
     (FLX_exp_valid p) (FLX_exp_monotone p) choice).
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct p choice Hp2 choice_sym).

Local Notation TwoSum := (TwoSum p choice).
Local Notation TwoSum_hi := (TwoSum_hi p choice).
Local Notation formatDWR := (formatDWR p).
Local Notation magnitudeDWR := (magnitudeDWR p).
Local Notation format_TwoSum := (format_TwoSum Hp2 choice).
Local Notation TwoSum_correct_loc :=
  (TwoSum_correct_loc Hp2 choice_sym).
Local Notation magnitude_TwoSum :=
  (magnitude_TwoSum Hp2 choice_sym).
Local Notation TwoSum_err_imul := (TwoSum_err_imul Hp2 choice_sym).
Local Notation TwoSum_err_uls_ge :=
  (TwoSum_err_uls_ge Hp2 choice_sym).

Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation format_lt_ulp_le := (@format_lt_ulp_le p Hp2).
Local Notation Pnonoverlap_imp_pairwise_ul :=
  (Pnonoverlap_imp_pairwise_ul Hp2).
Local Notation abs_le_ufp_norm := (abs_le_ufp_norm Hp2).
Local Notation small_head_zero := (@small_head_zero p Hp2).
Local Notation sumR_ufp_bound := (@sumR_ufp_bound p Hp2).
Local Notation nth_step_zero := (@nth_step_zero p Hp2).

(* Triple-word type and merge from [TWR.v]/[Merge.v]; fix [p].               *)
Local Notation isTW := (isTW p).
Local Notation isTW_sorted_mag := (isTW_sorted_mag Hp2).
Local Notation Merge_pairwise_ulp := (Merge_pairwise_ulp Hp2).

(* [VecSum.v] / [VSEB.v] / [Thm6.v] entry points; re-hide this format's      *)
(* [p]/[choice] (and the [Hp2]/[choice_sym] proofs).                         *)
Local Notation vecSum := (vecSum p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation size_vecSum := (size_vecSum p choice).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation format_vseb := (format_vseb Hp2).
Local Notation format_vsebK := (format_vsebK Hp2).
Local Notation vecSum_sum := (vecSum_sum Hp2 choice_sym).
Local Notation vseb_sum := (vseb_sum Hp2 choice_sym).
Local Notation vecSum_run_ufp := (vecSum_run_ufp Hp2 choice_sym).
Local Notation vecSum_err_ufp := (vecSum_err_ufp Hp2 choice_sym).
Local Notation vseb_Pnonoverlap :=
  (vseb_Pnonoverlap Hp2 choice_sym).
Local Notation vecSum_vseb_Pnonoverlap :=
  (vecSum_vseb_Pnonoverlap Hp2 Hp4 choice_sym).

(* ===========================================================================*)
(*  Algorithm 6 (ToTW): three FP numbers to a triple word (paper Thm 4).      *)
(*  ToTW a b c = VSEB(VecSum(d0, d1, c)) with (d0,d1) = 2Sum(a,b).  Unlike    *)
(*  TWSum this does NOT go through Theorem 6: the special input [d0; d1; c]   *)
(*  (a DW followed by one FP) makes VecSum's output already F-nonoverlapping, *)
(*  so Theorem 2 ([vseb_Pnonoverlap]) suffices.  See doc/thm4.md.             *)
(* ===========================================================================*)
Definition ToTW (a b c : R) : twR :=
  let: DWR d0 d1 := TwoSum a b in
  match vsebK 3 (vecSum [:: d0; d1; c]) with
  | [:: r0, r1, r2 & _] => TWR r0 r1 r2
  | [:: r0; r1]         => TWR r0 r1 0
  | [:: r0]             => TWR r0 0 0
  | [::]                => TWR 0 0 0
  end.

(* THE content of Theorem 4 (doc/thm4.md, the [(e1,e2)] argument): the        *)
(* VecSum of [d0; d1; c] is F-nonoverlapping.  [(e0,e1)] is free from the     *)
(* 2Sum half-ulp bound; [(e1,e2)] is a divisibility/ulp contradiction.        *)
(* Theorem 4 core (paper p.5), case [e_1 <> 0]: the last VecSum error [e_2] =  *)
(* error of [2Sum(d1,c)] is [<= 1/2 uls(e_1)].  [Rabs d1 <= 1/2 ulp d0] is the *)
(* DW property of [(d0,d1) = 2Sum(a,b)].                                       *)
Lemma ToTW_e1e2 (d0 d1 c s1 s0 e1 e2 : R) :
  ties_to_even choice -> format d0 -> format d1 -> format c ->
  TwoSum d1 c = DWR s1 e2 -> TwoSum d0 s1 = DWR s0 e1 ->
  Rabs d1 <= / 2 * ulp d0 -> e1 <> 0 ->
  Rabs e2 <= / 2 * uls e1.
Proof.
move=> Heven Fd0 Fd1 Fc E2 E1 Hd1 e1n0.
apply: Rnot_lt_le => Hgt.
have Fs1 : format s1 by have := format_TwoSum Fd1 Fc; rewrite E2; case.
have Fe1 : format e1 by have := format_TwoSum Fd0 Fs1; rewrite E1; case.
have Hs1v : s1 = RND (d1 + c) by have := TwoSum_hi d1 c; rewrite E2.
have Hc2 : s1 + e2 = d1 + c.
  move: E2 (TwoSum_correct_loc Fd1 Fc); case: (TwoSum d1 c) => sX eX.
  by case=> <- <- /= ->.
have Hm2 : Rabs e2 <= / 2 * ulp s1.
  have := magnitude_TwoSum Fd1 Fc; rewrite E2 /magnitudeDWR; lra.
have [k Hk] : exists e, uls e1 = pow e by apply: uls_pow.
rewrite Hk in Hgt.
have Hpk := bpow_gt_0 beta k.
(* Step 1 (paper's [s >= 1, 2u | s]): [cexp s1 >= k+1]                       *)
have Hulps1 : pow k < ulp s1 by lra.
have s1n0 : s1 <> 0 by move=> H0; move: Hulps1; rewrite H0 ulp_FLX_0; lra.
have Hcexp_s1 : (k < cexp s1)%Z.
  apply: (lt_bpow beta); apply: Rlt_le_trans Hulps1 _.
  rewrite ulp_neq_0 //; apply: Rle_refl.
(* Step 2 (paper's [e1 not div 2u, so d0 < 1]): [cexp d0 <= k]              *)
have Himul_e1 := TwoSum_err_imul Fd0 Fs1; rewrite E1 /= in Himul_e1.
have Hmin_le : (Z.min (cexp d0) (cexp s1) <= k)%Z.
  by apply: (le_bpow beta); rewrite -Hk; apply: is_imul_uls_ge.
have Hcexp_d0 : (cexp d0 <= k)%Z by move: Hmin_le Hcexp_s1; lia.
have d0n0 : d0 <> 0.
  move=> H0.
  have d1z : d1 = 0.
    by move: Hd1; rewrite H0 ulp_FLX_0 Rmult_0_r; split_Rabs; lra.
  have s1c : s1 = c by rewrite Hs1v d1z Rplus_0_l round_generic.
  by move: Hgt Hc2; rewrite d1z s1c; split_Rabs; lra.
(* Hence [|d1| <= 1/2 pow k] (paper's [|d1| <= 1/2 u])                       *)
have Hd1_le : Rabs d1 <= / 2 * pow k.
  apply: Rle_trans Hd1 _.
  rewrite ulp_neq_0 //.
  have : pow (cexp d0) <= pow k by apply: bpow_le.
  lra.
(* Finish: a 2Sum error never exceeds the OTHER operand ([c] is a float),   *)
(* so [|e2| <= |d1|] -- this is the paper's [s = c, e2 = d1], but immediate *)
(* from the nearest-float property (no [|c| >= 1] / tie analysis needed).   *)
have He2_le : Rabs e2 <= Rabs d1.
  have [_ Hnear] := round_N_pt beta fexp choice (d1 + c).
  have Hb := Hnear c Fc.
  have -> : Rabs e2 = Rabs (RND (d1 + c) - (d1 + c)).
    by rewrite -Hs1v; move: Hc2; split_Rabs; lra.
  apply: Rle_trans Hb _.
  have -> : c - (d1 + c) = - d1 by lra.
  rewrite Rabs_Ropp; apply: Rle_refl.
lra.
Qed.

(* Theorem 4 core, case [e_1 = 0]: the same bound against the surviving high  *)
(* word [s_0 = e_0] ("the same reasoning with [e_0] instead of [e_1]").        *)
Lemma ToTW_e1zero (d0 d1 c s1 s0 e1 e2 : R) :
  ties_to_even choice -> format d0 -> format d1 -> format c ->
  TwoSum d1 c = DWR s1 e2 -> TwoSum d0 s1 = DWR s0 e1 ->
  Rabs d1 <= / 2 * ulp d0 -> s0 <> 0 -> e1 = 0 ->
  Rabs e2 <= / 2 * uls s0.
Proof.
move=> Heven Fd0 Fd1 Fc E2 E1 Hd1 s0n0 e1z.
apply: Rnot_lt_le => Hgt.
have Fs1 : format s1 by have := format_TwoSum Fd1 Fc; rewrite E2; case.
have Fs0 : format s0 by have := format_TwoSum Fd0 Fs1; rewrite E1; case.
have Hs1v : s1 = RND (d1 + c) by have := TwoSum_hi d1 c; rewrite E2.
have Hc2 : s1 + e2 = d1 + c.
  move: E2 (TwoSum_correct_loc Fd1 Fc); case: (TwoSum d1 c) => sX eX.
  by case=> <- <- /= ->.
have Hc1 : s0 + e1 = d0 + s1.
  move: E1 (TwoSum_correct_loc Fd0 Fs1); case: (TwoSum d0 s1) => sX eX.
  by case=> <- <- /= ->.
have Hs0v : s0 = d0 + s1 by move: Hc1; rewrite e1z; lra.
have Hm2 : Rabs e2 <= / 2 * ulp s1.
  have := magnitude_TwoSum Fd1 Fc; rewrite E2 /magnitudeDWR; lra.
have [k Hk] : exists e, uls s0 = pow e by apply: uls_pow.
rewrite Hk in Hgt.
have Hpk := bpow_gt_0 beta k.
have Hulps1 : pow k < ulp s1 by lra.
have s1n0 : s1 <> 0 by move=> H0; move: Hulps1; rewrite H0 ulp_FLX_0; lra.
have Hcexp_s1 : (k < cexp s1)%Z.
  apply: (lt_bpow beta); apply: Rlt_le_trans Hulps1 _.
  rewrite ulp_neq_0 //; apply: Rle_refl.
(* Step 2 via [s0 = d0 + s1]: if [cexp d0 >= k+1] then [pow(k+1) | s0],      *)
(* contradicting [uls s0 = pow k] (the paper's "same reasoning with e0").    *)
have Hs1_imul : is_imul s1 (pow (k + 1)).
  by apply: is_imul_pow_le (format_imul_cexp Fs1) _; lia.
have Hcexp_d0 : (cexp d0 <= k)%Z.
  case: (Z_le_gt_dec (cexp d0) k) => // Hgt_d0.
  have Hd0_imul : is_imul d0 (pow (k + 1)).
    by apply: is_imul_pow_le (format_imul_cexp Fd0) _; lia.
  have Hs0_imul : is_imul s0 (pow (k + 1)) by rewrite Hs0v; apply: is_imul_add.
  have := is_imul_uls_ge Fs0 s0n0 Hs0_imul; rewrite Hk.
  by move/(le_bpow beta); lia.
have d0n0 : d0 <> 0.
  move=> H0.
  have d1z : d1 = 0.
    by move: Hd1; rewrite H0 ulp_FLX_0 Rmult_0_r; split_Rabs; lra.
  have s1c : s1 = c by rewrite Hs1v d1z Rplus_0_l round_generic.
  by move: Hgt Hc2; rewrite d1z s1c; split_Rabs; lra.
have Hd1_le : Rabs d1 <= / 2 * pow k.
  apply: Rle_trans Hd1 _.
  rewrite ulp_neq_0 //.
  have : pow (cexp d0) <= pow k by apply: bpow_le.
  lra.
have He2_le : Rabs e2 <= Rabs d1.
  have [_ Hnear] := round_N_pt beta fexp choice (d1 + c).
  have Hb := Hnear c Fc.
  have -> : Rabs e2 = Rabs (RND (d1 + c) - (d1 + c)).
    by rewrite -Hs1v; move: Hc2; split_Rabs; lra.
  apply: Rle_trans Hb _.
  have -> : c - (d1 + c) = - d1 by lra.
  rewrite Rabs_Ropp; apply: Rle_refl.
lra.
Qed.

Lemma ToTW_vecSum_Fnonoverlap a b c :
  ties_to_even choice -> format a -> format b -> format c ->
  Fnonoverlap (vecSum [:: dwh (TwoSum a b); dwl (TwoSum a b); c]).
Proof.
move=> Heven Fa Fb Fc.
have Fd0 : format (dwh (TwoSum a b))
  by have := format_TwoSum Fa Fb; case: (TwoSum a b) => ? ? [].
have Fd1 : format (dwl (TwoSum a b))
  by have := format_TwoSum Fa Fb; case: (TwoSum a b) => ? ? [].
have Hd1 : Rabs (dwl (TwoSum a b)) <= / 2 * ulp (dwh (TwoSum a b)).
  have := magnitude_TwoSum Fa Fb.
  by case: (TwoSum a b) => sh sl; rewrite /magnitudeDWR /dwh /dwl; lra.
set d0 := dwh (TwoSum a b).
set d1 := dwl (TwoSum a b).
have Hvs : vecSum [:: d0; d1; c] =
  let: DWR s1 e2 := TwoSum d1 c in
  let: DWR s0 e1 := TwoSum d0 s1 in [:: s0; e1; e2].
  rewrite /vecSum !vecSumAux_cons /=.
  by case: (TwoSum d1 c) => s1 e2; case: (TwoSum d0 s1) => s0 e1.
rewrite Hvs.
case E2 : (TwoSum d1 c) => [s1 e2].
case E1 : (TwoSum d0 s1) => [s0 e1].
have Fs1 : format s1 by have := format_TwoSum Fd1 Fc; rewrite E2; case.
have Fe1 : format e1 by have := format_TwoSum Fd0 Fs1; rewrite E1; case.
have Hm1 : Rabs e1 <= / 2 * ulp s0.
  have := magnitude_TwoSum Fd0 Fs1; rewrite E1 /magnitudeDWR; lra.
have HA : s0 <> 0 -> Rabs e1 <= / 2 * uls s0.
  move=> _; apply: Rle_trans Hm1 _.
  suff : ulp s0 <= uls s0 by lra.
  exact: ulp_le_ulps.
have HI : e1 <> 0 -> Rabs e2 <= / 2 * uls e1
  by move=> H; apply: (ToTW_e1e2 Heven Fd0 Fd1 Fc E2 E1 Hd1 H).
have HII : s0 <> 0 -> e1 = 0 -> Rabs e2 <= / 2 * uls s0
  by move=> H H0; apply: (ToTW_e1zero Heven Fd0 Fd1 Fc E2 E1 Hd1 H H0).
have Huls_mono : e1 <> 0 -> uls e1 <= uls s0.
  move=> e1n0.
  apply: Rle_trans (uls_le_abs Fe1 e1n0) _.
  apply: Rle_trans Hm1 _.
  have Hx : ulp s0 <= uls s0 by exact: ulp_le_ulps.
  have Hu0 : 0 <= ulp s0 by apply: ulp_ge_0.
  lra.
apply: Fnonoverlap_allpairs => i j iLj jLs ni0.
move: iLj jLs ni0.
case: i => [|[|[|i']]]; case: j => [|[|[|j']]] //= _ _ ni0.
case: (Req_dec e1 0) => [e1z|e1n0]; first by apply: HII.
apply: Rle_trans (HI e1n0) _.
have := Huls_mono e1n0; lra.
Qed.

(* Paper Theorem 4: [ToTW a b c] is a triple word (p >= 4; here p >= 6).      *)
(* Reduction to Theorem 2, mirroring [TWSum_isTW].                            *)
Lemma ToTW_isTW a b c :
  ties_to_even choice -> format a -> format b -> format c -> isTW (ToTW a b c).
Proof.
move=> Hceven Fa Fb Fc.
have HzF := ToTW_vecSum_Fnonoverlap Hceven Fa Fb Fc.
have [Fd0 Fd1] : format (dwh (TwoSum a b)) /\ format (dwl (TwoSum a b)).
  by have := format_TwoSum Fa Fb; case: (TwoSum a b) => h l [].
move: HzF Fd0 Fd1; rewrite /ToTW; case: (TwoSum a b) => d0 d1 /= HzF Fd0 Fd1.
pose z := [:: d0; d1; c].
have Hzf : {in z, forall t, format t}.
  by move=> t; rewrite !inE => /or3P[] /eqP->.
have Hsz : (Z.of_nat (size (vecSum z)) <= p + 1)%Z.
  by rewrite size_vecSum /=; move: Hp6; lia.
have Hr_nonover : Pnonoverlap (vsebK 3 (vecSum z)).
  apply/Pnonoverlap_take.
  by case: (vseb_Pnonoverlap Hsz (format_vecSum Hzf) HzF).
have Hr_format : {in vsebK 3 (vecSum z), forall t, format t}.
  by apply/format_vsebK/format_vecSum.
rewrite -/z.
move: Hr_nonover Hr_format;
  case: (vsebK 3 (vecSum z)) => [|r0 [|r1 [|r2 tl]]] Hno Hfmt.
- by split; try exact: generic_format_0; left.
- by split; try exact: generic_format_0;
     [apply: Hfmt; rewrite !inE eqxx | left | left].
- by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
           | exact: generic_format_0 | apply: (Hno 0%N) | left].
by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
         | apply: Hfmt; rewrite !inE eqxx !orbT | apply: (Hno 0%N)
         | apply: (Hno 1%N)].
Qed.

(* ===========================================================================*)
(*  Algorithm 7 (RoundTW): round a triple word to the nearest float           *)
(*  (paper Theorem 5).  See doc/thm5.md.                                      *)
(* ===========================================================================*)

(* [x0+x1] sits exactly halfway between its two nearest floats, i.e. [m] is    *)
(* the mean of its round-down and round-up (which for a non-float are the two  *)
(* consecutive floats bracketing it).                                          *)
Definition is_midpoint (m : R) : Prop :=
  2 * m = round beta fexp Zfloor m + round beta fexp Zceil m.

(* NOTE (2026-07): the inner test's polarity is FLIPPED with respect to        *)
(* Algorithm 7 as printed in the paper.  As printed, the directional branch is  *)
(* entered when [RN(-(3/2u-2u^2) x0) = x1]; that is incorrect -- it fires on the *)
(* paper's "special" non-midpoint case and falls through to [RN(x0+x1)] on       *)
(* genuine midpoints, ignoring [x2].  The correct condition takes the            *)
(* directional branch when [x0+2x1] is exact AND [RN(-(3/2u-2u^2) x0) <> x1].    *)
(* See doc/roundtw-erratum.md and doc/roundtw_bug.c for a verified counterexample*)
(* (the triple-word [(1, u, u^2)] rounds wrongly under the printed condition).   *)
Definition RoundTW (x0 x1 x2 : R) : R :=
  if Req_EM_T (RND (x0 + 2 * x1)) (x0 + 2 * x1) then
    if Req_EM_T (RND (- (3 / 2 * u - 2 * (u * u)) * x0)) x1 then RND (x0 + x1)
    else
      if Rlt_le_dec 0 x2 then RU (x0 + x1)
      else if Rlt_le_dec x2 0 then RD (x0 + x1)
      else RND (x0 + x1)
  else RND (x0 + x1).

(* A float plus a perturbation strictly below 1/4 ulp rounds back to the      *)
(* float.  [1/4] (not [1/2]) because at a power of two the predecessor is     *)
(* only [1/2 ulp] away, so its midpoint is [1/4 ulp] below.                   *)
Lemma RN_add_lt_quarter (f d : R) :
  format f -> Rabs d < / 4 * ulp f -> RND (f + d) = f.
Proof.
have Vf : Valid_exp fexp by apply: FLX_exp_valid.
(* The down-gap [f - pred f] is at least [1/2 ulp f]; at a power of two it is  *)
(* exactly that (the predecessor's ulp is halved), elsewhere it is a full ulp. *)
have gap_dn : forall y, format y -> 0 < y -> / 2 * ulp y <= y - pred beta fexp y.
  move=> y Fy ypos.
  have predpos : 0 < pred beta fexp y.
    rewrite pred_eq_pos //; last lra.
    suff : pred_pos beta fexp y <> 0.
      have H1 := @pred_pos_ge_0 beta fexp Vf y ypos Fy; lra.
    move=> Hz; have := @pred_pos_plus_ulp beta fexp Vf y ypos Fy.
    by rewrite Hz ulp_FLX_0 Rplus_0_l => yeq; lra.
  have Edp : y - pred beta fexp y = ulp (pred beta fexp y).
    have := @pred_pos_plus_ulp beta fexp Vf y ypos Fy.
    rewrite -(pred_eq_pos beta fexp y); [lra | lra].
  rewrite Edp.
  case: (@ulp_pred_pos beta fexp Vf y Fy predpos) => [Heq | ypow].
    rewrite Heq; have := ulp_ge_0 beta fexp y; lra.
  rewrite -Edp.
  have -> : pred beta fexp y = y - pow (fexp (mag beta y - 1)).
    by rewrite {1}ypow pred_bpow -ypow.
  have Uy : ulp y = pow (fexp (mag beta y)).
    by rewrite ulp_neq_0; [rewrite /cexp | lra].
  rewrite Uy.
  have -> : (fexp (mag beta y - 1) = fexp (mag beta y) - 1)%Z
    by rewrite /FLX_exp; lia.
  rewrite (bpow_plus _ _ (-1)) /=.
  have := bpow_gt_0 beta (fexp (mag beta y)).
  simpl; lra.
move=> Ff Hd.
have [feq0|f0] := Req_dec f 0.
  move: Hd; rewrite feq0 ulp_FLX_0 Rmult_0_r => Hd0.
  by have := Rabs_pos d; lra.
have ulpf_pos : 0 < ulp f by apply: ulp_gt_0.
(* Both neighbouring gaps are at least [1/2 ulp f], for either sign of [f].    *)
have gapUP : / 2 * ulp f <= succ beta fexp f - f.
  have [fpos|fneg] := Rle_lt_dec 0 f.
    rewrite succ_eq_pos //; have := ulp_ge_0 beta fexp f; lra.
  have E : succ beta fexp f = - pred beta fexp (- f).
    by rewrite -{1}[f]Ropp_involutive succ_opp.
  have Ff' := generic_format_opp beta fexp f Ff.
  have fpos' : 0 < - f by lra.
  have := gap_dn (- f) Ff' fpos'.
  rewrite ulp_opp E; lra.
have gapDN : / 2 * ulp f <= f - pred beta fexp f.
  have [fpos|fneg] := Rle_lt_dec 0 f.
    have fpos' : 0 < f by lra.
    have := gap_dn f Ff fpos'; lra.
  have E2 : pred beta fexp f = - succ beta fexp (- f).
    by rewrite -{1}[f]Ropp_involutive pred_opp.
  rewrite E2 succ_eq_pos; last lra.
  by rewrite ulp_opp; have := ulp_ge_0 beta fexp f; lra.
(* [|d| < 1/4 ulp f] keeps [f + d] strictly on [f]'s side of both midpoints.   *)
have /Rabs_lt_inv[Hd1 Hd2] := Hd.
apply: Rle_antisym.
  apply: round_N_le_midp => //; lra.
apply: round_N_ge_midp => //; lra.
Qed.

(* Helper A (paper's "if [x0+x1] is a FP number ..."): a float plus a tail    *)
(* below half its ulp rounds back to the float.                               *)
Lemma RoundTW_add_float x0 x1 x2 :
  format x0 -> format x1 -> Rabs x1 < ulp x0 -> format (x0 + x1) ->
  Rabs x2 < ulp x1 -> RND (x0 + x1 + x2) = x0 + x1.
Proof.
move=> Fx0 Fx1 Hx1 Fs Hx2.
have x0n0 : x0 <> 0.
  by move=> x00; move: Hx1; rewrite x00 ulp_FLX_0; have := Rabs_pos x1; lra.
have x1n0 : x1 <> 0.
  by move=> x10; move: Hx2; rewrite x10 ulp_FLX_0; have := Rabs_pos x2; lra.
have sn0 : x0 + x1 <> 0.
  move=> s0.
  have Ex : x1 = - x0 by lra.
  have := bpow_mag_le beta x0 x0n0.
  move: Hx1; rewrite Ex Rabs_Ropp ulp_neq_0 // /cexp /fexp => Hx1'.
  have : pow (mag beta x0 - p) <= pow (mag beta x0 - 1) by apply: bpow_le; lia.
  lra.
(* [|x1| < ulp x0] pins [x1] at least [p] binades below [x0] ...              *)
have M1 : (mag beta x1 <= mag beta x0 - p)%Z.
  have H := bpow_mag_le beta x1 x1n0.
  move: Hx1; rewrite ulp_neq_0 // /cexp /fexp => Hx1'.
  have HH : pow (mag beta x1 - 1) < pow (mag beta x0 - p) by lra.
  by move/lt_bpow: HH; lia.
(* ... while [x0 + x1] loses at most one binade off [x0].                     *)
have M2 : (mag beta x0 - 1 <= mag beta (x0 + x1))%Z.
  have Hlow : pow (mag beta x0 - 2) <= Rabs (x0 + x1).
    have H0 := bpow_mag_le beta x0 x0n0.
    have Ht := Rabs_triang_inv x0 (- x1).
    rewrite Rabs_Ropp in Ht.
    have Hs : Rabs (x0 - - x1) = Rabs (x0 + x1) by congr Rabs; ring.
    rewrite Hs in Ht.
    move: Hx1; rewrite ulp_neq_0 // /cexp /fexp => Hx1'.
    have Hp2b : pow (mag beta x0 - p) <= pow (mag beta x0 - 2)
      by apply: bpow_le; lia.
    have Hhalf : pow (mag beta x0 - 2) + pow (mag beta x0 - 2) <=
                 pow (mag beta x0 - 1).
      have -> : (mag beta x0 - 1 = (mag beta x0 - 2) + 1)%Z by lia.
      rewrite bpow_plus pow1E /=; lra.
    lra.
  have := mag_gt_bpow beta (x0 + x1) (mag beta x0 - 2) Hlow; lia.
(* Hence [|x2| < ulp x1 <= 2u . ulp(x0+x1) < 1/4 ulp(x0+x1)] ([p >= 3]).       *)
have Pm4 : pow (-2) = / 4.
  by rewrite (bpow_opp beta 2) (_ : pow 2 = 4) //;
     rewrite /= IZR_Zpower_pos /=; lra.
have Hb : Rabs x2 < / 4 * ulp (x0 + x1).
  have U1 : ulp x1 = pow (mag beta x1 - p) by rewrite ulp_neq_0 // /cexp /fexp.
  have Us : ulp (x0 + x1) = pow (mag beta (x0 + x1) - p)
    by rewrite ulp_neq_0 // /cexp /fexp.
  have step1 : ulp x1 <= pow (mag beta x0 - 2 * p)
    by rewrite U1; apply: bpow_le; lia.
  have step2 : pow (mag beta x0 - 2 * p) <= / 4 * ulp (x0 + x1).
    rewrite Us -Pm4 -bpow_plus; apply: bpow_le; lia.
  lra.
by apply: RN_add_lt_quarter.
Qed.

(* Helpers B/C (non-midpoint and midpoint), unified: a point strictly inside  *)
(* the rounding cell of a float [f] -- i.e. strictly between the two midpoints *)
(* [(pred f + f)/2] and [(f + succ f)/2] -- rounds to [f].  In the assembly    *)
(* the divisibility of [x0+x1] and its cell boundaries by [ulp x1] gives the   *)
(* two strict inequalities for [x = x0 + x1 + x2].                             *)
Lemma RN_between_midp (f x : R) :
  format f -> (pred beta fexp f + f) / 2 < x -> x < (f + succ beta fexp f) / 2 ->
  RND x = f.
Proof.
move=> Ff Hlo Hhi.
apply: Rle_antisym.
  by apply: round_N_le_midp.
by apply: round_N_ge_midp => //; lra.
Qed.

(* Two distinct multiples of a grid [pow k] are at least [pow k] apart.  This  *)
(* is the quantitative heart of the assembly: [x0+x1], its two neighbouring    *)
(* floats and their midpoint are all multiples of [ulp x1], so the tail [x2]   *)
(* (with [|x2| < ulp x1]) can never carry [x0+x1] across a rounding boundary.  *)
Lemma is_imul_gap (a b : R) (k : Z) :
  is_imul a (pow k) -> is_imul b (pow k) -> a <> b -> pow k <= Rabs (a - b).
Proof.
move=> Ha Hb Hab.
apply: is_imul_pow_le_abs; first by apply: is_imul_minus.
by move=> H0; apply: Hab; lra.
Qed.

(* --- Scale/sign normalisation for the tie-detector ------------------------ *)
(* Every ingredient of [RoundTW_cond] is invariant under scaling by a power of *)
(* two and under global sign change, so we may normalise [x0] into [[1,2)].    *)

Lemma is_midpoint_scale x e : is_midpoint (x * pow e) <-> is_midpoint x.
Proof.
rewrite /is_midpoint !round_bpow_FLX //.
have := bpow_gt_0 beta e; nra.
Qed.

Lemma is_midpoint_opp x : is_midpoint (- x) <-> is_midpoint x.
Proof.
rewrite /is_midpoint round_DN_opp round_UP_opp.
by split; lra.
Qed.

(* Normalised core of the tie-detector: [x0] scaled into [[1,2)].  This is the *)
(* delicate part (needs [p >= 4]): [x0+2x1] exact forces [x1] to a few concrete *)
(* multiples of [u], and [star] separates the genuine midpoints from the single *)
(* non-midpoint special case [x0 = 1+2u, x1 = -3/2 u].                          *)
Lemma RoundTW_cond_norm y0 y1 :
  format y0 -> format y1 -> 1 <= y0 < 2 -> Rabs y1 < ulp y0 ->
  ~ format (y0 + y1) ->
  (RND (y0 + 2 * y1) = y0 + 2 * y1 /\
   RND (- (3 / 2 * u - 2 * (u * u)) * y0) <> y1) <-> is_midpoint (y0 + y1).
Proof.
move=> Fy0 Fy1 y0rng Hy1 NFm.
(* [y0 in [1,2)] so [ulp y0 = 2u]; [y1] is a nonzero float with [|y1| < 2u].   *)
have u_pos : 0 < u by rewrite uE; apply: bpow_gt_0.
have magy0 : mag beta y0 = 1%Z :> Z.
  apply: mag_unique_pos.
  have -> : pow (1 - 1) = 1 by rewrite (_ : (1 - 1 = 0)%Z) //.
  by rewrite pow1E /=; lra.
have Uy0 : ulp y0 = 2 * u.
  rewrite ulp_neq_0; last lra.
  rewrite /cexp /fexp magy0 uE (_ : (1 - p = - p + 1)%Z); last lia.
  by rewrite bpow_plus pow1E /=; lra.
have y1n0 : y1 <> 0 by move=> y10; apply: NFm; rewrite y10 Rplus_0_r.
move: Hy1; rewrite Uy0 => Hy1.
have y0mul : is_imul y0 (2 * u).
  by have := format_imul_cexp Fy0; rewrite -ulp_neq_0; [rewrite Uy0 | lra].
have twou_pos : 0 < 2 * u by lra.
(* KEY REDUCTION: [x0+2x1] exact or [x0+x1] a midpoint both force [2 y1] to be *)
(* a multiple of [u]; with [|y1| < 2u] this pins [y1] to six concrete values.  *)
have y1vals : is_imul (2 * y1) u ->
   y1 = u \/ y1 = - u \/ y1 = u / 2 \/ y1 = - (u / 2) \/
   y1 = 3 * u / 2 \/ y1 = - (3 * u / 2).
  move=> [k Hk].
  have kabs : Rabs (IZR k) < 4.
    have H4 : Rabs (IZR k * u) < 4 * u.
      rewrite -Hk Rabs_mult (Rabs_pos_eq 2); last lra.
      by move: Hy1; lra.
    by move: H4; rewrite Rabs_mult (Rabs_pos_eq u); last lra; nra.
  have kn0 : k <> 0%Z by move=> k0; move: Hk; rewrite k0 /= Rmult_0_l => H;
    apply: y1n0; lra.
  have kr : (k = -3 \/ k = -2 \/ k = -1 \/ k = 1 \/ k = 2 \/ k = 3)%Z.
    move/Rabs_lt_inv: kabs => [H1 H2].
    suff : (-4 < k < 4)%Z by lia.
    by split; apply: lt_IZR; rewrite ?opp_IZR /=; lra.
  move: Hk; case: kr => [->|[->|[->|[->|[->|->]]]]] Hk.
  - by right; right; right; right; right; lra.
  - by right; left; lra.
  - by right; right; right; left; lra.
  - by right; right; left; lra.
  - by left; lra.
  - by right; right; right; right; left; lra.
have pm1 : pow (-1) = / 2.
  have h1 : pow 1 = 2 by rewrite pow1E /=; lra.
  have h2 : pow (-1) * pow 1 = 1.
    rewrite -bpow_plus.
    by have -> : (-1 + 1 = 0)%Z by [].
  by move: h2; rewrite h1; lra.
have four_u : 4 * u < / 2.
  rewrite uE (_ : 4 = pow 2); last by rewrite /= IZR_Zpower_pos /=; lra.
  rewrite -bpow_plus.
  apply: Rlt_le_trans (_ : pow (-1) <= _); last by rewrite pm1; lra.
  by apply: bpow_lt; lia.
have imul_u : forall z, format z -> / 2 < z -> is_imul z u.
  move=> z Fz Hz.
  have magz : (- p <= cexp z)%Z.
    rewrite /cexp /fexp; suff : (-1 < mag beta z)%Z by lia.
    apply: mag_gt_bpow; rewrite Rabs_pos_eq; last lra.
    by rewrite pm1; lra.
  by rewrite uE; apply: (is_imul_pow_le (format_imul_cexp Fz) magz).
have /Rabs_lt_inv[Hy1a Hy1b] := Hy1.
have y2low : / 2 < y0 + 2 * y1 by lra.
have y1low : / 2 < y0 + y1 by lra.
have imul2_e : RND (y0 + 2 * y1) = y0 + 2 * y1 -> is_imul (2 * y1) u.
  move=> Hex.
  have F2 : format (y0 + 2 * y1) by rewrite -Hex; exact: generic_format_round.
  have I2 := imul_u _ F2 y2low.
  have I0 : is_imul y0 u by apply: imul_u => //; lra.
  have := is_imul_minus I2 I0.
  by have -> : y0 + 2 * y1 - y0 = 2 * y1 by ring.
have ImP : forall j : Z, is_imul (pow j) (pow j) by move=> j; exists 1%Z; lra.
have magm_nn : (0 <= mag beta (y0 + y1))%Z.
  suff : (-1 < mag beta (y0 + y1))%Z by lia.
  apply: mag_gt_bpow; rewrite Rabs_pos_eq; last lra.
  by rewrite pm1; lra.
have imul2_m : is_midpoint (y0 + y1) -> is_imul (2 * y1) u.
  move=> Hmid.
  have IRU : is_imul (RU (y0 + y1)) u.
    apply: imul_u; first exact: generic_format_round.
    by have [_ H2] := round_DN_UP_le beta (y0 + y1) (FLX_exp_valid p); lra.
  have Iulp : is_imul (ulp (y0 + y1)) u.
    rewrite ulp_neq_0; last lra.
    by rewrite uE; apply: (is_imul_pow_le (ImP _)); rewrite /cexp /fexp; lia.
  have IRD : is_imul (RD (y0 + y1)) u.
    have HU := @round_UP_DN_ulp beta fexp (y0 + y1) NFm.
    have -> : RD (y0 + y1) = RU (y0 + y1) - ulp (y0 + y1) by lra.
    exact: is_imul_minus.
  have I2y0 : is_imul (2 * y0) u.
    have y0h : / 2 < y0 by lra.
    have [z Hz] := imul_u _ Fy0 y0h.
    by exists (2 * z)%Z; rewrite mult_IZR Hz; ring.
  have := is_imul_minus (is_imul_add IRD IRU) I2y0.
  by have -> : RD (y0 + y1) + RU (y0 + y1) - 2 * y0 = 2 * y1
    by move: Hmid; rewrite /is_midpoint; lra.
(* --- Small reusable facts for the six-way case analysis (u = 2^-p) --------- *)
have u_lt : u < 3 / 4 by lra.
have Kpos : 0 < 3 / 2 * u - 2 * (u * u) by nra.
have succy0 : succ beta fexp y0 = y0 + 2 * u by rewrite succ_eq_pos ?Uy0 //; lra.
have starneg : RND (- (3 / 2 * u - 2 * (u * u)) * y0) <= 0.
  rewrite -(round_0 beta fexp rnd); apply: round_le; nra.
have ulp12 : forall v : R, 1 <= v < 2 -> ulp v = 2 * u.
  move=> v vrng.
  rewrite ulp_neq_0; last lra.
  rewrite /cexp /fexp (_ : mag beta v = 1%Z :> Z); last first.
    apply: mag_unique_pos.
    have -> : pow (1 - 1) = 1 by rewrite (_ : (1 - 1 = 0)%Z) //.
    by rewrite pow1E /=; lra.
  by rewrite uE (_ : (1 - p = - p + 1)%Z); [rewrite bpow_plus pow1E /=; lra | lia].
have ulphalf : forall v : R, / 2 <= v < 1 -> ulp v = u.
  move=> v vrng.
  rewrite ulp_neq_0; last lra.
  rewrite /cexp /fexp (_ : mag beta v = 0%Z :> Z); last first.
    apply: mag_unique_pos.
    have -> : pow (0 - 1) = / 2 by rewrite (_ : (0 - 1 = -1)%Z) // pm1.
    by rewrite (_ : pow 0 = 1) //; lra.
  by rewrite uE; congr bpow; lia.
have imul12 : forall w : R, format w -> 1 <= w < 2 -> is_imul w (2 * u).
  move=> w Fw wrng.
  by have := format_imul_cexp Fw; rewrite -ulp_neq_0; [rewrite ulp12 | lra].
have not_imul_u_2u : ~ is_imul u (2 * u).
  move=> [k Hk].
  have : IZR (2 * k) = 1 by rewrite mult_IZR; nra.
  by move/eq_IZR; lia.
have midchar : forall g m : R, format g -> g < m < succ beta fexp g ->
    (is_midpoint m <-> 2 * m = g + succ beta fexp g).
  move=> g m Fg [Hgm Hmsg].
  rewrite /is_midpoint.
  have -> : RD m = g by apply: round_DN_eq => //; lra.
  have -> : RU m = succ beta fexp g.
    by apply: round_UP_eq; [exact: generic_format_succ | rewrite pred_succ //; lra].
  by [].
have fmt12 : forall w, is_imul w (2 * u) -> 1 <= w < 2 -> format w.
  move=> w Iw wrng.
  have I' : is_imul w (pow (1 - p)).
    rewrite (_ : pow (1 - p) = 2 * u) //.
    by rewrite uE (_ : (1 - p = - p + 1)%Z); [rewrite bpow_plus pow1E /=; lra | lia].
  apply: (imul_cexp_format I').
  rewrite /cexp /fexp (_ : mag beta w = 1%Z :> Z); first by lia.
  apply: mag_unique_pos.
  have -> : pow (1 - 1) = 1 by rewrite (_ : (1 - 1 = 0)%Z) //.
  by rewrite pow1E /=; lra.
have fmt_half : forall w, is_imul w u -> / 2 <= w < 1 -> format w.
  move=> w Iw wrng.
  have I' : is_imul w (pow (- p)) by rewrite -uE.
  apply: (imul_cexp_format I').
  rewrite /cexp /fexp (_ : mag beta w = 0%Z :> Z); first by lia.
  apply: mag_unique_pos.
  have -> : pow (0 - 1) = / 2 by rewrite (_ : (0 - 1 = -1)%Z) // pm1.
  by rewrite (_ : pow 0 = 1) //; lra.
have I2u : is_imul (2 * u) (2 * u) by exists 1%Z; lra.
have Iu : is_imul u u by exists 1%Z; lra.
have F1 : format (1 : R).
  by rewrite (_ : (1 : R) = pow 0) //; apply: generic_format_bpow; rewrite /fexp; lia.
have I1u : is_imul 1 u by apply: imul_u => //; lra.
have two_u_pow : 2 * u = pow (1 - p).
  by rewrite uE (_ : (1 - p = - p + 1)%Z); [rewrite bpow_plus pow1E /=; lra | lia].
have I1_2u : is_imul 1 (2 * u) by apply: imul12; [exact F1 | lra].
have mid_fmt : forall m, format m -> is_midpoint m.
  by move=> m Fm; rewrite /is_midpoint !round_generic //; ring.
have y0ge1 : y0 = 1 \/ 1 + 2 * u <= y0.
  have [->|y0gt1] := Req_dec y0 1; [by left | right].
  have Id : is_imul (y0 - 1) (pow (1 - p)) by rewrite -two_u_pow; apply: is_imul_minus.
  have Hd0 : y0 - 1 <> 0 by lra.
  by move: (is_imul_pow_le_abs Id Hd0); rewrite -two_u_pow (Rabs_pos_eq (y0 - 1)); lra.
have I2_2u : is_imul 2 (2 * u).
  rewrite two_u_pow (_ : (2 : R) = pow 1); last by rewrite pow1E /=; lra.
  by apply: (is_imul_pow_le (ImP _)); lia.
have y0le : y0 <= 2 - 2 * u.
  have Id : is_imul (2 - y0) (pow (1 - p)) by rewrite -two_u_pow; apply: is_imul_minus.
  have Hd0 : 2 - y0 <> 0 by lra.
  by move: (is_imul_pow_le_abs Id Hd0); rewrite -two_u_pow (Rabs_pos_eq (2 - y0)); lra.
have nfmt_off : forall d, ~ is_imul d (2 * u) -> 1 <= y0 + d < 2 -> ~ format (y0 + d).
  move=> d Hd drng Fyd.
  apply: Hd.
  have I := is_imul_minus (imul12 _ Fyd drng) y0mul.
  have -> : d = y0 + d - y0 by ring.
  exact: I.
have kill : forall d, ~ is_imul d (2 * u) -> 1 <= y0 + d < 2 ->
    RND (y0 + d) = y0 + d -> False.
  move=> d Hd drng Hexd.
  apply: (nfmt_off d Hd drng).
  by rewrite -Hexd; exact: generic_format_round.
have nimul_u : ~ is_imul u (2 * u) := not_imul_u_2u.
have nimul_nu : ~ is_imul (- u) (2 * u).
  by move=> H; apply: nimul_u; have := is_imul_opp H; rewrite Ropp_involutive.
have nimul_3u : ~ is_imul (3 * u) (2 * u).
  move=> [k Hk].
  have : IZR (2 * k) = 3 by rewrite mult_IZR; nra.
  by move/eq_IZR; lia.
have nimul_n3u : ~ is_imul (- (3 * u)) (2 * u).
  by move=> H; apply: nimul_3u; have := is_imul_opp H; rewrite Ropp_involutive.
(* The [3u/2] neighbourhood on the [2 u^2] grid: needed for the special case   *)
(* and for the "star" magnitude bound.                                         *)
have uu_pos : 0 < u * u by nra.
have u3_pos : 0 < u * u * u by nra.
have twouu_pow : 2 * (u * u) = pow (1 - 2 * p).
  rewrite (_ : u * u = pow (- (2 * p))); last by rewrite uE -bpow_plus; congr bpow; lia.
  rewrite (_ : (1 - 2 * p = 1 + - (2 * p))%Z); last lia.
  by rewrite bpow_plus pow1E /=; lra.
have up1_pow : u / 2 = pow (- p - 1).
  by rewrite uE (_ : (- p - 1 = - p + -1)%Z); [rewrite bpow_plus pm1; lra | lia].
have ulp_u2 : forall w, u <= w < 2 * u -> ulp w = 2 * (u * u).
  move=> w wr.
  rewrite ulp_neq_0; last lra.
  rewrite /cexp /fexp (_ : mag beta w = (1 - p)%Z :> Z); last first.
    apply: mag_unique_pos.
    rewrite (_ : pow (1 - p - 1) = u); last by rewrite uE; congr bpow; lia.
    rewrite (_ : pow (1 - p) = 2 * u); [lra |].
    by rewrite uE (_ : (1 - p = - p + 1)%Z); [rewrite bpow_plus pow1E /=; lra | lia].
  rewrite (_ : (1 - p - p = 1 - 2 * p)%Z); last lia.
  by rewrite twouu_pow.
have fmt_u2 : forall w, is_imul w (2 * (u * u)) -> u <= w < 2 * u -> format w.
  move=> w Iw wr.
  have I' : is_imul w (pow (1 - 2 * p)) by rewrite -twouu_pow.
  apply: (imul_cexp_format I').
  rewrite /cexp /fexp (_ : mag beta w = (1 - p)%Z :> Z); first lia.
  apply: mag_unique_pos.
  rewrite (_ : pow (1 - p - 1) = u); last by rewrite uE; congr bpow; lia.
  rewrite (_ : pow (1 - p) = 2 * u); [lra |].
  by rewrite uE (_ : (1 - p = - p + 1)%Z); [rewrite bpow_plus pow1E /=; lra | lia].
have I32p : is_imul (3 * u / 2) (pow (- p - 1)) by rewrite -up1_pow; exists 3%Z; lra.
have I32_2uu : is_imul (3 * u / 2) (2 * (u * u)).
  by rewrite twouu_pow; apply: (is_imul_pow_le I32p); lia.
have I2uu2 : is_imul (2 * (u * u)) (2 * (u * u)) by exists 1%Z; lra.
have F32m : format (3 * u / 2 - 2 * (u * u)).
  apply: fmt_u2.
    by apply: is_imul_minus; [exact: I32_2uu | exact: I2uu2].
  by nra.
have F32n : format (- (3 * u / 2))
  by apply: generic_format_opp; apply: fmt_u2; [exact: I32_2uu | nra].
have ulp32 : ulp (3 * u / 2) = 2 * (u * u) by apply: ulp_u2; nra.
have succ32m : succ beta fexp (3 * u / 2 - 2 * (u * u)) = 3 * u / 2
  by rewrite succ_eq_pos ?ulp_u2; nra.
have pred32 : pred beta fexp (3 * u / 2) = 3 * u / 2 - 2 * (u * u)
  by rewrite -{1}succ32m pred_succ.
have succ32 : succ beta fexp (3 * u / 2) = 3 * u / 2 + 2 * (u * u)
  by rewrite succ_eq_pos ?ulp32; nra.
have succn : succ beta fexp (- (3 * u / 2)) = - (3 * u / 2) + 2 * (u * u)
  by rewrite succ_opp pred32; lra.
have predn : pred beta fexp (- (3 * u / 2)) = - (3 * u / 2) - 2 * (u * u)
  by rewrite pred_opp succ32; lra.
(* [RN(-(3/2u-2u^2) y0)] is at most [-3u/2 + 2u^2] (round monotonicity from     *)
(* [y0 >= 1], the value at [y0 = 1] being the float [-(3u/2 - 2u^2)]).          *)
have Kval1 : RND (- (3 / 2 * u - 2 * (u * u)) * 1) = - (3 * u / 2) + 2 * (u * u).
  rewrite Rmult_1_r.
  have -> : - (3 / 2 * u - 2 * (u * u)) = - (3 * u / 2 - 2 * (u * u)) by field.
  rewrite round_generic; first by field.
  by apply: generic_format_opp.
have starlt : RND (- (3 / 2 * u - 2 * (u * u)) * y0) <= - (3 * u / 2) + 2 * (u * u).
  rewrite -Kval1; apply: round_le; nra.
split.
- (* FORWARD: exact /\ star <> y1 -> is_midpoint (y0 + y1) *)
  move=> [Hex Hstar].
  have Him := imul2_e Hex.
  case: (y1vals Him) => [Hy1E|[Hy1E|[Hy1E|[Hy1E|[Hy1E|Hy1E]]]]];
    rewrite Hy1E in Hex Hstar *.
  + have Hpos : y0 < y0 + u < succ beta fexp y0 by rewrite succy0; lra.
    by apply/(midchar _ _ Fy0 Hpos); rewrite succy0; lra.
  + case: y0ge1 => [y0eq1 | y0ge].
      rewrite y0eq1; apply: mid_fmt.
      have -> : 1 + - u = 1 - u by ring.
      by apply: fmt_half; [apply: is_imul_minus | move: four_u; lra].
    have Fg : format (y0 - 2 * u) by apply: fmt12; [apply: is_imul_minus | lra].
    have Hsg : succ beta fexp (y0 - 2 * u) = y0 by rewrite succ_eq_pos ?ulp12; lra.
    have Hpos : y0 - 2 * u < y0 + - u < succ beta fexp (y0 - 2 * u)
      by rewrite Hsg; lra.
    by apply/(midchar _ _ Fg Hpos); rewrite Hsg; lra.
  + exfalso; move: Hex; rewrite (_ : 2 * (u / 2) = u); last by field.
    by move=> Hexu; apply: (kill u nimul_u); [lra | exact Hexu].
  + case: y0ge1 => [y0eq1 | y0ge].
      rewrite y0eq1.
      have F1u : format (1 - u)
        by apply: fmt_half; [apply: is_imul_minus | move: four_u; lra].
      have Hsg : succ beta fexp (1 - u) = 1 by rewrite succ_eq_pos ?ulphalf; lra.
      have Hpos : 1 - u < 1 + - (u / 2) < succ beta fexp (1 - u) by rewrite Hsg; lra.
      by apply/(midchar _ _ F1u Hpos); rewrite Hsg; lra.
    exfalso; move: Hex; rewrite (_ : 2 * - (u / 2) = - u); last by field.
    by move=> Hexu; apply: (kill (- u) nimul_nu); [lra | exact Hexu].
  + have pow2E : pow 2 = 4 by rewrite /= IZR_Zpower_pos /=; lra.
    have [Hlt | Hge] := Rlt_le_dec (y0 + 3 * u) 2.
      exfalso; move: Hex; rewrite (_ : 2 * (3 * u / 2) = 3 * u); last by field.
      by move=> Hexu; apply: (kill (3 * u) nimul_3u); [lra | exact Hexu].
    have y0e : y0 = 2 - 2 * u.
      have Id : is_imul (2 - 2 * u - y0) (pow (1 - p)).
        rewrite -two_u_pow; apply: is_imul_minus; last exact: y0mul.
        by apply: is_imul_minus; [exact: I2_2u | exact: I2u].
      have [Heq|Hne] := Req_dec (2 - 2 * u - y0) 0; first lra.
      by move: (is_imul_pow_le_abs Id Hne); rewrite -two_u_pow Rabs_pos_eq; lra.
    exfalso.
    move: Hex; rewrite (_ : 2 * (3 * u / 2) = 3 * u); last by field.
    rewrite y0e (_ : 2 - 2 * u + 3 * u = 2 + u); last by ring.
    move=> Hex2.
    have F2u : format (2 + u) by rewrite -Hex2; exact: generic_format_round.
    have twou4_pow : 4 * u = pow (2 - p).
      by rewrite uE (_ : (2 - p = - p + 2)%Z); [rewrite bpow_plus pow2E; lra | lia].
    have ulp2u : ulp (2 + u) = 4 * u.
      rewrite ulp_neq_0; last lra.
      rewrite /cexp /fexp (_ : mag beta (2 + u) = 2%Z :> Z); last first.
        apply: mag_unique_pos.
        have -> : pow (2 - 1) = 2 by rewrite (_ : (2 - 1 = 1)%Z) // pow1E /=; lra.
        by rewrite pow2E; lra.
      by rewrite -twou4_pow.
    have I2u4 : is_imul (2 + u) (4 * u).
      by have := format_imul_cexp F2u; rewrite -ulp_neq_0; [rewrite ulp2u | lra].
    have I2_4u : is_imul 2 (4 * u).
      rewrite twou4_pow (_ : (2 : R) = pow 1); last by rewrite pow1E /=; lra.
      by apply: (is_imul_pow_le (ImP _)); lia.
    have nimul_u_4u : ~ is_imul u (4 * u).
      move=> [k Hk]; have : IZR (4 * k) = 1 by rewrite mult_IZR; nra.
      by move/eq_IZR; lia.
    apply: nimul_u_4u.
    have := is_imul_minus I2u4 I2_4u.
    by have -> : 2 + u - 2 = u by ring.
  + case: y0ge1 => [y0eq1 | y0ge].
      rewrite y0eq1.
      have I2uu : is_imul (2 * u) u by exists 2%Z; lra.
      have F12u : format (1 - 2 * u).
        by apply: fmt_half;
          [apply: is_imul_minus; [exact: I1u | exact: I2uu] | move: four_u; lra].
      have Hsg : succ beta fexp (1 - 2 * u) = 1 - u
        by rewrite succ_eq_pos ?ulphalf; lra.
      have Hpos : 1 - 2 * u < 1 + - (3 * u / 2) < succ beta fexp (1 - 2 * u)
        by rewrite Hsg; lra.
      by apply/(midchar _ _ F12u Hpos); rewrite Hsg; lra.
    have [y0e2 | y0ne] := Req_dec y0 (1 + 2 * u); last first.
      have y0ge4 : 1 + 4 * u <= y0.
        have I12u : is_imul (1 + 2 * u) (2 * u)
          by apply: is_imul_add; [exact: I1_2u | exact: I2u].
        have Id : is_imul (y0 - (1 + 2 * u)) (pow (1 - p)).
          by rewrite -two_u_pow; apply: is_imul_minus; [exact: y0mul | exact: I12u].
        have Hd0 : y0 - (1 + 2 * u) <> 0 by lra.
        by move: (is_imul_pow_le_abs Id Hd0);
           rewrite -two_u_pow (Rabs_pos_eq (y0 - (1 + 2 * u))); lra.
      exfalso; move: Hex; rewrite (_ : 2 * - (3 * u / 2) = - (3 * u)); last by field.
      by move=> Hexu; apply: (kill (- (3 * u)) nimul_n3u); [lra | exact Hexu].
    exfalso; apply: Hstar; rewrite y0e2.
    have -> : - (3 / 2 * u - 2 * (u * u)) * (1 + 2 * u) =
              - (3 * u / 2) + (- (u * u) + 4 * (u * u * u)) by field.
    apply: RN_between_midp => //.
      rewrite predn; lra.
    by rewrite succn; nra.
(* BACKWARD: is_midpoint (y0 + y1) -> exact /\ star <> y1 *)
move=> Hmid.
have Him := imul2_m Hmid.
case: (y1vals Him) => [Hy1E|[Hy1E|[Hy1E|[Hy1E|[Hy1E|Hy1E]]]]];
  rewrite Hy1E in Hmid NFm *.
- split; last by move=> H; move: starneg; rewrite H; lra.
  have F : format (y0 + 2 * u) by rewrite -succy0; apply: generic_format_succ.
  by apply: round_generic.
- case: y0ge1 => [y0eq1 | y0ge].
    exfalso; apply: NFm; rewrite y0eq1.
    have -> : 1 + - u = 1 - u by ring.
    by apply: fmt_half; [apply: is_imul_minus | move: four_u; lra].
  split; last by move=> H; move: starlt; rewrite H; nra.
  have F : format (y0 - 2 * u) by apply: fmt12; [apply: is_imul_minus | lra].
  have -> : y0 + 2 * - u = y0 - 2 * u by ring.
  by apply: round_generic.
- have Hpos : y0 < y0 + u / 2 < succ beta fexp y0 by rewrite succy0; lra.
  by move: Hmid; rewrite (midchar _ _ Fy0 Hpos) succy0; lra.
- case: y0ge1 => [y0eq1 | y0ge]; last first.
    have Fg : format (y0 - 2 * u) by apply: fmt12; [apply: is_imul_minus | lra].
    have Hsg : succ beta fexp (y0 - 2 * u) = y0 by rewrite succ_eq_pos ?ulp12; lra.
    have Hpos : y0 - 2 * u < y0 + - (u / 2) < succ beta fexp (y0 - 2 * u)
      by rewrite Hsg; lra.
    by move: Hmid; rewrite (midchar _ _ Fg Hpos) Hsg; lra.
  split; last by move=> H; move: starlt; rewrite H; nra.
  have F : format (1 - u)
    by apply: fmt_half; [apply: is_imul_minus | move: four_u; lra].
  by rewrite y0eq1 (_ : 1 + 2 * - (u / 2) = 1 - u); [apply: round_generic | field].
- have Hpos : y0 < y0 + 3 * u / 2 < succ beta fexp y0 by rewrite succy0; lra.
  by move: Hmid; rewrite (midchar _ _ Fy0 Hpos) succy0; lra.
- case: y0ge1 => [y0eq1 | y0ge]; last first.
    have Fg : format (y0 - 2 * u) by apply: fmt12; [apply: is_imul_minus | lra].
    have Hsg : succ beta fexp (y0 - 2 * u) = y0 by rewrite succ_eq_pos ?ulp12; lra.
    have Hpos : y0 - 2 * u < y0 + - (3 * u / 2) < succ beta fexp (y0 - 2 * u)
      by rewrite Hsg; lra.
    by move: Hmid; rewrite (midchar _ _ Fg Hpos) Hsg; lra.
  split; last first.
    rewrite y0eq1 Kval1.
    by move=> H; move: uu_pos; nra.
  have I3u_u : is_imul (3 * u) u by exists 3%Z; lra.
  have F13u : format (1 - 3 * u)
    by apply: fmt_half; [apply: is_imul_minus | move: four_u; lra].
  by rewrite y0eq1 (_ : 1 + 2 * - (3 * u / 2) = 1 - 3 * u); [apply: round_generic | field].
Qed.

Lemma RoundTW_cond x0 x1 :
  format x0 -> format x1 -> (x1 = 0 \/ Rabs x1 < ulp x0) -> ~ format (x0 + x1) ->
  (RND (x0 + 2 * x1) = x0 + 2 * x1 /\
   RND (- (3 / 2 * u - 2 * (u * u)) * x0) <> x1) <-> is_midpoint (x0 + x1).
Proof.
have RNo := @RN_sym p beta choice choice_sym.
pose K := (3 / 2 * u - 2 * (u * u)).
(* the whole statement is invariant under scaling by a power of two ... *)
have scaleG : forall y0 y1 t,
   ((RND (y0 * pow t + 2 * (y1 * pow t)) = y0 * pow t + 2 * (y1 * pow t) /\
     RND (- K * (y0 * pow t)) <> y1 * pow t) <->
        is_midpoint (y0 * pow t + y1 * pow t))
   <->
   ((RND (y0 + 2 * y1) = y0 + 2 * y1 /\ RND (- K * y0) <> y1) <->
     is_midpoint (y0 + y1)).
  move=> a b t; have pe := bpow_gt_0 beta t.
  have -> : a * pow t + 2 * (b * pow t) = (a + 2 * b) * pow t by ring.
  have -> : - K * (a * pow t) = (- K * a) * pow t by ring.
  have -> : a * pow t + b * pow t = (a + b) * pow t by ring.
  rewrite !round_bpow_FLX // is_midpoint_scale.
  have e1 : (RND (a + 2 * b) * pow t = (a + 2 * b) * pow t) <->
            (RND (a + 2 * b) = a + 2 * b) by split=> H; nra.
  have e2 : (RND (- K * a) * pow t <> b * pow t) <-> (RND (- K * a) <> b)
    by split=> H HH; apply: H; nra.
  by rewrite e1 e2.
(* ... and under global sign change. *)
have signG : forall y0 y1,
   ((RND (- y0 + 2 * (- y1)) = - y0 + 2 * (- y1) /\
     RND (- K * (- y0)) <> - y1) <-> is_midpoint (- y0 + - y1))
   <->
   ((RND (y0 + 2 * y1) = y0 + 2 * y1 /\ RND (- K * y0) <> y1) <->
      is_midpoint (y0 + y1)).
  move=> a b.
  have -> : - a + 2 * (- b) = -(a + 2 * b) by ring.
  have -> : - K * (- a) = -(- K * a) by ring.
  have -> : - a + - b = -(a + b) by ring.
  rewrite !RNo is_midpoint_opp.
  have e1 : (- RND (a + 2 * b) = -(a + 2 * b)) <->
            (RND (a + 2 * b) = a + 2 * b) by split; lra.
  have e2 : (- RND (- K * a) <> - b) <-> (RND (- K * a) <> b)
    by split=> H HH; apply: H; lra.
  by rewrite e1 e2.
have Fscale : forall z k, format z -> format (z * pow k).
  move=> z k Fz.
  have <- : RND (z * pow k) = z * pow k by rewrite round_bpow_FLX // round_generic.
  exact: generic_format_round.
have ulp_scale : forall z k, z <> 0 -> ulp (z * pow k) = ulp z * pow k.
  move=> z k zn0.
  have zkn0 : z * pow k <> 0 by have := bpow_gt_0 beta k; nra.
  rewrite (ulp_neq_0 _ _ _ zkn0) (ulp_neq_0 _ _ _ zn0) /cexp mag_mult_bpow //
          /fexp -bpow_plus; congr bpow; lia.
rewrite -/K.
(* normalise a positive [a0] into [[1,2)] and apply [RoundTW_cond_norm] *)
have norm : forall a0 a1, format a0 -> format a1 -> 0 < a0 -> a1 <> 0 ->
    Rabs a1 < ulp a0 -> ~ format (a0 + a1) ->
    (RND (a0 + 2 * a1) = a0 + 2 * a1 /\ RND (- K * a0) <> a1) <->
       is_midpoint (a0 + a1).
  move=> a0 a1 Fa0 Fa1 a0pos a1n0 Ha1 NFa.
  have a0n0 : a0 <> 0 by lra.
  pose t := (1 - mag beta a0)%Z.
  rewrite -(scaleG a0 a1 t).
  have pt := bpow_gt_0 beta t.
  have magat : mag beta (a0 * pow t) = 1%Z :> Z by rewrite mag_mult_bpow // /t; lia.
  have y0rng : 1 <= a0 * pow t < 2.
    have an0 : a0 * pow t <> 0 by nra.
    have Hle := bpow_mag_le beta (a0 * pow t) an0.
    have Hgt := bpow_mag_gt beta (a0 * pow t).
    move: Hle Hgt; rewrite magat Rabs_pos_eq; last nra.
    have -> : (1 - 1 = 0)%Z by lia.
    have -> : pow 0 = 1 by []; rewrite pow1E /=; lra.
  apply: RoundTW_cond_norm.
  - exact: Fscale.
  - exact: Fscale.
  - exact: y0rng.
  - rewrite ulp_scale // Rabs_mult (Rabs_pos_eq (pow t)); last lra.
    by nra.
  - have -> : a0 * pow t + a1 * pow t = (a0 + a1) * pow t by ring.
    move=> Fbad; apply: NFa.
    have H := Fscale ((a0 + a1) * pow t) (- t)%Z Fbad.
    move: H; rewrite Rmult_assoc -bpow_plus Z.add_opp_diag_r.
    have -> : pow 0 = 1 by []; by rewrite Rmult_1_r.
move=> Fx0 Fx1 H1 NFm.
have x1n0 : x1 <> 0 by move=> x10; apply: NFm; rewrite x10 Rplus_0_r.
have Hx1 : Rabs x1 < ulp x0 by case: H1 => // x10; case: x1n0.
have x0n0 : x0 <> 0.
  by move=> x00; move: Hx1; rewrite x00 ulp_FLX_0; have := Rabs_pos x1; lra.
have [x0pos | x0lt] := Rlt_le_dec 0 x0; first exact: norm.
have x0neg : 0 < - x0 by lra.
rewrite -signG.
apply: norm.
- exact: generic_format_opp.
- exact: generic_format_opp.
- exact: x0neg.
- by move=> H; apply: x1n0; lra.
- by rewrite Rabs_Ropp ulp_opp.
- rewrite -Ropp_plus_distr => Fbad; apply: NFm.
  by have := generic_format_opp _ _ _ Fbad; rewrite Ropp_involutive.
Qed.

(* Paper Theorem 5. *)
Lemma RoundTW_correct x0 x1 x2 :
  isTW (TWR x0 x1 x2) -> RoundTW x0 x1 x2 = RND (x0 + x1 + x2).
Proof.
move=> tw.
have [Fx0 Fx1 Fx2 H1 H2] := tw.
rewrite /RoundTW.
(* Degenerate limbs: [x1 = 0] forces [x2 = 0] and every branch is [round x0].  *)
have [x1z | x1nz] := H1.
  move: H2; rewrite x1z ulp_FLX_0 => H2'.
  have x2z : x2 = 0 by case: H2' => // H; have := Rabs_pos x2; lra.
  rewrite x2z !Rplus_0_r Rmult_0_r Rplus_0_r.
  have Rx0 : RND x0 = x0 by apply: round_generic.
  have RUx0 : RU x0 = x0 by apply: round_generic.
  have RDx0 : RD x0 = x0 by apply: round_generic.
  by repeat case: Req_EM_T => *; repeat case: Rlt_le_dec => *;
     rewrite ?Rx0 ?RUx0 ?RDx0.
have [x1eq0 | x1n0] := Req_dec x1 0.
  move: H2; rewrite x1eq0 ulp_FLX_0 => H2'.
  have x2z : x2 = 0 by case: H2' => // H; have := Rabs_pos x2; lra.
  rewrite x2z !Rplus_0_r Rmult_0_r Rplus_0_r.
  have Rx0 : RND x0 = x0 by apply: round_generic.
  have RUx0 : RU x0 = x0 by apply: round_generic.
  have RDx0 : RD x0 = x0 by apply: round_generic.
  by repeat case: Req_EM_T => *; repeat case: Rlt_le_dec => *;
     rewrite ?Rx0 ?RUx0 ?RDx0.
have Hx2 : Rabs x2 < ulp x1.
  case: H2 => [->|//]; rewrite Rabs_R0; exact: ulp_gt_0.
(* Case 1: [x0+x1] is a float -- Helper A, and every branch returns it.        *)
have [Es | Ens] := Req_EM_T (RND (x0 + x1)) (x0 + x1).
  have Fm : format (x0 + x1) by rewrite -Es; exact: generic_format_round.
  have Hrhs : RND (x0 + x1 + x2) = x0 + x1 by apply: RoundTW_add_float.
  rewrite Hrhs.
  have RUm : RU (x0 + x1) = x0 + x1 by apply: round_generic.
  have RDm : RD (x0 + x1) = x0 + x1 by apply: round_generic.
  by repeat case: Req_EM_T => *; repeat case: Rlt_le_dec => *;
     rewrite ?Es ?RUm ?RDm.
(* Case 2: [x0+x1] not a float.  Set up the divisibility infrastructure: all   *)
(* of [x0+x1], its two neighbouring floats [RD]/[RU] and their midpoint are     *)
(* multiples of [ulp x1], while [|x2| < ulp x1].                                *)
have NFm : ~ format (x0 + x1).
  by move=> Ffm; apply: Ens; apply: round_generic.
have x0n0 : x0 <> 0.
  by move=> x00; move: x1nz; rewrite x00 ulp_FLX_0; have := Rabs_pos x1; lra.
have M1 : (mag beta x1 <= mag beta x0 - p)%Z.
  have H := bpow_mag_le beta x1 x1n0.
  move: x1nz; rewrite ulp_neq_0 // /cexp /fexp => Hx1'.
  have HH : pow (mag beta x1 - 1) < pow (mag beta x0 - p) by lra.
  by move/lt_bpow: HH; lia.
have M2 : (mag beta x0 - 1 <= mag beta (x0 + x1))%Z.
  have Hlow : pow (mag beta x0 - 2) <= Rabs (x0 + x1).
    have H0 := bpow_mag_le beta x0 x0n0.
    have Ht := Rabs_triang_inv x0 (- x1).
    rewrite Rabs_Ropp in Ht.
    have Hs : Rabs (x0 - - x1) = Rabs (x0 + x1) by congr Rabs; ring.
    rewrite Hs in Ht.
    move: x1nz; rewrite ulp_neq_0 // /cexp /fexp => Hx1'.
    have Hp2b : pow (mag beta x0 - p) <= pow (mag beta x0 - 2)
      by apply: bpow_le; lia.
    have Hhalf : pow (mag beta x0 - 2) + pow (mag beta x0 - 2) <=
                 pow (mag beta x0 - 1).
      have -> : (mag beta x0 - 1 = (mag beta x0 - 2) + 1)%Z by lia.
      rewrite bpow_plus pow1E /=; lra.
    lra.
  have := mag_gt_bpow beta (x0 + x1) (mag beta x0 - 2) Hlow; lia.
have Le10 : (cexp x1 <= cexp x0)%Z by rewrite /cexp /fexp; lia.
have Imm : is_imul (x0 + x1) (pow (cexp x1)).
  apply: is_imul_add; last exact: format_imul_cexp.
  by apply: is_imul_pow_le (format_imul_cexp Fx0) _.
have Img : is_imul (RD (x0 + x1)) (pow (cexp x1))
  by apply: is_imul_pow_round.
have Imu : is_imul (RU (x0 + x1)) (pow (cexp x1))
  by apply: is_imul_pow_round.
have Fg : format (RD (x0 + x1)) by apply: generic_format_round.
have Fu : format (RU (x0 + x1)) by apply: generic_format_round.
have Vf : Valid_exp fexp by apply: FLX_exp_valid.
have [Hgm Hmu] := @round_DN_UP_lt beta fexp Vf (x0 + x1) NFm.
have DUulp : RU (x0 + x1) = RD (x0 + x1) + ulp (x0 + x1)
  by apply: round_UP_DN_ulp.
have mn0 : x0 + x1 <> 0.
  by move=> H0; apply: NFm; rewrite H0; exact: generic_format_0.
have Uk : ulp x1 = pow (cexp x1) by rewrite ulp_neq_0.
have ImPrefl : forall j : Z, is_imul (pow j) (pow j).
  by move=> j; exists 1%Z; lra.
have Le_mid : (cexp x1 <= cexp (x0 + x1) - 1)%Z by rewrite /cexp /fexp; lia.
have gap_gm : pow (cexp x1) <= (x0 + x1) - RD (x0 + x1).
  have := is_imul_gap Imm Img (Rgt_not_eq _ _ Hgm).
  by rewrite Rabs_pos_eq; lra.
have gap_mu : pow (cexp x1) <= RU (x0 + x1) - (x0 + x1).
  have := is_imul_gap Imu Imm (Rgt_not_eq _ _ Hmu).
  by rewrite Rabs_pos_eq; lra.
have SG : succ beta fexp (RD (x0 + x1)) = RU (x0 + x1) by apply: succ_DN_eq_UP.
have PU : pred beta fexp (RU (x0 + x1)) = RD (x0 + x1) by apply: pred_UP_eq_DN.
have predg_le : pred beta fexp (RD (x0 + x1)) <= RD (x0 + x1) by apply: pred_le_id.
have succu_ge : RU (x0 + x1) <= succ beta fexp (RU (x0 + x1)) by apply: succ_ge_id.
have half_ulp : / 2 * ulp (x0 + x1) = pow (cexp (x0 + x1) - 1).
  rewrite ulp_neq_0 //.
  have -> : pow (cexp (x0 + x1)) = pow 1 * pow (cexp (x0 + x1) - 1).
    by rewrite -bpow_plus; congr bpow; lia.
  rewrite pow1E /=; lra.
have Immid : is_imul ((RD (x0 + x1) + RU (x0 + x1)) / 2) (pow (cexp x1)).
  have -> : (RD (x0 + x1) + RU (x0 + x1)) / 2 =
            RD (x0 + x1) + / 2 * ulp (x0 + x1) by rewrite DUulp; field.
  apply: is_imul_add => //.
  by rewrite half_ulp; apply: is_imul_pow_le (ImPrefl _) Le_mid.
have Hx2b : x2 < pow (cexp x1) by rewrite -Uk; move: (Rle_abs x2); lra.
have Hx2a : - pow (cexp x1) < x2.
  by rewrite -Uk; move: (Rabs_le_inv x2 (ulp x1));
     have := Rle_abs (- x2); rewrite Rabs_Ropp; lra.
have Npt : RND (x0 + x1) = RD (x0 + x1) \/ RND (x0 + x1) = RU (x0 + x1).
  by apply: generic_N_pt_DN_or_UP => //; apply: round_N_pt.
have gap_mid : x0 + x1 <> (RD (x0 + x1) + RU (x0 + x1)) / 2 ->
               pow (cexp x1) <=
               Rabs (x0 + x1 - (RD (x0 + x1) + RU (x0 + x1)) / 2).
  by move=> Hne; apply: is_imul_gap.
(* The three rounding outcomes for [x0+x1+x2], via [RN_between_midp].           *)
have Hmid_pos : x0 + x1 = (RD (x0 + x1) + RU (x0 + x1)) / 2 -> 0 < x2 ->
                RND (x0 + x1 + x2) = RU (x0 + x1).
  move=> Hmeq Hpos; apply: RN_between_midp => //.
    by rewrite PU; lra.
  by move: gap_mu Hx2b succu_ge; lra.
have Hmid_neg : x0 + x1 = (RD (x0 + x1) + RU (x0 + x1)) / 2 -> x2 < 0 ->
                RND (x0 + x1 + x2) = RD (x0 + x1).
  move=> Hmeq Hneg; apply: RN_between_midp => //.
    by move: predg_le gap_gm Hx2a; lra.
  by rewrite SG; lra.
have Hnotmid_eq : x0 + x1 <> (RD (x0 + x1) + RU (x0 + x1)) / 2 ->
                  RND (x0 + x1 + x2) = RND (x0 + x1).
  move=> Hne; have Hg := gap_mid Hne.
  have [Hlt | Hgt] := Rdichotomy _ _ Hne.
    have Hmlt : (RD (x0 + x1) + RU (x0 + x1)) / 2 - (x0 + x1) >= pow (cexp x1).
      by move: Hg; rewrite Rabs_left; lra.
    have RD_eq : RND (x0 + x1) = RD (x0 + x1).
      apply: Rle_antisym; last first.
        by case: Npt => ->; move: DUulp (ulp_ge_0 beta fexp (x0 + x1)); lra.
      by apply: round_N_le_midp => //; rewrite SG; lra.
    rewrite RD_eq; apply: RN_between_midp => //.
      by move: predg_le gap_gm Hx2a; lra.
    by rewrite SG; move: Hmlt Hx2b; lra.
  have Hmgt : (x0 + x1) - (RD (x0 + x1) + RU (x0 + x1)) / 2 >= pow (cexp x1).
    by move: Hg; rewrite Rabs_pos_eq; lra.
  have RU_eq : RND (x0 + x1) = RU (x0 + x1).
    apply: Rle_antisym.
      by case: Npt => ->; move: DUulp (ulp_ge_0 beta fexp (x0 + x1)); lra.
    by apply: round_N_ge_midp => //; rewrite PU; lra.
  rewrite RU_eq; apply: RN_between_midp => //.
    by rewrite PU; move: Hmgt Hx2a; lra.
  by move: gap_mu Hx2b succu_ge; lra.
(* Tie-detector: the algorithm's first condition is false iff [x0+x1] is a      *)
(* midpoint; assemble the branches accordingly.                                 *)
have Hcond := RoundTW_cond Fx0 Fx1 H1 NFm.
have [Hmid | Hnmid] := Req_dec (2 * (x0 + x1)) (RD (x0 + x1) + RU (x0 + x1)).
  have Hmeq : x0 + x1 = (RD (x0 + x1) + RU (x0 + x1)) / 2 by lra.
  have [C1 C2] := proj2 Hcond Hmid.
  case: (Req_EM_T (RND (x0 + 2 * x1)) (x0 + 2 * x1)) => [e1 | ne1]; last first.
    by case: (ne1 C1).
  case: (Req_EM_T (RND (- (3 / 2 * u - 2 * (u * u)) * x0)) x1) => [e2 | ne2].
    by case: (C2 e2).
  rewrite /=.
  case: (Rlt_le_dec 0 x2) => [Hpos | Hle].
    by rewrite (Hmid_pos Hmeq Hpos).
  case: (Rlt_le_dec x2 0) => [Hneg | Hge].
    by rewrite (Hmid_neg Hmeq Hneg).
  rewrite /=.
  have Ez : x2 = 0 by lra.
  by rewrite Ez Rplus_0_r.
have Hne : x0 + x1 <> (RD (x0 + x1) + RU (x0 + x1)) / 2 by lra.
rewrite (Hnotmid_eq Hne).
case: (Req_EM_T (RND (x0 + 2 * x1)) (x0 + 2 * x1)) => [e1 | ne1];
    last by rewrite /=.
case: (Req_EM_T (RND (- (3 / 2 * u - 2 * (u * u)) * x0)) x1) => [e2 | ne2].
  by rewrite /=.
rewrite /=.
by exfalso; apply: Hnmid; exact: (proj1 Hcond (conj e1 ne2)).
Qed.

(* ===========================================================================*)
(*  Algorithm 8: TWSum -- the sum of two triple-word numbers.                 *)
(* ===========================================================================*)
Definition TWSum (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
  let: TWR y0 y1 y2 := y in
  let z := Merge [:: x0; x1; x2] [:: y0; y1; y2] in
  let e := vecSum z in
  match vsebK 3 e with
  | [:: r0, r1, r2 & _] => TWR r0 r1 r2
  | [:: r0; r1]         => TWR r0 r1 0
  | [:: r0]             => TWR r0 0 0
  | [::]                => TWR 0 0 0
  end.

(* The relative-error coefficient of the "Ensure" clause of Alg. 8.           *)
Local Notation errc := (2 * (u * u * u) + 42 / 10 * (u * u * u * u)).

(* ===========================================================================*)
(*  Correctness: TWSum returns a triple-word number (Theorem 6).              *)
(*                                                                            *)
(*  Sketch (paper, Section 5.1, p >= 4):                                      *)
(*   - Merge keeps floating-point numbers, magnitude-sorted, with the         *)
(*     pairwise-ulp separation, i.e. the hypotheses of Theorem 6.             *)
(*   - [VSEB (VecSum ...)] is P-nonoverlapping with the same exact sum         *)
(*     ([vecSum_vseb_Pnonoverlap], paper Theorem 6), so its first three        *)
(*     terms form a TW number.                                                *)
(*                                                                            *)
(*  NB.  The intermediate "[VecSum ...] is F-nonoverlapping" is NOT used any   *)
(*  more, because it is FALSE for merges of near-equal odd leaders (see the    *)
(*  note in [VecSum.v] and the machine-checked [CEThm6.v]).  Theorem 6 is a    *)
(*  DIRECT statement about [VSEB (VecSum ...)]: VSEB repairs the overlap that  *)
(*  VecSum can leave behind.                                                   *)
(* ===========================================================================*)
(* Paper Theorem 6 (the statement [TWSum] actually needs).  For at most SIX    *)
(* magnitude-sorted, pairwise-ulp-separated floating-point inputs (with no     *)
(* underflow: nonzero terms normal), running VecSum and then VSEB yields a     *)
(* P-nonoverlapping sequence.  Round-to-nearest must be TIES-TO-EVEN.          *)
(*                                                                            *)
(* This is DIRECT: the raw [vecSum l] is generally NOT F-nonoverlapping        *)
(* ([CEThm6.v]), so it does NOT factor through [vecSum_Fnonoverlap]/           *)
(* [vseb_Pnonoverlap].  The proof (paper Section 5.1, undetailed there) uses   *)
(* the run-bound [vecSum_run_ufp] and error-bound [vecSum_err_ufp], then a     *)
(* case study on how VSEB's Fast2Sum steps collapse the (few) overlaps VecSum  *)

Lemma TWSum_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (TWSum x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2 => Hceven Hx Hy.
pose z := Merge [:: x0; x1; x2] [:: y0; y1; y2].
pose e := vecSum z.
(* Merge keeps the six terms floating-point ...                               *)
have Hz_format : {in z, forall t, format t}.
  apply: format_Merge.
    by case: Hx => x0F x1F x2F _ _ z1; rewrite !inE => /or3P[] /eqP->.
  by case: Hy => y0F y1F y2F _ _ z1; rewrite !inE => /or3P[] /eqP->.
(* ... magnitude-sorted ...                                                   *)
have Hz_sorted : sorted_mag z.
  apply: Merge_sorted_mag; first by apply: isTW_sorted_mag Hx.
  by apply: isTW_sorted_mag Hy.
(* ... and pairwise ulp-separated: the hypotheses of Theorem 6.               *)
have Hz_ulp : pairwise_ulp z.
  apply: Merge_pairwise_ulp=> [u|u||].
  - by rewrite !inE => /or3P[] /eqP->; case: Hx.
  - by rewrite !inE => /or3P[] /eqP->; case: Hy.
  - by apply: isTW_Pnonoverlap Hx.
  by apply: isTW_Pnonoverlap Hy.
(* VecSum preserves the exact sum (Algorithm 4 is error-free).                *)
have He_sum : sumR e = sumR z by apply: vecSum_sum.
(* VSEB(3) of VecSum is P-nonoverlapping.  The chain (see the lemmas above):  *)
(*   - [vecSum_Fnonoverlap] (Thm 1): [e = vecSum z] is F-nonoverlapping (its  *)
(*     [.1]), using [Hz_format], [Hz_sorted] and [Hz_ulp];                    *)
(*   - [vseb_Pnonoverlap]  (Thm 2): hence [vseb e] is P-nonoverlapping (its   *)
(*     [.1]); its side conditions are [size e = 6 <= p + 1] and the formatness*)
(*     [format_vecSum Hz_format];                                             *)
(*   - [Pnonoverlap_take]         : [vsebK 3 e = take 3 (vseb e)] is a prefix,*)
(*     so it is P-nonoverlapping too.                                         *)
(* i.e. once the three lemmas are proved this closes with (writing [Hsz] for  *)
(* [Z.of_nat (size e) <= p + 1] -- here [size e = 6] as VecSum and Merge      *)
(* preserve length, and [p = 53])                                             *)
(*   [rewrite /vsebK; apply: Pnonoverlap_take;                                *)
(*    apply: (vseb_Pnonoverlap Hsz (format_vecSum Hz_format)                  *)
(*             (vecSum_Fnonoverlap Hz_format Hz_sorted Hz_ulp).1).1].         *)
have Hr_nonover : Pnonoverlap (vsebK 3 e).
  apply/Pnonoverlap_take.
  rewrite /e; apply: vecSum_vseb_Pnonoverlap.
  - exact: Hceven.
  - by rewrite /z size_Merge.
  - exact: Hz_format.
  - exact: Hz_sorted.
  exact: Hz_ulp.
(* and its terms are floating-point numbers.                                  *)
have Hr_format : {in vsebK 3 e, forall t, format t}.
  by apply/format_vsebK/format_vecSum.
(* Reading the first three terms off the P-nonoverlapping sequence            *)
(* yields a triple-word number.  Case on the (<=3, zero-padded) list [vsebK   *)
(* 3 e]; formats come from [Hr_format], the strict ulp bounds from either     *)
(* [Hr_nonover] (real terms) or [0 < ulp _] (the padding zeros).              *)
rewrite /TWSum -/z -/e.
move: Hr_nonover Hr_format; case: (vsebK 3 e) => [|r0 [|r1 [|r2 tl]]] Hno Hfmt.
- by split; try exact: generic_format_0; left.
- by split; try exact: generic_format_0;
     [apply: Hfmt; rewrite !inE eqxx | left | left].
- by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
           | exact: generic_format_0 | apply: (Hno 0%N) | left].
by split; [apply: Hfmt; rewrite !inE eqxx | apply: Hfmt; rewrite !inE eqxx orbT
         | apply: Hfmt; rewrite !inE eqxx !orbT | apply: (Hno 0%N)
         | apply: (Hno 1%N)].
Qed.

(* A float is at most [(2 - 2u) ufp] of itself (max-mantissa bound).  Holds   *)
(* also at 0 and in the subnormal range, so no no-underflow hypothesis.       *)
Lemma TWSum_error x y :
  ties_to_even choice ->
  isTW x -> isTW y ->
  Rabs (TWval (TWSum x y) - (TWval x + TWval y)) <=
     errc * Rabs (TWval x + TWval y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2 => Hceven Hx Hy.
pose z := Merge [:: x0; x1; x2] [:: y0; y1; y2].
pose e := vecSum z.
(* Merge is a permutation: it preserves the exact sum.                        *)
have Hmerge_sum : sumR z = (x0 + x1 + x2) + (y0 + y1 + y2).
  by rewrite Merge_sumR /=; lra.
(* VecSum is error-free.                                                      *)
have Hvec_sum : sumR e = sumR z.
  rewrite vecSum_sum //; apply: format_Merge; first by apply: (isTW_format Hx).
  by apply: isTW_format Hy.

(* VSEB is error-free on the full output.                                     *)
have Hvseb_sum : sumR (vseb e) = sumR e.
  apply: vseb_sum; apply: format_vecSum; apply: format_Merge.
  - by apply: (isTW_format Hx).
  by apply: isTW_format Hy.
(* Truncating to the first three terms loses at most errc of the sum          *)
(* (Theorem 3 with k = 3).                                                    *)
have Htrunc :
  Rabs (sumR (vseb e) - sumR (vsebK 3 e)) <= errc * Rabs (sumR e).
  have Hzf : {in z, forall t, format t}.
    apply: format_Merge.
      by case: Hx => x0F x1F x2F _ _ t; rewrite !inE => /or3P[] /eqP->.
    by case: Hy => y0F y1F y2F _ _ t; rewrite !inE => /or3P[] /eqP->.
  have Hzs : sorted_mag z.
    by apply: Merge_sorted_mag;
      [apply: isTW_sorted_mag Hx | apply: isTW_sorted_mag Hy].
  have Hzu : pairwise_ulp z.
    apply: Merge_pairwise_ulp => [t|t||].
    - by rewrite !inE => /or3P[] /eqP->; case: Hx.
    - by rewrite !inE => /or3P[] /eqP->; case: Hy.
    - by apply: isTW_Pnonoverlap Hx.
    by apply: isTW_Pnonoverlap Hy.
  have Fe : {in e, forall t, format t} by apply: format_vecSum.
  have Py : Pnonoverlap (vseb e).
    rewrite /e; apply: vecSum_vseb_Pnonoverlap.
    - exact: Hceven.
    - by rewrite /z size_Merge.
    - exact: Hzf.
    - exact: Hzs.
    exact: Hzu.
  have Fy : {in vseb e, forall t, format t} by apply: format_vseb.
  set y := vseb e.
  have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 y).
    by rewrite /vsebK -/y -{1}(cat_take_drop 3 y) sumR_cat; ring.
  rewrite Hsplit -Hvseb_sum -/y.
  (* The dropped tail is bounded by Theorem 3 (general k), at k = 3.          *)
  have Hu0 : 0 < u by rewrite uE; apply: bpow_gt_0.
  have Hu64 : u <= / 64.
    rewrite uE; have -> : (/ 64 = bpow beta (-6))%R
      by rewrite /= /Z.pow_pos /=; lra.
    by apply: bpow_le; lia.
  have -> : 2 * (u * u * u) + 42 / 10 * (u * u * u * u) =
            2 * u ^ 3 + 42 / 10 * u ^ 3.+1 by rewrite /=; ring.
  case: (Req_dec (nth 0 y 0) 0) => [Hy0z|Hy0n]; last first.
    by apply: Pnonoverlap_truncate_error.
  have H1 := nth_step_zero Py Fy Hy0z.
  have H2 := nth_step_zero Py Fy H1.
  have H3 := nth_step_zero Py Fy H2.
  have -> : sumR (drop 3 y) = 0.
    apply: small_head_zero; [by apply: Pnonoverlap_drop
      | by move=> t /mem_drop; apply: Fy | by rewrite nth_drop addn0].
  rewrite Rabs_R0; apply: Rmult_le_pos; last exact: Rabs_pos.
  have H4 : 0 <= u ^ 3 by apply: pow_le; lra.
  have H5 : 0 <= u ^ 3.+1 by apply: pow_le; lra.
  lra.
(* The result of TWSum is exactly the value of those three terms.  [vsebK 3 e]*)
(* has length <= 3 (it is a [take 3]); TWSum reads its (zero-padded) first    *)
(* three entries, whose sum is exactly [sumR (vsebK 3 e)].                    *)
have Hres : TWval (TWSum (TWR x0 x1 x2) (TWR y0 y1 y2)) = sumR (vsebK 3 e).
  have Hsz : (size (vsebK 3 e) <= 3)%N.
    rewrite /vsebK size_take; case: ifP => [_|Hf]; first by [].
    by rewrite leqNgt Hf.
  rewrite /TWSum -/z -/e.
  move: Hsz; case: (vsebK 3 e) => [|r0 [|r1 [|r2 [|r3 l]]]] /= H; try by lra.
  by exfalso; move/leP: H; lia.
(* Chaining the equalities and the truncation bound concludes.  Both operands *)
(* sum to [sumR (vseb e)] (Merge/VecSum/VSEB preserve the sum), the result is *)
(* [sumR (vsebK 3 e)] (Hres), so the error is the dropped tail bounded by     *)
(* [Htrunc].                                                                  *)
have E1 : TWval (TWR x0 x1 x2) + TWval (TWR y0 y1 y2) = sumR (vseb e).
  by rewrite /= Hvseb_sum Hvec_sum Hmerge_sum.
rewrite Hres E1 Rabs_minus_sym {2}Hvseb_sum.
exact: Htrunc.
Qed.


End SecTWSum.
