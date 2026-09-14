From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz.
From Flocq Require Import Operations Mult_error Plus_error.
From Coquelicot Require Import Coquelicot.
From Interval Require Import  Tactic.
Require Import Nmore Rmore Fmore Rstruct MULTmore.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Prelim.

Variable beta : radix.
Variables p : Z.
Hypothesis Hp2: Z.lt 1 p.

Let p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Defined.

Variable rnd : R -> Z.
Hypothesis valid_rnd : Valid_rnd rnd.

Variable fexp : Z -> Z.
Hypothesis valid_fexp : Valid_exp fexp.

Local Notation format := (generic_format beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation cexp := (cexp beta fexp).
Local Notation pow e := (bpow beta e).

Lemma round_le_l x y : format x -> x <= y -> x <= RND y.
Proof.
move=> xF xLy.
have <- : RND x = x by apply: round_generic.
by apply: round_le.
Qed.

Lemma round_le_r x y : format y -> x <= y -> RND x <= y.
Proof.
move=> yF xLy.
have <- : RND y = y by apply: round_generic.
by apply: round_le.
Qed.

Lemma Rabs_round_le_l f x : format f -> f <= Rabs x -> f <= Rabs (RND x).
Proof.
move=> fF.
have [x_pos|x_neg] := Rle_lt_dec 0 x.
  rewrite !Rabs_pos_eq //; last first.
    by apply : round_le_l => //; apply: generic_format_0.
  by apply: round_le_l.
rewrite !Rabs_left1; try lra; last first.
  by apply : round_le_r; [apply: generic_format_0 | lra].
suff : x <= - f -> RND x <= - f by lra.
by apply/round_le_r/generic_format_opp.
Qed.

Lemma Rabs_round_le_r f x : format f -> Rabs x <= f -> Rabs (RND x) <= f.
Proof.
move=> eLm.
have [x_pos|x_neg] := Rle_lt_dec 0 x.
  rewrite !Rabs_pos_eq //; last first.
    by apply : round_le_l => //; apply: generic_format_0.
  by apply: round_le_r.
rewrite !Rabs_left1; try lra; last first.
  by apply : round_le_r; [apply: generic_format_0 | lra].
suff : - f <= x ->  - f <= RND x by lra.
by apply/round_le_l/generic_format_opp.
Qed.

Local Notation ulp := (ulp beta fexp).

Lemma format_pos_le_ex_add_ulp f1 f2 :
  Monotone_exp fexp -> format f1 -> format f2 -> 0 < f1 <= f2 ->
  exists k, f2 = f1 + IZR k * ulp f1.
Proof.
move=> Mfexp Hf1 Hf2 f1Lf2.
red in Hf1.
have cf1Lcf2 : (cexp f1 <= cexp f2)%Z.
  have [cf2Lcf1|//] := Z_lt_le_dec (cexp f2) (cexp f1).
  suff : f2 < f1 by lra.
  by apply: lt_cexp_pos cf2Lcf1 => //; lra.
rewrite ulp_neq_0; last by lra.
rewrite {1}Hf1 {1}Hf2 /F2R /=.
set x1 := Ztrunc _; set x2 := Ztrunc _.
exists (x1 * beta ^ (cexp f2 - cexp f1) - x2)%Z.
rewrite minus_IZR mult_IZR IZR_Zpower; last by lia.
rewrite Rmult_minus_distr_r Rmult_assoc -bpow_plus -[bpow _ _]/(pow _).
rewrite -[bpow _ (cexp f1)]/(pow _).
rewrite -[bpow _ (_ + _)]/(pow _).
have -> : (cexp f2 - cexp f1 + cexp f1 = cexp f2)%Z by lia.
by lra.
Qed.

Local Notation R_UP := (round beta fexp Zceil).

Lemma round_up_lt x1 y1 : x1 < y1 -> x1 < R_UP y1.
Proof.
move=> x1Ly1.
apply: Rlt_le_trans x1Ly1 _.
case:(@round_DN_UP_le beta y1 fexp);lra.
Qed.

Local Notation R_DN := (round beta fexp Zfloor).

Lemma round_down_gt x1 y1 : x1 < y1 -> R_DN x1 < y1.
Proof.
move=> x1Ly1.
apply: Rle_lt_trans _ x1Ly1.
case:(@round_DN_UP_le beta  x1 fexp);lra.
Qed.

End Prelim.

Section FlxPrelim.

Variable beta : radix.
Variables p : Z.
Hypothesis Hp2: Z.lt 1 p.
Local Instance p_gt_0 : Prec_gt_0 p.
now apply Z.lt_trans with (2 := Hp2).
Qed.

Variable rnd : R -> Z.
Hypothesis valid_rnd : Valid_rnd rnd.

Local Notation FLX := (FLX_exp p).
Local Notation format := (generic_format beta FLX).
Local Notation RND := (round beta FLX rnd).
Local Notation pow e := (bpow beta e).
Local Notation float := (float beta).
Local Notation cexp := (cexp beta FLX).
Local Notation mant := (scaled_mantissa beta FLX).

Lemma format1_FLX : format 1.
Proof.
have -> : 1 = F2R (Float beta 1 0) by rewrite /F2R /=; lra.
apply: generic_format_FLX.
apply: FLX_spec (refl_equal _) _ => /=.
have -> : (1 = beta ^ 0)%Z by [].
by apply: Zpower_lt; lia. 
Qed.

Lemma pow_Rpower z : pow z = Rpower (IZR beta) (IZR z).
Proof. 
rewrite bpow_powerRZ powerRZ_Rpower //.
apply: IZR_lt.
apply: radix_gt_0.
Qed.

Lemma Rabs_round_ge_bpow x e : pow e <= Rabs x -> pow e <= Rabs (RND x).
Proof.
move=> eLx.
apply/Rabs_round_le_l => //.
by apply: format_pow.
Qed.

Lemma Rabs_round_le_bpow x e :  Rabs x <= pow e -> Rabs (RND x) <= pow e.
Proof.
move=> eLx.
by apply/Rabs_round_le_r => //; apply: format_pow.
Qed.

Lemma relative_error_FLT_alt x : x <> 0 -> (RND x) < Rabs x * (1 + pow (1 - p)).
Proof.
move=> x_neq0.
suff : Rabs (RND x - x) < pow (- p + 1) * Rabs x.
  have -> : (1 - p = -p + 1)%Z by lia.
  by split_Rabs; lra.
by apply: relative_error_FLX => //; lia.
Qed.

Lemma is_imul_bound_pow_format e x :
  pow e <= Rabs x -> format x -> is_imul x (pow (e - p + 1)).
Proof.
move=> eLx x_F.
have [->|x_neq0] := Req_dec x 0;  first by exists 0%Z; lra.
apply/(is_imul_format_mag_pow x_F)=>//.
apply/(Z.le_trans _ (mag beta x - p)%Z); last by  (rewrite /FLX; lia).
suff: (e + 1 <= mag beta x )%Z by lia.
apply/mag_ge_bpow.
by have->: (e + 1 -1 = e)%Z by lia.
Qed.

Theorem cexp_bpow_FLX  x e (xne0: x <> R0) : cexp (x * pow e) = (cexp x + e)%Z.
Proof. 
rewrite /cexp mag_mult_bpow //.
by rewrite /FLX; lia.
Qed.

Theorem mant_bpow_FLX x e : mant (x * pow e) = mant x.
Proof.
case: (Req_dec x 0) => [->|Zx]; first by rewrite Rmult_0_l.
rewrite /scaled_mantissa /cexp /FLX.
rewrite mag_mult_bpow //.
rewrite !Rmult_assoc.
apply: Rmult_eq_compat_l.
rewrite -bpow_plus.
congr bpow; lia.
Qed.

Theorem round_bpow_FLX x e : RND (x * pow e) = (RND x * pow e)%R.
Proof.
case: (Req_dec x 0) => [->|Zx] ; first by rewrite Rmult_0_l round_0 Rmult_0_l.
by rewrite /round /F2R /= mant_bpow_FLX // 
           cexp_bpow_FLX // bpow_plus Rmult_assoc.
Qed.

(* This proof should be reworked *)
Lemma imul_format z e b : 
  is_imul z (pow e) -> Rabs z <= b -> b <= (pow (p + e))
  -> format z.
Proof.
move=> [k ->] zB bB.
have {b zB bB}zLp : Rabs (IZR k * pow e) <= pow (p + e) by lra.
have {}zLp : Rabs (IZR k) <= pow p.
  apply: (Rmult_le_reg_r (pow e)); first by apply: bpow_gt_0.
  rewrite -bpow_plus -[pow e]Rabs_pos_eq; first by rewrite -Rabs_mult.
  by apply: bpow_ge_0.
have [E|D] := Req_dec (Rabs (IZR k)) (pow p).
  have[->|->] : IZR k = pow p \/ IZR k = - pow p by split_Rabs; lra.
    by rewrite -bpow_plus; apply: format_pow; lia.
  rewrite -Ropp_mult_distr_l; apply: generic_format_opp.
  by rewrite -bpow_plus; apply: format_pow; lia.
have -> : IZR k * pow e = Float beta k e by [].
apply: generic_format_FLX.
apply: FLX_spec (refl_equal _) _ => //=.
apply/lt_IZR.
by rewrite abs_IZR IZR_Zpower; [lra|lia].
Qed.

Lemma is_imul_format_round_gt_0 x y : 
  0 < x -> is_imul x (pow y) -> 0 < RND x.
Proof.
move=> x_gt_0 Mx.
pose f := Float beta 1 y.
have Ff : format f.
  apply: generic_format_FLX.
  apply: FLX_spec (refl_equal _) _ => //=.
  have -> : (1 = beta ^ 0)%Z by [].
  by apply: Zpower_lt; lia.
apply: Rlt_le_trans (_ : f <= _).
  by rewrite /F2R /= Rmult_1_l; apply: bpow_gt_0.
apply: round_le_l => //.
rewrite /F2R /= Rmult_1_l.
have [k kE] := Mx; rewrite kE in x_gt_0 *.
have F2 : 0 < pow y by apply: bpow_gt_0.
have F3 : (0 < k)%Z by apply: lt_IZR; nra.
have/IZR_le : (1 <= k)%Z by lia.
nra.
Qed.

Lemma round_ge_0 x : 0 <= x -> 0 <= RND x.
Proof.
move=> x_ge_0.
have <- : RND 0 = 0 by rewrite round_0.
by apply: round_le.
Qed.

Local Notation u := (u p beta).
Local Notation u_gt_0 := (u_gt_0 p beta).

Lemma relative_error_is_imul_eps x y :
  is_imul x (pow y) ->
  exists eps : R, Rabs eps < 2 * u /\ RND x = x * (1 + eps).
Proof.
move=> [z ->].
pose x1 := Float beta z y.
have <- : F2R x1 = IZR z * pow y by [].
have -> : 2 * u = pow (- p + 1).
  have -> : (- p + 1 = 1 - p)%Z by lia.
  by rewrite /u; lra.
by apply: relative_error_FLX_ex; lia.
Qed.

Lemma relative_error_is_imul_eps_bound x y eps :
  is_imul x (pow y) -> (x = 0 -> eps = 0) ->
  RND x = x * (1 + eps) -> Rabs eps < 2 * u.
Proof.
move=> Mxy Heps HRN.
have [x_eq0|x_neq0] := Req_dec x 0.
  rewrite Heps // Rabs_R0.
  by have := u_gt_0; lra.
have [eps1 [Heps1 H1eps1]] := relative_error_is_imul_eps Mxy.
by have <- : eps1 = eps by nra.
Qed.

Inductive dwR := DWR (xh : R) (xl : R).

Definition formatDw (d : dwR) :=
  let: (DWR xh xl) := d in 
  [/\ format xh, format xl & RND (xh + xl) = xh].

Definition exactMul (a b : R) : dwR := 
  let h := RND (a * b) in 
  let l := RND (a * b - h) in DWR h l.
  
Lemma exactMul0l b : exactMul 0 b = DWR 0 0.
Proof. by rewrite /exactMul !(Rsimp01, round_0). Qed.

Lemma exactMul0r a : exactMul a 0 = DWR 0 0.
Proof. by rewrite /exactMul !(Rsimp01, round_0). Qed.

Lemma exactMul_correct (a b : R) :
  format a -> format b ->
  let: DWR h l := exactMul a b in h + l = a * b.
Proof.
move=> Fa Fb /=.
rewrite -Ropp_minus_distr round_opp.
rewrite [X in -X]round_generic //; first by lra.
by apply: format_err_mul.
Qed.

Lemma format_exactMul (a b : float) : 
  format a -> format b -> formatDw (exactMul a b).
Proof. 
move=> Fa Fb /=; split; try by apply: generic_format_round.
by rewrite exactMul_correct.
Qed.


Definition fastTwoSum (a b : R) :=
  let h := RND (a + b) in
  let t := RND (h - a) in DWR h (RND (b - t)).

Lemma fastTwoSum_0 : fastTwoSum 0 0 = DWR 0 0.
Proof. by rewrite /fastTwoSum !(Rsimp01, round_0). Qed. 

Lemma fastTwoSum_0l f : format f -> fastTwoSum 0 f = DWR f 0.
Proof.
move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic //.
by rewrite (round_generic _ _ _ f) // !Rsimp01 round_0.
Qed.

Lemma fastTwoSum_0r f : format f -> fastTwoSum f 0 = DWR f 0.
Proof.
by move=> Ff; rewrite /fastTwoSum !Rsimp01 round_generic // !(Rsimp01, round_0).
Qed.

Definition twoSum (a : R) (b : dwR) :=  
  let: DWR bh bl := b in 
  let: DWR h t := fastTwoSum a bh in 
  let: l := RND (t + bl) in DWR h l.

Definition fastSum (a bh bl : R) := 
  let: DWR h t := fastTwoSum a bh in DWR h (RND (t + bl)).

Local Notation ulp := (ulp beta FLX).


Lemma error_le_ulp_add x : Rabs (RND x) <= Rabs x + ulp x.
Proof.
have : Rabs (RND x - x) <= ulp x by apply: error_le_ulp.
split_Rabs; lra.
Qed.

Lemma fastSum_0 : fastSum 0 0 0 = DWR 0 0.
Proof. by rewrite /fastSum fastTwoSum_0 Rsimp01 round_0. Qed. 

Lemma bound_ulp_FLX f e : Rabs f < pow (e + p) -> ulp f <= pow e.
Proof.
move=> epLe.
have [->|f_neq0] := Req_dec f 0.
  rewrite ulp_FLX_0.
  by apply: bpow_ge_0; lia.
rewrite ulp_neq_0 // /cexp /FLX.
apply: bpow_le.
have magfE : (mag beta f <= (e + p))%Z by apply: mag_le_bpow => //; lia.
by lia.
Qed.

Lemma format_decomp_prod x1 x2 : 
  generic_format beta (FLX_exp p) x1 -> 
  generic_format beta (FLX_exp p) x2 -> 
  exists m1, exists e1, x1 * x2 = IZR m1 * pow e1 /\
                        Rabs (IZR m1) < pow (2 * p).
Proof.
move=> x1F x2F.
exists ((Ztrunc (scaled_mantissa beta (FLX_exp p) x1)) * 
        (Ztrunc (scaled_mantissa beta (FLX_exp p)  x2)))%Z.
exists (Generic_fmt.cexp beta (FLX_exp p) x1 + 
        Generic_fmt.cexp beta (FLX_exp p) x2)%Z.
split.
  rewrite [in LHS]x1F [in LHS]x2F /F2R /=.
  rewrite mult_IZR bpow_plus.
  set xx1 := Ztrunc _.
  set xx2 := Ztrunc _.
  set yy1 := Generic_fmt.cexp _ _ _.
  set yy2 := Generic_fmt.cexp _ _ _.
  rewrite -[bpow _ yy1]/(pow _).
  rewrite -[bpow _ yy2]/(pow _).
  lra.
rewrite mult_IZR.
have -> : (2 * p = p + p)%Z by clear; lia.
rewrite bpow_plus Rabs_mult.
apply: Rmult_lt_compat; try by apply: Rabs_pos.
  rewrite -scaled_mantissa_generic //.
  have [x1_eq0|x1_neq0] := Req_dec x1 0.
    by rewrite x1_eq0 scaled_mantissa_0 Rabs_R0; apply: bpow_gt_0.
  suff : bpow beta (p - 1) <= Rabs (scaled_mantissa beta (FLX_exp p) x1) <=
          bpow beta p - 1 by lra.
  by apply: mant_bound_le.
rewrite -scaled_mantissa_generic //.
have [x2_eq0|x2_neq0] := Req_dec x2 0.
  by rewrite x2_eq0 scaled_mantissa_0 Rabs_R0; apply: bpow_gt_0.
suff : bpow beta (p - 1) <= Rabs (scaled_mantissa beta (FLX_exp p) x2) <=
        bpow beta p - 1 by lra.
by apply: mant_bound_le.
Qed.

End FlxPrelim.
