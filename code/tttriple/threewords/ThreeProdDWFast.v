(* ---------------------------------------------------------------------------*)
(* Algorithm 12 (3Prod^fast_{2,3}): the FAST product of a DOUBLE word by a    *)
(* triple word, and its two correctness results -- the result is a triple     *)
(* word                                                                       *)
(* ([ThreeProdDWFast_isTW]) and the relative error bound [18u^3 + 75u^4]      *)
(* ([ThreeProdDWFast_error]) -- paper doc/paper3.pdf, Section 7.2 (see        *)
(* doc/alg12.md).  Generic over the precision [p] (FLX, no [emin]); needs     *)
(* [p >= 6].                                                                  *)
(*                                                                            *)
(* Algorithm 12 is to Algorithm 11 ([ThreeProdDW.v]) what Algorithm 10 is to  *)
(* Algorithm 9: the last 2Sum becomes a single rounding [s3 = RN(c + z3)] and *)
(* the low word [e4] is dropped.  Equivalently it IS Algorithm 10             *)
(* ([ThreeProdFast.v]) with [x2 = 0], which is how correctness is inherited;  *)
(* the error bound is not -- taking [x2 = 0] into account gives               *)
(* [18u^3 + 75u^4] instead of [44u^3 + 176u^4].                               *)
(*                                                                            *)
(* STATUS: COMPLETE -- both theorems are PROVED, zero admits.  The file also  *)
(* carries Algorithm 12's head lemma for Algorithm 13 (old paper Section      *)
(* 8.3): [ThreeProdDWFast_head_gap_norm], with [inner_sum_err_dwF] and        *)
(* [inner_low_mass_dwF] -- the same two ingredients as Algorithm 11, over an  *)
(* inner VecSum with one entry fewer.                                         *)
(* [ThreeProdDWFast_isTW] is Algorithm 10's correctness at [x2 = 0] (two      *)
(* lemmas); [ThreeProdDWFast_error] follows doc/old-triplewors.pdf Section    *)
(* 7.5, which doc/paper3.pdf omits: the extra source [eps4' <= 8u^3] and a    *)
(* THREE-case assembly (the case study works with [s3] instead of [c] and     *)
(* [z3]).  See doc/alg12.md.                                                  *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProdDWFast.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 12, like Algorithms 9-11, needs [p >= 6] (paper Section 7.2).    *)
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

Local Notation float := (float radix2).
Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).

(* Building blocks, with this format's [p]/[choice] hidden.                   *)
Local Notation TwoProd := (TwoProd p radix2 rnd).
Local Notation TwoSum := (TwoSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vecSum := (vecSum p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebK := (vsebK p choice).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation Fnonoverlap := (Fnonoverlap p).
Local Notation isTW := (isTW p).

(* Algorithm 10, of which Algorithm 12 is the [x2 = 0] case, and the          *)
(* double-word predicates and normalisation of Algorithm 11.                  *)
Local Notation ThreeProdFast := (ThreeProdFast p choice).
Local Notation isDW := (isDW p).
Local Notation dw_norm := (dw_norm p).
Local Notation dw_normP := (dw_normP p).
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

(* ===========================================================================*)
(*  Algorithm 12 -- 3Prod^fast_{2,3}(x, y)                                    *)
(*  (37 operations & 1 test; paper Section 7.2).                              *)
(*                                                                            *)
(*  Algorithm 11 with [s3 = RN(c + z3)] in place of the last 2Sum: its error  *)
(*  term [e4] is NOT computed, so the final VecSum has four inputs and        *)
(*  [(r1, r2) = VSEB(2)(e1, e2, e3)].  The third limb of the first argument   *)
(*  is                                                                        *)
(*  ignored -- it is [0] for an [isDW] input.                                 *)
(* ===========================================================================*)
Definition ThreeProdDWFast (x y : twR) : twR :=
  let: TWR x0 x1 _ := x in
  let: TWR y0 y1 y2 := y in
  let: (z00p, z00m) := TwoProd x0 y0 in
  let: (z01p, z01m) := TwoProd x0 y1 in
  let: (z10p, z10m) := TwoProd x1 y0 in
  let b := vecSum [:: z00m; z01p; z10p] in
  let b0 := nth 0 b 0 in
  let b1 := nth 0 b 1 in
  let b2 := nth 0 b 2 in
  let c   := RND (b2 + x1 * y1) in
  let z31 := RND (z10m + x0 * y2) in
  let z3  := RND (z31 + z01m) in
  let s3  := RND (c + z3) in
  let e := vecSum [:: z00p; b0; b1; s3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* ===========================================================================*)
(*  Algorithm 12 IS Algorithm 10 at [x2 = 0]: the only difference is          *)
(*  [z32 = RN(z01- + 0 * y0) = z01-], since [z01-] is a rounded value, hence  *)
(*  a float ([round_generic]).                                                *)
(* ===========================================================================*)
Lemma ThreeProdDWFast_eq x y :
  ThreeProdDWFast x y = ThreeProdFast (TWR (tw0 x) (tw1 x) 0) y.
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdDWFast /ThreeProdFast.
have F01m : format (TwoProd x0 y1).2 by apply: generic_format_round.
case E00 : (TwoProd x0 y0) => [z00p z00m].
case E01 : (TwoProd x0 y1) => [z01p z01m].
case E10 : (TwoProd x1 y0) => [z10p z10m].
have F01 : format z01m by move: F01m; rewrite E01.
by rewrite Rmult_0_l Rplus_0_r (round_generic _ _ _ _ F01).
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: [ThreeProdDWFast x y] is a triple-word number.       *)
(*                                                                            *)
(*  As in Section 7.1, this is inherited: Algorithm 12 is Algorithm 10 at     *)
(*  [x2 = 0] (the only difference, [RN(z01- + 0 * y0) = z01-], is             *)
(*  [round_generic] on a rounded value) and a DW is a TW with a zero third    *)
(*  limb.                                                                     *)
(* ===========================================================================*)
Lemma ThreeProdDWFast_isTW x y :
  ties_to_even choice ->
  isDW x -> isTW y -> isTW (ThreeProdDWFast x y).
Proof.
move=> Hc Hx Hy.
rewrite ThreeProdDWFast_eq.
apply: (@ThreeProdFast_isTW p Hp2 Hp6 choice choice_sym) => //.
have Hx' := isDW_isTW Hx.
by case: x Hx Hx' => x0 x1 x2 [_ _ -> _].
Qed.

(* ===========================================================================*)
(*  The WLOG for Algorithm 12: every piece goes through [ThreeProdDWFast_eq]  *)
(*  and Algorithm 10's own scale/sign/zero lemmas.                            *)
(* ===========================================================================*)
Lemma ThreeProdDWFast_scale a b x y :
  ThreeProdDWFast (scaleTW a x) (scaleTW b y) =
    scaleTW (a + b) (ThreeProdDWFast x y).
Proof.
rewrite !ThreeProdDWFast_eq.
case: x => x0 x1 x2.
have -> : TWR (tw0 (scaleTW a (TWR x0 x1 x2)))
              (tw1 (scaleTW a (TWR x0 x1 x2))) 0
        = scaleTW a (TWR x0 x1 0) by rewrite /scaleTW /=; congr TWR; ring.
by rewrite ThreeProdFast_scale.
Qed.

Lemma ThreeProdDWFast_opp x y :
  ThreeProdDWFast (negTW x) y = negTW (ThreeProdDWFast x y).
Proof.
rewrite !ThreeProdDWFast_eq.
case: x => x0 x1 x2.
have -> : TWR (tw0 (negTW (TWR x0 x1 x2))) (tw1 (negTW (TWR x0 x1 x2))) 0
        = negTW (TWR x0 x1 0) by rewrite /negTW /=; congr TWR; ring.
by rewrite (@ThreeProdFast_opp p choice choice_sym).
Qed.

Lemma ThreeProdDWFast_opp_r x y :
  ThreeProdDWFast x (negTW y) = negTW (ThreeProdDWFast x y).
Proof.
by rewrite !ThreeProdDWFast_eq (@ThreeProdFast_opp_r p choice choice_sym).
Qed.

Lemma ThreeProdDWFast_0l y : ThreeProdDWFast (TWR 0 0 0) y = TWR 0 0 0.
Proof. by rewrite ThreeProdDWFast_eq (@ThreeProdFast_0l p choice). Qed.

Lemma ThreeProdDWFast_0r x : ThreeProdDWFast x (TWR 0 0 0) = TWR 0 0 0.
Proof. by rewrite ThreeProdDWFast_eq ThreeProdFast_0r. Qed.

(* [eps4' = (c + z3) - s3]: [<= 8u^3] -- the extra source of Algorithm 12,    *)
(* smaller than Algorithm 10's [16u^3] because [|c| <= 6u^2], [|z3| <= 7u^2]. *)
Lemma epsp4_bound_dw c z3 :
  Rabs c <= 6 * (u * u) -> Rabs z3 <= 7 * (u * u) ->
  Rabs (c + z3 - RND (c + z3)) <= 8 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (c + z3) < pow (4 - 2 * p).
  rewrite pow_4m2p.
  have H3 := Rabs_triang c z3.
  nra.
have Herr := @round_err_le p Hp2 choice _ _ Hw.
move: Herr; rewrite (_ : (4 - 2 * p - p = 4 - 3 * p)%Z); last by lia.
rewrite pow_4m3p; nra.
Qed.

(* The [eps5 <> 0] disjunction of Algorithm 12: as for Theorem 8, but on the  *)
(* FOUR-limb list, so the case study is on [s3] instead of [c] and [z3].      *)
Lemma eps5nz_dwF x0 x1 y0 y1 y2 :
  ties_to_even choice -> dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let s3 := RND (RND (nth 0 bb 2 + x1 * y1)
             + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                  + RND (x0 * y1 - RND (x0 * y1)))) in
  let e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3] in
  Rabs ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e)
    <= 22 * (u * u * u) - 2 * (u * u * u * u) ->
  sumR (vseb e) - sumR (vsebK 3 e) <> 0 ->
  2 - 5 * u <= (x0 + x1 + 0) * (y0 + y1 + y2) \/
  [\/ Rabs (RND (x0 * y1)) < u * u, Rabs (RND (x1 * y0)) < u * u
     | Rabs s3 < u * u].
Proof.
move=> Hc Nx Ny bb s3 e HNb HE5.
case: (Rle_lt_dec (2 - 5 * u) ((x0 + x1 + 0) * (y0 + y1 + y2)))
  => [Hbig|Hsmall]; first by left.
right.
case: (Rlt_le_dec (Rabs (RND (x0 * y1))) (u * u)) => [Hs|H1];
  first by apply: Or31.
case: (Rlt_le_dec (Rabs (RND (x1 * y0))) (u * u)) => [Hs|H2];
  first by apply: Or32.
case: (Rlt_le_dec (Rabs s3) (u * u)) => [Hs|H3]; first by apply: Or33.
(* All three terms are big: we show [eps5 = 0], contradicting [HE5].          *)
case: HE5.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Nx' : tw_norm x0 x1 0 by exact: (@dw_norm_tw_norm p x0 x1 Nx).
have [[Fx0 Fx1 Fx2'] Hx0l Hx0r _ _] := Nx'.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r _ _] := Ny.
(* Everything lives on the [2u^3 = pow (1 - 3p)] grid.                        *)
pose g := (1 - 3 * p)%Z.
have Hcexp : forall t : R, cexp t = (mag beta t - p)%Z
  by move=> t; rewrite /cexp /fexp /FLX_exp.
have Himcx : forall t : R, format t -> (g <= cexp t)%Z -> is_imul t (pow g).
  move=> t Ft Hct.
  by apply: (is_imul_pow_le (y1 := cexp t));
     [exact: format_imul_cexp | exact: Hct].
have Hu2 : u * u = pow (- (2 * p)) by rewrite u_pow -bpow_plus; congr bpow; lia.
have Hbig_imul : forall t : R, format t -> u * u <= Rabs t ->
    is_imul t (pow g).
  move=> t Ft Hge.
  apply: Himcx => //.
  rewrite Hcexp /g; suff : (1 - 2 * p <= mag beta t)%Z by lia.
  apply: mag_ge_bpow.
  have -> : (1 - 2 * p - 1 = - (2 * p))%Z by lia.
  by rewrite -Hu2.
have Iz00p : is_imul (RND (x0 * y0)) (pow g).
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp /g.
  have Hlb : 1 <= RND (x0 * y0)
    by apply: (@z00p_lb p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
  suff : (1 <= mag beta (RND (x0 * y0)))%Z by lia.
  by apply: mag_ge_bpow; rewrite pow0E Rabs_pos_eq; lra.
have Iz00m : is_imul (RND (x0 * y0 - RND (x0 * y0))) (pow g).
  rewrite round_generic; last first.
    rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0));
      last by ring.
    by apply: generic_format_opp; apply: format_err_mul.
  apply: (is_imul_pow_le (y1 := (2 - 2 * p)%Z)); last by rewrite /g; lia.
  rewrite pow_2m2p; exact: (@z00m_imul p choice x0 x1 0 y0 y1 y2 Nx' Ny).
have Iz01p : is_imul (RND (x0 * y1)) (pow g)
  by apply: Hbig_imul => //; apply: generic_format_round.
have Iz10p : is_imul (RND (x1 * y0)) (pow g)
  by apply: Hbig_imul => //; apply: generic_format_round.
have Is3 : is_imul s3 (pow g)
  by apply: Hbig_imul => //; rewrite /s3; apply: generic_format_round.
have Ia : is_imul (RND (RND (x0 * y1) + RND (x1 * y0))) (pow g)
  by apply: is_imul_pow_round; apply: is_imul_add.
have Hbbe : bb = [:: RND (RND (x0 * y0 - RND (x0 * y0))
                         + RND (RND (x0 * y1) + RND (x1 * y0)));
    RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))
      - RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0)));
    RND (x0 * y1) + RND (x1 * y0) - RND (RND (x0 * y1) + RND (x1 * y0))]
  by rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
       (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
       (generic_format_round _ _ _ _)).
have Ib0 : is_imul (nth 0 bb 0) (pow g).
  by rewrite Hbbe /=; apply: is_imul_pow_round; apply: is_imul_add;
    [exact: Iz00m | exact: Ia].
have Ib1 : is_imul (nth 0 bb 1) (pow g).
  rewrite Hbbe /=; apply: is_imul_minus.
    by apply: is_imul_add; [exact: Iz00m | exact: Ia].
  by apply: is_imul_pow_round; apply: is_imul_add; [exact: Iz00m | exact: Ia].
have Fbb : {in bb, forall t, format t}.
  apply: (@format_vecSum p Hp2 choice) => t; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Feinp : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3],
    forall t, format t}.
  move=> t; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
have Ieinp : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3],
    forall t, is_imul t (pow g)}.
  move=> t; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]].
have Ie : {in e, forall t, is_imul t (pow g)}
  by rewrite /e; apply: vecSum_imul_forward.
have Fe : {in e, forall t, format t}
  by rewrite /e; apply: (@format_vecSum p Hp2 choice).
have Ivse : {in vseb e, forall t, is_imul t (pow g)}
  by apply: vseb_imul_forward.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fno : Fnonoverlap e.
  have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
            = RND (x0 * y1 - RND (x0 * y1)).
    by rewrite Rmult_0_l Rplus_0_r round_generic //;
       apply: generic_format_round.
  have Fno0 := @innerF_Fnonoverlap p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2
    Hc Nx' Ny.
  have Fno1 : Fnonoverlap (vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
              + RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)))]) by exact: Fno0.
  by move: Fno1; rewrite Hz32.
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall t, format t}
  by apply: (@format_vseb p Hp2 choice e Fe).
have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 (vseb e))
  by rewrite /vsebK -{1}(cat_take_drop 3 (vseb e)) sumR_cat; ring.
rewrite Hsplit.
have Hxpos : 0 < (x0 + x1 + 0) * (y0 + y1 + y2).
  have Hx1b := @dw_norm_x1 p x0 x1 Nx.
  have Hy1b := @x1_tight p Hp2 y0 y1 y2 Ny.
  have Hy2b := @x2_tight p Hp2 y0 y1 y2 Ny.
  have := Rabs_le_inv _ _ Hx1b; have := Rabs_le_inv _ _ Hy1b;
    have := Rabs_le_inv _ _ Hy2b.
  move=> [Hy2l Hy2r] [Hy1l Hy1r] [Hx1l Hx1r].
  have Hxa : 0 < x0 + x1 + 0 by clear -Hx0l Hx1l Hu0 Hu64; lra.
  have Hyb : 0 < y0 + y1 + y2 by clear -Hy0l Hy1l Hy2l Hu0 Hu64; nra.
  by apply: Rmult_lt_0_compat.
(* The product being [< 2 - 5u] caps the head: [ufp(r0) < 2], so [|r0| < 2].  *)
have Hr0lt2 : Rabs (nth 0 (vseb e) 0) < 2.
  case: (Req_dec (nth 0 (vseb e) 0) 0) => [->|Hr0n];
    first by rewrite Rabs_R0; lra.
  have Hlow := @sumR_ufp_lower p Hp2 (vseb e) Pno Fvse Hr0n.
  have Hsume : Rabs (sumR (vseb e))
      <= 2 - 5 * u + (22 * (u * u * u) - 2 * (u * u * u * u)).
    rewrite Hsumeq.
    have -> : sumR e = (x0 + x1 + 0) * (y0 + y1 + y2)
        + (- ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e)) by ring.
    have := Rabs_triang ((x0 + x1 + 0) * (y0 + y1 + y2))
              (- ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e)).
    rewrite Rabs_Ropp (Rabs_pos_eq ((x0 + x1 + 0) * (y0 + y1 + y2)));
      last by lra.
    by clear -HNb Hsmall; lra.
  have HU := ufp_gt_0 (nth 0 (vseb e) 0).
  have Hufp : ufp (nth 0 (vseb e) 0) < pow 1.
    have Hp12 : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
    clear -Hlow Hsume Hu0 Hu64 Hp12 HU; nra.
  apply: (Rlt_le_trans _ _ _ (bpow_mag_gt beta (nth 0 (vseb e) 0))).
  have -> : 2 = pow 1 by rewrite /= /Z.pow_pos /=; lra.
  apply: bpow_le.
  by move: Hufp; rewrite /ufp => H; have := lt_bpow beta _ _ H; lia.
have Hstep : forall (i : nat) (K : Z), nth 0 (vseb e) i.+1 <> 0 ->
    (i.+1 < size (vseb e))%N -> Rabs (nth 0 (vseb e) i) < pow K ->
    Rabs (nth 0 (vseb e) i.+1) < pow (K - p).
  move=> i K Hn1 Hlt HK.
  have [Hz|Hb] := Pno i Hlt; first by case: Hn1.
  apply: (Rlt_le_trans _ _ _ Hb).
  have Hni : nth 0 (vseb e) i <> 0.
    move=> H0; move: Hb; rewrite H0 ulp_FLX_0 => Hb'.
    have := Rabs_pos (nth 0 (vseb e) i.+1); lra.
  rewrite ulp_neq_0 //; apply: bpow_le.
  rewrite Hcexp.
  suff : (mag beta (nth 0%R (vseb e) i) <= K)%Z by lia.
  by apply: mag_le_bpow.
(* A fourth nonzero limb would be [< 2u^3] and a nonzero multiple of it.      *)
have Hn3 : nth 0 (vseb e) 3 = 0.
  case: (Req_dec (nth 0 (vseb e) 0) 0) => [Hr0|Hr0n].
    have Ha1 := @nth_step_zero p Hp2 (vseb e) 0 Pno Fvse Hr0.
    have Ha2 := @nth_step_zero p Hp2 (vseb e) 1 Pno Fvse Ha1.
    exact: (@nth_step_zero p Hp2 (vseb e) 2 Pno Fvse Ha2).
  case: (Req_dec (nth 0 (vseb e) 3) 0) => [//|Hn3n].
  have Hn2n : nth 0 (vseb e) 2 <> 0
    by move=> H; apply: Hn3n;
       apply: (@nth_step_zero p Hp2 (vseb e) 2 Pno Fvse H).
  have Hn1n : nth 0 (vseb e) 1 <> 0
    by move=> H; apply: Hn2n;
       apply: (@nth_step_zero p Hp2 (vseb e) 1 Pno Fvse H).
  have Hsz3 : (3 < size (vseb e))%N
    by rewrite ltnNge; apply/negP => Hge; apply: Hn3n; rewrite nth_default.
  have Hsz2 : (2 < size (vseb e))%N by apply: ltn_trans Hsz3.
  have Hsz1 : (1 < size (vseb e))%N by apply: ltn_trans Hsz2.
  have Hr01 : Rabs (nth 0 (vseb e) 0) < pow 1.
    by have -> : pow 1 = 2 by rewrite /= /Z.pow_pos /=; lra.
  have Hm1 := Hstep 0%N 1%Z Hn1n Hsz1 Hr01.
  have Hm2 := Hstep 1%N (1 - p)%Z Hn2n Hsz2 Hm1.
  have Hm3 := Hstep 2%N (1 - p - p)%Z Hn3n Hsz3 Hm2.
  have Hge : pow g <= Rabs (nth 0 (vseb e) 3).
    apply: is_imul_pow_le_abs; last exact: Hn3n.
    by apply: Ivse; apply: mem_nth.
  have Hpg : (1 - p - p - p = g)%Z by rewrite /g; lia.
  by rewrite Hpg in Hm3; lra.
apply: (@small_head_zero p Hp2).
- exact: Pnonoverlap_drop.
- by move=> t /mem_drop; apply: Fvse.
- by rewrite nth_drop addn0.
Qed.

(* The error bound, normalised (paper WLOG [1 <= x0, y0 < 2]).                *)
(* ===========================================================================*)
(*  The head limb, for Algorithm 13 (old paper Section 8.3)                   *)
(*                                                                            *)
(*  Algorithm 12's version of ThreeProdDW.v's [inner_sum_err_dw] /            *)
(*  [inner_low_mass_dw] / [ThreeProdDW_head_gap_norm].  The inner VecSum has  *)
(*  FOUR entries here (Algorithm 10 merges [c] and [z3] into [s3]), so the    *)
(*  numerator carries the extra source [eps4' = c + z3 - s3 <= 8u^3] and the  *)
(*  tail is one term shorter.  Both constants of the DW case still fit.       *)
(* ===========================================================================*)

(* [D]: the product minus the exact sum of the inner VecSum's inputs.         *)
Lemma inner_sum_err_dwF x0 x1 y0 y1 y2 :
  ties_to_even choice -> dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Rabs ((x0 + x1 + 0) * (y0 + y1 + y2)
        - sumR (vecSum
            [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                RND (RND (nth 0 bb 2 + x1 * y1)
                   + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                        + RND (x0 * y1 - RND (x0 * y1))))]))
    <= 22 * (u * u * u) - 2 * (u * u * u * u).
Proof.
move=> Hc Nxd Ny bb.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Nx' : tw_norm x0 x1 0 by exact: (@dw_norm_tw_norm p x0 x1 Nxd).
set z01m := RND (x0 * y1 - RND (x0 * y1)).
set z10m := RND (x1 * y0 - RND (x1 * y0)).
set c := RND (nth 0 bb 2 + x1 * y1).
set z31 := RND (z10m + x0 * y2).
set z3 := RND (z31 + z01m).
set s3 := RND (c + z3).
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3].
have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
          = RND (x0 * y1 - RND (x0 * y1)).
  by rewrite Rmult_0_l Rplus_0_r round_generic //; apply: generic_format_round.
have Hdecomp0 := @sumR_eF_decomp p Hp2 choice choice_sym x0 x1 0 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) z01m (RND (x1 * y0)) z10m bb c z31
  (RND (z01m + 0 * y0)) (RND (z31 + RND (z01m + 0 * y0)))
  (RND (c + RND (z31 + RND (z01m + 0 * y0))))
  (ltac:(by case: Nx' => -[]) : format x0)
  (ltac:(by case: Nx' => -[]) : format x1)
  (ltac:(by case: Ny => -[]) : format y0)
  (ltac:(by case: Ny => -[]) : format y1)
  erefl erefl erefl erefl erefl erefl erefl erefl erefl.
move: Hdecomp0; rewrite Hz32 -/z3 -/s3 -/e => Hdecomp.
have HN : (x0 + x1 + 0) * (y0 + y1 + y2) - sumR e
        = x1 * y2 + (z10m + x0 * y2 - z31) + (z31 + z01m - z3)
          + (nth 0 bb 2 + x1 * y1 - c) + (c + z3 - s3)
  by rewrite Hdecomp -/z01m; ring.
have Hz10m : Rabs z10m <= u * u.
  rewrite /z10m round_generic;
    first by apply: (@z10m_bound_dw p Hp2 choice x0 x1 y0 y1 y2 Nxd Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  by apply: generic_format_opp; apply: format_err_mul.
have Hz01m : Rabs z01m <= 2 * (u * u).
  rewrite /z01m round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  by apply: generic_format_opp; apply: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 0 y0 y1 y2 Nx' Ny.
have Hx1y1 := @x1y1_bound_dw p x0 x1 y0 y1 y2 Nxd Ny.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
have Hz31 : Rabs z31 <= 5 * (u * u)
  by apply: (@z31_bound_dw p Hp2 Hp6 choice _ _ _ Hz10m Hx0y2).
have Hz3b : Rabs z3 <= 7 * (u * u)
  by apply: (@z3_bound_dw p Hp2 Hp6 choice _ _ Hz31 Hz01m).
have Hc6 : Rabs c <= 6 * (u * u)
  by apply: (@c_bound_dw p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
(* The five sources: Algorithm 11's four, plus [eps4' = c + z3 - s3].         *)
have Heps0 := @x1y2_bound_dw p Hp2 x0 x1 y0 y1 y2 Nxd Ny.
have Heps1 : Rabs (z10m + x0 * y2 - z31) <= 4 * (u * u * u)
  by apply: (@eps1_bound_dw p Hp2 choice _ _ _ Hz10m Hx0y2).
have Heps3 : Rabs (z31 + z01m - z3) <= 4 * (u * u * u)
  by apply: (@eps3_bound_dw p Hp2 choice _ _ Hz31 Hz01m).
have Heps4 : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 4 * (u * u * u)
  by apply: (@eps4_bound_dw p Hp2 choice _ _ _ Hb2 Hx1y1).
have Hepsp4 : Rabs (c + z3 - s3) <= 8 * (u * u * u)
  by apply: (epsp4_bound_dw Hc6 Hz3b).
rewrite HN.
have T1 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31) + (z31 + z01m - z3)
                        + (nth 0 bb 2 + x1 * y1 - c)) (c + z3 - s3).
have T2 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31)
                        + (z31 + z01m - z3)) (nth 0 bb 2 + x1 * y1 - c).
have T3 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31)) (z31 + z01m - z3).
have T4 := Rabs_triang (x1 * y2) (z10m + x0 * y2 - z31).
by lra.
Qed.

(* [B]: the three inner VecSum entries below the leading one are [O(u)].      *)
Lemma inner_low_mass_dwF x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  sumRabs [:: nth 0 bb 0; nth 0 bb 1;
              RND (RND (nth 0 bb 2 + x1 * y1)
                 + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                      + RND (x0 * y1 - RND (x0 * y1))))]
    <= 9 * u.
Proof.
move=> Nxd Ny bb.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Nx' : tw_norm x0 x1 0 by exact: (@dw_norm_tw_norm p x0 x1 Nxd).
have Fin : {in [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
                  RND (x1 * y0)], forall z : R, format z}.
  by move=> z; rewrite !inE => /or3P[] /eqP-> //; apply: generic_format_round.
have Hrun := @vecSumAux_run_le p Hp2 choice _ Fin.
have Hsep := @vecSum_head_sep p Hp2 choice choice_sym _ Fin (isT : (1 < 3)%N).
have Hz00m : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic;
    first by apply: (@z00m_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0));
    last by ring.
  by apply: generic_format_opp; apply: format_err_mul.
have Hz01p : Rabs (RND (x0 * y1)) <= 4 * u
  by apply: (@z01p_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
have Hz10p : Rabs (RND (x1 * y0)) <= 2 * u
  by apply: (@z10p_bound_dw p Hp2 choice x0 x1 y0 y1 y2 Nxd Ny).
have Hb0 : Rabs (nth 0 bb 0) <= (1 + u) ^ 3 * (8 * u).
  rewrite /bb vecSum_nth0.
  apply: Rle_trans Hrun _.
  have Hs3 : sumRabs [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
                         RND (x1 * y0)] <= 8 * u by rewrite /=; lra.
  have Hp3 : (0:R) <= (1 + u) ^ 3 by apply: pow_le; lra.
  by have -> : size [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
                        RND (x1 * y0)] = 3%N by []; nra.
have Hb1 : Rabs (nth 0 bb 1) <= u * Rabs (nth 0 bb 0).
  have Hu2 := @ulp_2u p beta Hp2 (nth 0 bb 0).
  by move: Hsep; rewrite -/bb => Hsep; lra.
have Hz10m : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= u * u.
  rewrite round_generic;
    first by apply: (@z10m_bound_dw p Hp2 choice x0 x1 y0 y1 y2 Nxd Ny).
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  by apply: generic_format_opp; apply: format_err_mul.
have Hz01m : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  by apply: generic_format_opp; apply: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 0 y0 y1 y2 Nx' Ny.
have Hx1y1 := @x1y1_bound_dw p x0 x1 y0 y1 y2 Nxd Ny.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
have Hz31 : Rabs (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)) <= 5 * (u * u)
  by apply: (@z31_bound_dw p Hp2 Hp6 choice _ _ _ Hz10m Hx0y2).
have Hz3b : Rabs (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                      + RND (x0 * y1 - RND (x0 * y1)))) <= 7 * (u * u)
  by apply: (@z3_bound_dw p Hp2 Hp6 choice _ _ Hz31 Hz01m).
have Hc6 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 6 * (u * u)
  by apply: (@c_bound_dw p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
(* [s3 = RN(c + z3)] is the one entry Algorithm 12 has that 11 has not.       *)
have Hepsp4 := epsp4_bound_dw Hc6 Hz3b.
have Ts3 := Rabs_triang (RND (nth 0 bb 2 + x1 * y1))
  (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
      + RND (x0 * y1 - RND (x0 * y1)))).
have E3 : (1 + u) ^ 3 = 1 + 3 * u + 3 * (u * u) + u * u * u by ring.
have Hu2 : u * u <= / 64 * u by nra.
have Hu3 : u * u * u <= / 64 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
have Hs3 : forall a b c : R, sumRabs [:: a; b; c] = Rabs a + Rabs b + Rabs c.
  by move=> a b c; rewrite /=; ring.
rewrite Hs3 E3 in Hb0 *.
have Hb0p := Rabs_pos (nth 0 bb 0).
have Habs3 : forall A B : R, Rabs B <= Rabs A + Rabs (A - B).
  move=> A B; have H := Rabs_triang A (B - A).
  have E : A + (B - A) = B by ring.
  by rewrite E Rabs_minus_sym in H.
have Hs3b := Habs3 (RND (nth 0 bb 2 + x1 * y1)
  + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
       + RND (x0 * y1 - RND (x0 * y1))))
  (RND (RND (nth 0 bb 2 + x1 * y1)
      + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
           + RND (x0 * y1 - RND (x0 * y1))))).
by clear -Hb0 Hb1 Hc6 Hz3b Hepsp4 Ts3 Hs3b Hu0 Hu64 Hu2 Hu3 Hu4 Hb0p; nra.
Qed.

(* The head lemma (normalised), exactly as in ThreeProdDW.v.                  *)
Lemma ThreeProdDWFast_head_gap_norm x y :
  ties_to_even choice -> dw_normP x -> tw_normP y ->
  Rabs (TWval x * TWval y - tw0 (ThreeProdDWFast x y))
    <= / 2 * ulp (tw0 (ThreeProdDWFast x y)) + 60 * (u * u).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 [Nxd ->].
case: y Ny => y0 y1 y2 Ny.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
have Nx' : tw_norm x0 x1 0 by exact: (@dw_norm_tw_norm p x0 x1 Nxd).
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
rewrite ThreeProdDWFast_eq !tw0E !tw1E.
rewrite (@ThreeProdFast_norm_eq p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2 Hc
  Nx' Ny').
have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
          = RND (x0 * y1 - RND (x0 * y1)).
  by rewrite Rmult_0_l Rplus_0_r round_generic //; apply: generic_format_round.
rewrite Hz32.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
                     RND (x1 * y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                    RND (RND (nth 0 bb 2 + x1 * y1)
                       + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                            + RND (x0 * y1 - RND (x0 * y1))))].
rewrite tw0E /TWval.
have FL4 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                   RND (RND (nth 0 bb 2 + x1 * y1)
                      + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                           + RND (x0 * y1 - RND (x0 * y1))))],
    forall z : R, format z}.
  have Fbb : {in bb, forall z : R, format z}.
    apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
    by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
  have Fnthbb : forall i, format (nth 0 bb i).
    move=> i; case: (ltnP i (size bb)) => Hi;
      last by rewrite nth_default //; exact: generic_format_0.
    by apply: Fbb; apply: mem_nth.
  move=> z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
(* The star identity, Algorithm 10's version.                                 *)
have Hstar : nth 0 (vseb e) 0 = nth 0 e 0.
  case: (Req_dec (nth 0 e 1) 0) => [He1|He1].
    have H := @vsebFast_head3_e1zero p Hp2 Hp6 choice choice_sym x0 x1 0
      y0 y1 y2 Hc Nx' Ny'.
    move: H; rewrite Hz32 -/bb -/e => H.
    by have [H0 _] := H He1.
  have Hs := @vseb_star p Hp2 choice choice_sym _ FL4 (isT : (1 < 4)%N) He1.
  by rewrite -/e in Hs; rewrite Hs.
have HD := inner_sum_err_dwF Hc Nxd Ny'.
have HB := inner_low_mass_dwF Nxd Ny'.
have HD2 : Rabs ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e)
    <= 22 * (u * u * u) - 2 * (u * u * u * u) by exact: HD.
have HB2 : sumRabs [:: nth 0 bb 0; nth 0 bb 1;
                       RND (RND (nth 0 bb 2 + x1 * y1)
                          + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                               + RND (x0 * y1 - RND (x0 * y1))))] <= 9 * u
  by exact: HB.
have HDL : Rabs ((x0 + x1 + 0) * (y0 + y1 + y2)
    - sumR [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
               RND (RND (nth 0 bb 2 + x1 * y1)
                  + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                       + RND (x0 * y1 - RND (x0 * y1))))])
    <= 22 * (u * u * u) - 2 * (u * u * u * u).
  by rewrite -(@vecSum_sum p Hp2 choice choice_sym _ FL4) -/e.
have Hgap := @vecSum_head_gap p Hp2 choice choice_sym
  [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
              + RND (x0 * y1 - RND (x0 * y1))))]
  ((x0 + x1 + 0) * (y0 + y1 + y2)) (22 * (u * u * u) - 2 * (u * u * u * u))
  (9 * u) FL4 (isT : (1 < 4)%N) HDL HB2.
rewrite Hstar.
rewrite -/e in Hgap.
apply: Rle_trans Hgap _.
have -> : (size [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                    RND (RND (nth 0 bb 2 + x1 * y1)
                       + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                            + RND (x0 * y1 - RND (x0 * y1))))]).-1 = 3%N by [].
have HI : INR 3 = 3 by rewrite /=; ring.
have E3 : (1 + u) ^ 3 = 1 + 3 * u + 3 * (u * u) + u * u * u by ring.
rewrite HI E3.
have Hu2 : u * u <= / 64 * u by nra.
have Hu3 : u * u * u <= / 64 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 64 * (u * u * u * u) by nra.
by clear -Hu0 Hu64 Hu2 Hu3 Hu4 Hu5; nra.
Qed.

Lemma ThreeProdDWFast_error_norm x y :
  ties_to_even choice -> dw_normP x -> tw_normP y ->
  Rabs (TWval (ThreeProdDWFast x y) - TWval x * TWval y) <=
     (18 * (u * u * u) + 75 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 [Nxd ->].
case: y Ny => y0 y1 y2 Ny.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
have Nx' : tw_norm x0 x1 0 by exact: (@dw_norm_tw_norm p x0 x1 Nxd).
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
rewrite ThreeProdDWFast_eq !tw0E !tw1E.
rewrite (@ThreeProdFast_norm_eq p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2 Hc
  Nx' Ny').
(* [x2 = 0] collapses Algorithm 10's [z32 = RN(z01- + x2 y0)] to [z01-].      *)
have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
          = RND (x0 * y1 - RND (x0 * y1)).
  by rewrite Rmult_0_l Rplus_0_r round_generic //; apply: generic_format_round.
rewrite Hz32.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
  RND (x1 * y0)].
set z01m := RND (x0 * y1 - RND (x0 * y1)).
set z10m := RND (x1 * y0 - RND (x1 * y0)).
set c := RND (nth 0 bb 2 + x1 * y1).
set z31 := RND (z10m + x0 * y2).
set z3 := RND (z31 + z01m).
set s3 := RND (c + z3).
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; s3].
have HTW3 : TWval (TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2))
    = sumR (vsebK 3 e).
  rewrite /TWval /vsebK.
  case E : (vseb e) => [|v0 [|v1 [|v2 r]]] /=.
  - ring.
  - ring.
  - ring.
  - rewrite take0 /=; ring.
rewrite HTW3.
have HXY : TWval (TWR x0 x1 0) * TWval (TWR y0 y1 y2)
    = (x0 + x1 + 0) * (y0 + y1 + y2) by rewrite /TWval.
rewrite HXY.
have Hsz4 : size e = 4%N by rewrite /e size_vecSum.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fnthbb : forall i, format (nth 0 bb i).
  move=> i; case: (ltnP i (size bb)) => Hi;
    last by rewrite nth_default //; exact: generic_format_0.
  by apply: Fbb; apply: mem_nth.
have Fe : {in e, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
    try apply: generic_format_round; apply: Fnthbb.
(* Algorithm 10's head VecSum is F-nonoverlapping, at [x2 = 0].               *)
have Fno : Fnonoverlap e.
  have Fno0 := @innerF_Fnonoverlap p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2
    Hc Nx' Ny'.
  have Fno1 : Fnonoverlap (vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (RND (nth 0 bb 2 + x1 * y1)
         + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
              + RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)))]) by exact: Fno0.
  by move: Fno1; rewrite Hz32.
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz4; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall z, format z}
  by apply: (@format_vseb p Hp2 choice e Fe).
(* Algorithm 10's error identity at [x2 = 0]: [eps0] loses its [x2] terms,    *)
(* [eps2] vanishes, and [eps4' = c + z3 - s3] is the extra source.            *)
have Hdecomp0 := @sumR_eF_decomp p Hp2 choice choice_sym x0 x1 0 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) z01m (RND (x1 * y0)) z10m bb c z31
  (RND (z01m + 0 * y0)) (RND (z31 + RND (z01m + 0 * y0)))
  (RND (c + RND (z31 + RND (z01m + 0 * y0))))
  (ltac:(by case: Nx' => -[]) : format x0)
  (ltac:(by case: Nx' => -[]) : format x1)
  (ltac:(by case: Ny' => -[]) : format y0)
  (ltac:(by case: Ny' => -[]) : format y1)
  erefl erefl erefl erefl erefl erefl erefl erefl erefl.
move: Hdecomp0; rewrite Hz32 -/z3 -/s3 -/e => Hdecomp.
have HN : (x0 + x1 + 0) * (y0 + y1 + y2) - sumR e
        = x1 * y2 + (z10m + x0 * y2 - z31) + (z31 + z01m - z3)
          + (nth 0 bb 2 + x1 * y1 - c) + (c + z3 - s3)
  by rewrite Hdecomp -/z01m; ring.
have Hz10m : Rabs z10m <= u * u.
  rewrite /z10m round_generic;
    first by apply: (@z10m_bound_dw p Hp2 choice x0 x1 y0 y1 y2 Nxd Ny').
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny'.
  by apply: generic_format_opp; apply: format_err_mul.
have Hz01m : Rabs z01m <= 2 * (u * u).
  rewrite /z01m round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny').
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny'.
  by apply: generic_format_opp; apply: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 0 y0 y1 y2 Nx' Ny'.
have Hx1y1 := @x1y1_bound_dw p x0 x1 y0 y1 y2 Nxd Ny'.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny').
have Hz31 : Rabs z31 <= 5 * (u * u)
  by apply: (@z31_bound_dw p Hp2 Hp6 choice _ _ _ Hz10m Hx0y2).
have Hz3b : Rabs z3 <= 7 * (u * u)
  by apply: (@z3_bound_dw p Hp2 Hp6 choice _ _ Hz31 Hz01m).
have Hc6 : Rabs c <= 6 * (u * u)
  by apply: (@c_bound_dw p Hp2 Hp6 choice _ _ _ Hb2 Hx1y1).
have Heps0 := @x1y2_bound_dw p Hp2 x0 x1 y0 y1 y2 Nxd Ny'.
have Heps1 : Rabs (z10m + x0 * y2 - z31) <= 4 * (u * u * u)
  by apply: (@eps1_bound_dw p Hp2 choice _ _ _ Hz10m Hx0y2).
have Heps3 : Rabs (z31 + z01m - z3) <= 4 * (u * u * u)
  by apply: (@eps3_bound_dw p Hp2 choice _ _ Hz31 Hz01m).
have Heps4 : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 4 * (u * u * u)
  by apply: (@eps4_bound_dw p Hp2 choice _ _ _ Hb2 Hx1y1).
have Hepsp4 : Rabs (c + z3 - s3) <= 8 * (u * u * u)
  by apply: (epsp4_bound_dw Hc6 Hz3b).
have Hxy1 := @xy_ge p Hp2 Hp6 x0 x1 0 y0 y1 y2 Nx' Ny'.
have Hs5 := @eps5_bound p Hp2 choice e Pno Fvse (@u_le_64 p Hp6).
have Hident : sumR (vsebK 3 e) - (x0 + x1 + 0) * (y0 + y1 + y2)
    = -((sumR (vseb e) - sumR (vsebK 3 e))
        + ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e))
  by rewrite Hsumeq; ring.
rewrite Hident Rabs_Ropp.
set S5 := sumR (vseb e) - sumR (vsebK 3 e).
set N := (x0 + x1 + 0) * (y0 + y1 + y2) - sumR e.
set r := Rabs ((x0 + x1 + 0) * (y0 + y1 + y2)).
have HNgen : forall E0 E1 E3 E4 E4p,
    Rabs (x1 * y2) <= E0 -> Rabs (z10m + x0 * y2 - z31) <= E1 ->
    Rabs (z31 + z01m - z3) <= E3 -> Rabs (nth 0 bb 2 + x1 * y1 - c) <= E4 ->
    Rabs (c + z3 - s3) <= E4p ->
    Rabs N <= E0 + E1 + E3 + E4 + E4p.
  move=> E0 E1 E3 E4 E4p H0 H1 H3 H4 H4p.
  rewrite /N HN.
  have T0 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31)
                          + (z31 + z01m - z3) + (nth 0 bb 2 + x1 * y1 - c))
                         (c + z3 - s3).
  have T1 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31)
                          + (z31 + z01m - z3)) (nth 0 bb 2 + x1 * y1 - c).
  have T2 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31))
                         (z31 + z01m - z3).
  have T3 := Rabs_triang (x1 * y2) (z10m + x0 * y2 - z31).
  lra.
have Hsm : forall K, Rabs N <= K -> Rabs (sumR (vseb e)) <= r + K.
  move=> K HK; rewrite Hsumeq.
  have -> : sumR e = (x0 + x1 + 0) * (y0 + y1 + y2) + (- N) by rewrite /N; ring.
  have := Rabs_triang ((x0 + x1 + 0) * (y0 + y1 + y2)) (- N).
  by rewrite Rabs_Ropp -/r; lra.
have HNnaive : Rabs N <= 22 * (u * u * u) - 2 * (u * u * u * u).
  have := HNgen _ _ _ _ _ Heps0 Heps1 Heps3 Heps4 Hepsp4; lra.
(* Case 1: the product is large ([>= 1.5 - 7u]); the naive numerator does.    *)
case: (Rle_lt_dec (15 / 10 - 7 * u) r) => [HA | Hlow].
  apply: (@assembly_dw_eps5 p
            (22 * (u * u * u) - 2 * (u * u * u * u)) (15 / 10 - 7 * u)
            _ N S5 (sumR (vseb e)) r).
  - clear -Hu0 Hu64; nra.
  - exact: HA.
  - clear -Hu0 Hu64; nra.
  - exact: HNnaive.
  - exact: Hs5.
  - by apply: Hsm.
  - have Hu2 : u * u <= / 64 * u by nra.
    have Hu3 : u * u * u <= / 64 * (u * u) by nra.
    have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
    clear -Hu0 Hu64 Hu2 Hu3 Hu4; nra.
(* Otherwise [eps1] and [eps4] are small (Theorem 8's refinement 1).          *)
have Hne1 : Rabs (z10m + x0 * y2 - z31) <= 2 * (u * u * u).
  case: (Rle_lt_dec (Rabs (z10m + x0 * y2 - z31)) (2 * (u * u * u)))
    => [//|Hbig].
  have Hb := @eps1_big_prod_dw p Hp2 Hp6 choice x0 x1 y0 y1 y2 Nxd Ny'
    Hbig.
  have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
  by rewrite -/r in Hlow *; lra.
have Hne4 : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 2 * (u * u * u).
  case: (Rle_lt_dec (Rabs (nth 0 bb 2 + x1 * y1 - c)) (2 * (u * u * u)))
    => [//|Hbig].
  have Hb : 15 / 10 - 7 * u <= (x0 + x1 + 0) * (y0 + y1 + y2)
    by apply: (@eps4_big_prod_dw p Hp2 Hp6 choice choice_sym x0 x1 y0 y1 y2
                 Nxd Ny');
       exact: Hbig.
  have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
  by rewrite -/r in Hlow *; lra.
case: (Req_dec S5 0) => [HS5z | HS5n].
  (* Case 2: [eps5 = 0], numerator [18u^3 - 2u^4].                            *)
  rewrite HS5z Rplus_0_l.
  apply: (@assembly_dw_zero
            (18 * (u * u * u) - 2 * (u * u * u * u)) (1 - 4 * u) _ N r).
  - clear -Hu0 Hu64; nra.
  - by rewrite -/r in Hxy1.
  - have := HNgen _ _ _ _ _ Heps0 Hne1 Heps3 Hne4 Hepsp4;
      clear -Hu0 Hu64; nra.
  - have Hu2 : u * u <= / 64 * u by nra.
    have Hu3 : u * u * u <= / 64 * (u * u) by nra.
    have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
    clear -Hu0 Hu64 Hu2 Hu3 Hu4; nra.
(* Case 3: [eps5 <> 0] shrinks one more source; numerator [16u^3 + 2u^4].     *)
have Hdisj := eps5nz_dwF Hc Nxd Ny' HNnaive HS5n.
have HNC : Rabs N <= 16 * (u * u * u) + 2 * (u * u * u * u).
  case: Hdisj => [Hbig | Hcase].
    have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
    by rewrite -/r in Hlow *; clear -Hlow Hbig Hu0 Hu64; lra.
  case: Hcase => [H1|H2|H3].
  - have H0 := @eps0_small_of_z01p p Hp2 Hp6 choice x0 x1 y0 y1 y2 Nxd Ny' H1.
    have := HNgen _ _ _ _ _ H0 Hne1 Heps3 Hne4 Hepsp4;
      clear -Hu0 Hu64; nra.
  - have H0 := @eps0_small_of_z10p p Hp2 Hp6 choice x0 x1 y0 y1 y2 Nxd Ny' H2.
    have := HNgen _ _ _ _ _ H0 Hne1 Heps3 Hne4 Hepsp4;
      clear -Hu0 Hu64; nra.
  - have H4' : Rabs (c + z3 - s3) <= / 2 * (u * u * u)
      by rewrite /s3; apply: (@err_small_of_round p Hp2 choice); rewrite -/s3.
    have := HNgen _ _ _ _ _ Heps0 Hne1 Heps3 Hne4 H4';
      clear -Hu0 Hu64; nra.
apply: (@assembly_dw_eps5 p
          (16 * (u * u * u) + 2 * (u * u * u * u)) (1 - 4 * u)
          _ N S5 (sumR (vseb e)) r).
- clear -Hu0 Hu64; nra.
- by rewrite -/r in Hxy1.
- clear -Hu0 Hu64; nra.
- exact: HNC.
- exact: Hs5.
- by apply: Hsm.
- have Hu2 : u * u <= / 64 * u by nra.
  have Hu3 : u * u * u <= / 64 * (u * u) by nra.
  have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
  have Hu5 : u * u * u * u * u <= / 64 * (u * u * u * u) by nra.
  clear -Hu0 Hu64 Hu2 Hu3 Hu4 Hu5; nra.
Qed.

(* ===========================================================================*)
(*  The error bound: [<= 18u^3 + 75u^4] (paper Section 7.2).                  *)
(*                                                                            *)
(*  Proof OMITTED in doc/paper3.pdf, recovered from doc/old-triplewors.pdf    *)
(*  Section 7.5 -- see doc/alg12.md.  The five sources of Theorem 8 are       *)
(*  unchanged (no [eps2], and [eps0 = x1 y2 <= 2u^3 - 2u^4]) and there is one *)
(*  more, the term Algorithm 12 drops:                                        *)
(*                                                                            *)
(*    |eps4'| = |(c + z3) - s3| <= u ufp(6u^2 + 7u^2) <= 8u^3                 *)
(*                                                                            *)
(*  so the naive numerator is [22u^3 - 2u^4].  Three cases then suffice --    *)
(*  the case study is SHORTER than Theorem 8's because it works with [s3]     *)
(*  instead of [c] and [z3]:                                                  *)
(*                                                                            *)
(*    x*y >= 1.5 - 7u          : K = 22u^3 - 2u^4 (naive), with eps5          *)
(*    x*y < 1.5 - 7u, eps5 = 0 : K = 18u^3 - 2u^4 ([eps1], [eps4] halved)     *)
(*    x*y < 1.5 - 7u, eps5 <> 0: K = 16u^3 + 2u^4 (one more source shrinks)   *)
(* ===========================================================================*)
Lemma ThreeProdDWFast_error x y :
  ties_to_even choice ->
  isDW x -> isTW y ->
  Rabs (TWval (ThreeProdDWFast x y) - TWval x * TWval y) <=
     (18 * (u * u * u) + 75 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy.
set C := (18 * _ + _).
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  have Hxz : x = TWR 0 0 0.
    by apply: (@isTW_zero_lead p Hp2) => //; exact: isDW_isTW.
  rewrite Hxz ThreeProdDWFast_0l.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (@isTW_zero_lead p Hp2 y Hy y0z) ThreeProdDWFast_0r.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_r Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
have [cx _ [Hxp Hxn]] := @isDW_normalize p Hp2 choice x Hx x0n.
have [cy _ [Hyp Hyn]] := @isTW_normalize p Hp2 choice y Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
apply: (@error_scale_transfer (cx + cy)%Z (TWval (ThreeProdDWFast x y))
                              (TWval x * TWval y) C).
case: Hxsg => Hxs; case: Hysg => Hys.
- have Hn := ThreeProdDWFast_error_norm Hc (Hxp Hxs) (Hyp Hys).
  rewrite ThreeProdDWFast_scale !TWval_scale in Hn.
  rewrite (_ : TWval x * pow cx * (TWval y * pow cy) = TWval x * TWval y * pow
    (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
- have Hn := ThreeProdDWFast_error_norm Hc (Hxp Hxs) (Hyn Hys).
  rewrite ThreeProdDWFast_scale ThreeProdDWFast_opp_r !TWval_scale !TWval_opp
    in Hn.
  move: Hn.
  have E : TWval x * pow cx * (- TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProdDWFast x y) * pow (cx + cy)
      - - (TWval x * TWval y * pow (cx + cy))
    = - (TWval (ThreeProdDWFast x y) * pow (cx + cy)
         - TWval x * TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProdDWFast_error_norm Hc (Hxn Hxs) (Hyp Hys).
  rewrite ThreeProdDWFast_scale ThreeProdDWFast_opp !TWval_scale !TWval_opp
    in Hn.
  move: Hn.
  have E : - TWval x * pow cx * (TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProdDWFast x y) * pow (cx + cy)
      - - (TWval x * TWval y * pow (cx + cy))
    = - (TWval (ThreeProdDWFast x y) * pow (cx + cy)
         - TWval x * TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProdDWFast_error_norm Hc (Hxn Hxs) (Hyn Hys).
  have Hxy : ThreeProdDWFast (negTW x) (negTW y) = ThreeProdDWFast x y.
    by rewrite ThreeProdDWFast_opp ThreeProdDWFast_opp_r negTW_id.
  rewrite ThreeProdDWFast_scale Hxy !TWval_scale !TWval_opp in Hn.
  rewrite (_ : - TWval x * pow cx * (- TWval y * pow cy) = TWval x * TWval y *
    pow (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
Qed.

End SecThreeProdDWFast.
