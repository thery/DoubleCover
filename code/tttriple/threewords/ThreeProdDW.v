(* ---------------------------------------------------------------------------*)
(* Algorithm 11 (3Prod^acc_{2,3}): the product of a DOUBLE word by a triple   *)
(* word, and its two correctness results -- the result is a triple word       *)
(* ([ThreeProdDW_isTW]) and the relative error bound [10.5u^3 + 39u^4]        *)
(* ([ThreeProdDW_error]) -- paper Theorem 8 (doc/paper3.pdf, Section 7; see   *)
(* doc/thm8.md).  Generic over the precision [p] (FLX, no [emin]); needs      *)
(* [p >= 6].                                                                  *)
(*                                                                            *)
(* Algorithm 11 IS Algorithm 9 ([ThreeProd.v]) with [x2 = 0]: the FMA         *)
(* [z32 = RN(z01- + x2 y0)] collapses to [z01-] (a float), saving one         *)
(* operation.  Correctness is therefore inherited from Theorem 7; the error   *)
(* bound is not -- taking [x2 = 0] into account gives [10.5u^3 + 39u^4]       *)
(* instead of [28u^3 + 107u^4].                                               *)
(*                                                                            *)
(* STATUS: COMPLETE -- both theorems are PROVED, zero admits.  The file also  *)
(* carries the HEAD lemma Algorithm 13 needs (old paper Section 8.3):         *)
(* [ThreeProdDW_head_gap_norm], the leading limb is within half an ulp plus   *)
(* [60u^2] of the exact product, on top of [inner_sum_err_dw] (the Section    *)
(* 7.2 sources again) and [inner_low_mass_dw].                                *)
(* [ThreeProdDW_isTW] is Theorem 7 at [x2 = 0] (three short lemmas);          *)
(* [ThreeProdDW_error] follows doc/old-triplewors.pdf Section 7.4, which      *)
(* doc/paper3.pdf omits: the tighter Section-7.2 term bounds, the two         *)
(* refinements (a large [eps1] or [eps4] forces a large product; [eps5 <> 0]  *)
(* forces one term below [u^2]) and a five-case assembly.  See doc/thm8.md.   *)
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
Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThreeProdDW.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 11, like Algorithm 9, needs [p >= 6] (paper Section 7).          *)
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

(* Algorithm 9, of which Algorithm 11 is the [x2 = 0] case.                   *)
Local Notation ThreeProd := (ThreeProd p choice).

(* The paper's normalisation [1 <= x0, y0 < 2] and its triple-word packing,   *)
(* both from ThreeProd.v.                                                     *)
Local Notation tw_norm := (tw_norm p).
Local Notation tw_normP := (tw_normP p).

(* ===========================================================================*)
(*  Double-word numbers (paper Definition 3): a pair of floats with           *)
(*  [2|x1| <= ulp x0] -- the standard [x0 = RN(x0 + x1)] separation, STRICTER *)
(*  than the P-nonoverlapping [|x1| < ulp x0] of a triple word.  It is        *)
(*  packaged as a [twR] with a zero third limb, so that Algorithm 9's         *)
(*  machinery (scaling, sign, [isTW]) applies unchanged.                      *)
(* ===========================================================================*)
Definition isDW (x : twR) : Prop :=
  let: TWR x0 x1 x2 := x in
  [/\ format x0, format x1, x2 = 0 & x1 = 0 \/ 2 * Rabs x1 <= ulp x0].

(* ===========================================================================*)
(*  Algorithm 11 -- 3Prod^acc_{2,3}(x, y)                                     *)
(*  (45 operations & 2 tests; paper Section 7).                               *)
(*                                                                            *)
(*  The first five lines are those of Algorithm 9 ([ThreeProd]); then         *)
(*  [z3 = RN(z31 + z01-)] replaces Algorithm 9's [RN(z31 + z32)], since       *)
(*  [z32 = RN(z01- + x2 y0) = z01-] when [x2 = 0].  The third limb of the     *)
(*  first argument is ignored -- it is [0] for a [isDW] input.                *)
(* ===========================================================================*)
Definition ThreeProdDW (x y : twR) : twR :=
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
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* A double word is a triple word with a zero third limb: the DW separation   *)
(* [2|x1| <= ulp x0] is stronger than the P-nonoverlapping [|x1| < ulp x0].   *)
Lemma isDW_isTW x : isDW x -> isTW x.
Proof.
case: x => x0 x1 x2 [F0 F1 -> Hsep].
split=> //; first exact: generic_format_0.
- case: Hsep => [->|Hs]; first by left.
  case: (Req_dec x1 0) => [->|Hx1n]; first by left.
  by right; have := Rabs_pos_lt _ Hx1n; lra.
- by left.
Qed.

(* ===========================================================================*)
(*  Algorithm 11 IS Algorithm 9 at [x2 = 0]: the only difference is           *)
(*  [z32 = RN(z01- + 0 * y0) = z01-], since [z01-] is a rounded value, hence  *)
(*  a float ([round_generic]).  This is the paper's                           *)
(*  "Algorithm 11 is a particular case of Algorithm 9".                       *)
(* ===========================================================================*)
Lemma ThreeProdDW_eq x y :
  ThreeProdDW x y = ThreeProd (TWR (tw0 x) (tw1 x) 0) y.
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProdDW /ThreeProd.
have F01m : format (TwoProd x0 y1).2 by apply: generic_format_round.
case E00 : (TwoProd x0 y0) => [z00p z00m].
case E01 : (TwoProd x0 y1) => [z01p z01m].
case E10 : (TwoProd x1 y0) => [z10p z10m].
have F01 : format z01m by move: F01m; rewrite E01.
by rewrite Rmult_0_l Rplus_0_r (round_generic _ _ _ _ F01).
Qed.

(* ===========================================================================*)
(*  Correctness, part 1: [ThreeProdDW x y] is a triple-word number.           *)
(*                                                                            *)
(*  Paper Section 7.1: since Algorithm 11 is a particular case of Algorithm   *)
(*  9, correctness is directly ensured for [p >= 6].  Formally                *)
(*  [ThreeProdDW x y = ThreeProd (TWR (tw0 x) (tw1 x) 0) y] -- the only       *)
(*  difference, [RN(z01- + 0 * y0) = z01-], is [round_generic] on             *)
(*  [format_err_mul] -- and a DW is a TW with a zero third limb.              *)
(* ===========================================================================*)
Lemma ThreeProdDW_isTW x y :
  ties_to_even choice ->
  isDW x -> isTW y -> isTW (ThreeProdDW x y).
Proof.
move=> Hc Hx Hy.
rewrite ThreeProdDW_eq.
apply: (@ThreeProd_isTW p Hp2 Hp6 choice choice_sym) => //.
have Hx' := isDW_isTW Hx.
by case: x Hx Hx' => x0 x1 x2 [_ _ -> _].
Qed.

(* ===========================================================================*)
(*  The WLOG for Theorem 8.  Every piece goes through [ThreeProdDW_eq] and    *)
(*  Algorithm 9's own scale/sign/zero lemmas -- no induction is redone.       *)
(*  [dw_norm] is [tw_norm] at [x2 = 0] with the DOUBLE-word separation, which *)
(*  is what gives the sharper [|x1| <= u] (Algorithm 9 only had [< 2u]).      *)
(* ===========================================================================*)
Definition dw_norm (x0 x1 : R) : Prop :=
  [/\ format x0, format x1, 1 <= x0, x0 < 2 & x1 = 0 \/ 2 * Rabs x1 <= ulp x0].

Definition dw_normP (t : twR) : Prop :=
  let: TWR t0 t1 t2 := t in dw_norm t0 t1 /\ t2 = 0.

Lemma dw_norm_tw_norm x0 x1 : dw_norm x0 x1 -> tw_norm x0 x1 0.
Proof.
move=> [F0 F1 Hl Hr Hsep].
have F2 : format 0 by exact: generic_format_0.
split=> //.
- case: Hsep => [->|Hs]; first by left.
  case: (Req_dec x1 0) => [->|Hx1n]; first by left.
  by right; have := Rabs_pos_lt _ Hx1n; lra.
- by left.
Qed.

(* The double-word gain: [|x1| <= u], half of what a triple word guarantees.  *)
Lemma dw_norm_x1 x0 x1 : dw_norm x0 x1 -> Rabs x1 <= u.
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulp : ulp x0 = 2 * u
  by apply: (@tw_norm_ulp0 p x0 x1 0); exact: dw_norm_tw_norm.
case: Hn => _ _ _ _ [->|Hs]; first by rewrite Rabs_R0; lra.
by move: Hs; rewrite Hulp; lra.
Qed.

Lemma isDW_scale c t : isDW t -> isDW (scaleTW c t).
Proof.
case: t => t0 t1 t2 [F0 F1 -> Hsep].
have Hpc : 0 < pow c by apply: bpow_gt_0.
split; rewrite /scaleTW /=.
- by apply/(@format_scale p Hp2 choice).
- by apply/(@format_scale p Hp2 choice).
- by ring.
case: Hsep => [->|Hs]; first by left; ring.
right; rewrite (@ulp_scale p Hp2) !Rabs_mult (Rabs_pos_eq (pow c));
  last by lra.
by rewrite -Rmult_assoc; apply: Rmult_le_compat_r; lra.
Qed.

Lemma isDW_opp t : isDW t -> isDW (negTW t).
Proof.
case: t => t0 t1 t2 [F0 F1 -> Hsep].
split; rewrite /negTW /=.
- exact: generic_format_opp.
- exact: generic_format_opp.
- by ring.
case: Hsep => [->|Hs]; first by left; ring.
by right; rewrite Rabs_Ropp ulp_opp.
Qed.

Lemma isDW_normalize t :
  isDW t -> tw0 t <> 0 ->
  exists2 c : Z, True &
    (0 < tw0 t -> dw_normP (scaleTW c t)) /\
    (tw0 t < 0 -> dw_normP (scaleTW c (negTW t))).
Proof.
move=> Ht t0n0.
have [c _ [Hp Hn]] := @isTW_normalize p Hp2 choice t (isDW_isTW Ht) t0n0.
exists c => //; split=> Hsg.
- have Hd := isDW_scale c Ht.
  have Hn' := Hp Hsg.
  case: (scaleTW c t) Hd Hn' => s0 s1 s2 [F0 F1 Hs2 Hsep] [_ Hl Hr _ _].
  by split=> //; split.
have Hd := isDW_scale c (isDW_opp Ht).
have Hn' := Hn Hsg.
case: (scaleTW c (negTW t)) Hd Hn' => s0 s1 s2 [F0 F1 Hs2 Hsep] [_ Hl Hr _ _].
by split=> //; split.
Qed.

Lemma ThreeProdDW_scale a b x y :
  ThreeProdDW (scaleTW a x) (scaleTW b y) =
    scaleTW (a + b) (ThreeProdDW x y).
Proof.
rewrite !ThreeProdDW_eq.
case: x => x0 x1 x2.
have -> : TWR (tw0 (scaleTW a (TWR x0 x1 x2)))
              (tw1 (scaleTW a (TWR x0 x1 x2))) 0
        = scaleTW a (TWR x0 x1 0) by rewrite /scaleTW /=; congr TWR; ring.
by rewrite ThreeProd_scale.
Qed.

Lemma ThreeProdDW_opp x y :
  ThreeProdDW (negTW x) y = negTW (ThreeProdDW x y).
Proof.
rewrite !ThreeProdDW_eq.
case: x => x0 x1 x2.
have -> : TWR (tw0 (negTW (TWR x0 x1 x2))) (tw1 (negTW (TWR x0 x1 x2))) 0
        = negTW (TWR x0 x1 0) by rewrite /negTW /=; congr TWR; ring.
by rewrite (@ThreeProd_opp p choice choice_sym).
Qed.

Lemma ThreeProdDW_opp_r x y :
  ThreeProdDW x (negTW y) = negTW (ThreeProdDW x y).
Proof.
by rewrite !ThreeProdDW_eq (@ThreeProd_opp_r p choice choice_sym).
Qed.

Lemma ThreeProdDW_0l y : ThreeProdDW (TWR 0 0 0) y = TWR 0 0 0.
Proof.
by rewrite ThreeProdDW_eq (@ThreeProd_0l p choice).
Qed.

Lemma ThreeProdDW_0r x : ThreeProdDW x (TWR 0 0 0) = TWR 0 0 0.
Proof.
by rewrite ThreeProdDW_eq ThreeProd_0r.
Qed.

(* ===========================================================================*)
(*  Section 7.2 -- the term bounds.  They are Section 6.1's, sharpened by     *)
(*  [x2 = 0] and by the double-word [|x1| <= u] (Algorithm 9 had [< 2u]):     *)
(*  [|x1y1| < 2u^2] (was [< 4u^2]), [|z10+| <= 2u] (was [< 4u]),              *)
(*  [|z10-| <= u^2] (was [<= 2u^2]), [|c| <= 6u^2] (was [<= 8u^2]),           *)
(*  [|z31| <= 5u^2] (was [<= 6u^2]), [|z3| <= 7u^2] (was [<= 12u^2]).         *)
(* ===========================================================================*)

Lemma x1y1_bound_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 -> Rabs (x1 * y1) < 2 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := dw_norm_x1 Nx.
have Hy1 := @tw_norm_x1 p y0 y1 y2 Ny.
rewrite Rabs_mult.
by have := Rabs_pos x1; have := Rabs_pos y1; nra.
Qed.

(* [eps0 = x1 y2] -- the ONLY ignored product left when [x2 = 0].             *)
Lemma x1y2_bound_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  Rabs (x1 * y2) <= 2 * (u * u * u) - 2 * (u * u * u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := dw_norm_x1 Nx.
have Hy2 := @x2_tight p Hp2 y0 y1 y2 Ny.
rewrite Rabs_mult.
by have := Rabs_pos x1; have := Rabs_pos y2; nra.
Qed.

Lemma z10p_bound_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 -> Rabs (RND (x1 * y0)) <= 2 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := dw_norm_x1 Nx.
case: Ny => _ Hy0l Hy0r _ _.
have F2u : format (2 * u) by rewrite -pow_1mp; apply: format_pow.
apply: Rabs_round_le_r => //.
rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
by have := Rabs_pos x1; nra.
Qed.

Lemma z10m_bound_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  Rabs (x1 * y0 - RND (x1 * y0)) <= u * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := dw_norm_x1 Nx.
case: Ny => _ Hy0l Hy0r _ _.
have Hprod : Rabs (x1 * y0) < 2 * u.
  rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
  by have := Rabs_pos x1; nra.
case: (Req_dec (x1 * y0) 0) => [Hz|Hn0].
  by rewrite Hz round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp (x1 * y0) <= 2 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_1m2p; apply: bpow_le.
  suff : (mag beta (x1 * y0) <= 1 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_1mp.
have He : Rabs (RND (x1 * y0) - x1 * y0) <= / 2 * ulp (x1 * y0)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

Lemma c_bound_dw b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 2 * (u * u) ->
  Rabs (RND (b2 + x1 * y1)) <= 6 * (u * u).
Proof.
move=> H1 H2.
have F6 : format (6 * (u * u))
  by apply: (@format_imul_u2 p Hp2 6); have := @two_p_ge_64 p Hp6; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang b2 (x1 * y1); lra.
Qed.

Lemma z31_bound_dw z10m x0 y2 :
  Rabs z10m <= u * u -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (RND (z10m + x0 * y2)) <= 5 * (u * u).
Proof.
move=> H1 H2.
have F5 : format (5 * (u * u))
  by apply: (@format_imul_u2 p Hp2 5); have := @two_p_ge_64 p Hp6; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z10m (x0 * y2); lra.
Qed.

Lemma z3_bound_dw z31 z01m :
  Rabs z31 <= 5 * (u * u) -> Rabs z01m <= 2 * (u * u) ->
  Rabs (RND (z31 + z01m)) <= 7 * (u * u).
Proof.
move=> H1 H2.
have F7 : format (7 * (u * u))
  by apply: (@format_imul_u2 p Hp2 7); have := @two_p_ge_64 p Hp6; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z31 z01m; lra.
Qed.

(* The three rounding error sources ([eps2] of Algorithm 9 vanishes).         *)
Lemma eps1_bound_dw z10m x0 y2 :
  Rabs z10m <= u * u -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (z10m + x0 * y2 - RND (z10m + x0 * y2)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z10m + x0 * y2) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang z10m (x0 * y2).
  nra.
have Herr := @round_err_le p Hp2 choice _ _ Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

Lemma eps3_bound_dw z31 z01m :
  Rabs z31 <= 5 * (u * u) -> Rabs z01m <= 2 * (u * u) ->
  Rabs (z31 + z01m - RND (z31 + z01m)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z31 + z01m) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang z31 z01m.
  nra.
have Herr := @round_err_le p Hp2 choice _ _ Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

Lemma eps4_bound_dw b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 2 * (u * u) ->
  Rabs (b2 + x1 * y1 - RND (b2 + x1 * y1)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (b2 + x1 * y1) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang b2 (x1 * y1).
  nra.
have Herr := @round_err_le p Hp2 choice _ _ Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

(* ===========================================================================*)
(*  Section 7.4 -- the assemblies.  With [q = 2u^3 + 4.2u^4] the [eps5]       *)
(*  factor and [K] a bound on the numerator [|eps0+eps1+eps3+eps4|], the      *)
(*  relative error over a product [>= A] is [q + (1+q) K / A], so it fits     *)
(*  [C0] as soon as [q A + (1+q) K <= C0 A].  The paper's five cases are      *)
(*  five instances (three with [eps5], two without).                          *)
(* ===========================================================================*)
Lemma assembly_dw_eps5 (K A C0 N S5 sm r : R) :
  0 < A -> A <= r -> 0 <= K -> Rabs N <= K ->
  Rabs S5 <= (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * Rabs sm ->
  Rabs sm <= r + K ->
  (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * A
    + (2 * (u * u * u) + 42 / 10 * (u * u * u * u) + 1) * K <= C0 * A ->
  Rabs (S5 + N) <= C0 * r.
Proof.
move=> HA0 HAr HK0 HN HS5 Hsm Hside.
have Hu0 : 0 < u by apply: u_gt_0.
set q := 2 * (u * u * u) + 42 / 10 * (u * u * u * u).
have Hq0 : 0 <= q by rewrite /q; nra.
have Hsm0 : 0 <= Rabs sm by apply: Rabs_pos.
have HT := Rabs_triang S5 N.
have H1 : Rabs S5 <= q * (r + K).
  by apply: (Rle_trans _ _ _ HS5); apply: Rmult_le_compat_l.
have Hdiff : (q + 1) * K <= (C0 - q) * A by rewrite /q in Hside *; lra.
have Hpos : 0 <= (C0 - q) * A by nra.
have HC0q : 0 <= C0 - q by nra.
have H2 : (C0 - q) * A <= (C0 - q) * r by apply: Rmult_le_compat_l.
lra.
Qed.

Lemma assembly_dw_zero (K A C0 N r : R) :
  0 < A -> A <= r -> Rabs N <= K -> K <= C0 * A -> Rabs N <= C0 * r.
Proof.
move=> HA0 HAr HN HKC.
have Hpos : 0 <= Rabs N by apply: Rabs_pos.
have HC0 : 0 <= C0 by nra.
have H2 : C0 * A <= C0 * r by apply: Rmult_le_compat_l.
lra.
Qed.

(* ===========================================================================*)
(*  Section 7.4, refinement 1 -- a LARGE rounding error forces a LARGE        *)
(*  product.  If [|eps1| > 2u^3] then [|z10- + x0 y2| >= 4u^2], and since     *)
(*  [|z10-| <= u^2] this needs [|x0 y2| >= 3u^2], i.e. [x0 > 1.5].  If        *)
(*  [|eps4| > 2u^3] then [|b2| > 2u^2], so [|z01+ + z10+| >= 4u], which needs *)
(*  [2 x0 + y0 >= 4 - 2u] and hence [x0 y0 >= 1.5 - 2u].  Either way the      *)
(*  product is [>= 1.5 - 6u] instead of just [>= 1 - 4u].                     *)
(* ===========================================================================*)
Lemma eps1_big_prod_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  2 * (u * u * u) <
    Rabs (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2
          - RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)) ->
  15 / 10 - 6 * u <= (x0 + x1 + 0) * (y0 + y1 + y2).
Proof.
move=> Nx Ny Hbig.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hx1 := dw_norm_x1 Nx.
have Hy1 := @x1_tight p Hp2 y0 y1 y2 Ny.
have Hy2 := @x2_tight p Hp2 y0 y1 y2 Ny.
case: (Nx) => _ _ Hx0l Hx0r _.
case: (Ny) => _ Hy0l Hy0r _ _.
have Hz10m : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= u * u.
  rewrite round_generic; first by apply: (z10m_bound_dw Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  case: (Nx) => Fx0 Fx1 _ _ _; case: (Ny) => -[Fy0 Fy1 Fy2] _ _ _ _.
  by apply: generic_format_opp; apply: format_err_mul.
have Hp2m3 : pow (2 - 3 * p) = 4 * (u * u * u).
  rewrite (_ : (2 - 3 * p = 2 + - (3 * p))%Z); last by lia.
  by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
(* A large [eps1] forces [|z10- + x0 y2| >= 4u^2] ...                         *)
have Hge : 4 * (u * u) <= Rabs (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2).
  case: (Rlt_le_dec (Rabs (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2))
          (4 * (u * u))) => [Hsmall|//].
  have Hw : Rabs (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2) < pow (2 - 2 * p)
    by rewrite pow_2m2p.
  have Herr := @round_err_le p Hp2 choice _ _ Hw.
  move: Herr; rewrite (_ : (2 - 2 * p - p = 2 - 3 * p)%Z); last by lia.
  by rewrite Hp2m3; lra.
(* ... hence [|x0 y2| >= 3u^2], and with [|y2| <= 2u^2(1-u)], [x0 >= 1.5].    *)
have Hx0y2 : 3 * (u * u) <= Rabs (x0 * y2).
  have := Rabs_triang (RND (x1 * y0 - RND (x1 * y0))) (x0 * y2).
  by clear -Hge Hz10m; lra.
have Hx0 : 15 / 10 <= x0.
  move: Hx0y2; rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
  move=> H.
  have H2 : x0 * Rabs y2 <= x0 * (2 * (u * u) - 2 * (u * u * u)).
    by apply: Rmult_le_compat_l; [lra | exact: Hy2].
  have Hu2pos : 0 < u * u by nra.
  have H4 : 3 <= 2 * x0 * (1 - u).
    apply: (Rmult_le_reg_r (u * u)) => //.
    clear -H H2 Hu0 Hu64 Hx0l; nra.
  clear -H4 Hu0 Hu64 Hx0l; nra.
have Hyv : 1 - 2 * u - 2 * (u * u) <= y0 + y1 + y2.
  have := Rabs_le_inv _ _ Hy1; have := Rabs_le_inv _ _ Hy2.
  move=> [Hy2l Hy2r] [Hy1l Hy1r]; clear -Hy0l Hy1l Hy2l Hu0 Hu64; nra.
have Hxv : 15 / 10 - u <= x0 + x1 + 0.
  have := Rabs_le_inv _ _ Hx1.
  by move=> [Hx1l Hx1r]; clear -Hx0 Hx1l Hu0; lra.
have Hpos : 0 < 1 - 2 * u - 2 * (u * u) by clear -Hu0 Hu64; nra.
clear -Hxv Hyv Hpos Hu0 Hu64; nra.
Qed.

Lemma eps4_big_prod_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  2 * (u * u * u) <
    Rabs (nth 0 bb 2 + x1 * y1 - RND (nth 0 bb 2 + x1 * y1)) ->
  15 / 10 - 7 * u <= (x0 + x1 + 0) * (y0 + y1 + y2).
Proof.
move=> Nx Ny bb Hbig.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hx1 := dw_norm_x1 Nx.
have Hy1 := @x1_tight p Hp2 y0 y1 y2 Ny.
have Hy2 := @x2_tight p Hp2 y0 y1 y2 Ny.
case: (Nx) => Fx0 Fx1 Hx0l Hx0r _.
case: (Ny) => -[Fy0 Fy1 Fy2] Hy0l Hy0r _ _.
have Hx1y1 := x1y1_bound_dw Nx Ny.
have Hp2m3 : pow (2 - 3 * p) = 4 * (u * u * u).
  rewrite (_ : (2 - 3 * p = 2 + - (3 * p))%Z); last by lia.
  by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
(* A large [eps4] forces [|b2| > 2u^2] ...                                    *)
have Hge : 4 * (u * u) <= Rabs (nth 0 bb 2 + x1 * y1).
  case: (Rlt_le_dec (Rabs (nth 0 bb 2 + x1 * y1)) (4 * (u * u)))
    => [Hsmall|//].
  have Hw : Rabs (nth 0 bb 2 + x1 * y1) < pow (2 - 2 * p) by rewrite pow_2m2p.
  have Herr := @round_err_le p Hp2 choice _ _ Hw.
  move: Herr; rewrite (_ : (2 - 2 * p - p = 2 - 3 * p)%Z); last by lia.
  by rewrite Hp2m3; lra.
have Hb2big : 2 * (u * u) < Rabs (nth 0 bb 2).
  have := Rabs_triang (nth 0 bb 2) (x1 * y1); clear -Hge Hx1y1; lra.
have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
    - RND (RND (x0 * y1) + RND (x1 * y0)).
  rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
    (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
    (generic_format_round _ _ _ _)) /=; ring.
(* ... [b2] being a 2Sum error, [ulp(z01+ + z10+) > 4u^2], so                 *)
(* [|z01+ + z10+| >= 4u] ...                                                  *)
set w := RND (x0 * y1) + RND (x1 * y0).
have Hulpw : 4 * (u * u) < ulp w.
  have Herr : Rabs (RND w - w) <= / 2 * ulp w by apply: error_le_half_ulp.
  move: Hb2big; rewrite Hb2eq -/w.
  by rewrite (_ : w - RND w = -(RND w - w)); [rewrite Rabs_Ropp | ring]; lra.
have Hw4u : 4 * u <= Rabs w.
  case: (Req_dec w 0) => [Hz|Hn0].
    by move: Hulpw; rewrite Hz ulp_FLX_0 => H; clear -H Hu0; nra.
  have Hmag : (3 - p <= mag beta w)%Z.
    have H1 : pow (2 - 2 * p) < pow (cexp w)
      by rewrite -(ulp_neq_0 _ _ _ Hn0) pow_2m2p.
    have := lt_bpow beta _ _ H1.
    by rewrite /cexp /fexp /FLX_exp; lia.
  apply: (Rle_trans _ (pow (mag beta w - 1))); last by apply: bpow_mag_le.
  by rewrite -pow_2mp; apply: bpow_le; lia.
(* ... which needs [2 x0 + y0 (1 + u) >= 4], hence [x0 y0 >= 1.5 - u].        *)
have Hz01p : Rabs (RND (x0 * y1)) <= 2 * u * x0.
  have Hrel := relative_error_le beta Hp2 choice (x0 * y1).
  have Ht := Rabs_triang (x0 * y1) (RND (x0 * y1) - x0 * y1).
  rewrite (_ : x0 * y1 + (RND (x0 * y1) - x0 * y1) = RND (x0 * y1)) in Ht;
    last by ring.
  have Hp' : Rabs (x0 * y1) <= 2 * u * x0 * (1 - u).
    rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
    have := Rabs_pos y1; clear -Hy1 Hx0l Hx0r Hu0 Hu64; nra.
  have Habs := Rabs_pos (x0 * y1).
  clear -Ht Hrel Hp' Hu0 Hu64 Hx0l Hx0r Habs; nra.
have Hz10p : Rabs (RND (x1 * y0)) <= u * y0 * (1 + u).
  have Hrel2 := relative_error_le beta Hp2 choice (x1 * y0).
  have Ht2 := Rabs_triang (x1 * y0) (RND (x1 * y0) - x1 * y0).
  rewrite (_ : x1 * y0 + (RND (x1 * y0) - x1 * y0) = RND (x1 * y0)) in Ht2;
    last by ring.
  have Hp' : Rabs (x1 * y0) <= u * y0.
    rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
    have := Rabs_pos x1; clear -Hx1 Hy0l Hy0r Hu0; nra.
  have Habs2 := Rabs_pos (x1 * y0).
  clear -Ht2 Hrel2 Hp' Hu0 Hu64 Hy0l Hy0r Habs2; nra.
have Hlin : 4 <= 2 * x0 + y0 * (1 + u).
  have HT := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)).
  have H4 : 4 * u <= 2 * u * x0 + u * y0 * (1 + u)
    by rewrite /w in Hw4u; clear -Hw4u HT Hz01p Hz10p; lra.
  apply: (Rmult_le_reg_r u) => //.
  clear -H4 Hu0; nra.
have Hx0y0 : 15 / 10 - u <= x0 * y0.
  case: (Rle_lt_dec x0 (15 / 10 - u)) => [Hle|Hgt].
    have Hy0g : 4 - 2 * u - 2 * x0 <= y0
      by clear -Hlin Hy0l Hy0r Hu0 Hu64; nra.
    clear -Hy0g Hle Hx0l Hy0l Hu0 Hu64; nra.
  clear -Hgt Hy0l Hx0l Hu0; nra.
have Hyv : y0 - 2 * u <= y0 + y1 + y2.
  have := Rabs_le_inv _ _ Hy1; have := Rabs_le_inv _ _ Hy2.
  move=> [Hy2l Hy2r] [Hy1l Hy1r]; clear -Hy1l Hy2l Hu0 Hu64; nra.
have Hxv : x0 - u <= x0 + x1 + 0.
  have := Rabs_le_inv _ _ Hx1.
  by move=> [Hx1l Hx1r]; clear -Hx1l; lra.
have Hpos1 : 0 < x0 - u by clear -Hx0l Hu0 Hu64; lra.
have Hpos2 : 0 < y0 - 2 * u by clear -Hy0l Hu0 Hu64; lra.
have Hprod : (x0 - u) * (y0 - 2 * u) <= (x0 + x1 + 0) * (y0 + y1 + y2).
  apply: Rmult_le_compat; try lra.
clear -Hprod Hx0y0 Hx0l Hx0r Hy0l Hy0r Hu0 Hu64; nra.
Qed.

(* ===========================================================================*)
(*  Section 7.4, refinement 2 -- [eps5 <> 0] is constraining.  Either the     *)
(*  head [r0] is [>= 2] (and then the product is [>= 2 - 5u]), or one of the  *)
(*  four terms fails to be a multiple of [2u^3], hence is [< u^2] -- which    *)
(*  shrinks [eps0], [eps3] or [eps4].                                         *)
(* ===========================================================================*)
Lemma eps5nz_dw x0 x1 y0 y1 y2 :
  ties_to_even choice -> dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (x0 * y1 - RND (x0 * y1))) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3] in
  Rabs ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e)
    <= 14 * (u * u * u) - 2 * (u * u * u * u) ->
  sumR (vseb e) - sumR (vsebK 3 e) <> 0 ->
  2 - 5 * u <= (x0 + x1 + 0) * (y0 + y1 + y2) \/
  [\/ Rabs (RND (x0 * y1)) < u * u, Rabs (RND (x1 * y0)) < u * u,
       Rabs c < u * u | Rabs z3 < u * u].
Proof.
move=> Hc Nx Ny bb c z3 e HNb HE5.
case: (Rle_lt_dec (2 - 5 * u) ((x0 + x1 + 0) * (y0 + y1 + y2)))
  => [Hbig|Hsmall]; first by left.
right.
case: (Rlt_le_dec (Rabs (RND (x0 * y1))) (u * u)) => [Hs|H1];
  first by apply: Or41.
case: (Rlt_le_dec (Rabs (RND (x1 * y0))) (u * u)) => [Hs|H2];
  first by apply: Or42.
case: (Rlt_le_dec (Rabs c) (u * u)) => [Hs|H3]; first by apply: Or43.
case: (Rlt_le_dec (Rabs z3) (u * u)) => [Hs|H4]; first by apply: Or44.
(* All four terms are big: we show [eps5 = 0], contradicting [HE5].           *)
case: HE5.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Nx' : tw_norm x0 x1 0 by exact: dw_norm_tw_norm Nx.
have [[Fx0 Fx1 Fx2'] Hx0l Hx0r _ _] := Nx'.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r _ _] := Ny.
(* Everything lives on the [2u^3 = pow (1 - 3p)] grid: a float [>= u^2] has   *)
(* [cexp >= 1 - 3p].                                                          *)
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
have Ic : is_imul c (pow g)
  by apply: Hbig_imul => //; rewrite /c; apply: generic_format_round.
have Iz3 : is_imul z3 (pow g)
  by apply: Hbig_imul => //; rewrite /z3; apply: generic_format_round.
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
have Feinp : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3],
    forall t, format t}.
  move=> t; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
    try apply: generic_format_round; apply: Fnthbb.
have Ieinp : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3],
    forall t, is_imul t (pow g)}.
  move=> t; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]].
have Ie : {in e, forall t, is_imul t (pow g)}
  by rewrite /e; apply: vecSum_imul_forward.
have Fe : {in e, forall t, format t}
  by rewrite /e; apply: (@format_vecSum p Hp2 choice).
have Ivse : {in vseb e, forall t, is_imul t (pow g)}
  by apply: vseb_imul_forward.
have Hsz5 : size e = 5%N by rewrite /e size_vecSum.
have Fno : Fnonoverlap e.
  have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
            = RND (x0 * y1 - RND (x0 * y1)).
    by rewrite Rmult_0_l Rplus_0_r round_generic //;
       apply: generic_format_round.
  have Fno0 := @inner_Fnonoverlap p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2
    Hc Nx' Ny.
  have Fno1 : Fnonoverlap (vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + x1 * y1);
      RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0))]) by exact: Fno0.
  by move: Fno1; rewrite Hz32.
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall t, format t}
  by apply: (@format_vseb p Hp2 choice e Fe).
have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 (vseb e))
  by rewrite /vsebK -{1}(cat_take_drop 3 (vseb e)) sumR_cat; ring.
rewrite Hsplit.
have Hxpos : 0 < (x0 + x1 + 0) * (y0 + y1 + y2).
  have Hx1b := dw_norm_x1 Nx.
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
      <= 2 - 5 * u + (14 * (u * u * u) - 2 * (u * u * u * u)).
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

(* [|RN t| < u^2] caps the rounding error at [1/2 u^3] (Algorithm 9's [Hred]  *)
(* pattern one binade lower); used for the [|c| < u^2] and [|z3| < u^2] cases.*)
Lemma err_small_of_round t :
  Rabs (RND t) < u * u -> Rabs (t - RND t) <= / 2 * (u * u * u).
Proof.
move=> Hlt.
have Hu0 : 0 < u by apply: u_gt_0.
have Herr := @error_le_half_ulp_round beta (FLX_exp p)
  (FLX_exp_valid p) (FLX_exp_monotone p) choice t.
have Hulp : ulp (RND t) <= u * u * u.
  case: (Req_dec (RND t) 0) => [Hz|Hn0].
    rewrite Hz ulp_FLX_0; clear -Hu0; nra.
  rewrite ulp_neq_0 //.
  rewrite u3_pow; apply: bpow_le.
  have Hmag : (mag beta (RND t) <= - (2 * p))%Z.
    by apply: mag_le_bpow => //; rewrite -u2_pow.
  have Hcx : cexp (RND t) = (mag beta (RND t) - p)%Z
    by rewrite /cexp /fexp /FLX_exp.
  rewrite Hcx; lia.
have Hpp : Prec_gt_0 p by rewrite /Prec_gt_0; lia.
move: (Herr Hpp); rewrite Rabs_minus_sym; lra.
Qed.

(* A small [z01+] (resp. [z10+]) caps [eps0 = x1 y2] at [2u^4].               *)
Lemma eps0_small_of_z01p x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 -> Rabs (RND (x0 * y1)) < u * u ->
  Rabs (x1 * y2) <= 2 * (u * u * u * u).
Proof.
move=> Nx Ny Hlt.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hx1 := dw_norm_x1 Nx.
case: (Nx) => _ _ Hx0l Hx0r _.
have Hrel := relative_error_le beta Hp2 choice (x0 * y1).
have Hprod : Rabs (x0 * y1) < 2 * (u * u).
  have Ht : Rabs (x0 * y1) <= Rabs (RND (x0 * y1)) + u * Rabs (x0 * y1).
    have := Rabs_triang (RND (x0 * y1)) (x0 * y1 - RND (x0 * y1)).
    have -> : RND (x0 * y1) + (x0 * y1 - RND (x0 * y1)) = x0 * y1 by ring.
    by rewrite Rabs_minus_sym in Hrel; lra.
  clear -Ht Hlt Hu0 Hu64; nra.
have Hy1 : Rabs y1 < 2 * (u * u).
  move: Hprod; rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
  by have := Rabs_pos y1; nra.
have Hulpy1 : ulp y1 <= 2 * (u * u * u).
  rewrite -pow_1m3p; apply: bound_ulp_FLX => //.
  by rewrite (_ : (1 - 3 * p + p = 1 - 2 * p)%Z) ?pow_1m2p //; lia.
have Hy2 : Rabs y2 <= 2 * (u * u * u).
  case: Ny => _ _ _ _ [->|Hy2o]; first by rewrite Rabs_R0; nra.
  by lra.
rewrite Rabs_mult.
by have := Rabs_pos x1; have := Rabs_pos y2; nra.
Qed.

Lemma eps0_small_of_z10p x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 -> Rabs (RND (x1 * y0)) < u * u ->
  Rabs (x1 * y2) <= 2 * (u * u * u * u).
Proof.
move=> Nx Ny Hlt.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Hy2 := @x2_tight p Hp2 y0 y1 y2 Ny.
case: (Ny) => _ Hy0l Hy0r _ _.
have Hrel := relative_error_le beta Hp2 choice (x1 * y0).
have Hprod : Rabs (x1 * y0) * (1 - u) < u * u.
  have Ht : Rabs (x1 * y0) <= Rabs (RND (x1 * y0)) + u * Rabs (x1 * y0).
    have := Rabs_triang (RND (x1 * y0)) (x1 * y0 - RND (x1 * y0)).
    have -> : RND (x1 * y0) + (x1 * y0 - RND (x1 * y0)) = x1 * y0 by ring.
    by rewrite Rabs_minus_sym in Hrel; lra.
  clear -Ht Hlt Hu0 Hu64; nra.
have Hx1 : Rabs x1 * (1 - u) < u * u.
  move: Hprod; rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
  by have := Rabs_pos x1; nra.
rewrite Rabs_mult.
have H2 : Rabs x1 * Rabs y2 <= Rabs x1 * (2 * (u * u) - 2 * (u * u * u)).
  by apply: Rmult_le_compat_l => //; apply: Rabs_pos.
have Hx1p := Rabs_pos x1.
clear -H2 Hx1 Hu0 Hu64 Hx1p; nra.
Qed.

(* ===========================================================================*)
(*  The head limb, for Algorithm 13 (old paper Section 8.3)                   *)
(*                                                                            *)
(*  [3Reci] needs to know that the leading limb of [3Prod_{2,3}(b, x)] is     *)
(*  exactly [1] when the product is within [35u^2] of [1].  No property of    *)
(*  the OUTPUT can give that -- [(1 + 2u, -2u + 2u^2, ...)] is a legal triple *)
(*  word summing to [1 + O(u^2)] -- so the argument runs on the INNER VecSum, *)
(*  whose two leading limbs are the two words of a single 2Sum and are        *)
(*  therefore half an ulp apart ([vecSum_head_gap] in VecSum.v).              *)
(*                                                                            *)
(*  What that generic lemma asks of the algorithm is exactly two numbers:     *)
(*  [D], how far the product is from the exact sum of the VecSum inputs       *)
(*  ([inner_sum_err_dw], the Section 7.2 error sources again), and [B], the   *)
(*  mass of the four inputs below the leading one ([inner_low_mass_dw] --     *)
(*  they are all [O(u)] here, which is what makes the whole tail [O(u^2)]     *)
(*  against the half-ulp).                                                    *)
(* ===========================================================================*)

(* [D]: the product minus the exact sum of the inner VecSum's inputs.  This   *)
(* is the numerator [N] of Theorem 8's proof, at its naive bound.             *)
Lemma inner_sum_err_dw x0 x1 y0 y1 y2 :
  ties_to_even choice -> dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Rabs ((x0 + x1 + 0) * (y0 + y1 + y2)
        - sumR (vecSum
            [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                RND (nth 0 bb 2 + x1 * y1);
                RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                   + RND (x0 * y1 - RND (x0 * y1)))]))
    <= 14 * (u * u * u) - 2 * (u * u * u * u).
Proof.
move=> Hc Nxd Ny bb.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Nx' : tw_norm x0 x1 0 by exact: dw_norm_tw_norm Nxd.
set z01m := RND (x0 * y1 - RND (x0 * y1)).
set z10m := RND (x1 * y0 - RND (x1 * y0)).
set c := RND (nth 0 bb 2 + x1 * y1).
set z31 := RND (z10m + x0 * y2).
set z3 := RND (z31 + z01m).
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3].
(* [x2 = 0] collapses Algorithm 9's [z32 = RN(z01- + x2 y0)] to [z01-].       *)
have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
          = RND (x0 * y1 - RND (x0 * y1)).
  by rewrite Rmult_0_l Rplus_0_r round_generic //; apply: generic_format_round.
have Hdecomp0 := @sumR_e_decomp p Hp2 choice choice_sym x0 x1 0 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) z01m (RND (x1 * y0)) z10m bb c z31
  (RND (z01m + 0 * y0)) (RND (z31 + RND (z01m + 0 * y0)))
  (ltac:(by case: Nx' => -[]) : format x0)
  (ltac:(by case: Nx' => -[]) : format x1)
  (ltac:(by case: Ny => -[]) : format y0)
  (ltac:(by case: Ny => -[]) : format y1)
  erefl erefl erefl erefl erefl erefl erefl erefl.
move: Hdecomp0; rewrite Hz32 -/z3 -/e => Hdecomp.
have HN : (x0 + x1 + 0) * (y0 + y1 + y2) - sumR e
        = x1 * y2 + (z10m + x0 * y2 - z31) + (z31 + z01m - z3)
          + (nth 0 bb 2 + x1 * y1 - c) by rewrite Hdecomp -/z01m; ring.
have Hz10m : Rabs z10m <= u * u.
  rewrite /z10m round_generic; first by apply: (z10m_bound_dw Nxd Ny).
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0));
    last by ring.
  by apply: generic_format_opp; apply: format_err_mul.
have Hz01m : Rabs z01m <= 2 * (u * u).
  rewrite /z01m round_generic;
    first by apply: (@z01m_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
  have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
  have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1));
    last by ring.
  by apply: generic_format_opp; apply: format_err_mul.
have Hx0y2 := @x0y2_bound p Hp2 x0 x1 0 y0 y1 y2 Nx' Ny.
have Hx1y1 := x1y1_bound_dw Nxd Ny.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
have Hz31 : Rabs z31 <= 5 * (u * u) by apply: (z31_bound_dw Hz10m Hx0y2).
(* The four Section-7.2 error sources ([eps2] vanishes with [x2 = 0]).        *)
have Heps0 := x1y2_bound_dw Nxd Ny.
have Heps1 : Rabs (z10m + x0 * y2 - z31) <= 4 * (u * u * u)
  by apply: (eps1_bound_dw Hz10m Hx0y2).
have Heps3 : Rabs (z31 + z01m - z3) <= 4 * (u * u * u)
  by apply: (eps3_bound_dw Hz31 Hz01m).
have Heps4 : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 4 * (u * u * u)
  by apply: (eps4_bound_dw Hb2 Hx1y1).
rewrite HN.
have T1 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31)
                        + (z31 + z01m - z3)) (nth 0 bb 2 + x1 * y1 - c).
have T2 := Rabs_triang (x1 * y2 + (z10m + x0 * y2 - z31)) (z31 + z01m - z3).
have T3 := Rabs_triang (x1 * y2) (z10m + x0 * y2 - z31).
by lra.
Qed.

(* [B]: the four inner VecSum entries below the leading one are all [O(u)].   *)
Lemma inner_low_mass_dw x0 x1 y0 y1 y2 :
  dw_norm x0 x1 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  sumRabs [:: nth 0 bb 0; nth 0 bb 1;
              RND (nth 0 bb 2 + x1 * y1);
              RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (x0 * y1 - RND (x0 * y1)))]
    <= 9 * u.
Proof.
move=> Nxd Ny bb.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
have Nx' : tw_norm x0 x1 0 by exact: dw_norm_tw_norm Nxd.
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
have Hz10p : Rabs (RND (x1 * y0)) <= 2 * u by apply: (z10p_bound_dw Nxd Ny).
(* [b0] is a running sum of three [O(u)] terms; [b1] is its 2Sum error.       *)
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
  rewrite round_generic; first by apply: (z10m_bound_dw Nxd Ny).
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
have Hx1y1 := x1y1_bound_dw Nxd Ny.
have Hz31 : Rabs (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)) <= 5 * (u * u)
  by apply: (z31_bound_dw Hz10m Hx0y2).
have Hz3 : Rabs (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                     + RND (x0 * y1 - RND (x0 * y1)))) <= 7 * (u * u)
  by apply: (z3_bound_dw Hz31 Hz01m).
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny).
have Hc6 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 6 * (u * u)
  by apply: (c_bound_dw Hb2 Hx1y1).
have E3 : (1 + u) ^ 3 = 1 + 3 * u + 3 * (u * u) + u * u * u by ring.
have Hu2 : u * u <= / 64 * u by nra.
have Hu3 : u * u * u <= / 64 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
(* [sumRabs] on the explicit four-element list -- NOT [/=], which would       *)
(* unfold the [vecSum] hiding in [bb].                                        *)
have Hs4 : forall a b c d : R,
    sumRabs [:: a; b; c; d] = Rabs a + Rabs b + Rabs c + Rabs d.
  by move=> a b c d; rewrite /=; ring.
rewrite Hs4 E3 in Hb0 *.
have Hb0p := Rabs_pos (nth 0 bb 0).
by clear -Hb0 Hb1 Hc6 Hz3 Hu0 Hu64 Hu2 Hu3 Hu4 Hb0p; nra.
Qed.

(* The head lemma itself (normalised): the leading limb of the result is      *)
(* within HALF AN ULP of itself, plus [60u^2], of the exact product.  This is *)
(* [vecSum_head_gap] on the inner VecSum, fed with [inner_sum_err_dw] ([D])   *)
(* and [inner_low_mass_dw] ([B]); the leading limb of the OUTPUT is the       *)
(* leading limb of that VecSum by the star identity of Section 6.2.           *)
Lemma ThreeProdDW_head_gap_norm x y :
  ties_to_even choice -> dw_normP x -> tw_normP y ->
  Rabs (TWval x * TWval y - tw0 (ThreeProdDW x y))
    <= / 2 * ulp (tw0 (ThreeProdDW x y)) + 60 * (u * u).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 [Nxd ->].
case: y Ny => y0 y1 y2 Ny.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
have Nx' : tw_norm x0 x1 0 by exact: dw_norm_tw_norm Nxd.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
rewrite ThreeProdDW_eq !tw0E !tw1E.
rewrite (@ThreeProd_norm_eq p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2 Hc
  Nx' Ny').
have Hz32 : RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0)
          = RND (x0 * y1 - RND (x0 * y1)).
  by rewrite Rmult_0_l Rplus_0_r round_generic //; apply: generic_format_round.
rewrite Hz32.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1);
                     RND (x1 * y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                    RND (nth 0 bb 2 + x1 * y1);
                    RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                       + RND (x0 * y1 - RND (x0 * y1)))].
rewrite tw0E /TWval.
have FL5 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                   RND (nth 0 bb 2 + x1 * y1);
                   RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                      + RND (x0 * y1 - RND (x0 * y1)))],
    forall z : R, format z}.
  have Fbb : {in bb, forall z : R, format z}.
    apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
    by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
  have Fnthbb : forall i, format (nth 0 bb i).
    move=> i; case: (ltnP i (size bb)) => Hi;
      last by rewrite nth_default //; exact: generic_format_0.
    by apply: Fbb; apply: mem_nth.
  move=> z; rewrite !inE.
  move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
    try apply: generic_format_round; apply: Fnthbb.
(* The star identity of Section 6.2: [VSEB] emits the leading VecSum limb     *)
(* unchanged, so the head of the OUTPUT is the head of the inner VecSum.      *)
have Hstar : nth 0 (vseb e) 0 = nth 0 e 0.
  case: (Req_dec (nth 0 e 1) 0) => [He1|He1].
    have H := @vseb_head3_e1zero p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2
      Hc Nx' Ny'.
    move: H; rewrite Hz32 -/bb -/e => H.
    by have [H0 _] := H He1.
  have Hs := @vseb_star p Hp2 choice choice_sym _ FL5 (isT : (1 < 5)%N) He1.
  by rewrite -/e in Hs; rewrite Hs.
have HD := inner_sum_err_dw Hc Nxd Ny'.
have HB := inner_low_mass_dw Nxd Ny'.
(* [let]-bound statements do not rewrite; bridge them by conversion.          *)
have HD2 : Rabs ((x0 + x1 + 0) * (y0 + y1 + y2) - sumR e)
    <= 14 * (u * u * u) - 2 * (u * u * u * u) by exact: HD.
have HB2 : sumRabs [:: nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
                       RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                          + RND (x0 * y1 - RND (x0 * y1)))] <= 9 * u
  by exact: HB.
(* [vecSum] is exact as a sum, so [D] may be read on the INPUT list.          *)
have HDL : Rabs ((x0 + x1 + 0) * (y0 + y1 + y2)
    - sumR [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
               RND (nth 0 bb 2 + x1 * y1);
               RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                  + RND (x0 * y1 - RND (x0 * y1)))])
    <= 14 * (u * u * u) - 2 * (u * u * u * u).
  by rewrite -(@vecSum_sum p Hp2 choice choice_sym _ FL5) -/e.
have Hgap := @vecSum_head_gap p Hp2 choice choice_sym
  [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
      RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (x0 * y1 - RND (x0 * y1)))]
  ((x0 + x1 + 0) * (y0 + y1 + y2)) (14 * (u * u * u) - 2 * (u * u * u * u))
  (9 * u) FL5 (isT : (1 < 5)%N) HDL HB2.
rewrite Hstar.
rewrite -/e in Hgap.
apply: Rle_trans Hgap _.
have -> : (size [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
                    RND (nth 0 bb 2 + x1 * y1);
                    RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                       + RND (x0 * y1 - RND (x0 * y1)))]).-1 = 4%N by [].
have HI : INR 4 = 4 by rewrite /=; ring.
have E4 : (1 + u) ^ 4 = 1 + 4 * u + 6 * (u * u) + 4 * (u * u * u)
                        + u * u * u * u by ring.
rewrite HI E4.
have Hu2 : u * u <= / 64 * u by nra.
have Hu3 : u * u * u <= / 64 * (u * u) by nra.
have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
have Hu5 : u * u * u * u * u <= / 64 * (u * u * u * u) by nra.
by clear -Hu0 Hu64 Hu2 Hu3 Hu4 Hu5; nra.
Qed.

(* Theorem 8, normalised (paper WLOG [1 <= x0, y0 < 2]).                      *)
Lemma ThreeProdDW_error_norm x y :
  ties_to_even choice -> dw_normP x -> tw_normP y ->
  Rabs (TWval (ThreeProdDW x y) - TWval x * TWval y) <=
     (105 / 10 * (u * u * u) + 39 * (u * u * u * u)) *
       Rabs (TWval x * TWval y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 [Nxd ->].
case: y Ny => y0 y1 y2 Ny.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
have Nx' : tw_norm x0 x1 0 by exact: dw_norm_tw_norm Nxd.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := @u_le_64 p Hp6.
rewrite ThreeProdDW_eq !tw0E !tw1E.
rewrite (@ThreeProd_norm_eq p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2 Hc
  Nx' Ny').
(* [x2 = 0] collapses Algorithm 9's [z32 = RN(z01- + x2 y0)] to [z01-].       *)
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
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3].
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
(* Algorithm 9's F-nonoverlapping of the inner VecSum, at [x2 = 0].           *)
have Fno : Fnonoverlap e.
  have Fno0 := @inner_Fnonoverlap p Hp2 Hp6 choice choice_sym x0 x1 0 y0 y1 y2
    Hc Nx' Ny'.
  have Fno1 : Fnonoverlap (vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + x1 * y1);
      RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + 0 * y0))]) by exact: Fno0.
  by move: Fno1; rewrite Hz32.
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall z, format z}
  by apply: (@format_vseb p Hp2 choice e Fe).
(* Algorithm 9's error identity, again at [x2 = 0]: [eps0] loses its [x2]     *)
(* terms and [eps2] vanishes.                                                 *)
have Hdecomp0 := @sumR_e_decomp p Hp2 choice choice_sym x0 x1 0 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) z01m (RND (x1 * y0)) z10m bb c z31
  (RND (z01m + 0 * y0)) (RND (z31 + RND (z01m + 0 * y0)))
  (ltac:(by case: Nx' => -[]) : format x0)
  (ltac:(by case: Nx' => -[]) : format x1)
  (ltac:(by case: Ny' => -[]) : format y0)
  (ltac:(by case: Ny' => -[]) : format y1)
  erefl erefl erefl erefl erefl erefl erefl erefl.
move: Hdecomp0; rewrite Hz32 -/z3 -/e => Hdecomp.
have HN : (x0 + x1 + 0) * (y0 + y1 + y2) - sumR e
        = x1 * y2 + (z10m + x0 * y2 - z31) + (z31 + z01m - z3)
          + (nth 0 bb 2 + x1 * y1 - c) by rewrite Hdecomp -/z01m; ring.
have Hz10m : Rabs z10m <= u * u.
  rewrite /z10m round_generic; first by apply: (z10m_bound_dw Nxd Ny').
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
have Hx1y1 := x1y1_bound_dw Nxd Ny'.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (@vecSum3 p Hp2 choice choice_sym _ _ _
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (@b2_bound p Hp2 choice x0 x1 0 y0 y1 y2 Nx' Ny').
have Hz31 : Rabs z31 <= 5 * (u * u) by apply: (z31_bound_dw Hz10m Hx0y2).
have Hz3b : Rabs z3 <= 7 * (u * u) by apply: (z3_bound_dw Hz31 Hz01m).
have Hc6 : Rabs c <= 6 * (u * u) by apply: (c_bound_dw Hb2 Hx1y1).
have Heps0 := x1y2_bound_dw Nxd Ny'.
have Heps1 : Rabs (z10m + x0 * y2 - z31) <= 4 * (u * u * u)
  by apply: (eps1_bound_dw Hz10m Hx0y2).
have Heps3 : Rabs (z31 + z01m - z3) <= 4 * (u * u * u)
  by apply: (eps3_bound_dw Hz31 Hz01m).
have Heps4 : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 4 * (u * u * u)
  by apply: (eps4_bound_dw Hb2 Hx1y1).
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
have HNgen : forall E0 E1 E3 E4,
    Rabs (x1 * y2) <= E0 -> Rabs (z10m + x0 * y2 - z31) <= E1 ->
    Rabs (z31 + z01m - z3) <= E3 -> Rabs (nth 0 bb 2 + x1 * y1 - c) <= E4 ->
    Rabs N <= E0 + E1 + E3 + E4.
  move=> E0 E1 E3 E4 H0 H1 H3 H4.
  rewrite /N HN.
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
have HNnaive : Rabs N <= 14 * (u * u * u) - 2 * (u * u * u * u).
  have := HNgen _ _ _ _ Heps0 Heps1 Heps3 Heps4; lra.
(* Case 1: the product is large, [x*y >= 2 - 5u]; the naive numerator does.   *)
case: (Rle_lt_dec (2 - 5 * u) r) => [HA | Hlt2].
  apply: (@assembly_dw_eps5 (14 * (u * u * u) - 2 * (u * u * u * u))
            (2 - 5 * u) _ N S5 (sumR (vseb e)) r).
  - clear -Hu0 Hu64; nra.
  - exact: HA.
  - clear -Hu0 Hu64; nra.
  - exact: HNnaive.
  - exact: Hs5.
  - by apply: Hsm.
  - clear -Hu0 Hu64; nra.
(* Cases 2-3: [x*y >= 1.5 - 6u].                                              *)
case: (Rle_lt_dec (15 / 10 - 7 * u) r) => [HB | Hlow].
  case: (Req_dec S5 0) => [HS5z | HS5n].
    rewrite HS5z Rplus_0_l.
    apply: (@assembly_dw_zero (14 * (u * u * u) - 2 * (u * u * u * u))
              (15 / 10 - 7 * u) _ N r).
    - clear -Hu0 Hu64; nra.
    - exact: HB.
    - exact: HNnaive.
    - have Hu2 : u * u <= / 64 * u by nra.
      have Hu3 : u * u * u <= / 64 * (u * u) by nra.
      have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
      clear -Hu0 Hu64 Hu2 Hu3 Hu4; nra.
  (* [eps5 <> 0] shrinks one source: worst case [12u^3 + 2u^4].               *)
  have Hdisj := eps5nz_dw Hc Nxd Ny' HNnaive HS5n.
  have HNC : Rabs N <= 12 * (u * u * u) + 2 * (u * u * u * u).
    case: Hdisj => [Hbig | Hcase].
      have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
      by rewrite -/r in Hlt2 *; lra.
    case: Hcase => [H1|H2|H3|H4].
    - have H0 := eps0_small_of_z01p Nxd Ny' H1.
      have := HNgen _ _ _ _ H0 Heps1 Heps3 Heps4; clear -Hu0 Hu64; nra.
    - have H0 := eps0_small_of_z10p Nxd Ny' H2.
      have := HNgen _ _ _ _ H0 Heps1 Heps3 Heps4; clear -Hu0 Hu64; nra.
    - have H4' : Rabs (nth 0 bb 2 + x1 * y1 - c) <= / 2 * (u * u * u)
        by apply: err_small_of_round.
      have := HNgen _ _ _ _ Heps0 Heps1 Heps3 H4'; clear -Hu0 Hu64; nra.
    - have H3' : Rabs (z31 + z01m - z3) <= / 2 * (u * u * u)
        by apply: err_small_of_round.
      have := HNgen _ _ _ _ Heps0 Heps1 H3' Heps4; clear -Hu0 Hu64; nra.
  apply: (@assembly_dw_eps5 (12 * (u * u * u) + 2 * (u * u * u * u))
            (15 / 10 - 7 * u) _ N S5 (sumR (vseb e)) r).
  - clear -Hu0 Hu64; nra.
  - exact: HB.
  - clear -Hu0 Hu64; nra.
  - exact: HNC.
  - exact: Hs5.
  - by apply: Hsm.
  - have Hu2 : u * u <= / 64 * u by nra.
    have Hu3 : u * u * u <= / 64 * (u * u) by nra.
    have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
    clear -Hu0 Hu64 Hu2 Hu3 Hu4; nra.
(* Cases 4-5: the product is small, so [eps1] and [eps4] are small too        *)
(* (contrapositive of the two refinement lemmas).                             *)
have Hne1 : Rabs (z10m + x0 * y2 - z31) <= 2 * (u * u * u).
  case: (Rle_lt_dec (Rabs (z10m + x0 * y2 - z31)) (2 * (u * u * u)))
    => [//|Hbig].
  have Hb := eps1_big_prod_dw Nxd Ny' Hbig.
  have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
  by rewrite -/r in Hlow *; lra.
have Hne4 : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 2 * (u * u * u).
  case: (Rle_lt_dec (Rabs (nth 0 bb 2 + x1 * y1 - c)) (2 * (u * u * u)))
    => [//|Hbig].
  have Hb := eps4_big_prod_dw Nxd Ny' Hbig.
  have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
  by rewrite -/r in Hlow *; lra.
case: (Req_dec S5 0) => [HS5z | HS5n].
  rewrite HS5z Rplus_0_l.
  apply: (@assembly_dw_zero (10 * (u * u * u) - 2 * (u * u * u * u))
            (1 - 4 * u) _ N r).
  - clear -Hu0 Hu64; nra.
  - by rewrite -/r in Hxy1.
  - have := HNgen _ _ _ _ Heps0 Hne1 Heps3 Hne4; clear -Hu0 Hu64; nra.
  - have Hu2 : u * u <= / 64 * u by nra.
    have Hu3 : u * u * u <= / 64 * (u * u) by nra.
    have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
    clear -Hu0 Hu64 Hu2 Hu3 Hu4; nra.
have Hdisj := eps5nz_dw Hc Nxd Ny' HNnaive HS5n.
have HNE : Rabs N <= 85 / 10 * (u * u * u) - 2 * (u * u * u * u).
  case: Hdisj => [Hbig | Hcase].
    have := Rle_abs ((x0 + x1 + 0) * (y0 + y1 + y2)).
    by rewrite -/r in Hlt2 *; lra.
  case: Hcase => [H1|H2|H3|H4].
  - have H0 := eps0_small_of_z01p Nxd Ny' H1.
    have := HNgen _ _ _ _ H0 Hne1 Heps3 Hne4; clear -Hu0 Hu64; nra.
  - have H0 := eps0_small_of_z10p Nxd Ny' H2.
    have := HNgen _ _ _ _ H0 Hne1 Heps3 Hne4; clear -Hu0 Hu64; nra.
  - have H4' : Rabs (nth 0 bb 2 + x1 * y1 - c) <= / 2 * (u * u * u)
      by apply: err_small_of_round.
    have := HNgen _ _ _ _ Heps0 Hne1 Heps3 H4'; clear -Hu0 Hu64; nra.
  - have H3' : Rabs (z31 + z01m - z3) <= / 2 * (u * u * u)
      by apply: err_small_of_round.
    have := HNgen _ _ _ _ Heps0 Hne1 H3' Hne4; clear -Hu0 Hu64; nra.
apply: (@assembly_dw_eps5 (85 / 10 * (u * u * u) - 2 * (u * u * u * u))
          (1 - 4 * u) _ N S5 (sumR (vseb e)) r).
- clear -Hu0 Hu64; nra.
- by rewrite -/r in Hxy1.
- clear -Hu0 Hu64; nra.
- exact: HNE.
- exact: Hs5.
- by apply: Hsm.
- have Hu2 : u * u <= / 64 * u by nra.
  have Hu3 : u * u * u <= / 64 * (u * u) by nra.
  have Hu4 : u * u * u * u <= / 64 * (u * u * u) by nra.
  have Hu5 : u * u * u * u * u <= / 64 * (u * u * u * u) by nra.
  clear -Hu0 Hu64 Hu2 Hu3 Hu4 Hu5; nra.
Qed.

(* ===========================================================================*)
(*  Theorem 8: relative error of [ThreeProdDW] is [<= 10.5u^3 + 39u^4].       *)
(*                                                                            *)
(*  Proof OMITTED in doc/paper3.pdf; recovered from doc/old-triplewors.pdf    *)
(*  Section 7.4 (Theorem 11) -- see doc/thm8.md.  With [x2 = 0] the error     *)
(*  sources shrink to                                                         *)
(*                                                                            *)
(*    |eps0| = |x1 y2| <= 2u^3 - 2u^4     (and [|x1| <= u], a DW)             *)
(*    |eps1| = |(z10- + x0 y2) - z31| <= 4u^3                                 *)
(*    |eps3| = |(z31 + z01-) - z3|    <= 4u^3       (there is NO eps2)        *)
(*    |eps4| = |(b2 + x1 y1) - c|     <= 4u^3                                 *)
(*    |eps5| <= (2u^3 + 4.2u^4)|z00+ + b0 + b1 + c + z3|                      *)
(*                                                                            *)
(*  giving a naive [16u^3 + 62u^4]; the paper's [10.5u^3 + 39u^4] needs two   *)
(*  refinements (a large [eps1] or [eps4] forces [x*y >= 1.5 - 6u], and       *)
(*  [eps5 <> 0] forces one of the terms below [u^2]) and a five-case          *)
(*  assembly.                                                                 *)
(* ===========================================================================*)
Lemma ThreeProdDW_error x y :
  ties_to_even choice ->
  isDW x -> isTW y ->
  Rabs (TWval (ThreeProdDW x y) - TWval x * TWval y) <=
     (105 / 10 * (u * u * u) + 39 * (u * u * u * u)) *
       Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy.
set C := (105 / 10 * _ + _).
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  have Hxz : x = TWR 0 0 0.
    by apply: (@isTW_zero_lead p Hp2) => //; exact: isDW_isTW.
  rewrite Hxz ThreeProdDW_0l.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (@isTW_zero_lead p Hp2 y Hy y0z) ThreeProdDW_0r.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_r Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
have [cx _ [Hxp Hxn]] := isDW_normalize Hx x0n.
have [cy _ [Hyp Hyn]] := @isTW_normalize p Hp2 choice y Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
apply: (@error_scale_transfer (cx + cy)%Z (TWval (ThreeProdDW x y))
                              (TWval x * TWval y) C).
case: Hxsg => Hxs; case: Hysg => Hys.
- have Hn := ThreeProdDW_error_norm Hc (Hxp Hxs) (Hyp Hys).
  rewrite ThreeProdDW_scale !TWval_scale in Hn.
  rewrite (_ : TWval x * pow cx * (TWval y * pow cy) = TWval x * TWval y * pow
    (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
- have Hn := ThreeProdDW_error_norm Hc (Hxp Hxs) (Hyn Hys).
  rewrite ThreeProdDW_scale ThreeProdDW_opp_r !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : TWval x * pow cx * (- TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProdDW x y) * pow (cx + cy) - - (TWval x * TWval y *
    pow (cx + cy)) = - (TWval (ThreeProdDW x y) * pow (cx + cy) - TWval x *
    TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProdDW_error_norm Hc (Hxn Hxs) (Hyp Hys).
  rewrite ThreeProdDW_scale ThreeProdDW_opp !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : - TWval x * pow cx * (TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProdDW x y) * pow (cx + cy) - - (TWval x * TWval y *
    pow (cx + cy)) = - (TWval (ThreeProdDW x y) * pow (cx + cy) - TWval x *
    TWval y * pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProdDW_error_norm Hc (Hxn Hxs) (Hyn Hys).
  have Hxy : ThreeProdDW (negTW x) (negTW y) = ThreeProdDW x y.
    by rewrite ThreeProdDW_opp ThreeProdDW_opp_r negTW_id.
  rewrite ThreeProdDW_scale Hxy !TWval_scale !TWval_opp in Hn.
  rewrite (_ : - TWval x * pow cx * (- TWval y * pow cy) = TWval x * TWval y *
    pow (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
Qed.

End SecThreeProdDW.
