(* ---------------------------------------------------------------------------*)
(* Algorithm 9 (3Prod^acc_{3,3}): the product of two triple-word numbers,     *)
(* and its two correctness results -- the result is a triple word             *)
(* ([ThreeProd_isTW]) and the relative error bound [28u^3 + 107u^4]           *)
(* ([ThreeProd_error]) -- paper Theorem 7 (doc/paper3.pdf, Section 6; see     *)
(* doc/thm7.md).  This starts the multiplication half of the paper.  Generic  *)
(* over the precision [p] (FLX, no [emin]); needs [p >= 6].                   *)
(*                                                                            *)
(* STATUS: COMPLETE (zero admits).  The definition transcribes Algorithm 9    *)
(* verbatim on top of [TwoProd] (Alg 3), [vecSum] (Alg 4) and [vsebK]         *)
(* (Alg 5).  Both theorems are PROVED, reduced by the FLX WLOG                *)
(* (scale-invariance [ThreeProd_scale] and sign-invariance                    *)
(* [ThreeProd_opp]/[_opp_r], the paper's 1 <= x0, y0 < 2) to their            *)
(* normalised forms [ThreeProd_isTW_norm]/[ThreeProd_error_norm], which carry *)
(* the Section-6.2 mathematics; see doc/thm7.md and doc/thm7-eps5.md.  The    *)
(* fast variant, Algorithm 10, is in ThreeProdFast.v and reuses this file's   *)
(* lemmas (doc/alg10.md).                                                     *)
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

Section SecThreeProd.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* Algorithm 9 / Theorem 7 need [p >= 6] (paper Section 6.2).                 *)
Hypothesis Hp6 : (6 <= p)%Z.

Fact Hp4 : (4 <= p)%Z. Proof. by lia. Qed.

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
Local Notation Fnonoverlap_aux := (Fnonoverlap_aux p).
Local Notation isTW := (isTW p).

(* ===========================================================================*)
(*  Algorithm 9 -- 3Prod^acc_{3,3}(x, y)                                      *)
(*  (46 operations & 2 tests; paper Section 6).                               *)
(*                                                                            *)
(*  The four [RN(_ + _ * _)] terms ([c], [z31], [z32]) are FMAs (a single     *)
(*  rounding).  The [b_i]/[e_i] are read off the (fixed-length) [vecSum]      *)
(*  outputs by position; [r0 = e0] and [(r1, r2) = VSEB(2)(e1, e2, e3, e4)].  *)
(* ===========================================================================*)
Definition ThreeProd (x y : twR) : twR :=
  let: TWR x0 x1 x2 := x in
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
  let z32 := RND (z01m + x2 * y0) in
  let z3  := RND (z31 + z32) in
  let e := vecSum [:: z00p; b0; b1; c; z3] in
  let e0 := nth 0 e 0 in
  match vsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4] with
  | [:: r1, r2 & _] => TWR e0 r1 r2
  | [:: r1]         => TWR e0 r1 0
  | [::]            => TWR e0 0 0
  end.

(* ===========================================================================*)
(*  Lemma 1 (paper): [1/2 ulp(x)] divides [RN(x + y)].  Used for the          *)
(*  [b0]/[b1] divisibility in the Theorem-7 correctness case study.           *)
(* ===========================================================================*)
Lemma half_ulp_div_RN_add (x y : R) :
  format x -> format y -> x <> 0 ->
  is_imul (RND (x + y)) (/ 2 * ulp x).
Proof.
move=> Fx Fy x_neq0.
have He : / 2 * ulp x = pow (cexp x - 1).
  rewrite ulp_neq_0 //.
  have -> : / 2 = pow (-1) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -bpow_plus; congr bpow; lia.
rewrite He; set e := (cexp x - 1)%Z.
(* [x] itself is a multiple of [pow (cexp x)], hence of [1/2 ulp x = pow e].  *)
have Imx : is_imul x (pow e).
  by apply: is_imul_pow_le (format_imul_cexp Fx) _; rewrite /e; lia.
have [Ley|yLe] := Zle_or_lt e (cexp y).
  (* [y] no smaller than [1/2 ulp x]: [x + y] is on the [pow e] grid, so      *)
  (* [RN(x+y)] stays on it too.                                               *)
  apply: is_imul_pow_round; apply: is_imul_add => //.
  by apply: is_imul_pow_le (format_imul_cexp Fy) _.
(* [y] strictly smaller (its ulp [<= 1/4 ulp x]): then [|y| < pow(mag x - 2)] *)
(* and [|x| >= pow(mag x - 1) = 2 pow(mag x - 2)], so [|x + y|] -- and hence  *)
(* [|RN(x+y)|] -- stays [>= pow(mag x - 2)].  Thus [mag(RN(x+y)) >= mag x-1]  *)
(* and [cexp(RN(x+y)) >= e], making [RN(x+y)] a multiple of [pow e].          *)
have [->|y0] := Req_dec y 0.
  by rewrite Rplus_0_r (round_generic _ _ _ _ Fx).
have Hy : Rabs y < pow (mag beta x - 2).
  apply: (Rlt_le_trans _ (pow (mag beta y))); first by apply: bpow_mag_gt.
  by apply: bpow_le; move: yLe; rewrite /e /cexp /fexp; lia.
have Hx := bpow_mag_le beta x x_neq0.
have E2 : pow (mag beta x - 1) = 2 * pow (mag beta x - 2).
  have -> : (mag beta x - 1 = mag beta x - 2 + 1)%Z by lia.
  by rewrite bpow_plus_1.
have Hxy : pow (mag beta x - 2) <= Rabs (x + y).
  have Ht := Rabs_triang_inv x (- y).
  rewrite Rabs_Ropp in Ht.
  have Hxy0 : x - - y = x + y by lra.
  by rewrite Hxy0 in Ht; lra.
have HR : pow (mag beta x - 2) <= Rabs (RND (x + y)).
  by apply: Rabs_round_ge_bpow.
have Fr : format (RND (x + y)) by apply: generic_format_round.
apply: is_imul_pow_le (format_imul_cexp Fr) _.
have cexpE z : cexp z = (mag beta z - p)%Z by rewrite /cexp /fexp; lia.
rewrite /e !cexpE.
suff : (mag beta x - 1 <= mag beta (RND (x + y)))%Z by lia.
apply: mag_ge_bpow.
by have -> : (mag beta x - 1 - 1 = mag beta x - 2)%Z by lia.
Qed.

(* ===========================================================================*)
(*  Section 6.1 -- bounds on the intermediate terms.                          *)
(*                                                                            *)
(* The paper WLOGs [1 <= x0, y0 < 2] (so [ufp x0 = ufp y0 = 1]). We package   *)
(* that normalisation together with the triple-word separation of one factor  *)
(* as [tw_norm]. Every bound of Section 6.1 is a lemma over [tw_norm].        *)
(* ===========================================================================*)
Definition tw_norm (x0 x1 x2 : R) : Prop :=
  [/\ [/\ format x0, format x1 & format x2], 1 <= x0, x0 < 2,
      (x1 = 0 \/ Rabs x1 < ulp x0) & (x2 = 0 \/ Rabs x2 < ulp x1)].

(* Two [pow] rewrites used throughout: [2u = pow(1-p)] and [2u^2 =            *)
(* pow(1-2p)].                                                                *)
Lemma pow_1mp : pow (1 - p) = 2 * u.
Proof. by rewrite /u; lra. Qed.

Lemma pow_1m2p : pow (1 - 2 * p) = 2 * (u * u).
Proof.
rewrite /u.
have -> : (1 - 2 * p = (1 - p) + ((1 - p) + (-1)))%Z by lia.
rewrite !bpow_plus.
have -> : pow (-1) = /2 by rewrite /= /Z.pow_pos /=; lra.
lra.
Qed.

(* Under the normalisation the leading limb has [ulp x0 = 2u].                *)
Lemma tw_norm_ulp0 x0 x1 x2 : tw_norm x0 x1 x2 -> ulp x0 = 2 * u.
Proof.
move=> [] _ Hx0l Hx0r _ _.
have x0n0 : x0 <> 0 by lra.
have Hmag : (mag beta x0 = 1%Z :> Z).
  apply: mag_unique_pos; rewrite /= /Z.pow_pos /=; lra.
by rewrite ulp_neq_0 // /cexp /fexp Hmag /u; lra.
Qed.

(* First off-limb: [|x1| < 2u]. (Covers the [x1 = 0] case since [u > 0].)     *)
Lemma tw_norm_x1 x0 x1 x2 : tw_norm x0 x1 x2 -> Rabs x1 < 2 * u.
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulp := tw_norm_ulp0 Hn.
case: Hn => _ _ _ [Hx1|Hx1] _.
  by rewrite Hx1 Rabs_R0; lra.
by rewrite -Hulp.
Qed.

(* Second off-limb: [|x2| < 2u^2].                                            *)
Lemma tw_norm_x2 x0 x1 x2 : tw_norm x0 x1 x2 -> Rabs x2 < 2 * (u * u).
Proof.
move=> Hn.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1b := tw_norm_x1 Hn.
have Hulpx1 : ulp x1 <= 2 * (u * u).
  case: (Req_dec x1 0) => [->|x1n0].
    by rewrite ulp_FLX_0 -pow_1m2p; apply: bpow_ge_0.
  have Hmag : (mag beta x1 <= 1 - p)%Z.
    by apply: mag_le_bpow => //; rewrite pow_1mp.
  by rewrite ulp_neq_0 // /cexp /fexp -pow_1m2p; apply: bpow_le; lia.
case: Hn => _ _ _ _ [->|Hx2].
  rewrite Rabs_R0.
  have Huu : 0 < u * u by nra.
  lra.
exact: (Rlt_le_trans _ _ _ Hx2 Hulpx1).
Qed.

(* [u = pow(-p)]: the workhorse rewrite for the product-term bounds.          *)
Lemma u_pow : u = pow (- p).
Proof.
rewrite /u.
have -> : (1 - p = 1 + - p)%Z by lia.
by rewrite bpow_plus bpow_1 /=; lra.
Qed.

(* A normalised leading limb is at most [2 - 2u] (the largest float below 2). *)
Lemma tw_norm_hi x0 x1 x2 : tw_norm x0 x1 x2 -> x0 <= 2 - 2 * u.
Proof.
move=> Hn; have Hulp := tw_norm_ulp0 Hn.
case: Hn => -[Fx0 _ _] Hx0l Hx0r _ _.
have x0n0 : x0 <> 0 by lra.
have [k Hk] : is_imul x0 (2 * u).
  have Ix0 := format_imul_cexp Fx0.
  have Hc : pow (cexp x0) = 2 * u by rewrite -Hulp; symmetry; apply: ulp_neq_0.
  by rewrite Hc in Ix0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hpp : pow p * u = 1.
  by rewrite u_pow -bpow_plus (_ : (p + - p = 0)%Z) ?pow0E; [lra|lia].
have Hp2u : pow p * (2 * u) = 2.
  have -> : pow p * (2 * u) = 2 * (pow p * u) by ring.
  by rewrite Hpp; lra.
have Hkub : (k <= 2 ^ p - 1)%Z.
  suff : (IZR k < IZR (2 ^ p))%R by move/lt_IZR; lia.
  rewrite IZR_2powp //.
  apply: (Rmult_lt_reg_r (2 * u)); first by lra.
  by rewrite -Hk Hp2u.
have -> : (2 - 2 * u = IZR (2 ^ p - 1) * (2 * u)).
  rewrite minus_IZR IZR_2powp //.
  by rewrite Rmult_minus_distr_r Hp2u; lra.
rewrite Hk; apply: Rmult_le_compat_r; first by lra.
by apply: IZR_le.
Qed.

(* ===========================================================================*)
(* FLX scale-invariance (the paper's "WLOG 1 <= x0, y0 < 2").                 *)
(*                                                                            *)
(* In FLX every operation of Algorithm 9 commutes with scaling an input by a  *)
(* power of two ([round_bpow_FLX]). We propagate this through the building    *)
(* blocks ([TwoSum], [vecSum], [vsebAux]/[vseb]/[vsebK], [TwoProd]) and hence *)
(* through [ThreeProd]; combined with the scale-invariance of [isTW] and the  *)
(* scaling of [TWval], it lets the two theorems reduce to normalised inputs.  *)
(* ===========================================================================*)

(* [RND] commutes with scaling by a power of two (FLX; no underflow).         *)
Lemma round_scale x c : RND (x * pow c) = RND x * pow c.
Proof. exact: round_bpow_FLX. Qed.

(* [TwoSum] scales: both output words pick up the common factor [pow c].      *)
Lemma TwoSum_scale a b c :
  TwoSum (a * pow c) (b * pow c) =
  DWR (dwh (TwoSum a b) * pow c) (dwl (TwoSum a b) * pow c).
Proof.
rewrite /TwoSum /dwh /dwl.
have Add : forall x y : R, x * pow c + y * pow c = (x + y) * pow c by move=> *;
  ring.
have Sub : forall x y : R, x * pow c - y * pow c = (x - y) * pow c by move=> *;
  ring.
by do 6! (rewrite ?Add ?Sub ?round_scale).
Qed.

(* [vecSumAux] scales: the emitted list and the running sum both pick up [pow *)
(* c].                                                                        *)
Lemma vecSumAux_scale l c :
  vecSumAux [seq z * pow c | z <- l] =
  ([seq z * pow c | z <- (vecSumAux l).1], (vecSumAux l).2 * pow c).
Proof.
elim: l => [|x l IH].
  by rewrite /= Rmult_0_l.
case: l IH => [|y l'] IH; first by [].
rewrite map_cons map_cons vecSumAux_cons.
rewrite -map_cons IH.
case E0 : (vecSumAux (y :: l')) => [es0 s0].
rewrite TwoSum_scale.
rewrite vecSumAux_cons E0.
by case E1 : (TwoSum x s0) => [si0 ei0].
Qed.

(* [vecSum] scales.                                                           *)
Lemma vecSum_scale l c :
  vecSum [seq z * pow c | z <- l] = [seq z * pow c | z <- vecSum l].
Proof.
rewrite /vecSum vecSumAux_scale.
by case: (vecSumAux l) => es s0.
Qed.

(* [vsebAux] scales (the [et = 0] branch test is preserved: [pow c <> 0]).    *)
Lemma vsebAux_scale eps l c :
  vsebAux (eps * pow c) [seq z * pow c | z <- l] =
  [seq z * pow c | z <- vsebAux eps l].
Proof.
have pcn0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
elim: l eps => [|e l IH] eps; first by [].
case: l IH => [|e2 l'] IH.
  rewrite map_cons vsebAux_1 vsebAux_1 TwoSum_scale.
  by case E1 : (TwoSum eps e) => [y0 y1].
rewrite map_cons map_cons vsebAux_consS.
rewrite TwoSum_scale.
rewrite vsebAux_consS.
case E1 : (TwoSum eps e) => [r0 et0].
rewrite dwhE dwlE.
case: (Req_EM_T et0 0) => [Et0|Et0].
  have Ec : et0 * pow c = 0 by rewrite Et0; ring.
  have -> : is_left (Req_EM_T (et0 * pow c) 0) = true.
    by case: (Req_EM_T (et0 * pow c) 0) => // H; case: (H Ec).
  by rewrite -map_cons IH.
have -> : is_left (Req_EM_T (et0 * pow c) 0) = false.
  case: (Req_EM_T (et0 * pow c) 0) => // H.
  by case: (Rmult_integral _ _ H) => k; [case: (Et0 k) | case: (pcn0 k)].
by rewrite -map_cons IH.
Qed.

(* [vseb] and [vsebK] scale.                                                  *)
Lemma vseb_scale l c :
  vseb [seq z * pow c | z <- l] = [seq z * pow c | z <- vseb l].
Proof.
case: l => [|e0 l'] //.
by rewrite map_cons /vseb vsebAux_scale.
Qed.

Lemma vsebK_scale k l c :
  vsebK k [seq z * pow c | z <- l] = [seq z * pow c | z <- vsebK k l].
Proof.
rewrite /vsebK vseb_scale.
by rewrite map_take.
Qed.

(* [TwoProd] scales: with factors [pow c1] on [a] and [pow c2] on [b], both   *)
(* words pick up [pow (c1 + c2)].                                             *)
Lemma TwoProd_scale a b c1 c2 :
  TwoProd (a * pow c1) (b * pow c2) =
  ((TwoProd a b).1 * pow (c1 + c2), (TwoProd a b).2 * pow (c1 + c2)).
Proof.
rewrite /TwoProd /=.
have Hprod : a * pow c1 * (b * pow c2) = a * b * pow (c1 + c2).
  by rewrite bpow_plus; ring.
rewrite Hprod round_scale.
congr pair.
have -> : a * b * pow (c1 + c2) - RND (a * b) * pow (c1 + c2) =
          (a * b - RND (a * b)) * pow (c1 + c2) by ring.
by rewrite round_scale.
Qed.

(* [nth] through a scaling [map] (the default [0] is fixed by the factor).    *)
Lemma nth_map_scale (l : seq R) (c : Z) i :
  nth 0 [seq z * pow c | z <- l] i = nth 0 l i * pow c.
Proof. by elim: l i => [|x l IH] [|i] //=; rewrite ?Rmult_0_l //. Qed.

(* [format], [ulp] under scaling by a power of two.                           *)
Lemma format_scale x c : format (x * pow c) <-> format x.
Proof.
have pcn0 : pow c <> 0 by apply: Rgt_not_eq; apply: bpow_gt_0.
split=> Hf.
  have Hr : RND x * pow c = x * pow c.
    by rewrite -round_scale (round_generic _ _ _ _ Hf).
  have HRx : RND x = x by apply: (Rmult_eq_reg_r (pow c)).
  by rewrite -HRx; apply: generic_format_round.
have HRxc : RND (x * pow c) = x * pow c.
  by rewrite round_scale (round_generic _ _ _ _ Hf).
by rewrite -HRxc; apply: generic_format_round.
Qed.

Lemma ulp_scale x c : ulp (x * pow c) = ulp x * pow c.
Proof.
case: (Req_dec x 0) => [->|xn0].
  by rewrite Rmult_0_l !ulp_FLX_0 Rmult_0_l.
have xcn0 : x * pow c <> 0.
  apply: Rmult_integral_contrapositive_currified => //.
  by apply: Rgt_not_eq; apply: bpow_gt_0.
rewrite !ulp_neq_0 // cexp_bpow_FLX // bpow_plus; ring.
Qed.

(* Scaling a triple word by [pow c] (component-wise).                         *)
Definition scaleTW (c : Z) (t : twR) : twR :=
  let: TWR t0 t1 t2 := t in TWR (t0 * pow c) (t1 * pow c) (t2 * pow c).

Lemma TWval_scale c t : TWval (scaleTW c t) = TWval t * pow c.
Proof. by case: t => t0 t1 t2 /=; ring. Qed.

(* ... and the head limb alone scales.                                        *)
Lemma tw0_scale c t : tw0 (scaleTW c t) = tw0 t * pow c.
Proof. by case: t. Qed.

(* Scaling is a monoid action: needed whenever an algorithm feeds a SCALED    *)
(* triple word to a product and the property to reuse is stated on the        *)
(* unscaled one -- Algorithm 15 does exactly that with its [b' = b/2].        *)
Lemma scaleTW_0 t : scaleTW 0 t = t.
Proof. by case: t => t0 t1 t2; rewrite /scaleTW /= !Rmult_1_r. Qed.

Lemma scaleTW_add c d t : scaleTW c (scaleTW d t) = scaleTW (c + d) t.
Proof.
by case: t => t0 t1 t2; rewrite /scaleTW /= bpow_plus; congr TWR; ring.
Qed.

(* [isTW] is scale-invariant (formats, and the strict [ulp] gaps, both        *)
(* scale).                                                                    *)
Lemma isTW_scale c t : isTW (scaleTW c t) <-> isTW t.
Proof.
have pc0 : 0 < pow c by apply: bpow_gt_0.
have Rc : Rabs (pow c) = pow c by apply: Rabs_pos_eq; lra.
case: t => t0 t1 t2 /=; split=> -[F0 F1 F2 H1 H2]; split.
- by rewrite -(format_scale t0 c).
- by rewrite -(format_scale t1 c).
- by rewrite -(format_scale t2 c).
- case: H1 => [H1|H1]; [left; nra | right].
  move: H1; rewrite ulp_scale Rabs_mult Rc => HH.
  by apply: (Rmult_lt_reg_r (pow c)).
- case: H2 => [H2|H2]; [left; nra | right].
  move: H2; rewrite ulp_scale Rabs_mult Rc => HH.
  by apply: (Rmult_lt_reg_r (pow c)).
- by rewrite (format_scale t0 c).
- by rewrite (format_scale t1 c).
- by rewrite (format_scale t2 c).
- case: H1 => [->|H1]; [left; ring | right].
  rewrite ulp_scale Rabs_mult Rc.
  by apply: Rmult_lt_compat_r.
- case: H2 => [->|H2]; [left; ring | right].
  rewrite ulp_scale Rabs_mult Rc.
  by apply: Rmult_lt_compat_r.
Qed.

(* ===========================================================================*)
(* Algorithm 9 is scale-equivariant: [ThreeProd] of scaled inputs is the      *)
(* scaled [ThreeProd]. This is the FLX "WLOG 1 <= x0, y0 < 2" made explicit.  *)
(* ===========================================================================*)
Lemma ThreeProd_scale a b x y :
  ThreeProd (scaleTW a x) (scaleTW b y) = scaleTW (a + b) (ThreeProd x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProd /scaleTW.
have P1 : x1 * pow a * (y1 * pow b) = x1 * y1 * pow (a + b) by rewrite
  bpow_plus; ring.
have P2 : x0 * pow a * (y2 * pow b) = x0 * y2 * pow (a + b) by rewrite
  bpow_plus; ring.
have P3 : x2 * pow a * (y0 * pow b) = x2 * y0 * pow (a + b) by rewrite
  bpow_plus; ring.
rewrite !P1 !P2 !P3 !TwoProd_scale.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: w00m * pow (a+b); w01p * pow (a+b); w10p *
  pow (a+b)]) i = nth 0 (vecSum [:: w00m; w01p; w10p]) i * pow (a+b).
  move=> i.
  have -> : [:: w00m * pow (a+b); w01p * pow (a+b); w10p * pow (a+b)] = [seq z *
    pow (a+b) | z <- [:: w00m; w01p; w10p]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (t * pow (a+b) + x1 * y1 * pow (a+b)) = RND (t + x1
  * y1) * pow (a+b).
  move=> t.
  have -> : t * pow (a+b) + x1 * y1 * pow (a+b) = (t + x1 * y1) * pow (a+b) by
    ring.
  by rewrite round_scale.
have E5 : RND (RND (w10m * pow (a+b) + x0 * y2 * pow (a+b)) + RND (w01m * pow
  (a+b) + x2 * y0 * pow (a+b))) = RND (RND (w10m + x0 * y2) + RND (w01m + x2 *
  y0)) * pow (a+b).
  have -> : w10m * pow (a+b) + x0 * y2 * pow (a+b) = (w10m + x0 * y2) * pow
    (a+b) by ring.
  have -> : w01m * pow (a+b) + x2 * y0 * pow (a+b) = (w01m + x2 * y0) * pow
    (a+b) by ring.
  rewrite !round_scale.
  have -> : RND (w10m + x0 * y2) * pow (a+b) + RND (w01m + x2 * y0) * pow (a+b)
    = (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b) by ring.
  by rewrite round_scale.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b);
  nth 0 bb 1 * pow (a+b); RND (nth 0 bb 2 + x1 * y1) * pow (a+b); RND (RND (w10m
  + x0 * y2) + RND (w01m + x2 * y0)) * pow (a+b)]) i = nth 0 (vecSum [:: w00p;
  nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2)
  + RND (w01m + x2 * y0))]) i * pow (a+b).
  move=> i.
  have -> : [:: w00p * pow (a+b); nth 0 bb 0 * pow (a+b); nth 0 bb 1 * pow
    (a+b); RND (nth 0 bb 2 + x1 * y1) * pow (a+b); RND (RND (w10m + x0 * y2) +
    RND (w01m + x2 * y0)) * pow (a+b)] = [seq z * pow (a+b) | z <- [:: w00p; nth
    0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m + x0 * y2) +
    RND (w01m + x2 * y0))]] by [].
  by rewrite vecSum_scale nth_map_scale.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
  RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))].
have Ev : vsebK 2 [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3
  * pow (a+b); nth 0 ee 4 * pow (a+b)] = [seq z * pow (a+b) | z <- vsebK 2 [::
  nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]].
  have -> : [:: nth 0 ee 1 * pow (a+b); nth 0 ee 2 * pow (a+b); nth 0 ee 3 * pow
    (a+b); nth 0 ee 4 * pow (a+b)] = [seq z * pow (a+b) | z <- [:: nth 0 ee 1;
    nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]] by [].
  by rewrite vsebK_scale.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

(* ===========================================================================*)
(* Sign-equivariance: negating [x_bar] alone flips every intermediate (each   *)
(* is odd of degree one in the [x] limbs), so [ThreeProd] is odd in its first *)
(* argument. Together with [ThreeProd_scale] this yields the paper's full     *)
(* "WLOG 1 <= x0, y0 < 2" (positive, normalised).                             *)
(* ===========================================================================*)

(* [RND] commutes with negation (symmetric ties-to-even, via [choice_sym]).   *)
Lemma round_opp x : RND (- x) = - RND x.
Proof. exact: (RN_opp_sym p choice_sym). Qed.

Lemma nth_map_opp (l : seq R) i :
  nth 0 [seq - z | z <- l] i = - nth 0 l i.
Proof. by elim: l i => [|x l IH] [|i] //=; rewrite ?Ropp_0 //. Qed.

Lemma TwoSum_opp a b :
  TwoSum (- a) (- b) = DWR (- dwh (TwoSum a b)) (- dwl (TwoSum a b)).
Proof.
rewrite /TwoSum /dwh /dwl.
have Add : forall u v : R, - u + - v = - (u + v) by move=> *; ring.
have Sub : forall u v : R, - u - - v = - (u - v) by move=> *; ring.
by do 6! (rewrite ?Add ?Sub ?round_opp).
Qed.

Lemma vecSumAux_opp l :
  vecSumAux [seq - z | z <- l] =
  ([seq - z | z <- (vecSumAux l).1], - (vecSumAux l).2).
Proof.
elim: l => [|x l IH].
  by rewrite /= Ropp_0.
case: l IH => [|y l'] IH; first by [].
rewrite map_cons map_cons vecSumAux_cons.
rewrite -map_cons IH.
case E0 : (vecSumAux (y :: l')) => [es0 s0].
rewrite TwoSum_opp.
rewrite vecSumAux_cons E0.
by case E1 : (TwoSum x s0) => [si0 ei0].
Qed.

Lemma vecSum_opp l :
  vecSum [seq - z | z <- l] = [seq - z | z <- vecSum l].
Proof.
rewrite /vecSum vecSumAux_opp.
by case: (vecSumAux l) => es s0.
Qed.

Lemma vsebAux_opp eps l :
  vsebAux (- eps) [seq - z | z <- l] = [seq - z | z <- vsebAux eps l].
Proof.
elim: l eps => [|e l IH] eps; first by [].
case: l IH => [|e2 l'] IH.
  rewrite map_cons vsebAux_1 vsebAux_1 TwoSum_opp.
  by case E1 : (TwoSum eps e) => [y0 y1].
rewrite map_cons map_cons vsebAux_consS.
rewrite TwoSum_opp.
rewrite vsebAux_consS.
case E1 : (TwoSum eps e) => [r0 et0].
rewrite dwhE dwlE.
case: (Req_EM_T et0 0) => [Et0|Et0].
  have Ec : - et0 = 0 by rewrite Et0; ring.
  have -> : is_left (Req_EM_T (- et0) 0) = true.
    by case: (Req_EM_T (- et0) 0) => // H; case: (H Ec).
  by rewrite -map_cons IH.
have -> : is_left (Req_EM_T (- et0) 0) = false.
  case: (Req_EM_T (- et0) 0) => // H.
  have E0 : et0 = 0 by lra.
  by case: (Et0 E0).
by rewrite -map_cons IH.
Qed.

Lemma vseb_opp l :
  vseb [seq - z | z <- l] = [seq - z | z <- vseb l].
Proof.
case: l => [|e0 l'] //.
by rewrite map_cons /vseb vsebAux_opp.
Qed.

Lemma vsebK_opp k l :
  vsebK k [seq - z | z <- l] = [seq - z | z <- vsebK k l].
Proof.
rewrite /vsebK vseb_opp.
by rewrite map_take.
Qed.

(* [TwoProd] with the LEFT factor negated: both words flip sign.              *)
Lemma TwoProd_opp_l a b :
  TwoProd (- a) b = (- (TwoProd a b).1, - (TwoProd a b).2).
Proof.
rewrite /TwoProd /=.
have -> : - a * b = - (a * b) by ring.
rewrite round_opp.
congr pair.
have -> : - (a * b) - - RND (a * b) = - (a * b - RND (a * b)) by ring.
by rewrite round_opp.
Qed.

(* Negating a triple word (component-wise).                                   *)
Definition negTW (t : twR) : twR :=
  let: TWR t0 t1 t2 := t in TWR (- t0) (- t1) (- t2).

Lemma TWval_opp t : TWval (negTW t) = - TWval t.
Proof. by case: t => t0 t1 t2 /=; ring. Qed.

(* ... and the head limb alone changes sign.                                  *)
Lemma tw0_opp t : tw0 (negTW t) = - tw0 t.
Proof. by case: t. Qed.

Lemma isTW_opp t : isTW (negTW t) <-> isTW t.
Proof.
have Fo : forall z, format (- z) <-> format z.
  move=> z; split=> H; last by apply: generic_format_opp.
  by rewrite -[z]Ropp_involutive; apply: generic_format_opp.
case: t => t0 t1 t2 /=; split=> -[F0 F1 F2 H1 H2]; split; rewrite ?ulp_opp.
- by apply/Fo.
- by apply/Fo.
- by apply/Fo.
- case: H1 => [H1|H1]; [left; lra | right].
  by move: H1; rewrite Rabs_Ropp ulp_opp.
- case: H2 => [H2|H2]; [left; lra | right].
  by move: H2; rewrite Rabs_Ropp ulp_opp.
- by apply/Fo.
- by apply/Fo.
- by apply/Fo.
- case: H1 => [H1|H1]; [left; lra | right].
  by rewrite Rabs_Ropp.
- case: H2 => [H2|H2]; [left; lra | right].
  by rewrite Rabs_Ropp.
Qed.

(* Algorithm 9 is odd in its first argument.                                  *)
Lemma ThreeProd_opp x y : ThreeProd (negTW x) y = negTW (ThreeProd x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProd /negTW.
have P1 : (- x1) * y1 = - (x1 * y1) by ring.
have P2 : (- x0) * y2 = - (x0 * y2) by ring.
have P3 : (- x2) * y0 = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !TwoProd_opp_l.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0
  (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite round_opp.
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND
  (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !round_opp.
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0
    * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite round_opp.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND
  (nth 0 bb 2 + x1 * y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))])
  i = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 *
  y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND (nth 0 bb 2 + x1 *
    y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))] = [seq - z | z <-
    [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m
    + x0 * y2) + RND (w01m + x2 * y0))]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
  RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] =
  [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] = [seq -
    z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]] by [].
  by rewrite vsebK_opp.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

(* [TwoProd] with the RIGHT factor negated: both words flip sign.             *)
Lemma TwoProd_opp_r a b :
  TwoProd a (- b) = (- (TwoProd a b).1, - (TwoProd a b).2).
Proof.
rewrite /TwoProd /=.
have -> : a * - b = - (a * b) by ring.
rewrite round_opp.
congr pair.
have -> : - (a * b) - - RND (a * b) = - (a * b - RND (a * b)) by ring.
by rewrite round_opp.
Qed.

(* Algorithm 9 is odd in its second argument, too.                            *)
Lemma ThreeProd_opp_r x y : ThreeProd x (negTW y) = negTW (ThreeProd x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite /ThreeProd /negTW.
have P1 : x1 * (- y1) = - (x1 * y1) by ring.
have P2 : x0 * (- y2) = - (x0 * y2) by ring.
have P3 : x2 * (- y0) = - (x2 * y0) by ring.
rewrite !P1 !P2 !P3 !TwoProd_opp_r.
case: (TwoProd x0 y0) => w00p w00m.
case: (TwoProd x0 y1) => w01p w01m.
case: (TwoProd x1 y0) => w10p w10m.
have F1 : forall u v : R, (u, v).1 = u by [].
have F2 : forall u v : R, (u, v).2 = v by [].
rewrite !F1 !F2.
have Eb : forall i, nth 0 (vecSum [:: - w00m; - w01p; - w10p]) i = - nth 0
  (vecSum [:: w00m; w01p; w10p]) i.
  move=> i.
  have -> : [:: - w00m; - w01p; - w10p] = [seq - z | z <- [:: w00m; w01p; w10p]]
    by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Eb.
set bb := vecSum [:: w00m; w01p; w10p].
have E4 : forall t : R, RND (- t + - (x1 * y1)) = - RND (t + x1 * y1).
  move=> t.
  have -> : - t + - (x1 * y1) = - (t + x1 * y1) by ring.
  by rewrite round_opp.
have E5 : RND (RND (- w10m + - (x0 * y2)) + RND (- w01m + - (x2 * y0))) = - RND
  (RND (w10m + x0 * y2) + RND (w01m + x2 * y0)).
  have -> : - w10m + - (x0 * y2) = - (w10m + x0 * y2) by ring.
  have -> : - w01m + - (x2 * y0) = - (w01m + x2 * y0) by ring.
  rewrite !round_opp.
  have -> : - RND (w10m + x0 * y2) + - RND (w01m + x2 * y0) = - (RND (w10m + x0
    * y2) + RND (w01m + x2 * y0)) by ring.
  by rewrite round_opp.
rewrite !E4 !E5.
have Ee : forall i, nth 0 (vecSum [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND
  (nth 0 bb 2 + x1 * y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))])
  i = - nth 0 (vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 *
  y1); RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))]) i.
  move=> i.
  have -> : [:: - w00p; - nth 0 bb 0; - nth 0 bb 1; - RND (nth 0 bb 2 + x1 *
    y1); - RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))] = [seq - z | z <-
    [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1); RND (RND (w10m
    + x0 * y2) + RND (w01m + x2 * y0))]] by [].
  by rewrite vecSum_opp nth_map_opp.
rewrite !Ee.
set ee := vecSum [:: w00p; nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
  RND (RND (w10m + x0 * y2) + RND (w01m + x2 * y0))].
have Ev : vsebK 2 [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] =
  [seq - z | z <- vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]].
  have -> : [:: - nth 0 ee 1; - nth 0 ee 2; - nth 0 ee 3; - nth 0 ee 4] = [seq -
    z | z <- [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4]] by [].
  by rewrite vsebK_opp.
rewrite Ev.
set V := vsebK 2 [:: nth 0 ee 1; nth 0 ee 2; nth 0 ee 3; nth 0 ee 4].
by case: V => [|r1 [|r2 rr]] //=; congr TWR; ring.
Qed.

(* ===========================================================================*)
(* WLOG reduction: [ThreeProd_isTW]/[ThreeProd_error] reduce to normalised    *)
(* positive inputs ([tw_norm]). [tw_normP] packages [tw_norm] on a [twR].     *)
(* ===========================================================================*)
Definition tw_normP (t : twR) : Prop :=
  let: TWR t0 t1 t2 := t in tw_norm t0 t1 t2.

(* An [isTW] whose leading limb sits in [1, 2) is exactly a normalised [twR]. *)
Lemma isTW_tw_normP t : isTW t -> 1 <= tw0 t < 2 -> tw_normP t.
Proof.
by case: t => t0 t1 t2 [F0 F1 F2 H1 H2] /= [Hl Hr]; split=> //; split.
Qed.

(* Any nonzero [isTW] can be scaled (and sign-flipped) to a normalised [twR]. *)
Lemma isTW_normalize t :
  isTW t -> tw0 t <> 0 ->
  exists2 c : Z, True &
    (0 < tw0 t -> tw_normP (scaleTW c t)) /\
    (tw0 t < 0 -> tw_normP (scaleTW c (negTW t))).
Proof.
move=> Ht t0n0.
set m := mag beta (tw0 t).
have Hmag : pow (m - 1) <= Rabs (tw0 t) by apply: bpow_mag_le.
have Hmag2 : Rabs (tw0 t) < pow m by apply: bpow_mag_gt.
have Hp1m : 0 < pow (1 - m) by apply: bpow_gt_0.
have Hlo : pow (m - 1) * pow (1 - m) = 1.
  by rewrite -bpow_plus (_ : (m - 1 + (1 - m) = 0)%Z) ?pow0E //; lia.
have Hhi : pow m * pow (1 - m) = 2.
  rewrite -bpow_plus (_ : (m + (1 - m) = 1)%Z); last by lia.
  by rewrite /= /Z.pow_pos /=; lra.
exists (1 - m)%Z => //; split=> Hsg.
- apply: isTW_tw_normP; first by apply/isTW_scale.
  rewrite tw0_scale; rewrite Rabs_pos_eq in Hmag Hmag2; try lra.
  split.
    by rewrite -Hlo; apply: Rmult_le_compat_r; lra.
  by rewrite -Hhi; apply: Rmult_lt_compat_r; lra.
apply: isTW_tw_normP; first by apply/isTW_scale; apply/isTW_opp.
rewrite tw0_scale tw0_opp; rewrite Rabs_left in Hmag Hmag2; try lra.
split.
  by rewrite -Hlo; apply: Rmult_le_compat_r; lra.
by rewrite -Hhi; apply: Rmult_lt_compat_r; lra.
Qed.

(* The normalised (paper WLOG) forms [ThreeProd_isTW_norm] /                  *)
(* [ThreeProd_error_norm] carry the actual Section-6.2 mathematics and are    *)
(* proved BELOW, after the Section-6.1/6.2 term bounds and structural lemmas  *)
(* they depend on (just before [ThreeProd_isTW]).                             *)

(* ===========================================================================*)
(* Section 6.1 -- product-term bounds. Each is a lemma over the two           *)
(* normalisation contexts [tw_norm x0 x1 x2] / [tw_norm y0 y1 y2].            *)
(* ===========================================================================*)

(* The leading product [z00p = RN(x0 y0)] lies in [1, 4).                     *)
Lemma z00p_lb x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> 1 <= RND (x0 * y0).
Proof.
move=> Nx Ny.
have F1 : format 1 by rewrite -(pow0E beta); apply: format_pow.
case: Nx => _ Hx0l _ _ _.
case: Ny => _ Hy0l _ _ _.
have H1 : 1 <= x0 * y0 by nra.
rewrite -{1}(round_generic _ _ _ _ F1).
by apply: round_le.
Qed.

Lemma z00p_ub x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> RND (x0 * y0) < 4.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hxhi := tw_norm_hi Nx.
have Hyhi := tw_norm_hi Ny.
case: Nx => _ Hx0l _ _ _.
case: Ny => _ Hy0l _ _ _.
have Hprod : x0 * y0 <= 4 - 4 * u by nra.
have F44 : format (4 - 4 * u).
  have Hpm : pow p * u = 1.
    by rewrite u_pow -bpow_plus (_ : (p + - p = 0)%Z) ?pow0E //; lia.
  have -> : 4 - 4 * u = IZR (2 ^ p - 1) * (4 * u).
    rewrite minus_IZR IZR_2powp //.
    have -> : (pow p - 1) * (4 * u) = 4 * (pow p * u) - 4 * u by ring.
    by rewrite Hpm; ring.
  have -> : 4 * u = pow (2 - p).
    rewrite u_pow (_ : (2 - p = 2 + - p)%Z); last by lia.
    by rewrite bpow_plus /= /Z.pow_pos /=; lra.
  by apply: (format_mult_pow Hp2); rewrite Z.abs_eq; move: pow2_ge_16; lia.
apply: (Rle_lt_trans _ (4 - 4 * u)); last by lra.
rewrite -(round_generic _ _ _ _ F44).
by apply: round_le.
Qed.

(* [4u = pow(2-p)], used for the [< 4u] product bounds.                       *)
Lemma pow_2mp : pow (2 - p) = 4 * u.
Proof.
rewrite (_ : (2 - p = 2 + - p)%Z); last by lia.
by rewrite bpow_plus u_pow /= /Z.pow_pos /=; lra.
Qed.

(* Cross products [z01p = RN(x0 y1)], [z10p = RN(x1 y0)] are [<= 4u].         *)
Lemma z01p_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (RND (x0 * y1)) <= 4 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Fx4 : format (4 * u) by rewrite -pow_2mp; apply: format_pow.
apply: Rabs_round_le_r => //.
case: Nx => _ Hx0l Hx0r _ _.
have Hy1 := tw_norm_x1 Ny.
have := Rabs_pos y1.
rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
by nra.
Qed.

Lemma z10p_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (RND (x1 * y0)) <= 4 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Fx4 : format (4 * u) by rewrite -pow_2mp; apply: format_pow.
apply: Rabs_round_le_r => //.
case: Ny => _ Hy0l Hy0r _ _.
have Hx1 := tw_norm_x1 Nx.
have := Rabs_pos x1.
rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
by nra.
Qed.

(* The ignored/second-order products [x1 y1], [x0 y2], [x2 y0] are [< 4u^2].  *)
Lemma x1y1_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (x1 * y1) < 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := tw_norm_x1 Nx.
have Hy1 := tw_norm_x1 Ny.
have := Rabs_pos x1; have := Rabs_pos y1.
by rewrite Rabs_mult; nra.
Qed.

Lemma x0y2_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (x0 * y2) < 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx0hi := tw_norm_hi Nx.
have Hy2 := tw_norm_x2 Ny.
have := Rabs_pos y2.
case: Nx => _ Hx0l _ _ _.
by rewrite Rabs_mult (Rabs_pos_eq x0); [nra | lra].
Qed.

Lemma x2y0_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 -> Rabs (x2 * y0) < 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hy0hi := tw_norm_hi Ny.
have Hx2 := tw_norm_x2 Nx.
have := Rabs_pos x2.
case: Ny => _ Hy0l _ _ _.
by rewrite Rabs_mult (Rabs_pos_eq y0); [nra | lra].
Qed.

(* [u^2 = pow(-2p)], [4u^2 = pow(2-2p)], and a float multiple of [u^2].       *)
Lemma u2_pow : u * u = pow (- (2 * p)).
Proof. by rewrite u_pow -bpow_plus; congr bpow; lia. Qed.

Lemma pow_2m2p : pow (2 - 2 * p) = 4 * (u * u).
Proof.
rewrite (_ : (2 - 2 * p = 2 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma format_imul_u2 k : (Z.abs k < 2 ^ p)%Z -> format (IZR k * (u * u)).
Proof. by move=> Hk; rewrite u2_pow; apply: format_mult_pow. Qed.

(* [2^p >= 64] (from [p >= 6]); clears the [Z.abs k < 2^p] side-conditions.   *)
Fact two_p_ge_64 : (64 <= 2 ^ p)%Z.
Proof.
apply: (Z.le_trans _ (2 ^ 6)); first by [].
by apply: Z.pow_le_mono_r; lia.
Qed.

(* [8u = pow(3-p)] and [8u^2 = pow(3-2p)], used for the [b2] 2Sum-error       *)
(* bound.                                                                     *)
Lemma pow_3mp : pow (3 - p) = 8 * u.
Proof.
rewrite (_ : (3 - p = 3 + - p)%Z); last by lia.
by rewrite bpow_plus u_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma pow_3m2p : pow (3 - 2 * p) = 8 * (u * u).
Proof.
rewrite (_ : (3 - 2 * p = 3 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

(* [vecSum] of a 3-list, unfolded: [b0], [b1] (the [z00m + a] 2Sum) and [b2]  *)
(* (the [z01p + z10p] 2Sum error).                                            *)
Lemma vecSum3 a b c :
  format a -> format b -> format c ->
  vecSum [:: a; b; c] =
  [:: RND (a + RND (b + c)); a + RND (b + c) - RND (a + RND (b + c));
      b + c - RND (b + c)].
Proof.
move=> Fa Fb Fc.
rewrite /vecSum !vecSumAux_cons.
have -> : vecSumAux [:: c] = ([::], c) by [].
case Ebc : (TwoSum b c) => [s1 e1].
case Eac : (TwoSum a s1) => [s0 e0].
have Hs1 : s1 = RND (b + c) by move: (TwoSum_hi p choice b c); rewrite Ebc.
move: (TwoSum_correct_loc Hp2 choice_sym Fb Fc); rewrite Ebc => Hbc.
have Fs1 : format s1 by rewrite Hs1; apply: generic_format_round.
have Hs0 : s0 = RND (a + s1) by move: (TwoSum_hi p choice a s1); rewrite Eac.
move: (TwoSum_correct_loc Hp2 choice_sym Fa Fs1); rewrite Eac => Hac.
have -> : s0 = RND (a + RND (b + c)) by rewrite Hs0 Hs1.
have -> : e0 = a + RND (b + c) - RND (a + RND (b + c)) by rewrite -Hs1 -Hs0;
  lra.
have -> : e1 = b + c - RND (b + c) by rewrite -Hs1; lra.
by [].
Qed.

(* Leading product error [z00m = x0 y0 - RN(x0 y0)]: [|z00m| <= 2u].          *)
Lemma z00m_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x0 * y0 - RND (x0 * y0)) <= 2 * u.
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
case: (Nx) => _ Hx0l Hx0r _ _.
case: (Ny) => _ Hy0l Hy0r _ _.
have Hn0 : x0 * y0 <> 0 by nra.
have Hulp : ulp (x0 * y0) <= 4 * u.
  rewrite ulp_neq_0 // /cexp /fexp -pow_2mp; apply: bpow_le.
  suff : (mag beta (x0 * y0) <= 2)%Z by lia.
  apply: mag_le_bpow => //.
  rewrite Rabs_pos_eq; last by nra.
  have -> : pow 2 = 4 by rewrite /= /Z.pow_pos /=; lra.
  nra.
have He : Rabs (RND (x0 * y0) - x0 * y0) <= / 2 * ulp (x0 * y0)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

(* ... and [z00m] is a multiple of [4u^2] (whence [uls z00m >= 4u^2]).        *)
Lemma z00m_imul x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  is_imul (x0 * y0 - RND (x0 * y0)) (4 * (u * u)).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulpx := tw_norm_ulp0 Nx.
have Hulpy := tw_norm_ulp0 Ny.
case: (Nx) => -[Fx0 _ _] Hx0l Hx0r _ _.
case: (Ny) => -[Fy0 _ _] Hy0l Hy0r _ _.
have x0n0 : x0 <> 0 by lra.
have y0n0 : y0 <> 0 by lra.
have Ix0 : is_imul x0 (pow (1 - p)).
  have Hc : pow (cexp x0) = pow (1 - p) by rewrite -ulp_neq_0 // Hulpx pow_1mp.
  by rewrite -Hc; apply: format_imul_cexp.
have Iy0 : is_imul y0 (pow (1 - p)).
  have Hc : pow (cexp y0) = pow (1 - p) by rewrite -ulp_neq_0 // Hulpy pow_1mp.
  by rewrite -Hc; apply: format_imul_cexp.
rewrite -pow_2m2p.
have Ip : is_imul (x0 * y0) (pow (2 - 2 * p)).
  have := is_imul_mul Ix0 Iy0.
  by rewrite -bpow_plus (_ : (1 - p + (1 - p) = 2 - 2 * p)%Z); last by lia.
apply: is_imul_minus => //.
by apply: is_imul_pow_round.
Qed.

(* Cross product errors [z01m], [z10m]: [<= 2u^2].                            *)
Lemma z01m_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x0 * y1 - RND (x0 * y1)) <= 2 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
case: (Nx) => _ Hx0l Hx0r _ _.
have Hy1 := tw_norm_x1 Ny.
have Hprod : Rabs (x0 * y1) < 4 * u.
  rewrite Rabs_mult (Rabs_pos_eq x0); last by lra.
  have := Rabs_pos y1; nra.
case: (Req_dec (x0 * y1) 0) => [Hz|Hn0].
  by rewrite Hz round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp (x0 * y1) <= 4 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_2m2p; apply: bpow_le.
  suff : (mag beta (x0 * y1) <= 2 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_2mp.
have He : Rabs (RND (x0 * y1) - x0 * y1) <= / 2 * ulp (x0 * y1)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

Lemma z10m_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x1 * y0 - RND (x1 * y0)) <= 2 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
case: (Ny) => _ Hy0l Hy0r _ _.
have Hx1 := tw_norm_x1 Nx.
have Hprod : Rabs (x1 * y0) < 4 * u.
  rewrite Rabs_mult (Rabs_pos_eq y0); last by lra.
  have := Rabs_pos x1; nra.
case: (Req_dec (x1 * y0) 0) => [Hz|Hn0].
  by rewrite Hz round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp (x1 * y0) <= 4 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_2m2p; apply: bpow_le.
  suff : (mag beta (x1 * y0) <= 2 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_2mp.
have He : Rabs (RND (x1 * y0) - x1 * y0) <= / 2 * ulp (x1 * y0)
  by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

(* The FMA terms [z31 = RN(z10m + x0 y2)], [z32 = RN(z01m + x2 y0)]:          *)
(* [<= 6u^2].                                                                 *)
Lemma z31_bound z10m x0 y2 :
  Rabs z10m <= 2 * (u * u) -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (RND (z10m + x0 * y2)) <= 6 * (u * u).
Proof.
move=> H1 H2.
have F6 : format (6 * (u * u)).
  by apply: (format_imul_u2 (k := 6)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z10m (x0 * y2); lra.
Qed.

Lemma z32_bound z01m x2 y0 :
  Rabs z01m <= 2 * (u * u) -> Rabs (x2 * y0) < 4 * (u * u) ->
  Rabs (RND (z01m + x2 * y0)) <= 6 * (u * u).
Proof.
move=> H1 H2.
have F6 : format (6 * (u * u)).
  by apply: (format_imul_u2 (k := 6)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z01m (x2 * y0); lra.
Qed.

(* [z3 = RN(z31 + z32)]: [<= 12u^2].                                          *)
Lemma z3_bound z31 z32 :
  Rabs z31 <= 6 * (u * u) -> Rabs z32 <= 6 * (u * u) ->
  Rabs (RND (z31 + z32)) <= 12 * (u * u).
Proof.
move=> H1 H2.
have F12 : format (12 * (u * u)).
  by apply: (format_imul_u2 (k := 12)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang z31 z32; lra.
Qed.

(* [b2 = z01p + z10p - RN(z01p + z10p)] (the third VecSum limb): [<= 4u^2].   *)
Lemma b2_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (RND (x0 * y1) + RND (x1 * y0) - RND (RND (x0 * y1) + RND (x1 * y0)))
    <= 4 * (u * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
set s := RND (x0 * y1) + RND (x1 * y0).
have Hz01 := z01p_bound Nx Ny.
have Hz10 := z10p_bound Nx Ny.
have Hs8 : Rabs s <= 8 * u.
  by rewrite /s; have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); lra.
case: (Rlt_le_dec (Rabs s) (8 * u)) => Hs; last first.
  have Heq : Rabs s = 8 * u by lra.
  have Fs : format s.
    have Hor : s = 8 * u \/ s = - (8 * u) by split_Rabs; lra.
    have F8 : format (8 * u) by rewrite -pow_3mp; apply: format_pow.
    by case: Hor => ->; [ | apply: generic_format_opp].
  by rewrite (round_generic _ _ _ _ Fs) Rminus_diag Rabs_R0; nra.
case: (Req_dec s 0) => [->|sn0].
  by rewrite round_0 Rminus_0_r Rabs_R0; nra.
have Hulp : ulp s <= 8 * (u * u).
  rewrite ulp_neq_0 // /cexp /fexp -pow_3m2p; apply: bpow_le.
  suff : (mag beta s <= 3 - p)%Z by lia.
  by apply: mag_le_bpow => //; rewrite pow_3mp.
have He : Rabs (RND s - s) <= / 2 * ulp s by apply: error_le_half_ulp.
rewrite Rabs_minus_sym; lra.
Qed.

(* [c = RN(b2 + x1 y1)]: [<= 8u^2].                                           *)
Lemma c_bound b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 4 * (u * u) ->
  Rabs (RND (b2 + x1 * y1)) <= 8 * (u * u).
Proof.
move=> H1 H2.
have F8 : format (8 * (u * u)).
  by apply: (format_imul_u2 (k := 8)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang b2 (x1 * y1); lra.
Qed.

(* [s3 = RN(c + z3)]: [<= 20u^2].                                             *)
Lemma s3_bound c z3 :
  Rabs c <= 8 * (u * u) -> Rabs z3 <= 12 * (u * u) ->
  Rabs (RND (c + z3)) <= 20 * (u * u).
Proof.
move=> H1 H2.
have F20 : format (20 * (u * u)).
  by apply: (format_imul_u2 (k := 20)); have := two_p_ge_64; lia.
apply: Rabs_round_le_r => //.
by have := Rabs_triang c z3; lra.
Qed.

(* ===========================================================================*)
(* Section 6.2 (part 2) -- the error sources. [ThreeProd_error_norm] sums six *)
(* terms [eps0..eps5]; [eps1..eps4] are single-rounding errors bounded here   *)
(* by [k u^3]. ([eps0] is a pure product bound; [eps5] is the VSEB            *)
(* truncation, Theorem 3.)                                                    *)
(* ===========================================================================*)

(* [16u^2 = pow(4-2p)], [u^3 = pow(-3p)], [8u^3 = pow(3-3p)],                 *)
(* [16u^3 = pow(4-3p)]                                                        *)
Lemma pow_4m2p : pow (4 - 2 * p) = 16 * (u * u).
Proof.
rewrite (_ : (4 - 2 * p = 4 + - (2 * p))%Z); last by lia.
by rewrite bpow_plus u2_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma u3_pow : u * u * u = pow (- (3 * p)).
Proof. by rewrite u2_pow u_pow -bpow_plus; congr bpow; lia. Qed.

Lemma pow_3m3p : pow (3 - 3 * p) = 8 * (u * u * u).
Proof.
rewrite (_ : (3 - 3 * p = 3 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

Lemma pow_4m3p : pow (4 - 3 * p) = 16 * (u * u * u).
Proof.
rewrite (_ : (4 - 3 * p = 4 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

(* Master rounding-error bound: [|w| < pow e] gives [|w - RN w| <= half pow   *)
(* (e-p)].                                                                    *)
Lemma round_err_le w e :
  Rabs w < pow e -> Rabs (w - RND w) <= / 2 * pow (e - p).
Proof.
move=> Hw.
case: (Req_dec w 0) => [->|wn0].
  rewrite round_0 Rminus_0_r Rabs_R0.
  by apply: Rmult_le_pos; [lra | apply: bpow_ge_0].
have Hulp : ulp w <= pow (e - p).
  rewrite ulp_neq_0 // /cexp /fexp; apply: bpow_le.
  suff : (mag beta w <= e)%Z by lia.
  by apply: mag_le_bpow.
have He : Rabs (RND w - w) <= / 2 * ulp w by apply: error_le_half_ulp.
rewrite Rabs_minus_sym.
have Hu0 : 0 < / 2 by lra.
lra.
Qed.

(* [u <= 1/64] (from [p >= 6]); the slack the [eps0] and assembly bounds      *)
(* need.                                                                      *)
Lemma u_le_64 : u <= / 64.
Proof.
have -> : / 64 = pow (-6) by rewrite /= /Z.pow_pos /=; lra.
rewrite u_pow; apply: bpow_le; lia.
Qed.

(* [2u^3 = pow(1-3p)]: the tight cap on the third-order limbs.                *)
Lemma pow_1m3p : pow (1 - 3 * p) = 2 * (u * u * u).
Proof.
rewrite (_ : (1 - 3 * p = 1 + - (3 * p))%Z); last by lia.
by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
Qed.

(* A float below [pow e] is at most its predecessor [pow e - pow(e-p)] (it is *)
(* a multiple of [pow(e-p)] and strictly below [2^p pow(e-p)]).               *)
Lemma float_lt_bpow_le x e :
  format x -> Rabs x < pow e -> Rabs x <= pow e - pow (e - p).
Proof.
move=> Fx Hx.
have FRx : format (Rabs x) by apply: generic_format_abs.
have Fpe : format (pow e) by apply: format_pow.
have V : Valid_exp fexp by apply: FLX_exp_valid.
have Hpred := (@pred_ge_gt beta fexp V _ _ FRx Fpe Hx).
move: Hpred; rewrite pred_bpow.
move=> H; exact: H.
Qed.

(* Tight limb caps: the largest float below [2u] is [2u - 2u^2], below [2u^2] *)
(* is [2u^2 - 2u^3]. (Needed for the [eps0] product bound.)                   *)
Lemma x1_tight x0 x1 x2 :
  tw_norm x0 x1 x2 -> Rabs x1 <= 2 * u - 2 * (u * u).
Proof.
move=> N.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx1 := tw_norm_x1 N.
have Fx1 : format x1 by case: N => -[_ Fx1 _].
have Hlt : Rabs x1 < pow (1 - p) by rewrite pow_1mp.
have Hb := float_lt_bpow_le Fx1 Hlt.
move: Hb; rewrite pow_1mp (_ : (1 - p - p = 1 - 2 * p)%Z); last by lia.
rewrite pow_1m2p; lra.
Qed.

Lemma x2_tight x0 x1 x2 :
  tw_norm x0 x1 x2 -> Rabs x2 <= 2 * (u * u) - 2 * (u * u * u).
Proof.
move=> N.
have Hu0 : 0 < u by apply: u_gt_0.
have Hx2 := tw_norm_x2 N.
have Fx2 : format x2 by case: N => -[_ _ Fx2].
have Hlt : Rabs x2 < pow (1 - 2 * p) by rewrite pow_1m2p.
have Hb := float_lt_bpow_le Fx2 Hlt.
move: Hb; rewrite pow_1m2p (_ : (1 - 2 * p - p = 1 - 3 * p)%Z); last by lia.
rewrite pow_1m3p; lra.
Qed.

(* [eps0 = x1 y2 + x2 y1 + x2 y2] (the ignored products): [<= 8u^3 -          *)
(* 11.9u^4].                                                                  *)
Lemma eps0_bound x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (x1 * y2 + x2 * y1 + x2 * y2) <= 8 * (u * u * u) - 119 / 10 * (u * u * u
    * u).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have Hx1 := x1_tight Nx.
have Hy1 := x1_tight Ny.
have Hx2 := x2_tight Nx.
have Hy2 := x2_tight Ny.
have P1 := Rabs_pos x1; have P2 := Rabs_pos x2.
have Q1 := Rabs_pos y1; have Q2 := Rabs_pos y2.
apply: (Rle_trans _ (Rabs (x1 * y2) + Rabs (x2 * y1) + Rabs (x2 * y2))).
  have H1 := Rabs_triang (x1 * y2 + x2 * y1) (x2 * y2).
  have H2 := Rabs_triang (x1 * y2) (x2 * y1).
  lra.
rewrite !Rabs_mult.
nra.
Qed.

(* [eps1 = (z10m + x0 y2) - z31], [eps2 = (z01m + x2 y0) - z32]: [<= 4u^3].   *)
Lemma eps1_bound z10m x0 y2 :
  Rabs z10m <= 2 * (u * u) -> Rabs (x0 * y2) < 4 * (u * u) ->
  Rabs (z10m + x0 * y2 - RND (z10m + x0 * y2)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z10m + x0 * y2) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang z10m (x0 * y2).
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

Lemma eps2_bound z01m x2 y0 :
  Rabs z01m <= 2 * (u * u) -> Rabs (x2 * y0) < 4 * (u * u) ->
  Rabs (z01m + x2 * y0 - RND (z01m + x2 * y0)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z01m + x2 * y0) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang z01m (x2 * y0).
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

(* [eps3 = (z31 + z32) - z3]: [<= 8u^3].                                      *)
Lemma eps3_bound z31 z32 :
  Rabs z31 <= 6 * (u * u) -> Rabs z32 <= 6 * (u * u) ->
  Rabs (z31 + z32 - RND (z31 + z32)) <= 8 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (z31 + z32) < pow (4 - 2 * p).
  rewrite pow_4m2p.
  have H3 := Rabs_triang z31 z32.
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (4 - 2 * p - p = 4 - 3 * p)%Z); last by lia.
rewrite pow_4m3p; nra.
Qed.

(* [eps4 = (b2 + x1 y1) - c]: [<= 4u^3].                                      *)
Lemma eps4_bound b2 x1 y1 :
  Rabs b2 <= 4 * (u * u) -> Rabs (x1 * y1) < 4 * (u * u) ->
  Rabs (b2 + x1 * y1 - RND (b2 + x1 * y1)) <= 4 * (u * u * u).
Proof.
move=> H1 H2.
have Hu0 : 0 < u by apply: u_gt_0.
have Hw : Rabs (b2 + x1 * y1) < pow (3 - 2 * p).
  rewrite pow_3m2p.
  have H3 := Rabs_triang b2 (x1 * y1).
  nra.
have Herr := round_err_le Hw.
move: Herr; rewrite (_ : (3 - 2 * p - p = 3 - 3 * p)%Z); last by lia.
rewrite pow_3m3p; nra.
Qed.

(* Summing the five constant error sources [eps0..eps4]: the numerator        *)
(* [8u^3-11.9u^4 + 4u^3 + 4u^3 + 8u^3 + 4u^3 = 28u^3 - 11.9u^4].              *)
Lemma eps04_sum e0 e1 e2 e3 e4 :
  Rabs e0 <= 8 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  Rabs e1 <= 4 * (u * u * u) -> Rabs e2 <= 4 * (u * u * u) ->
  Rabs e3 <= 8 * (u * u * u) -> Rabs e4 <= 4 * (u * u * u) ->
  Rabs (e0 + e1 + e2 + e3 + e4) <= 28 * (u * u * u) - 119 / 10 * (u * u * u *
    u).
Proof.
move=> H0 H1 H2 H3 H4.
have T1 := Rabs_triang (e0 + e1 + e2 + e3) e4.
have T2 := Rabs_triang (e0 + e1 + e2) e3.
have T3 := Rabs_triang (e0 + e1) e2.
have T4 := Rabs_triang e0 e1.
lra.
Qed.

(* [eps5]: the VSEB truncation error. Given the VSEB output [vseb e] is       *)
(* P-nonoverlapping (this is exactly the [ThreeProd_isTW_norm] ingredient),   *)
(* the tail dropped by keeping 3 limbs is [<= (2u^3 + 4.2u^4)|sum|] by        *)
(* Theorem 3 ([Pnonoverlap_truncate_error] at k = 3). Stated conditionally so *)
(* it can be discharged now; the P-nonoverlap hypothesis comes from part 1.   *)
Lemma eps5_bound e :
  Pnonoverlap (vseb e) -> {in vseb e, forall z, format z} -> u <= / 64 ->
  Rabs (sumR (vseb e) - sumR (vsebK 3 e)) <=
    (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * Rabs (sumR (vseb e)).
Proof.
move=> Py Fy Hu64.
set y := vseb e.
have Hsplit : sumR y - sumR (vsebK 3 e) = sumR (drop 3 y).
  by rewrite /vsebK -/y -{1}(cat_take_drop 3 y) sumR_cat; ring.
rewrite Hsplit.
have -> : 2 * (u * u * u) + 42 / 10 * (u * u * u * u) =
          2 * u ^ 3 + 42 / 10 * u ^ 3.+1 by rewrite /=; ring.
case: (Req_dec (nth 0 y 0) 0) => [Hy0z|Hy0n]; last first.
  by apply: Pnonoverlap_truncate_error.
have H1 := @nth_step_zero p Hp2 y 0 Py Fy Hy0z.
have H2 := @nth_step_zero p Hp2 y 1 Py Fy H1.
have H3 := @nth_step_zero p Hp2 y 2 Py Fy H2.
have -> : sumR (drop 3 y) = 0.
  apply: (@small_head_zero p Hp2);
    [by apply: Pnonoverlap_drop
    | by move=> t /mem_drop; apply: Fy
    | by rewrite nth_drop addn0].
rewrite Rabs_R0.
have Hu0 : 0 < u by apply: u_gt_0.
apply: Rmult_le_pos; last exact: Rabs_pos.
have H4 : 0 <= u ^ 3 by apply: pow_le; lra.
have H5 : 0 <= u ^ 4 by apply: pow_le; lra.
lra.
Qed.

(* Projection-form [2Prod] facts (avoid the [let] in [TwoProd_correct], which *)
(* blocks [rewrite]): exactness and the two output formats.                   *)
Lemma TwoProd_exact a b :
  format a -> format b -> (TwoProd a b).1 + (TwoProd a b).2 = a * b.
Proof.
move=> Fa Fb.
rewrite /TwoProd /=.
have Fe : format (a * b - RND (a * b)).
  rewrite (_ : a * b - RND (a * b) = - (RND (a * b) - a * b)); last by ring.
  apply: generic_format_opp; exact: format_err_mul.
rewrite (round_generic _ _ _ _ Fe); ring.
Qed.

Lemma TwoProd_fmt1 a b : format a -> format b -> format (TwoProd a b).1.
Proof. by move=> Fa Fb; rewrite /TwoProd /=; apply: generic_format_round. Qed.

Lemma TwoProd_fmt2 a b : format a -> format b -> format (TwoProd a b).2.
Proof. by move=> Fa Fb; rewrite /TwoProd /=; apply: generic_format_round. Qed.

(* The error identity (algebraic core). Given the three [2Prod] exactness     *)
(* facts and that [VecSum] preserves sums ([b0+b1+b2 = z00m+z01p+z10p]), the  *)
(* product minus the pre-truncation sum [z00p+b0+b1+c+z3] equals the five     *)
(* error sources [eps0+eps1+eps2+eps3+eps4].                                  *)
Lemma error_decomp x0 x1 x2 y0 y1 y2
    z00p z00m z01p z01m z10p z10m b0 b1 b2 c z31 z32 z3 :
  z00p + z00m = x0 * y0 ->
  z01p + z01m = x0 * y1 ->
  z10p + z10m = x1 * y0 ->
  b0 + b1 + b2 = z00m + z01p + z10p ->
  (x0 + x1 + x2) * (y0 + y1 + y2) - (z00p + b0 + b1 + c + z3) =
    (x1 * y2 + x2 * y1 + x2 * y2)
    + (z10m + x0 * y2 - z31)
    + (z01m + x2 * y0 - z32)
    + (z31 + z32 - z3)
    + (b2 + x1 * y1 - c).
Proof.
move=> H1 H2 H3 H4.
have Hexp : (x0 + x1 + x2) * (y0 + y1 + y2) =
    x0 * y0 + x0 * y1 + x0 * y2 + x1 * y0 + x1 * y1 + x1 * y2
    + x2 * y0 + x2 * y1 + x2 * y2 by ring.
rewrite Hexp; lra.
Qed.

(* The concrete identity on [ThreeProd]'s own subterms: the product minus the *)
(* pre-truncation VecSum sum [sumR e] equals [eps0+eps1+eps2+eps3+eps4]. The  *)
(* [2Prod] exactness comes from [TwoProd_correct]; [b]'s sum from [vecSum3];  *)
(* [sumR e] from [vecSum_sum].                                                *)
Lemma sumR_e_decomp x0 x1 x2 y0 y1 y2
    z00p z00m z01p z01m z10p z10m b c z31 z32 z3 :
  format x0 -> format x1 -> format y0 -> format y1 ->
  TwoProd x0 y0 = (z00p, z00m) ->
  TwoProd x0 y1 = (z01p, z01m) ->
  TwoProd x1 y0 = (z10p, z10m) ->
  b = vecSum [:: z00m; z01p; z10p] ->
  c = RND (nth 0 b 2 + x1 * y1) ->
  z31 = RND (z10m + x0 * y2) ->
  z32 = RND (z01m + x2 * y0) ->
  z3 = RND (z31 + z32) ->
  (x0 + x1 + x2) * (y0 + y1 + y2) -
    sumR (vecSum [:: z00p; nth 0 b 0; nth 0 b 1; c; z3]) =
    (x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
    + (z01m + x2 * y0 - z32) + (z31 + z32 - z3) + (nth 0 b 2 + x1 * y1 - c).
Proof.
move=> Fx0 Fx1 Fy0 Fy1 HP00 HP01 HP10 Hb Hc H31 H32 H3.
have Ez00 : z00p + z00m = x0 * y0 by have := TwoProd_exact Fx0 Fy0; rewrite
  HP00.
have Ez01 : z01p + z01m = x0 * y1 by have := TwoProd_exact Fx0 Fy1; rewrite
  HP01.
have Ez10 : z10p + z10m = x1 * y0 by have := TwoProd_exact Fx1 Fy0; rewrite
  HP10.
have Fz00p : format z00p by have := TwoProd_fmt1 Fx0 Fy0; rewrite HP00.
have Fz00m : format z00m by have := TwoProd_fmt2 Fx0 Fy0; rewrite HP00.
have Fz01p : format z01p by have := TwoProd_fmt1 Fx0 Fy1; rewrite HP01.
have Fz10p : format z10p by have := TwoProd_fmt1 Fx1 Fy0; rewrite HP10.
have Eb : nth 0 b 0 + nth 0 b 1 + nth 0 b 2 = z00m + z01p + z10p.
  by rewrite Hb (vecSum3 Fz00m Fz01p Fz10p) /=; ring.
have Fb : {in b, forall z, format z}.
  rewrite Hb; apply: (@format_vecSum p Hp2 choice).
  by move=> z; rewrite !inE => /or3P[] /eqP-> //.
have Hsz : size b = 3%N by rewrite Hb size_vecSum.
have Fb0 : format (nth 0 b 0) by apply: Fb; rewrite mem_nth // Hsz.
have Fb1 : format (nth 0 b 1) by apply: Fb; rewrite mem_nth // Hsz.
have Fc : format c by rewrite Hc; apply: generic_format_round.
have Fz3 : format z3 by rewrite H3; apply: generic_format_round.
have Ee : sumR (vecSum [:: z00p; nth 0 b 0; nth 0 b 1; c; z3]) =
          z00p + nth 0 b 0 + nth 0 b 1 + c + z3.
  rewrite (@vecSum_sum p Hp2 choice choice_sym); last first.
    by move=> z; rewrite !inE =>
      /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]] //.
  by rewrite /=; ring.
rewrite Ee.
apply: (@error_decomp x0 x1 x2 y0 y1 y2 z00p z00m z01p z01m z10p z10m
          (nth 0 b 0) (nth 0 b 1) (nth 0 b 2) c z31 z32 z3) => //.
Qed.

(* Reading a triple word off a P-nonoverlapping list of floats: its first     *)
(* three (zero-padded) limbs form an [isTW]. This is the [TWSum_isTW]         *)
(* read-off, factored out; [ThreeProd_isTW_norm] ends the same way.           *)
Lemma Pnonoverlap_isTW3 (l : seq R) :
  Pnonoverlap l -> {in l, forall z, format z} ->
  isTW (TWR (nth 0 l 0) (nth 0 l 1) (nth 0 l 2)).
Proof.
move=> Hno Hfmt.
case: l Hno Hfmt => [|r0 [|r1 [|r2 tl]]] Hno Hfmt /=.
- by split; try exact: generic_format_0; left.
- by split; try exact: generic_format_0;
     [apply: Hfmt; rewrite !inE eqxx | left | left].
- by split; [apply: Hfmt; rewrite !inE eqxx
           | apply: Hfmt; rewrite !inE eqxx orbT
           | exact: generic_format_0 | apply: (Hno 0%N) | left].
by split; [apply: Hfmt; rewrite !inE eqxx
         | apply: Hfmt; rewrite !inE eqxx orbT
         | apply: Hfmt; rewrite !inE eqxx !orbT
         | apply: (Hno 0%N) | apply: (Hno 1%N)].
Qed.

(* Peeling the last 2Sum of a 5-element VecSum: [c, d] merge into [s3 =       *)
(* dwh(TwoSum c d)] with error [dwl(TwoSum c d)] emitted last. So the actual  *)
(* [vecSum [z00p;b0;b1;c;z3]] is [vecSum [z00p;b0;b1;s3]] with [e4] appended  *)
(* -- the paper's reduction to [VecSum(z00p,b0,b1,s3)] plus the trailing      *)
(* [e4].                                                                      *)
Lemma vecSum_split5 a b0 b1 c d :
  vecSum [:: a; b0; b1; c; d] =
  vecSum [:: a; b0; b1; dwh (TwoSum c d)] ++ [:: dwl (TwoSum c d)].
Proof.
rewrite /vecSum.
case E : (TwoSum c d) => [s ecd].
rewrite !vecSumAux_cons.
have -> : vecSumAux [:: d] = ([::], d) by [].
have -> : vecSumAux [:: s] = ([::], s) by [].
rewrite E !dwlE.
by case: (TwoSum b1 s) => sb1 eb1; case: (TwoSum b0 sb1) => sb0 eb0;
   case: (TwoSum a sb0) => sa ea.
Qed.

(* The trailing error [e4 = dwl(TwoSum c d)] of the peeled 2Sum is at most    *)
(* [1/2 ulp(s3)] ([s3 = dwh]). This is the paper's [ulp(s3) >= 2|e4|], the    *)
(* magnitude side of the [e4] F-nonoverlap step (item (b)).                   *)
Lemma e4_le_half_ulp c d :
  format c -> format d ->
  2 * Rabs (dwl (TwoSum c d)) <= ulp (dwh (TwoSum c d)).
Proof.
move=> Fc Fd.
have := magnitude_TwoSum Hp2 choice_sym Fc Fd.
rewrite /magnitudeDWR.
by case: (TwoSum c d) => s e /= H; lra.
Qed.

(* Top-of-VecSum property: the head of a VecSum output equals [RN] of (head + *)
(* next). Because [e0 = RN(x0 + s)] is the last 2Sum's high word and [e1 = x0 *)
(* + s - e0] its low word, so [e0 + e1 = x0 + s] and [RN(e0 + e1) = e0]. This *)
(* is the [(star)] premise consumed by [vseb_cons_round].                     *)
Lemma vecSum_top_round l :
  {in l, forall z, format z} -> (1 < size l)%N ->
  RND (nth 0 (vecSum l) 0 + nth 0 (vecSum l) 1) = nth 0 (vecSum l) 0.
Proof.
move=> Fl Hsz.
case: l Fl Hsz => [|x0 [|x1 l']] Fl // _.
set rest := x1 :: l'.
have Fx0 : format x0 by apply: Fl; rewrite inE eqxx.
have Frest : {in rest, forall z, format z}
  by move=> z zI; apply: Fl; rewrite inE zI orbT.
set s := (vecSumAux rest).2.
have Fs : format s.
  rewrite /s -vecSum_nth0.
  apply: (@format_vecSum p Hp2 choice rest Frest).
  by apply: mem_nth; rewrite size_vecSum.
have HV : vecSum (x0 :: rest) =
    RND (x0 + s) :: (x0 + s - RND (x0 + s)) :: (vecSumAux rest).1.
  rewrite /vecSum vecSumAux_cons.
  case E1 : (vecSumAux rest) => [es s0].
  have Hs0 : s0 = s by rewrite /s E1.
  rewrite Hs0.
  case E2 : (TwoSum x0 s) => [si ei] /=.
  have Hsi : si = RND (x0 + s) by move: (TwoSum_hi p choice x0 s); rewrite E2.
  move: (TwoSum_correct_loc Hp2 choice_sym Fx0 Fs); rewrite E2 => Hsum.
  by rewrite Hsi; congr (_ :: _ :: _); lra.
rewrite HV /=.
have -> : RND (x0 + s) + (x0 + s - RND (x0 + s)) = x0 + s by ring.
by [].
Qed.

(* The [star] head-emit step: when [RN(e0 + e1) = e0] (the top-of-VecSum      *)
(* property) and [e1 <> 0], VSEB emits [e0] and continues on the tail. This   *)
(* is the [e1 <> 0] half of the paper's [(r0, VSEB(2)) = VSEB(3)] identity.   *)
Lemma vseb_cons_round e0 e1 l :
  format e0 -> format e1 -> RND (e0 + e1) = e0 -> e1 <> 0 ->
  vseb (e0 :: e1 :: l) = e0 :: vseb (e1 :: l).
Proof.
move=> Fe0 Fe1 Hr Hne1.
have HT : TwoSum e0 e1 = DWR e0 e1.
  move: (TwoSum_correct_loc Hp2 choice_sym Fe0 Fe1) (TwoSum_hi p choice e0 e1).
  rewrite Hr.
  case: (TwoSum e0 e1) => s et /= Hsum Hs.
  by rewrite Hs; congr DWR; lra.
rewrite /vseb.
case: l => [|e2 l].
  by rewrite vsebAux_1 HT.
rewrite vsebAux_consS HT.
have -> : is_left (Req_EM_T e1 0) = false.
  by case: (Req_EM_T e1 0) => [E1|//]; case: (Hne1 E1).
by [].
Qed.

(* Appending a trailing element [e] finer than every nonzero element of [l]   *)
(* (bound [1/2 uls] against each) preserves F-nonoverlap. This is the shape   *)
(* of the [e4] tail: [e4] is divisible by [ulp(s3)], finer than every output  *)
(* limb.                                                                      *)
Lemma Fnonoverlap_aux_rcons prev l e :
  Rabs e <= / 2 * uls prev ->
  (forall x, x \in l -> Rabs e <= / 2 * uls x) ->
  Fnonoverlap_aux prev l -> Fnonoverlap_aux prev (rcons l e).
Proof.
elim: l prev => [|x l IH] prev Hp Hl Hf.
  by rewrite /=; split=> // _; case: (Req_EM_T e 0).
have Hlx : forall z, z \in l -> Rabs e <= / 2 * uls z.
  by move=> z zI; apply: Hl; rewrite inE zI orbT.
rewrite rcons_cons.
case: (Req_dec x 0) => [x0|xn0].
  rewrite x0 Fnonoverlap_aux_cons0; apply: IH => //.
  by move: Hf; rewrite x0 Fnonoverlap_aux_cons0.
apply: Fnonoverlap_aux_consN => //.
  by move: Hf => [Hx _]; apply: Hx.
apply: IH => //.
  by apply: Hl; rewrite inE eqxx.
move: Hf => [_ Hrec]; move: Hrec.
by have -> : is_left (Req_EM_T x 0) = false by
  case: (Req_EM_T x 0) => [xe|//]; case: (xn0 xe).
Qed.

Lemma Fnonoverlap_rcons l e :
  Fnonoverlap l -> (forall x, x \in l -> x <> 0 -> Rabs e <= / 2 * uls x) ->
  Fnonoverlap (rcons l e).
Proof.
move=> Fl Hb.
case: (Req_dec e 0) => [e0|en0].
  by rewrite e0; move: Fl; rewrite /Fnonoverlap filter_rcons eqxx.
rewrite /Fnonoverlap filter_rcons ifT; last by apply/eqP.
have Hsurv : forall x, x \in [seq z <- l | z != 0 :> R] ->
    Rabs e <= / 2 * uls x.
  move=> x; rewrite mem_filter => /andP[xn0 xI].
  by apply: Hb => // /eqP; rewrite (negbTE xn0).
move: Fl; rewrite /Fnonoverlap.
case E : [seq z <- l | z != 0 :> R] => [|x l'] /=.
  by split=> // _; case: (Req_EM_T e 0).
move=> Faux; apply: Fnonoverlap_aux_rcons => //.
  by apply: Hsurv; rewrite E inE eqxx.
by move=> z zI; apply: Hsurv; rewrite E inE zI orbT.
Qed.

(* The paper's [(r0, VSEB(2)) = VSEB(3)] star identity, non-degenerate half.  *)
(* When the second VecSum limb [e1] is nonzero, [vseb] emits the head [e0]    *)
(* unchanged and recurses on the tail -- so [VSEB(3)(e0..e4)] agrees with the *)
(* algorithm's [(e0, VSEB(2)(e1..e4))]. [RN(e0 + e1) = e0] is the             *)
(* top-of-VecSum property [vecSum_top_round].                                 *)
Lemma vseb_star l :
  {in l, forall z, format z} -> (1 < size l)%N ->
  nth 0 (vecSum l) 1 <> 0 ->
  vseb (vecSum l) = nth 0 (vecSum l) 0 :: vseb (behead (vecSum l)).
Proof.
move=> Fl Hsz Hne1.
have Hr := vecSum_top_round Fl Hsz.
have Fe : {in vecSum l, forall z, format z}.
  by move=> z zI; apply: (@format_vecSum p Hp2 choice l Fl).
have Hsze : (1 < size (vecSum l))%N.
  by rewrite size_vecSum; move: Hsz; case: (size l) => [|[|n]].
case E : (vecSum l) => [|e0 [|e1 rest]].
- by rewrite E in Hsze.
- by rewrite E in Hsze.
rewrite E /= in Hr Hne1 *.
apply: vseb_cons_round => //.
- by apply: Fe; rewrite E inE eqxx.
- by apply: Fe; rewrite E !inE eqxx orbT.
Qed.

(* Final assembly: an error numerator [<= 28u^3 - 11.9u^4] over a product of  *)
(* magnitude [>= 1 - 4u] yields the relative bound [28u^3 + 107u^4]. The      *)
(* [107u^4] slack is exactly what makes [(28u^3-11.9u^4)/(1-4u) <= 28u^3+     *)
(* 107u^4] hold at [u = 1/64] ([p >= 6]).                                     *)
Lemma error_assembly err xy :
  Rabs err <= 28 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  1 - 4 * u <= Rabs xy ->
  Rabs err <= (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs xy.
Proof.
move=> Hn Hxy.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
set B := 28 * (u * u * u) + 107 * (u * u * u * u).
have HB0 : 0 <= B by rewrite /B; nra.
apply: (Rle_trans _ (B * (1 - 4 * u))); last first.
  by apply: Rmult_le_compat_l.
apply: (Rle_trans _ _ _ Hn).
rewrite /B; nra.
Qed.

(* ---- degenerate inputs (a zero factor) -----------------------------------*)

Lemma negTW_id t : negTW (negTW t) = t.
Proof. by case: t => t0 t1 t2 /=; rewrite !Ropp_involutive. Qed.

(* A [twR] with a zero leading limb is the zero triple word.                  *)
Lemma isTW_zero_lead t : isTW t -> tw0 t = 0 -> t = TWR 0 0 0.
Proof.
case: t => t0 t1 t2 [_ _ _ H1 H2] /= t0z.
move: H1 H2; rewrite {}t0z => H1 H2.
have Ht1 : t1 = 0.
  case: H1 => // H1; move: H1; rewrite ulp_FLX_0 => H1; split_Rabs; lra.
have Ht2 : t2 = 0.
  move: H2; rewrite Ht1 => H2.
  case: H2 => // H2; move: H2; rewrite ulp_FLX_0 => H2; split_Rabs; lra.
by rewrite Ht1 Ht2.
Qed.

Lemma isTW_TWR000 : isTW (TWR 0 0 0).
Proof. by split; try exact: generic_format_0; left. Qed.

Lemma TwoSum00 : TwoSum 0 0 = DWR 0 0.
Proof.
rewrite /TwoSum Rplus_0_r round_0.
by do 8! (rewrite ?Rminus_0_l ?Rminus_0_r ?round_0 ?Ropp_0 ?Rplus_0_r
  ?Rplus_0_l).
Qed.

Lemma TwoProd00l a : TwoProd 0 a = (0, 0).
Proof.
by rewrite /TwoProd Rmult_0_l round_0 Rminus_0_r round_0.
Qed.

Lemma TwoProd00r a : TwoProd a 0 = (0, 0).
Proof.
by rewrite /TwoProd Rmult_0_r round_0 Rminus_0_r round_0.
Qed.

Lemma vsebAux_zeros n : vsebAux 0 (nseq n.+1 0) = [:: 0; 0].
Proof.
elim: n => [|n IH]; first by rewrite vsebAux_1 TwoSum00.
rewrite [nseq n.+2 0]/= vsebAux_consS TwoSum00.
by case: (Req_EM_T 0 0) => // _; rewrite -[0 :: nseq n 0]/(nseq n.+1 0) IH.
Qed.

(* [ThreeProd] of the zero triple word is zero (either argument).             *)
Lemma ThreeProd_0l y : ThreeProd (TWR 0 0 0) y = TWR 0 0 0.
Proof.
case: y => y0 y1 y2.
rewrite /ThreeProd !TwoProd00l /=.
rewrite !Rmult_0_l !Rplus_0_r !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0; 0] = nseq 2.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

Lemma ThreeProd_0r x : ThreeProd x (TWR 0 0 0) = TWR 0 0 0.
Proof.
case: x => x0 x1 x2.
rewrite /ThreeProd !TwoProd00r /=.
rewrite !Rmult_0_r !Rplus_0_l !round_0.
do 40! (rewrite ?round_0 ?Rplus_0_r ?Rplus_0_l ?Rminus_0_r ?Rminus_0_l ?Ropp_0).
rewrite /vsebK /vseb.
have -> : [:: 0; 0; 0] = nseq 2.+1 0 by [].
by rewrite vsebAux_zeros.
Qed.

(* ===========================================================================*)
(*  Section 6.2, part 1 -- the normalised [isTW] theorem and its crux.        *)
(* ===========================================================================*)

(* THE CRUX (paper Section 6.2, part 1): the inner VecSum [VecSum(z00+, b0,   *)
(* b1, c, z3)] is F-nonoverlapping. Route: peel the last 2Sum [(c, z3)] into  *)
(* [s3 = RN(c + z3)] plus the trailing error [e4] ([vecSum_split5]); the head *)
(* [VecSum(z00+, b0, b1, s3)] meets the Theorem-1 conditions through the      *)
(* four-case study of the overlap-index set [I] (Corollary 1,                 *)
(* [vecSum_Fnonoverlap_sep]); and [e4] is divisible by [ulp(s3)], finer than  *)
(* every output limb, so it appends by [Fnonoverlap_rcons]. See [doc/thm7.md] *)
(* Section 6.2 part 1.                                                        *)

(* [u |x| <= ulp x]: the workhorse for the [x1]-relative magnitude bounds.    *)
(* The rounding error [<= 1/2 ulp <= u|.|] converts a product/sum's absolute  *)
(* size into a multiple of the operand's [ulp] without any [mag] case study.  *)
Lemma u_abs_le_ulp x : u * Rabs x <= ulp x.
Proof.
have [->|xn0] := Req_dec x 0.
  by rewrite Rabs_R0 Rmult_0_r ulp_FLX_0 //; apply: Rle_refl.
by rewrite u_pow; have := ulp_FLX_gt p beta xn0; lra.
Qed.

(* A rounded product's error is [<= 2 ulp] of a factor when the OTHER factor  *)
(* is [<= 2] in magnitude (the normalised leading limbs [x0, y0 < 2]). Via    *)
(* [Rabs(RN t - t) <= u|t|] and [u|a*b| = u|a||b| <= 2 u|a| <= 2 ulp a].      *)
(* [ulp 1 = 2u]: the gap just above [1].  Used wherever a triple word has     *)
(* head [1] (Algorithm 13's [i], Algorithm 18's second argument).             *)
Lemma ulp_one : ulp 1 = 2 * u.
Proof.
have -> : (1 = pow 0)%R by [].
by rewrite ulp_bpow /FLX_exp u_pow bpow_plus; have -> : pow 1 = 2 by []; ring.
Qed.

(* [|RN t| <= (1 + u)|t|]: the relative-error bound, in the form the term     *)
(* bounds use it.                                                             *)
Lemma abs_round_le_rel t : Rabs (RND t) <= (1 + u) * Rabs t.
Proof.
have H := @relative_error_le p beta Hp2 choice t.
have T := Rabs_triang (RND t - t) t.
have E : RND t - t + t = RND t by ring.
rewrite E in T.
by have := Rabs_pos t; lra.
Qed.

Lemma err_mul_le_ulp a b :
  Rabs b <= 2 -> Rabs (a * b - RND (a * b)) <= 2 * ulp a.
Proof.
move=> Hb.
have [Herr1 Herr2] := error_bound_ulp_u beta Hp2 choice (a * b).
have Hua : u * Rabs a <= ulp a by apply: u_abs_le_ulp.
rewrite [Rabs (a * b - RND (a * b))]Rabs_minus_sym.
move: Herr2; rewrite Rabs_mult => Herr2.
have Hpa := Rabs_pos a; have Hpb := Rabs_pos b.
have Hu0 : 0 < u by apply: u_gt_0.
have Hula : 0 <= ulp a by apply: ulp_ge_0.
have H3 : u * (Rabs a * Rabs b) <= 2 * ulp a by nra.
lra.
Qed.

(* The [x1]-relative magnitude bound (paper Section 6.2 part 1): [|s3|] is    *)
(* [O(max(ulp x1, ulp y1))] -- every limb of [c, z3] is [O(ulp)] of the       *)
(* larger of [x1, y1] ([|x2| < ulp x1], [|y2| < ulp y1], the 2Prod/2Sum       *)
(* errors [<= 1/2 ulp], [|x1 y1| < 2 max]). The pure component-magnitude crux *)
(* behind [s3_ulp_op]. The [16] is generous ([p >= 6] gives [16 < 2^(p-1)]).  *)
Lemma s3_le_15max x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (dwh (TwoSum (RND (nth 0 (vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)]) 2
      + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))))
    <= 15 * Rmax (ulp x1) (ulp y1).
Proof.
move=> Hc Nx Ny.
rewrite (TwoSum_hi p choice).
set z00m := RND (x0 * y0 - RND (x0 * y0)).
set z01p := RND (x0 * y1).
set z10p := RND (x1 * y0).
set b2 := nth 0 (vecSum [:: z00m; z01p; z10p]) 2.
set c := RND (b2 + x1 * y1).
set z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2) +
               RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)).
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
have Hcb : Rabs c <= (1 + u) * (4 * (1 + u) * M + 2 * M).
  rewrite /c.
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang b2 (x1 * y1); lra.
have HA : Rabs (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2))
          <= (1 + u) * (2 * M + 2 * M).
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang (RND (x1 * y0 - RND (x1 * y0))) (x0 * y2); lra.
have HB : Rabs (RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))
          <= (1 + u) * (2 * M + 2 * M).
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang (RND (x0 * y1 - RND (x0 * y1))) (x2 * y0); lra.
have Hzb : Rabs z3 <= (1 + u) * ((1 + u) * (2 * M + 2 * M)
                                 + (1 + u) * (2 * M + 2 * M)).
  rewrite /z3.
  apply: (Rle_trans _ _ _ (RNrel _)).
  apply: Rmult_le_compat_l; first lra.
  have := Rabs_triang (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2))
                      (RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)); lra.
apply: (Rle_trans _ _ _ (RNrel _)).
apply: (Rle_trans _ ((1 + u) * (Rabs c + Rabs z3))).
  apply: Rmult_le_compat_l; first lra.
  exact: Rabs_triang.
apply: (Rle_trans _ ((1 + u) * ((1 + u) * (4 * (1 + u) * M + 2 * M)
    + (1 + u) * ((1 + u) * (2 * M + 2 * M) + (1 + u) * (2 * M + 2 * M))))).
  apply: Rmult_le_compat_l; first lra.
  by have := Hcb; have := Hzb; lra.
have Heq : (1 + u) * ((1 + u) * (4 * (1 + u) * M + 2 * M)
    + (1 + u) * ((1 + u) * (2 * M + 2 * M) + (1 + u) * (2 * M + 2 * M)))
    = M * ((1 + u) * ((1 + u) * (4 * (1 + u) + 2)
      + (1 + u) * ((1 + u) * 4 + (1 + u) * 4))) by ring.
rewrite Heq.
have HK : (1 + u) * ((1 + u) * (4 * (1 + u) + 2)
      + (1 + u) * ((1 + u) * 4 + (1 + u) * 4)) <= 15 by nra.
have := HM0; nra.
Qed.

(* Symmetric [<= 16] corollary of the tighter [s3_le_15max]; kept for the     *)
(* [s3_ulp_op] magnitude argument (the strict [< 16] margin is only needed    *)
(* for the [I]-set divisibility of [inner_head_Fnonoverlap]).                 *)
Lemma s3_le_16max x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  Rabs (dwh (TwoSum (RND (nth 0 (vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)]) 2
      + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))))
    <= 16 * Rmax (ulp x1) (ulp y1).
Proof.
move=> Hc Nx Ny.
have H := s3_le_15max Hc Nx Ny.
have H0 : 0 <= Rmax (ulp x1) (ulp y1)
  by apply: (Rle_trans _ _ _ (ulp_ge_0 beta fexp x1)); apply: Rmax_l.
lra.
Qed.

(* The [x1]-relative magnitude bound (paper Section 6.2 part 1): [ulp(s3)] is *)
(* at most half the [ulp] of one of the two cross-product rounds -- i.e. [2   *)
(* ulp(s3) <= ulp(z10+)] or [<= ulp(z01+)] (whichever is the larger operand). *)
(* From [|s3| <= 16 max(ulp x1, ulp y1) < ufp(larger) <= |larger round|]. The *)
(* larger operand is nonzero ([s3_le_16max] forces [s3 = 0] when both         *)
(* vanish).                                                                   *)
Lemma s3_ulp_op x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let s3 := dwh (TwoSum (RND (nth 0 (vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)]) 2
      + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) in
  s3 <> 0 ->
  2 * ulp s3 <= ulp (RND (x1 * y0)) \/ 2 * ulp s3 <= ulp (RND (x0 * y1)).
Proof.
move=> Hc Nx Ny s3 Hs3n0.
have Hmax : Rabs s3 <= 16 * Rmax (ulp x1) (ulp y1) := s3_le_16max Hc Nx Ny.
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

(* The Lemma-1 divisibility core (paper Section 6.2 part 1):                  *)
(* [a = RN(z01+ + z10+)] is divisible by [ulp(s3)]. Via Lemma 1               *)
(* [half_ulp_div_RN_add] on the larger                                        *)
(* operand ([s3_ulp_op]): [1/2 ulp(op) | a] and [ulp(s3) <= 1/2 ulp(op)].     *)
(* Reduced to the magnitude crux [s3_ulp_op].                                 *)
Lemma a_imul_ulp_s3 x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let s3 := dwh (TwoSum (RND (nth 0 (vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)]) 2
      + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) in
  s3 <> 0 ->
  is_imul (RND (RND (x0 * y1) + RND (x1 * y0))) (ulp s3).
Proof.
move=> Hc Nx Ny s3 Hs3n0.
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
have [Hop | Hop] := s3_ulp_op Hc Nx Ny Hs3n0.
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

(* The shared divisibility crux (paper Section 6.2 part 1): when [s3 <> 0],   *)
(* the leading input [z00+] and the [b0, b1] limbs are all divisible by       *)
(* [ulp(s3)]. [z00+]: [ulp(z00+) >= 2u > ulp(s3)]. [z00-]: [is_imul _ 4u^2]   *)
(* ([z00m_imul]). [b0 = RN(z00- + a)], [b1 = z00- + a - b0]: divisible via    *)
(* [a_imul_ulp_s3] + [is_imul_add]/[is_imul_pow_round]/[is_imul_minus]. Feeds *)
(* both [e4_dominates] (item b) and the [I]-set study                         *)
(* [inner_head_Fnonoverlap] (item a).                                         *)
Lemma inner_inputs_imul x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let s3 := dwh (TwoSum (RND (nth 0 bb 2 + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) in
  s3 <> 0 ->
  [/\ is_imul (RND (x0 * y0)) (ulp s3),
      is_imul (nth 0 bb 0) (ulp s3) & is_imul (nth 0 bb 1) (ulp s3)].
Proof.
move=> Hc Nx Ny bb s3 Hs3n0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z10m_bound Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z01m_bound Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz3 := z3_bound (z31_bound Hz10m2 (x0y2_bound Nx Ny))
                     (z32_bound Hz01m2 (x2y0_bound Nx Ny)).
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx Ny).
have Hc8 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 8 * (u * u)
  by apply: c_bound => //; apply: (x1y1_bound Nx Ny).
have Hs3E : s3 = RND (RND (nth 0 bb 2 + x1 * y1)
    + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))
  by rewrite /s3 TwoSum_hi.
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
have Ha := a_imul_ulp_s3 Hc Nx Ny Hs3n0.
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

(* Item (b) (paper Section 6.2 part 1): the trailing [e4 = dwl(TwoSum c z3)]  *)
(* is finer than every nonzero output limb of the head VecSum -- [ulp(s3) >=  *)
(* 2|e4|] and each limb is divisible by [ulp(s3)], so [|e4| <= 1/2            *)
(* uls(limb)]. Feeds [Fnonoverlap_rcons]. Reduced to [inner_inputs_imul] via  *)
(* [vecSum_imul_forward] and [is_imul_uls_ge]; the [e4 = 0] case ([s3 = 0])   *)
(* is trivial.                                                                *)
Lemma e4_dominates x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  forall x,
    x \in vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        dwh (TwoSum (RND (nth 0 bb 2 + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) ] ->
    x <> 0 ->
    Rabs (dwl (TwoSum (RND (nth 0 bb 2 + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))))
      <= / 2 * uls x.
Proof.
move=> Hc Nx Ny bb x xI xn0.
set c := RND (nth 0 bb 2 + x1 * y1) in xI *.
set z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
       + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in xI *.
have Fc : format c by apply: generic_format_round.
have Fz3 : format z3 by apply: generic_format_round.
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
have [Hz Hb0 Hb1] := inner_inputs_imul Hc Nx Ny Hs3n0.
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

(* From [|s| <= 15 ulp x] (strictly below [16 ulp x = pow(mag x - p + 4)])    *)
(* the magnitude of [s] is at most [mag x - p + 4]. The strict [15 < 16]      *)
(* margin is exactly what the p=6-tight [I]-set divisibility below needs.     *)
Lemma mag_le_of_le_15ulp x s : x <> 0 -> s <> 0 ->
  Rabs s <= 15 * ulp x -> (mag beta s <= mag beta x - p + 4)%Z.
Proof.
move=> xn0 sn0 Hs.
have Hulp : ulp x = pow (mag beta x - p).
  by rewrite ulp_neq_0 // /cexp /fexp /FLX_exp.
have H16 : 16 * ulp x = pow (mag beta x - p + 4).
  rewrite Hulp (_ : (mag beta x - p + 4 = 4 + (mag beta x - p))%Z); last by lia.
  by rewrite bpow_plus (_ : pow 4 = 16); [ring | rewrite /= /Z.pow_pos /=; lra].
have Hs0 : Rabs s < pow (mag beta x - p + 4).
  have Hup : 0 < ulp x by rewrite Hulp; apply: bpow_gt_0.
  rewrite -H16; lra.
by apply: mag_le_bpow.
Qed.

(* The Lemma-1 divisibility on the ACTUAL operand grid (paper Section 6.2     *)
(* part 1: "1/2 ulp(x1) | b0, b1"): for [w] either [x1] or [y1] (nonzero),    *)
(* the [b0, b1] limbs are divisible by [1/2 ulp w]. [a = RN(z01+ + z10+)] is  *)
(* [1/2 ulp]-divisible by its larger operand round ([half_ulp_div_RN_add]),   *)
(* whose [ulp] dominates [ulp w] ([|z.0+| >= |w|]); [z00-] is far finer       *)
(* ([4u^2 | z00-]). Feeds the [I]-set [ufp] bounds.                           *)
Lemma b01_imul_half_ulp x0 x1 x2 y0 y1 y2 (w : R) :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  (w = x1 \/ w = y1) -> w <> 0 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  is_imul (nth 0 bb 0) (/ 2 * ulp w) /\ is_imul (nth 0 bb 1) (/ 2 * ulp w).
Proof.
move=> Nx Ny Hw wn0 bb.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1o Hx2o] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r Hy1o Hy2o] := Ny.
have Hu0 : 0 < u by apply: u_gt_0.
set z00m := RND (x0 * y0 - RND (x0 * y0)).
set z01p := RND (x0 * y1).
set z10p := RND (x1 * y0).
have Fz00m : format z00m by apply: generic_format_round.
have Fz01p : format z01p by apply: generic_format_round.
have Fz10p : format z10p by apply: generic_format_round.
set a := RND (z01p + z10p).
have Hbb0 : nth 0 bb 0 = RND (z00m + a).
  by rewrite /bb (vecSum3 Fz00m Fz01p Fz10p).
have Hbb1 : nth 0 bb 1 = z00m + a - RND (z00m + a).
  by rewrite /bb (vecSum3 Fz00m Fz01p Fz10p).
have Hhw : / 2 * ulp w = pow (cexp w - 1).
  rewrite ulp_neq_0 // (_ : / 2 = pow (-1)); last by rewrite /= /Z.pow_pos /=;
    lra.
  by rewrite -bpow_plus; congr bpow; lia.
have Hwabs : Rabs w < 2 * u
  by case: Hw => ->; [apply: (tw_norm_x1 Nx) | apply: (tw_norm_x1 Ny)].
have Hwmag : (mag beta w <= 2 - p)%Z.
  apply: mag_le_bpow => //.
  apply: (Rlt_le_trans _ _ _ Hwabs).
  by rewrite -pow_1mp; apply: bpow_le; lia.
have Hzm : is_imul z00m (/ 2 * ulp w).
  rewrite Hhw.
  apply: (is_imul_pow_le (y1 := (2 - 2 * p)%Z)); last first.
    by rewrite /cexp /fexp /FLX_exp; lia.
  rewrite /z00m round_generic; last first.
    rewrite (_ : x0 * y0 - RND (x0 * y0) = - (RND (x0 * y0) - x0 * y0)); last by
      ring.
    by apply: generic_format_opp; exact: format_err_mul.
  rewrite pow_2m2p; exact: (z00m_imul Nx Ny).
have Ha : is_imul a (/ 2 * ulp w).
  have key : forall op oth : R, format op -> format oth -> op <> 0 ->
      (mag beta w <= mag beta op)%Z -> a = RND (op + oth) ->
      is_imul a (/ 2 * ulp w).
    move=> op oth Fop Foth opn0 Hmag ->.
    rewrite Hhw.
    apply: (is_imul_pow_le (y1 := (cexp op - 1)%Z)); last first.
      by rewrite /cexp /fexp /FLX_exp; lia.
    have -> : pow (cexp op - 1) = / 2 * ulp op.
      rewrite ulp_neq_0 // (_ : / 2 = pow (-1)); last by rewrite /= /Z.pow_pos
        /=; lra.
      by rewrite -bpow_plus; congr bpow; lia.
    exact: (half_ulp_div_RN_add Fop Foth opn0).
  case: Hw => Hw.
  - apply: (key z10p z01p Fz10p Fz01p) => //.
    + move=> H0; apply: wn0; rewrite Hw.
      have Hle : Rabs x1 <= Rabs (x1 * y0).
        rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
        have := Rabs_pos x1; nra.
      have Hr : Rabs x1 <= Rabs (RND (x1 * y0)).
        by apply: Rabs_round_le_l; [exact: generic_format_abs | exact: Hle].
      move: Hr; rewrite -/z10p H0 Rabs_R0 => Hr.
      by move: Hr; split_Rabs; lra.
    + rewrite Hw -(mag_abs beta x1) -(mag_abs beta z10p).
      apply: mag_le; first by apply: Rabs_pos_lt; move: wn0; rewrite Hw.
      rewrite /z10p; apply: Rabs_round_le_l; first exact: generic_format_abs.
      by rewrite Rabs_mult (Rabs_pos_eq y0); [have := Rabs_pos x1; nra | lra].
    + by rewrite /a Rplus_comm.
  - apply: (key z01p z10p Fz01p Fz10p) => //.
    + move=> H0.
      have Hle : Rabs y1 <= Rabs (x0 * y1).
        rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
        have := Rabs_pos y1; nra.
      have Hr : Rabs y1 <= Rabs (RND (x0 * y1)).
        by apply: Rabs_round_le_l; [exact: generic_format_abs | exact: Hle].
      move: Hr; rewrite -/z01p H0 Rabs_R0 => Hr.
      by move: wn0; rewrite Hw; move: Hr; split_Rabs; lra.
    + rewrite Hw -(mag_abs beta y1) -(mag_abs beta z01p).
      apply: mag_le; first by apply: Rabs_pos_lt; move: wn0; rewrite Hw.
      rewrite /z01p; apply: Rabs_round_le_l; first exact: generic_format_abs.
      by rewrite Rabs_mult (Rabs_pos_eq x0); [have := Rabs_pos y1; nra | lra].
rewrite Hbb0 Hbb1; split.
- rewrite Hhw; apply: is_imul_pow_round; rewrite -Hhw.
  by apply: is_imul_add; [exact: Hzm | exact: Ha].
apply: is_imul_minus.
  by apply: is_imul_add; [exact: Hzm | exact: Ha].
rewrite Hhw; apply: is_imul_pow_round; rewrite -Hhw.
by apply: is_imul_add; [exact: Hzm | exact: Ha].
Qed.

(* The packaged [I]-set facts (paper Section 6.2 part 1): for the [WLOG]      *)
(* larger operand [w] ([x1] or [y1]), [4 ulp s3 <= ulp w] and [ufp s3 <= 8    *)
(* ulp w] (from the strict [|s3| <= 15 ulp w], p>=6-tight) and [1/2 ulp w |   *)
(* b0, b1] ([b01_imul_half_ulp]). These four facts discharge every [Cor1_hyp] *)
(* [ufp] side-condition of the [I]-set cases.                                 *)
Lemma s3_div_facts x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let s3 := dwh (TwoSum (RND (nth 0 bb 2 + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) in
  s3 <> 0 ->
  exists w : R, [/\ w <> 0,
     4 * ulp s3 <= ulp w,
     ufp s3 <= 8 * ulp w,
     is_imul (nth 0 bb 0) (/ 2 * ulp w) & is_imul (nth 0 bb 1) (/ 2 * ulp w)].
Proof.
move=> Hc Nx Ny bb s3 Hs3n0.
have Hu0 : 0 < u by apply: u_gt_0.
have Hmax : Rabs s3 <= 15 * Rmax (ulp x1) (ulp y1) := s3_le_15max Hc Nx Ny.
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

(* [TwoSum 0 y = DWR y 0] for a float [y] (the accumulator starts at 0).      *)
Lemma TwoSum_0l y : format y -> TwoSum 0 y = DWR y 0.
Proof.
move=> Fy.
move: (TwoSum_correct_loc Hp2 choice_sym (@generic_format_0 beta fexp) Fy)
      (TwoSum_hi p choice 0 y).
rewrite Rplus_0_l (round_generic _ _ _ _ Fy).
by case: (TwoSum 0 y) => s et /= Hsum Hs; rewrite Hs; congr DWR; lra.
Qed.

(* Zero inputs are inert for [VecSum]: a [0] entry only prepends a [0] error  *)
(* limb and leaves the running sum unchanged ([TwoSum 0 s = DWR s 0]). Hence  *)
(* the zero-filtered [VecSum] output is the same whether or not the zero      *)
(* inputs are dropped first -- so [Fnonoverlap (vecSum l)] (which is read off *)
(* the zero-filtered output) equals [Fnonoverlap (vecSum (filter nonzero      *)
(* l))]. This is the bridge that lets [Cor1_hyp] (which demands all-nonzero)  *)
(* apply to the [I]-set cases where [b0], [b1], or [s3] vanish.               *)
Lemma vecSum_filter0 l : {in l, forall z, format z} ->
  [seq z <- vecSum l | z != 0 :> R] =
  [seq z <- vecSum [seq x <- l | x != 0 :> R] | z != 0 :> R].
Proof.
move=> Fl.
suff aux : forall m : seq R, {in m, forall z : R, format z} ->
    (vecSumAux m).2 = (vecSumAux [seq x <- m | x != 0 :> R]).2 /\
    [seq z <- (vecSumAux m).1 | z != 0 :> R] =
      [seq z <- (vecSumAux [seq x <- m | x != 0 :> R]).1 | z != 0 :> R].
  have [Hs Hes] := aux l Fl.
  rewrite /vecSum.
  move: Hs Hes; case: (vecSumAux l) => es s; case: (vecSumAux _) => es2 s2 /= ->
    Hes.
  by rewrite /= Hes.
elim => [|x m IH] Hm; first by split.
have Fx : format x by apply: Hm; rewrite inE eqxx.
have Hmf : {in m, forall z : R, format z}
  by move=> z zm; apply: Hm; rewrite inE zm orbT.
have [IHs IHes] := IH Hmf.
have Fs : format (vecSumAux m).2
  by have [] := @format_vecSumAux p Hp2 choice m Hmf.
have U : forall n : seq R, {in n, forall z : R, format z} ->
   (vecSumAux (x :: n)).2 = dwh (TwoSum x (vecSumAux n).2) /\
   [seq z <- (vecSumAux (x :: n)).1 | z != 0] =
   [seq z <- dwl (TwoSum x (vecSumAux n).2) :: (vecSumAux n).1 | z != 0].
  move=> n Hn; case: n Hn => [_|c n' Hn].
  - have Hhi : dwh (TwoSum x 0) = x
      by rewrite (TwoSum_hi p choice) Rplus_0_r round_generic.
    have Hlo : dwl (TwoSum x 0) = 0.
      have Hc : dwh (TwoSum x 0) + dwl (TwoSum x 0) = x + 0
        by exact: (TwoSum_correct_loc Hp2 choice_sym Fx (@generic_format_0 beta
          fexp)).
      by move: Hc; rewrite Hhi; lra.
    have E0 : (vecSumAux (@nil R)).2 = 0 by [].
    have Ex1 : (vecSumAux [:: x]).1 = [::] by [].
    have Ex2 : (vecSumAux [:: x]).2 = x by [].
    rewrite E0 Ex1 Ex2 Hhi Hlo; split => //.
    by rewrite /= eqxx.
  rewrite vecSumAux_cons.
  case E : (vecSumAux (c :: n')) => [es s].
  by case E2 : (TwoSum x s) => [si ei]; rewrite /=.
have Hfmf : {in [seq x0 <- m | x0 != 0], forall z : R, format z}
  by move=> z; rewrite mem_filter => /andP[_ zm]; apply: Hmf.
have [Um2 Um1] := U m Hmf.
have [Uf2 Uf1] := U [seq x0 <- m | x0 != 0] Hfmf.
case: (Req_dec x 0) => [x0|xn0].
- have Hf : [seq z <- x :: m | z != 0] = [seq z <- m | z != 0]
    by rewrite /= x0 eqxx.
  have HT0 : TwoSum x (vecSumAux m).2 = DWR (vecSumAux m).2 0
    by rewrite x0; apply: TwoSum_0l.
  rewrite Hf; split.
  + by rewrite Um2 HT0 /= IHs.
  + by rewrite Um1 HT0 /= eqxx IHes.
have Hf : [seq z <- x :: m | z != 0] = x :: [seq z <- m | z != 0]
  by rewrite /= ifT //; apply/eqP.
rewrite Hf; split.
- by rewrite Um2 Uf2 IHs.
rewrite Um1 Uf1 IHs.
set d := dwl (TwoSum x (vecSumAux [seq x0 <- m | x0 != 0]).2).
by rewrite /= IHes.
Qed.

(* Corollary of [vecSum_filter0]: to prove [Fnonoverlap (vecSum l)] it        *)
(* suffices to prove it for the nonzero-filtered inputs -- exactly what lets  *)
(* [Cor1_hyp] (all-nonzero) apply after dropping the vanishing [b0], [b1],    *)
(* [s3].                                                                      *)
Lemma Fnonoverlap_vecSum_filter l : {in l, forall z : R, format z} ->
  Fnonoverlap (vecSum [seq x <- l | x != 0 :> R]) -> Fnonoverlap (vecSum l).
Proof. by move=> Fl; rewrite /Fnonoverlap (vecSum_filter0 Fl). Qed.

(* Item (a) (paper Section 6.2 part 1): the head VecSum [(z00+, b0, b1, s3)]  *)
(* (with [s3 = dwh(TwoSum c z3) = RN(c + z3)]) is F-nonoverlapping -- the     *)
(* four-case study of the overlap-index set [I] (Corollary 1,                 *)
(* [vecSum_Fnonoverlap_sep]). The intricate core; see [doc/thm7.md].          *)
Lemma inner_head_Fnonoverlap x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Fnonoverlap (vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
        dwh (TwoSum (RND (nth 0 bb 2 + x1 * y1))
             (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
                 + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))))]).
Proof.
move=> Hc Nx Ny bb.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
set z00p := RND (x0 * y0).
set c := RND (nth 0 bb 2 + x1 * y1).
set z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)).
set b0 := nth 0 bb 0.
set b1 := nth 0 bb 1.
set s3 := dwh (TwoSum c z3).
have Fc : format c by apply: generic_format_round.
have Fz3 : format z3 by apply: generic_format_round.
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
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z10m_bound Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z01m_bound Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz3b := z3_bound (z31_bound Hz10m2 (x0y2_bound Nx Ny))
                      (z32_bound Hz01m2 (x2y0_bound Nx Ny)).
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx Ny).
have Hc8 : Rabs c <= 8 * (u * u) by apply: (c_bound Hb2 (x1y1_bound Nx Ny)).
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
  have [w [wn0 H4w Hufpw Hb0im Hb1im]] := s3_div_facts Hc Nx Ny s3n0.
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

Lemma inner_Fnonoverlap x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  Fnonoverlap (vecSum
    [:: RND (x0 * y0);
        nth 0 bb 0;
        nth 0 bb 1;
        RND (nth 0 bb 2 + x1 * y1);
        RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
           + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))]).
Proof.
move=> Hc Nx Ny bb.
rewrite (vecSum_split5 (RND (x0 * y0)) (nth 0 bb 0) (nth 0 bb 1)
  (RND (nth 0 bb 2 + x1 * y1))
  (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
      + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))).
rewrite cats1.
apply: Fnonoverlap_rcons.
  by apply: (inner_head_Fnonoverlap Hc Nx Ny).
by apply: (e4_dominates Hc Nx Ny).
Qed.

(* Round-to-nearest keeps a float [x] when the perturbation [y] stays within  *)
(* half the gap to each neighbour ([x - pred x] below, [succ x - x] above).   *)
(* Both midpoint tests ([round_N_le_midp]/[round_N_ge_midp]).                 *)
Lemma RN_add_keep x y :
  format x -> Rabs y < / 2 * (x - pred beta fexp x) ->
  Rabs y < / 2 * (succ beta fexp x - x) -> RND (x + y) = x.
Proof.
move=> Fx Hlo Hhi.
have Hy := Rle_abs y.
have Hy' : - Rabs y <= y by split_Rabs; lra.
have Hle : RND (x + y) <= x.
  apply: round_N_le_midp => //; move: Hhi Hy; lra.
have Hge : x <= RND (x + y).
  apply: round_N_ge_midp => //; move: Hlo Hy'; lra.
by apply: Rle_antisym.
Qed.

(* For a float [x >= 3/4] the neighbour gaps are at least [u]: [ulp x >= u]   *)
(* and [x - pred x = ulp(pred x) >= u] (as [pred x >= 1/2]).                  *)
Lemma pred_gap_ge x : format x -> 3 / 4 <= x -> u <= x - pred beta fexp x.
Proof.
move=> Fx Hx.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have V : Valid_exp fexp by apply: FLX_exp_valid.
have M : Monotone_exp fexp by apply: FLX_exp_monotone.
have F12 : format (/ 2).
  by rewrite (_ : / 2 = pow (-1)); [apply: format_pow | rewrite /= /Z.pow_pos
    /=; lra].
have H12x : / 2 < x by lra.
have Hpx : / 2 <= pred beta fexp x by apply: (@pred_ge_gt beta fexp V _ _ F12 Fx
  H12x).
have Fp : format (pred beta fexp x) by apply: generic_format_pred.
have Hgap : x - pred beta fexp x = ulp (pred beta fexp x).
  have := @succ_pred beta fexp V x Fx; rewrite succ_eq_pos; last by lra.
  by lra.
rewrite Hgap.
have Hu12 : ulp (/ 2) = u.
  rewrite (_ : / 2 = pow (-1)); last by rewrite /= /Z.pow_pos /=; lra.
  rewrite ulp_bpow /fexp /FLX_exp.
  have -> : (-1 + 1 - p = - p)%Z by lia.
  by rewrite -u_pow.
rewrite -Hu12.
by apply: ulp_le_pos => //; lra.
Qed.

(* [u <= ulp x] for a float [x >= 1/2] (both neighbour gaps of an [x >= 3/4]  *)
(* are then at least [u]).                                                    *)
Lemma ulp_ge_u x : 1 / 2 <= x -> u <= ulp x.
Proof.
move=> Hx.
have Hu0 : 0 < u by apply: u_gt_0.
have V : Valid_exp fexp by apply: FLX_exp_valid.
have M : Monotone_exp fexp by apply: FLX_exp_monotone.
have Hu12 : ulp (/ 2) = u.
  rewrite (_ : / 2 = pow (-1)); last by rewrite /= /Z.pow_pos /=; lra.
  rewrite ulp_bpow /fexp /FLX_exp.
  have -> : (-1 + 1 - p = - p)%Z by lia.
  by rewrite -u_pow.
rewrite -Hu12; apply: ulp_le_pos => //; lra.
Qed.

(* Specialisation of [RN_add_keep] used for VSEB head domination: when        *)
(* [x >= 3/4] and the perturbation is [< u/2], round-to-nearest keeps [x]     *)
(* (both gaps are at least [u]).                                              *)
Lemma RN_add_keep_small x y :
  format x -> 3 / 4 <= x -> 2 * Rabs y < u -> RND (x + y) = x.
Proof.
move=> Fx Hx Hy.
have Hpred := pred_gap_ge Fx Hx.
have Hsucc : u <= succ beta fexp x - x.
  have Hx0 : 0 <= x by lra.
  rewrite (succ_eq_pos beta fexp x Hx0).
  have -> : x + ulp x - x = ulp x by ring.
  by apply: ulp_ge_u; lra.
apply: RN_add_keep => //; lra.
Qed.

(* A 2Sum whose second operand is dominated ([2|x| < u], head [>= 3/4]) keeps *)
(* the head: [TwoSum e0 x = DWR e0 x].                                        *)
Lemma TwoSum_keep e0 x :
  format e0 -> format x -> 3 / 4 <= e0 -> 2 * Rabs x < u ->
  TwoSum e0 x = DWR e0 x.
Proof.
move=> Fe0 Fx He0 Hx.
have Hrn : RND (e0 + x) = e0 by apply: RN_add_keep_small.
move: (TwoSum_correct_loc Hp2 choice_sym Fe0 Fx) (TwoSum_hi p choice e0 x).
rewrite Hrn.
by case: (TwoSum e0 x) => s et /= Hsum Hs; rewrite Hs; congr DWR; lra.
Qed.


(* Prepending a zero to a format list leaves every [vseb] entry unchanged     *)
(* (the leading zero merges away; the two runs may differ only in a trailing  *)
(* zero, so equality is at the [nth] level).                                  *)
Lemma vseb_cons0_nth l :
  {in l, forall z, format z} ->
  forall j, nth 0 (vseb (0 :: l)) j = nth 0 (vseb l) j.
Proof.
move=> Fl j.
have E0 : vseb (0 :: l) = vsebAux 0 l by [].
rewrite E0; clear E0.
case: l Fl => [|y [|z l]] Fl.
- by case: j => [|[|j]].
- rewrite vsebAux_1 TwoSum_0l; last by apply: Fl; rewrite inE eqxx.
  have -> : vseb [:: y] = [:: y] by [].
  case: j => [|[|j]] //=.
  by rewrite nth_nil.
- rewrite vsebAux_consS TwoSum_0l; last by apply: Fl; rewrite inE eqxx.
  by case: (Req_EM_T 0 0) => // _.
Qed.

(* VSEB head domination ([nth] level): a head [e0 >= 3/4] whose every tail    *)
(* limb is [2|x| < u] (so [RN(e0 + x) = e0]) is emitted first, then VSEB      *)
(* recurses on the tail. Equality up to trailing zeros, so stated on [nth].   *)
Lemma vsebAux_dom_nth e0 l :
  format e0 -> 3 / 4 <= e0 -> {in l, forall z, format z} ->
  (forall x, x \in l -> 2 * Rabs x < u) ->
  forall j, nth 0 (vsebAux e0 l) j = nth 0 (e0 :: vseb l) j.
Proof.
move=> Fe0 He0.
elim: l => [|x l IH] Fl Hb j; first by [].
have Fx : format x by apply: Fl; rewrite inE eqxx.
have Hx : 2 * Rabs x < u by apply: Hb; rewrite inE eqxx.
have Hfl : {in l, forall z, format z}
  by move=> z zI; apply: Fl; rewrite inE zI orbT.
have Hbl : forall z, z \in l -> 2 * Rabs z < u
  by move=> z zI; apply: Hb; rewrite inE zI orbT.
case: l IH Fl Hb Hfl Hbl => [|y l'] IH Fl Hb Hfl Hbl.
  by rewrite vsebAux_1 (TwoSum_keep Fe0 Fx He0 Hx); case: j => [|[|j]].
rewrite vsebAux_consS (TwoSum_keep Fe0 Fx He0 Hx).
case: (Req_dec x 0) => [x0|xn0].
  have -> : is_left (Req_EM_T x 0) = true.
    by case: (Req_EM_T x 0) => [//|E]; case: (E x0).
  rewrite (IH Hfl Hbl j).
  case: j => [|j] //=.
  rewrite x0.
  by rewrite (vseb_cons0_nth Hfl).
have -> : is_left (Req_EM_T x 0) = false.
  by case: (Req_EM_T x 0) => [E|//]; case: (xn0 E).
by case: j => [|j] //=.
Qed.

(* The running-sum recurrence of [vecSumAux]: the high word of a [>= 2]       *)
(* element list is [RN] of the head plus the running high word of the tail.   *)
Lemma vecSumAux_run_cons a b l :
  (vecSumAux [:: a, b & l]).2 = RND (a + (vecSumAux (b :: l)).2).
Proof.
rewrite vecSumAux_cons.
case E : (vecSumAux (b :: l)) => [es s] /=.
by rewrite -(TwoSum_hi p choice a s); case: (TwoSum a s).
Qed.

(* The generic read-off behind the [e1 = 0] star case, SHARED by Algorithm 9  *)
(* ([vseb_head3_e1zero]) and Algorithm 10 ([vsebFast_head3_e1zero] in         *)
(* ThreeProdFast.v): a head limb [>= 3/4] dominating every other limb         *)
(* ([2|x| < u]) is emitted first by VSEB, so the first three limbs of         *)
(* [vseb l] are [l0] and the first two of [vseb (behead l)].  No algorithm    *)
(* specifics -- only [vsebAux_dom_nth].                                       *)
Lemma vseb_head3_dom l :
  {in l, forall z, format z} -> (0 < size l)%N -> 3 / 4 <= nth 0 l 0 ->
  (forall x, x \in behead l -> 2 * Rabs x < u) ->
  nth 0 (vseb l) 0 = nth 0 l 0 /\
  nth 0 (vseb l) 1 = nth 0 (vseb (behead l)) 0 /\
  nth 0 (vseb l) 2 = nth 0 (vseb (behead l)) 1.
Proof.
move=> Fl Hsz He0 Hdom.
have Hl0 : l = nth 0 l 0 :: behead l by case: (l) Hsz => [|a s].
have Hkey : forall j, nth 0 (vseb l) j = nth 0 (nth 0 l 0 :: vseb (behead l)) j.
  move=> j.
  have -> : vseb l = vsebAux (nth 0 l 0) (behead l) by rewrite {1}Hl0.
  apply: vsebAux_dom_nth => //.
    by apply: Fl; rewrite Hl0 inE eqxx.
  by move=> z zI; apply: Fl; rewrite Hl0 inE zI orbT.
split; [|split].
- by rewrite (Hkey 0%N).
- by rewrite (Hkey 1%N).
- by rewrite (Hkey 2%N).
Qed.

(* The [e1 = 0] half of the star identity (paper Section 6.2, part 1): when   *)
(* the second VecSum limb vanishes, [|s1|,|s2|,|s3| < 16u <= 1/2 ufp(z00+)],  *)
(* so the next nonzero limb is still [< 1/2 ulp(e0)] and [VSEB] reproduces    *)
(* [(e0, VSEB(2))]. Unlike [e1 <> 0] (which is the structural top-of-VecSum   *)
(* [vecSum_top_round]), this needs the Section-6.1 magnitudes --              *)
(* [Fnonoverlap] alone bounds by [1/2 uls], too weak under FLX where [uls >=  *)
(* ulp]. Returns the three head-limb identities shared by                     *)
(* [ThreeProd_norm_eq]. See [doc/thm7.md] Section 6.2 part 1 (the [e1 = 0]    *)
(* bullet).                                                                   *)
Lemma vseb_head3_e1zero x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0);
        nth 0 bb 0;
        nth 0 bb 1;
        RND (nth 0 bb 2 + x1 * y1);
        RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
           + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))] in
  nth 0 e 1 = 0 ->
  nth 0 (vseb e) 0 = nth 0 e 0 /\
  nth 0 (vseb e) 1 = nth 0 (vseb (behead e)) 0 /\
  nth 0 (vseb e) 2 = nth 0 (vseb (behead e)) 1.
Proof.
move=> Hc Nx Ny bb e He1.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have Hp4 : (4 <= p)%Z by lia.
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny.
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z10m_bound Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z01m_bound Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := x0y2_bound Nx Ny.
have Hx2y0 := x2y0_bound Nx Ny.
have Hx1y1 := x1y1_bound Nx Ny.
have Hz31 := z31_bound Hz10m2 Hx0y2.
have Hz32 := z32_bound Hz01m2 Hx2y0.
have Hz3 := z3_bound Hz31 Hz32.
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
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx Ny).
have Hc8 : Rabs (RND (nth 0 bb 2 + x1 * y1)) <= 8 * (u * u)
  by apply: c_bound.
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
have Hr3 : Rabs (RND (RND (nth 0 bb 2 + x1 * y1)
    + RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))) <= 20 * (u * u)
  by apply: s3_bound.
set c := RND (nth 0 bb 2 + x1 * y1).
set z3v := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
       + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)).
have Hr3' : Rabs ((vecSumAux [:: c; z3v]).2) <= 20 * (u * u).
  by rewrite vecSumAux_run_cons.
have Hr2 : Rabs ((vecSumAux [:: nth 0 bb 1; c; z3v]).2) <= 32 * (u * u).
  rewrite vecSumAux_run_cons.
  have F32 : format (32 * (u * u))
    by apply: (format_imul_u2 (k := 32)); have := two_p_ge_64; lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 1) ((vecSumAux [:: c; z3v]).2).
  move: Hb1 Hr3' Ht; nra.
have Hr1 : Rabs ((vecSumAux [:: nth 0 bb 0; nth 0 bb 1; c; z3v]).2) <= 11 * u.
  rewrite vecSumAux_run_cons.
  have F11 : format (11 * u) by apply: Fku; have := two_p_ge_64; simpl; lia.
  apply: Rabs_round_le_r => //.
  have Ht := Rabs_triang (nth 0 bb 0) ((vecSumAux [:: nth 0 bb 1; c; z3v]).2).
  move: Hb0 Hr2 Ht Hu0 Hu64; nra.
have He0 : 3 / 4 <= nth 0 e 0.
  rewrite /e vecSum_nth0 vecSumAux_run_cons.
  have F34 : format (3 / 4).
    have -> : 3 / 4 = IZR 3 * pow (-2) by rewrite /= /Z.pow_pos /=; lra.
    by apply: format_mult_pow; have := two_p_ge_64; simpl; lia.
  apply: round_le_l => //.
  have Hz00p1 : 1 <= RND (x0 * y0) by apply: (z00p_lb Nx Ny).
  rewrite -/c -/z3v.
  set r1 := (vecSumAux [:: nth 0 bb 0; nth 0 bb 1; c; z3v]).2.
  set z := RND (x0 * y0).
  move: Hr1 Hz00p1; rewrite -/r1 -/z => Hr1 Hz00p1.
  have Hr1c := Rabs_le_inv _ _ Hr1.
  lra.
have HL5f : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v],
    forall z, format z}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
    try exact: generic_format_round; exact: Fnthbb.
have Ee : e = vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v]
  by rewrite /e -/c -/z3v.
have Hstep : forall k : nat, (k.+1 < 5)%N ->
    Rabs ((vecSumAux
      (drop k [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v])).2) < 16 * u
        ->
    2 * Rabs (nth 0 e k.+1) < u.
  move=> k Hk Hrk.
  have Hle := @vecSum_err_le_half_ulp_run p Hp2 choice choice_sym
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v] k Hk HL5f.
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
    have -> : drop 1 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v]
      = [:: nth 0 bb 0; nth 0 bb 1; c; z3v] by [].
    by move: Hr1 Hu0; lra.
  - apply: (Hstep 2%N) => //.
    have -> : drop 2 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v]
      = [:: nth 0 bb 1; c; z3v] by [].
    by move: Hr2 Hu0 Hu64; nra.
  - apply: (Hstep 3%N) => //.
    have -> : drop 3 [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3v]
      = [:: c; z3v] by [].
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

(* The paper's star identity [(r0, VSEB(2)) = VSEB(3)]: [ThreeProd (x, y)]'s  *)
(* output equals the first three limbs of [vseb e], with [e = VecSum(z00+,    *)
(* b0, b1, c, z3)] the pre-truncation VecSum output. [e1 <> 0] uses           *)
(* [vseb_star] (structural), [e1 = 0] uses [vseb_head3_e1zero]. Shared by     *)
(* [ThreeProd_isTW_norm] and [ThreeProd_error_norm].                          *)
Lemma ThreeProd_norm_eq x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
        RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
           + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))] in
  ThreeProd (TWR x0 x1 x2) (TWR y0 y1 y2) =
    TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2).
Proof.
move=> Hc Nx' Ny'.
rewrite /ThreeProd /TwoProd.
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + x1 * y1);
  RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
     + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))].
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
    by apply: (vseb_head3_e1zero Hc Nx' Ny').
  have FL5 : {in [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
      RND (nth 0 bb 2 + x1 * y1);
      RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
         + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))],
      forall z, format z}.
    move=> z; rewrite !inE.
    move=> /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]];
      try apply: generic_format_round; apply: Fnthbb.
  have Hstar := vseb_star FL5 (isT : (1 < 5)%N) He1.
  have Hs : vseb e = nth 0 e 0 :: vseb (behead e) by exact: Hstar.
  rewrite Hs; split; [exact: erefl | split; exact: erefl].
by rewrite Hbeh H0 H1 H2.
Qed.

(* Section 6.2, part 1 -- [ThreeProd (x, y)] is a triple word (normalised).   *)
(* The inner VecSum is F-nonoverlapping ([inner_Fnonoverlap]), so [vseb e] is *)
(* P-nonoverlapping (Theorem 2); [ThreeProd_norm_eq] identifies the output    *)
(* with the first three limbs of [vseb e], a TW by [Pnonoverlap_isTW3].       *)
Lemma ThreeProd_isTW_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y -> isTW (ThreeProd x y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 Nx.
case: y Ny => y0 y1 y2 Ny.
have Nx' : tw_norm x0 x1 x2 by exact: Nx.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
rewrite (ThreeProd_norm_eq Hc Nx' Ny').
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + x1 * y1);
  RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
     + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))].
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
have Fno : Fnonoverlap e by rewrite /e /bb; apply: (inner_Fnonoverlap Hc Nx'
  Ny').
have Pno : Pnonoverlap (vseb e).
  have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
  by have [] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
apply: Pnonoverlap_isTW3; first exact: Pno.
by apply: (@format_vseb p Hp2 choice e Fe).
Qed.

(* The normalised product [x*y >= 1 - 4u] (paper Section 6.2). Both factors   *)
(* are [>= 1 - 2u] (limbs [x1_tight]/[x2_tight]), and both are positive.      *)
Lemma xy_ge x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  1 - 4 * u <= Rabs ((x0 + x1 + x2) * (y0 + y1 + y2)).
Proof.
move=> Nx Ny.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have Hx1 := x1_tight Nx; have Hx2 := x2_tight Nx.
have Hy1 := x1_tight Ny; have Hy2 := x2_tight Ny.
case: Nx => _ Hx0l Hx0h _ _.
case: Ny => _ Hy0l Hy0h _ _.
have Hx : 1 - 2 * u <= x0 + x1 + x2 by split_Rabs; nra.
have Hy : 1 - 2 * u <= y0 + y1 + y2 by split_Rabs; nra.
rewrite Rabs_pos_eq; nra.
Qed.

(* Error assembly for the [eps5 <> 0] branch (paper omitted;                  *)
(* doc/thm7-eps5.md). When [eps5 <> 0] one source term is small, so the       *)
(* numerator [eps0+..+eps4] drops to [26u^3-11.9u^4]; keeping the FULL [eps5] *)
(* truncation term still fits the [28u^3+107u^4] budget (the old draft's [<=  *)
(* 28u^3+103u^4]). [num] is the reduced numerator, [s5] the truncation error, *)
(* [sm = sumR(vseb e)].                                                       *)
Lemma error_assembly_eps5 (num s5 sm xy : R) :
  Rabs num <= 26 * (u * u * u) - 119 / 10 * (u * u * u * u) ->
  Rabs s5 <= (2 * (u * u * u) + 42 / 10 * (u * u * u * u)) * Rabs sm ->
  Rabs sm <= Rabs xy + (26 * (u * u * u) - 119 / 10 * (u * u * u * u)) ->
  1 - 4 * u <= Rabs xy ->
  Rabs (s5 + num) <= (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs xy.
Proof.
move=> Hnum Hs5 Hsm Hxy.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have Ht := Rabs_triang s5 num.
have Hxy0 : 0 <= Rabs xy by apply: Rabs_pos.
have Hsm0 : 0 <= Rabs sm by apply: Rabs_pos.
have Hs5' : Rabs s5 <= (2 * (u * u * u) + 42 / 10 * (u * u * u * u))
    * (Rabs xy + (26 * (u * u * u) - 119 / 10 * (u * u * u * u))).
  apply: (Rle_trans _ _ _ Hs5); apply: Rmult_le_compat_l; [nra | exact: Hsm].
move: Ht Hnum Hs5' Hxy; set r := Rabs xy; set a := Rabs (s5 + num);
  set b := Rabs s5; set d := Rabs num.
move=> Ht Hnum Hs5' Hxy.
have Hr : (26 * (u*u*u) + 1028/10 * (u*u*u*u)) * (1 - 4*u)
    <= (26 * (u*u*u) + 1028/10 * (u*u*u*u)) * r
  by apply: Rmult_le_compat_l; [nra | lra].
have Hpoly : (2*(u*u*u) + 42/10*(u*u*u*u) + 1) * (26*(u*u*u) - 119/10*(u*u*u*u))
    <= (26*(u*u*u) + 1028/10*(u*u*u*u)) * (1 - 4*u) by clear -Hu0 Hu64; nra.
clear -Ht Hnum Hs5' Hr Hpoly; nra.
Qed.

(* [vsebAux]/[vseb] forward the [pow g] grid: a 2Sum of multiples of [pow g]  *)
(* has both words multiples of [pow g], so the whole VSEB walk stays on the   *)
(* grid.                                                                      *)
Lemma vsebAux_imul_forward g l : forall eps : R,
  format eps -> {in l, forall z, format z} ->
  is_imul eps (pow g) -> {in l, forall z, is_imul z (pow g)} ->
  {in vsebAux eps l, forall z, is_imul z (pow g)}.
Proof.
have Hdw : forall a b : R, format a -> format b ->
    is_imul a (pow g) -> is_imul b (pow g) ->
    is_imul (dwh (TwoSum a b)) (pow g) /\ is_imul (dwl (TwoSum a b)) (pow g).
  move=> a b Fa Fb Ia Ib.
  have Hhi : dwh (TwoSum a b) = RND (a + b) by rewrite (TwoSum_hi p choice).
  have Hsum : dwh (TwoSum a b) + dwl (TwoSum a b) = a + b
    by exact: (TwoSum_correct_loc Hp2 choice_sym Fa Fb).
  split; first by rewrite Hhi; apply: is_imul_pow_round; apply: is_imul_add.
  have -> : dwl (TwoSum a b) = a + b - dwh (TwoSum a b) by lra.
  apply: is_imul_minus; first by apply: is_imul_add.
  by rewrite Hhi; apply: is_imul_pow_round; apply: is_imul_add.
elim: l => [|e l IH] eps Feps Fl Ieps Il z.
  by rewrite /= inE => /eqP->.
have Fe : format e by apply: Fl; rewrite inE eqxx.
have Ie : is_imul e (pow g) by apply: Il; rewrite inE eqxx.
have Fl' : {in l, forall z, format z}
  by move=> t tl; apply: Fl; rewrite inE tl orbT.
have Il' : {in l, forall z, is_imul z (pow g)}
  by move=> t tl; apply: Il; rewrite inE tl orbT.
have [Hdh Hdl] := Hdw eps e Feps Fe Ieps Ie.
have [Fr Fet] := @format_TwoSum p Hp2 choice eps e Feps Fe.
clear Fl Il.
case: l IH Fl' Il' => [|e2 l'] IH Fl' Il'.
  move: z Hdh Hdl; rewrite vsebAux_1; case: (TwoSum eps e) => y0 y1 /= z Hdh
    Hdl.
  by rewrite !inE => /orP[/eqP->|/eqP->].
move: z; rewrite vsebAux_consS.
clear Fr Fet.
have FT := @format_TwoSum p Hp2 choice eps e Feps Fe.
move: Hdh Hdl FT; case E : (TwoSum eps e) => [r et] Hdh Hdl [Fr Fet].
case: (Req_EM_T et 0) => [et0|etn0].
  change (forall z, z \in vsebAux r (e2 :: l') -> is_imul z (pow g)).
  exact: (IH r Fr Fl' Hdh Il').
change (forall z, z \in r :: vsebAux et (e2 :: l') -> is_imul z (pow g)).
move=> z; rewrite inE => /orP[/eqP->|]; first exact: Hdh.
exact: (IH et Fet Fl' Hdl Il').
Qed.

Lemma vseb_imul_forward g l :
  {in l, forall z, format z} -> {in l, forall z, is_imul z (pow g)} ->
  {in vseb l, forall z, is_imul z (pow g)}.
Proof.
case: l => [//|e0 l] Fl Il /=; apply: vsebAux_imul_forward.
- by apply: Fl; rewrite inE eqxx.
- by move=> t tl; apply: Fl; rewrite inE tl orbT.
- by apply: Il; rewrite inE eqxx.
by move=> t tl; apply: Il; rewrite inE tl orbT.
Qed.

(* The all-big case (paper omitted; old draft Theorem 10 / doc/thm7-eps5.md): *)
(* when [u^2<=|y2|], [u^2<=|x2|], [4u^2<=|c|] and [4u^2<=|z3|] the leading    *)
(* terms [z00+, b0, b1, c, z3] are all divisible by [8u^3] and [|z00+         *)
(* +b0+b1+c+z3| < 5], so [|r0| <= 5]; a fourth nonzero P-nonoverlapping limb  *)
(* of [vseb e] would then be [< 8u^3] yet a nonzero multiple of [8u^3],       *)
(* impossible. Hence VSEB(3) drops nothing and [eps5 = 0]. THE hard           *)
(* divisibility chunk (see doc/thm7-eps5.md).                                 *)
Lemma eps5_zero_all_big x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3] in
  u * u <= Rabs x2 -> u * u <= Rabs y2 ->
  4 * (u * u) <= Rabs c -> 4 * (u * u) <= Rabs z3 ->
  sumR (vseb e) - sumR (vsebK 3 e) = 0.
Proof.
move=> Hc Nx Ny bb c z3 e Hx2h Hy2h Hcb Hz3b.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1o Hx2o] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r Hy1o Hy2o] := Ny.
have Hu2 : u * u = pow (- (2 * p)) by rewrite u_pow -bpow_plus; congr bpow; lia.
(* [u^2 <= |x2|] with [|x2| < ulp x1] forces [ulp x1 > u^2], hence [u <=      *)
(* |x1|].                                                                     *)
have Hderive : forall (w1 w2 : R), w2 = 0 \/ Rabs w2 < ulp w1 ->
    u * u <= Rabs w2 -> u <= Rabs w1.
  move=> w1 w2 Hw2o Hw2h.
  have Hw2n0 : w2 <> 0.
    by move=> H0; move: Hw2h; rewrite H0 Rabs_R0 => H; nra.
  have Hw2lt : Rabs w2 < ulp w1 by case: Hw2o => // H0; case: Hw2n0.
  have Hw1n0 : w1 <> 0.
    move=> H0; move: Hw2lt; rewrite H0 ulp_FLX_0 => H.
    by have := Rabs_pos w2; nra.
  have Hmagw1 : (1 - p <= mag beta w1)%Z.
    have Hulp : pow (- (2 * p)) < ulp w1 by rewrite -Hu2; lra.
    move: Hulp; rewrite ulp_neq_0 // /cexp /fexp /FLX_exp => H.
    by have := lt_bpow beta _ _ H; lia.
  apply: (Rle_trans _ (pow (mag beta w1 - 1))).
    by rewrite u_pow; apply: bpow_le; lia.
  by have := ufp_le_abs Hw1n0; rewrite /ufp.
have Hx1b : u <= Rabs x1 by apply: (Hderive x1 x2 Hx2o Hx2h).
have Hy1b : u <= Rabs y1 by apply: (Hderive y1 y2 Hy2o Hy2h).
pose g := (3 - 3 * p)%Z.
have Himcx : forall x : R, format x -> (g <= cexp x)%Z -> is_imul x (pow g).
  move=> x Fx Hcx.
  by apply: (is_imul_pow_le (y1 := cexp x)); [exact: format_imul_cexp | exact:
    Hcx].
have Hcexp : forall x : R, cexp x = (mag beta x - p)%Z
  by move=> x; rewrite /cexp /fexp /FLX_exp.
have Iz00p : is_imul (RND (x0 * y0)) (pow g).
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp; have Hlb : 1 <= RND (x0 * y0) by apply: (z00p_lb Nx Ny).
  suff : (1 <= mag beta (RND (x0 * y0)))%Z by rewrite /g; lia.
  by apply: mag_ge_bpow; rewrite pow0E Rabs_pos_eq; lra.
have Fu : format u by rewrite u_pow; apply: format_pow.
have Iz00m : is_imul (RND (x0 * y0 - RND (x0 * y0))) (pow g).
  rewrite round_generic; last first.
    rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
      ring.
    by apply: generic_format_opp; exact: format_err_mul.
  apply: (is_imul_pow_le (y1 := (2 - 2 * p)%Z)); last by rewrite /g; lia.
  rewrite pow_2m2p; exact: (z00m_imul Nx Ny).
have Iz01p : is_imul (RND (x0 * y1)) (pow g).
  have Hge : u <= Rabs (RND (x0 * y1)).
    apply: Rabs_round_le_l => //.
    rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
    have := Rabs_pos y1; nra.
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp /g; suff : (1 - p <= mag beta (RND (x0 * y1)))%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (1 - p - 1 = - p)%Z); last by lia.
  by rewrite -u_pow.
have Iz10p : is_imul (RND (x1 * y0)) (pow g).
  have Hge : u <= Rabs (RND (x1 * y0)).
    apply: Rabs_round_le_l => //.
    rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
    have := Rabs_pos x1; nra.
  apply: Himcx; first by apply: generic_format_round.
  rewrite Hcexp /g; suff : (1 - p <= mag beta (RND (x1 * y0)))%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (1 - p - 1 = - p)%Z); last by lia.
  by rewrite -u_pow.
have Ia : is_imul (RND (RND (x0 * y1) + RND (x1 * y0))) (pow g)
  by apply: is_imul_pow_round; apply: is_imul_add.
have Fz00mf : format (RND (x0 * y0 - RND (x0 * y0))) by apply:
  generic_format_round.
have Fz01pf : format (RND (x0 * y1)) by apply: generic_format_round.
have Fz10pf : format (RND (x1 * y0)) by apply: generic_format_round.
have Hbbe : bb = [:: RND (RND (x0 * y0 - RND (x0 * y0))
                         + RND (RND (x0 * y1) + RND (x1 * y0)));
    RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))
      - RND (RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 *
        y0)));
    RND (x0 * y1) + RND (x1 * y0) - RND (RND (x0 * y1) + RND (x1 * y0))]
  by rewrite /bb (vecSum3 Fz00mf Fz01pf Fz10pf).
have Ib0 : is_imul (nth 0 bb 0) (pow g).
  by rewrite Hbbe /=; apply: is_imul_pow_round; apply: is_imul_add;
    [exact: Iz00m | exact: Ia].
have Ib1 : is_imul (nth 0 bb 1) (pow g).
  rewrite Hbbe /=; apply: is_imul_minus.
    by apply: is_imul_add; [exact: Iz00m | exact: Ia].
  by apply: is_imul_pow_round; apply: is_imul_add; [exact: Iz00m | exact: Ia].
have Ic : is_imul c (pow g).
  apply: Himcx; first by rewrite /c; apply: generic_format_round.
  rewrite Hcexp /g; suff : (3 - 2 * p <= mag beta c)%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (3 - 2 * p - 1 = 2 - 2 * p)%Z); last by lia.
  by rewrite pow_2m2p.
have Iz3 : is_imul z3 (pow g).
  apply: Himcx; first by rewrite /z3; apply: generic_format_round.
  rewrite Hcexp /g; suff : (3 - 2 * p <= mag beta z3)%Z by lia.
  apply: mag_ge_bpow; rewrite (_ : (3 - 2 * p - 1 = 2 - 2 * p)%Z); last by lia.
  by rewrite pow_2m2p.
have Fz00pf : format (RND (x0 * y0)) by apply: generic_format_round.
have Fcf : format c by rewrite /c; apply: generic_format_round.
have Fz3f : format z3 by rewrite /z3; apply: generic_format_round.
have Fbb : {in bb, forall z, format z}.
  apply: (@format_vecSum p Hp2 choice) => z; rewrite !inE.
  by move=> /orP[/eqP->|/orP[/eqP->|/eqP->]]; apply: generic_format_round.
have Fb0 : format (nth 0 bb 0) by apply: Fbb; rewrite /bb mem_nth //
  size_vecSum.
have Fb1 : format (nth 0 bb 1) by apply: Fbb; rewrite /bb mem_nth //
  size_vecSum.
pose l0 := [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3].
have Feinp : {in l0, forall z, format z}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]] //.
have Ieinp : {in l0, forall z, is_imul z (pow g)}.
  move=> z; rewrite !inE
    => /orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]]] //.
have Ie : {in e, forall z, is_imul z (pow g)}
  by rewrite /e; apply: vecSum_imul_forward.
have Fe : {in e, forall z, format z}
  by rewrite /e; apply: (@format_vecSum p Hp2 choice).
have Ivse : {in vseb e, forall z, is_imul z (pow g)}
  by apply: vseb_imul_forward.
have Hsz5 : size e = 5%N by rewrite /e size_vecSum.
have Fno : Fnonoverlap e by rewrite /e /bb; apply: (inner_Fnonoverlap Hc Nx Ny).
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall z, format z}
  by apply: (@format_vseb p Hp2 choice e Fe).
have Hsume : sumR e = RND (x0 * y0) + nth 0 bb 0 + nth 0 bb 1 + c + z3.
  rewrite /e (@vecSum_sum p Hp2 choice choice_sym); last by apply: Feinp.
  by rewrite /=; ring.
have Hsplit : sumR (vseb e) - sumR (vsebK 3 e) = sumR (drop 3 (vseb e))
  by rewrite /vsebK -{1}(cat_take_drop 3 (vseb e)) sumR_cat; ring.
rewrite Hsplit.
have RNrel : forall t : R, Rabs (RND t) <= (1 + u) * Rabs t.
  move=> t; have Ht := relative_error_le beta Hp2 choice t.
  have H2 : Rabs (RND t) <= Rabs t + Rabs (RND t - t)
    by have := Rabs_triang t (RND t - t);
       rewrite (_ : t + (RND t - t) = RND t); [lra | ring].
  have := Rabs_pos t; nra.
have Hz00mb : Rabs (RND (x0 * y0 - RND (x0 * y0))) <= 2 * u.
  rewrite round_generic; first by apply: (z00m_bound Nx Ny).
  rewrite (_ : x0 * y0 - RND (x0 * y0) = -(RND (x0 * y0) - x0 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01pb := z01p_bound Nx Ny.
have Hz10pb := z10p_bound Nx Ny.
have Hab : Rabs (RND (RND (x0 * y1) + RND (x1 * y0))) <= 9 * u.
  apply: (Rle_trans _ _ _ (RNrel _)).
  have := Rabs_triang (RND (x0 * y1)) (RND (x1 * y0)); nra.
have Hb01 : nth 0 bb 0 + nth 0 bb 1
    = RND (x0 * y0 - RND (x0 * y0)) + RND (RND (x0 * y1) + RND (x1 * y0))
  by rewrite Hbbe /=; ring.
have Hz00pu : RND (x0 * y0) < 4 by apply: (z00p_ub Nx Ny).
have Hz00pl : 1 <= RND (x0 * y0) by apply: (z00p_lb Nx Ny).
have Hz10m2 : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z10m_bound Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m2 : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z01m_bound Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz3ub : Rabs z3 <= 12 * (u * u)
  := z3_bound (z31_bound Hz10m2 (x0y2_bound Nx Ny))
              (z32_bound Hz01m2 (x2y0_bound Nx Ny)).
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx Ny).
have Hc8 : Rabs c <= 8 * (u * u) := c_bound Hb2 (x1y1_bound Nx Ny).
have Hb01b : Rabs (nth 0 bb 0 + nth 0 bb 1) <= 11 * u.
  rewrite Hb01.
  have := Rabs_triang (RND (x0 * y0 - RND (x0 * y0)))
                      (RND (RND (x0 * y1) + RND (x1 * y0))); lra.
have Hsum5 : Rabs (sumR e) < 5.
  rewrite Hsume.
  have -> : RND (x0 * y0) + nth 0 bb 0 + nth 0 bb 1 + c + z3
      = RND (x0 * y0) + (nth 0 bb 0 + nth 0 bb 1) + (c + z3) by ring.
  set S := nth 0 bb 0 + nth 0 bb 1.
  have T1 := Rabs_triang (RND (x0 * y0) + S) (c + z3).
  have T2 := Rabs_triang (RND (x0 * y0)) S.
  have T3 := Rabs_triang c z3.
  have Hz00pa : Rabs (RND (x0 * y0)) < 4 by rewrite Rabs_pos_eq; lra.
  have HS : Rabs S <= 11 * u by exact: Hb01b.
  clear -T1 T2 T3 Hz00pa HS Hc8 Hz3ub Hu0 Hu64; nra.
have Hsvse : Rabs (sumR (vseb e)) < 5 by rewrite Hsumeq.
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
have Hn3 : nth 0 (vseb e) 3 = 0.
  case: (Req_dec (nth 0 (vseb e) 0) 0) => [Hr0|Hr0n].
    have H1 := @nth_step_zero p Hp2 (vseb e) 0 Pno Fvse Hr0.
    have H2 := @nth_step_zero p Hp2 (vseb e) 1 Pno Fvse H1.
    exact: (@nth_step_zero p Hp2 (vseb e) 2 Pno Fvse H2).
  case: (Req_dec (nth 0 (vseb e) 3) 0) => [//|Hn3n].
  have Hn2n : nth 0 (vseb e) 2 <> 0
    by move=> H; apply: Hn3n; apply: (@nth_step_zero p Hp2 (vseb e) 2 Pno Fvse
      H).
  have Hn1n : nth 0 (vseb e) 1 <> 0
    by move=> H; apply: Hn2n; apply: (@nth_step_zero p Hp2 (vseb e) 1 Pno Fvse
      H).
  have Hsz3 : (3 < size (vseb e))%N
    by rewrite ltnNge; apply/negP => Hge; apply: Hn3n; rewrite nth_default.
  have Hsz2 : (2 < size (vseb e))%N by apply: ltn_trans Hsz3.
  have Hsz1 : (1 < size (vseb e))%N by apply: ltn_trans Hsz2.
  have Hr08 : Rabs (nth 0 (vseb e) 0) < pow 3.
    have Hlow := @sumR_ufp_lower p Hp2 (vseb e) Pno Fvse Hr0n.
    have HU := ufp_gt_0 (nth 0 (vseb e) 0).
    have Hufp8 : ufp (nth 0 (vseb e) 0) < pow 3.
      have Hp38 : pow 3 = 8 by rewrite /= /Z.pow_pos /=; lra.
      clear -Hlow Hsvse Hu0 Hu64 HU Hp38; nra.
    apply: (Rlt_le_trans _ _ _ (bpow_mag_gt beta (nth 0 (vseb e) 0))).
    apply: bpow_le.
    by move: Hufp8; rewrite /ufp => H; have := lt_bpow beta _ _ H; lia.
  have Hm1 := Hstep 0%N (3%Z) Hn1n Hsz1 Hr08.
  have Hm2 := Hstep 1%N (3 - p)%Z Hn2n Hsz2 Hm1.
  have Hm3 := Hstep 2%N (3 - p - p)%Z Hn3n Hsz3 Hm2.
  have Hge : pow g <= Rabs (nth 0 (vseb e) 3).
    apply: is_imul_pow_le_abs; last exact: Hn3n.
    by apply: Ivse; apply: mem_nth.
  have Hpg : (3 - p - p - p = g)%Z by rewrite /g; lia.
  by rewrite Hpg in Hm3; lra.
apply: (@small_head_zero p Hp2).
- exact: Pnonoverlap_drop.
- by move=> z /mem_drop; apply: Fvse.
- by rewrite nth_drop addn0.
Qed.

(* [eps5 <> 0] forces one of the four "small term" cases (paper omitted; old  *)
(* draft Theorem 10 / doc/thm7-eps5.md). Contrapositive of                    *)
(* [eps5_zero_all_big]: if none of the four smallness bounds holds we are     *)
(* all-big, forcing [eps5 = 0].                                               *)
Lemma eps5nz_forces_small x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3] in
  sumR (vseb e) - sumR (vsebK 3 e) <> 0 ->
  [\/ Rabs y2 < u * u, Rabs x2 < u * u, Rabs c < 4 * (u * u) | Rabs z3 < 4 * (u
    * u)].
Proof.
move=> Hc Nx Ny bb c z3 e HE5.
case: (Rlt_le_dec (Rabs y2) (u * u)) => Hy2; first by apply: Or41.
case: (Rlt_le_dec (Rabs x2) (u * u)) => Hx2; first by apply: Or42.
case: (Rlt_le_dec (Rabs c) (4 * (u * u))) => Hcb; first by apply: Or43.
case: (Rlt_le_dec (Rabs z3) (4 * (u * u))) => Hz3b; first by apply: Or44.
by case: HE5; apply: (eps5_zero_all_big Hc Nx Ny).
Qed.

(* In any of the four small-term cases the numerator [x*y - sumR e] (=        *)
(* [eps0+.. +eps4]) drops from [28u^3-11.9u^4] to [26u^3-11.9u^4]: one        *)
(* [eps_i] halves ([eps1]/[eps2] via [|x0 y2|]/[|x2 y0|] < 2u^2, [eps4] via   *)
(* [|c|<4u^2] so [|b2+x1 y1|<8u^2->... ], [eps3] via [|z3|<4u^2]). Reuses the *)
(* [eps_i] bounds.                                                            *)
Lemma eps5nz_numerator x0 x1 x2 y0 y1 y2 :
  tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let c := RND (nth 0 bb 2 + x1 * y1) in
  let z3 := RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
             + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)) in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; c; z3] in
  [\/ Rabs y2 < u * u, Rabs x2 < u * u, Rabs c < 4 * (u * u) | Rabs z3 < 4 * (u
    * u)] ->
  Rabs ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e)
    <= 26 * (u * u * u) - 119 / 10 * (u * u * u * u).
Proof.
move=> Nx Ny bb c z3 e Hdisj.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu64 := u_le_64.
have [[Fx0 Fx1 Fx2] Hx0l Hx0r Hx1o Hx2o] := Nx.
have [[Fy0 Fy1 Fy2] Hy0l Hy0r Hy1o Hy2o] := Ny.
set z10m := RND (x1 * y0 - RND (x1 * y0)).
set z01m := RND (x0 * y1 - RND (x0 * y1)).
set z31 := RND (z10m + x0 * y2).
set z32 := RND (z01m + x2 * y0).
have Hz10m : Rabs z10m <= 2 * (u * u).
  rewrite /z10m round_generic; first by apply: (z10m_bound Nx Ny).
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m : Rabs z01m <= 2 * (u * u).
  rewrite /z01m round_generic; first by apply: (z01m_bound Nx Ny).
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := x0y2_bound Nx Ny.
have Hx2y0 := x2y0_bound Nx Ny.
have Hx1y1 := x1y1_bound Nx Ny.
have Hz31 := z31_bound Hz10m Hx0y2.
have Hz32 := z32_bound Hz01m Hx2y0.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx Ny).
have Hdecomp := @sumR_e_decomp x0 x1 x2 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) z01m (RND (x1 * y0)) z10m bb c z31 z32 z3
  Fx0 Fx1 Fy0 Fy1 erefl erefl erefl erefl erefl erefl erefl erefl.
have -> : (x0 + x1 + x2) * (y0 + y1 + y2) - sumR e
    = (x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32) + (z31 + z32 - z3)
      + (nth 0 bb 2 + x1 * y1 - c) by exact: Hdecomp.
have He0 := eps0_bound Nx Ny.
have He2 := eps2_bound Hz01m Hx2y0.
have He3 := eps3_bound Hz31 Hz32.
have He4 := eps4_bound Hb2 Hx1y1.
have He1 := eps1_bound Hz10m Hx0y2.
have T1 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32) + (z31 + z32 - z3)) (nth 0 bb 2 + x1 * y1 - c).
have T2 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31)
      + (z01m + x2 * y0 - z32)) (z31 + z32 - z3).
have T3 := Rabs_triang ((x1 * y2 + x2 * y1 + x2 * y2) + (z10m + x0 * y2 - z31))
      (z01m + x2 * y0 - z32).
have T4 := Rabs_triang (x1 * y2 + x2 * y1 + x2 * y2) (z10m + x0 * y2 - z31).
rewrite -/z31 in He1.
rewrite -/z32 in He2.
rewrite -/z31 -/z32 -/z3 in He3.
have Hp2m3 : pow (2 - 3 * p) = 4 * (u * u * u).
  rewrite (_ : (2 - 3 * p = 2 + - (3 * p))%Z); last by lia.
  by rewrite bpow_plus u3_pow /= /Z.pow_pos /=; lra.
have Hred : forall t : R, Rabs (RND t) < 4 * (u * u) ->
    Rabs (t - RND t) <= 2 * (u * u * u).
  move=> t Hlt.
  have Herr := @error_le_half_ulp_round beta (FLX_exp p)
    (FLX_exp_valid p) (FLX_exp_monotone p) choice t.
  have Hulp : ulp (RND t) <= 4 * (u * u * u).
    case: (Req_dec (RND t) 0) => [Hz|Hn0].
      rewrite Hz ulp_FLX_0; clear -Hu0; nra.
    rewrite ulp_neq_0 //.
    apply: (Rle_trans _ (pow (2 - 3 * p))); last by rewrite Hp2m3; apply:
      Rle_refl.
    have Hmag : (mag beta (RND t) <= 2 - 2 * p)%Z.
      by apply: mag_le_bpow; [exact: Hn0 | rewrite pow_2m2p; exact: Hlt].
    apply: bpow_le.
    have Hcx : cexp (RND t) = (mag beta (RND t) - p)%Z
      by rewrite /cexp /fexp /FLX_exp.
    rewrite Hcx; lia.
  have Hpp : Prec_gt_0 p by rewrite /Prec_gt_0; lia.
  move: (Herr Hpp); rewrite Rabs_minus_sym; lra.
case: Hdisj => [Hy2 | Hx2 | Hcs | Hz3s].
- have He1' : Rabs (z10m + x0 * y2 - z31) <= 2 * (u * u * u).
    have Hw : Rabs (z10m + x0 * y2) < pow (2 - 2 * p).
      rewrite pow_2m2p.
      have Hxy : Rabs (x0 * y2) < 2 * (u * u).
        rewrite Rabs_mult (Rabs_pos_eq x0); last lra.
        clear -Hx0l Hx0r Hy2 Hu0; have := Rabs_pos y2; nra.
      have H3 := Rabs_triang z10m (x0 * y2); clear -Hz10m Hxy H3; lra.
    have Herr := round_err_le Hw.
    move: Herr; rewrite (_ : (2 - 2 * p - p = 2 - 3 * p)%Z) ?Hp2m3 -/z31;
      last by lia.
    lra.
  rewrite -/c in He4; lra.
- have He2' : Rabs (z01m + x2 * y0 - z32) <= 2 * (u * u * u).
    have Hw : Rabs (z01m + x2 * y0) < pow (2 - 2 * p).
      rewrite pow_2m2p.
      have Hxy : Rabs (x2 * y0) < 2 * (u * u).
        rewrite Rabs_mult (Rabs_pos_eq y0); last lra.
        clear -Hx2 Hy0l Hy0r Hu0; have := Rabs_pos x2; nra.
      have H3 := Rabs_triang z01m (x2 * y0); clear -Hz01m Hxy H3; lra.
    have Herr := round_err_le Hw.
    move: Herr; rewrite (_ : (2 - 2 * p - p = 2 - 3 * p)%Z) ?Hp2m3 -/z32;
      last by lia.
    lra.
  rewrite -/c in He4; lra.
- have He4' : Rabs (nth 0 bb 2 + x1 * y1 - c) <= 2 * (u * u * u).
    by apply: (Hred (nth 0 bb 2 + x1 * y1)); rewrite -/c.
  lra.
- have He3' : Rabs (z31 + z32 - z3) <= 2 * (u * u * u).
    by apply: (Hred (z31 + z32)); rewrite -/z3.
  rewrite -/c in He4; lra.
Qed.

(* The [eps5 <> 0] case of the error bound (paper Section 6.2, part 2: "the   *)
(* error is shown not too large when eps5 <> 0", details OMITTED in the       *)
(* paper). The naive triangle [|eps0..4| + |eps5|] over-counts here (it       *)
(* reaches ~30u^3), so a tighter analysis of the mutually-exclusive tightness *)
(* of the sources is needed. Stated over the algorithm context; see           *)
(* [doc/thm7.md] Section 6.2 part 2 and [doc/old-triplewors.pdf] for the      *)
(* missing steps.                                                             *)
Lemma ThreeProd_error_eps5nz x0 x1 x2 y0 y1 y2 :
  ties_to_even choice -> tw_norm x0 x1 x2 -> tw_norm y0 y1 y2 ->
  let bb := vecSum
    [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 * y0)] in
  let e := vecSum
    [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1; RND (nth 0 bb 2 + x1 * y1);
        RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
           + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))] in
  sumR (vseb e) - sumR (vsebK 3 e) <> 0 ->
  Rabs (sumR (vsebK 3 e) - (x0 + x1 + x2) * (y0 + y1 + y2)) <=
     (28 * (u * u * u) + 107 * (u * u * u * u)) *
       Rabs ((x0 + x1 + x2) * (y0 + y1 + y2)).
Proof.
move=> Hc Nx Ny bb e HE5.
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
have Fno : Fnonoverlap e by rewrite /e /bb; apply: (inner_Fnonoverlap Hc Nx Ny).
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
have [Pno Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Fvse : {in vseb e, forall z, format z}
  by apply: (@format_vseb p Hp2 choice e Fe).
have Hdisj := eps5nz_forces_small Hc Nx Ny HE5.
have Hnum := eps5nz_numerator Nx Ny Hdisj.
have Hnum2 : Rabs ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e)
    <= 26 * (u * u * u) - 119 / 10 * (u * u * u * u) by exact: Hnum.
have Hs5 := eps5_bound Pno Fvse u_le_64.
have Hsm : Rabs (sumR (vseb e))
    <= Rabs ((x0 + x1 + x2) * (y0 + y1 + y2))
       + (26 * (u * u * u) - 119 / 10 * (u * u * u * u)).
  rewrite Hsumeq.
  have H1 : sumR e = (x0 + x1 + x2) * (y0 + y1 + y2)
      + (sumR e - (x0 + x1 + x2) * (y0 + y1 + y2)) by ring.
  rewrite {1}H1; apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
  have -> : Rabs (sumR e - (x0 + x1 + x2) * (y0 + y1 + y2))
      = Rabs ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e) by rewrite
        Rabs_minus_sym.
  move: Hnum2; lra.
have Hident : sumR (vsebK 3 e) - (x0 + x1 + x2) * (y0 + y1 + y2)
    = -((sumR (vseb e) - sumR (vsebK 3 e))
        + ((x0 + x1 + x2) * (y0 + y1 + y2) - sumR e)).
  by rewrite Hsumeq; ring.
rewrite Hident Rabs_Ropp.
apply: (error_assembly_eps5 (sm := sumR (vseb e))).
- exact: Hnum2.
- exact: Hs5.
- exact: Hsm.
- exact: (xy_ge Nx Ny).
Qed.

(* Section 6.2, part 2 -- relative error [<= 28u^3 + 107u^4] (normalised).    *)
(* [ThreeProd_norm_eq] gives [TWval (ThreeProd x y) = sumR (vsebK 3 e)]; the  *)
(* error identity [sumR_e_decomp] plus [vseb_sum] rewrites the numerator as   *)
(* [eps0+..+eps4] (when [eps5 = 0]) or delegates to [ThreeProd_error_eps5nz]. *)
(* [eps5 = 0]: [eps04_sum] bounds the numerator by [28u^3-11.9u^4], closed    *)
(* over [x*y >= 1 - 4u] ([xy_ge]) by [error_assembly].                        *)
Lemma ThreeProd_error_norm x y :
  ties_to_even choice -> tw_normP x -> tw_normP y ->
  Rabs (TWval (ThreeProd x y) - TWval x * TWval y) <=
     (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Nx Ny.
case: x Nx => x0 x1 x2 Nx.
case: y Ny => y0 y1 y2 Ny.
have Nx' : tw_norm x0 x1 x2 by exact: Nx.
have Ny' : tw_norm y0 y1 y2 by exact: Ny.
rewrite (ThreeProd_norm_eq Hc Nx' Ny').
set bb := vecSum [:: RND (x0 * y0 - RND (x0 * y0)); RND (x0 * y1); RND (x1 *
  y0)].
set e := vecSum [:: RND (x0 * y0); nth 0 bb 0; nth 0 bb 1;
  RND (nth 0 bb 2 + x1 * y1);
  RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
     + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))].
have HTW3 : TWval (TWR (nth 0 (vseb e) 0) (nth 0 (vseb e) 1) (nth 0 (vseb e) 2))
    = sumR (vsebK 3 e).
  rewrite /TWval /vsebK.
  case E : (vseb e) => [|v0 [|v1 [|v2 r]]] /=.
  - ring.
  - ring.
  - ring.
  - rewrite take0 /=; ring.
rewrite HTW3.
have HXY : TWval (TWR x0 x1 x2) * TWval (TWR y0 y1 y2)
    = (x0 + x1 + x2) * (y0 + y1 + y2) by rewrite /TWval.
rewrite HXY.
case: (Req_dec (sumR (vseb e) - sumR (vsebK 3 e)) 0) => [HE5z|HE5n]; last first.
  by apply: (ThreeProd_error_eps5nz Hc Nx' Ny' HE5n).
have [[Fx0 Fx1 Fx2] _ _ _ _] := Nx'.
have [[Fy0 Fy1 Fy2] _ _ _ _] := Ny'.
have Hz10m : Rabs (RND (x1 * y0 - RND (x1 * y0))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z10m_bound Nx' Ny').
  rewrite (_ : x1 * y0 - RND (x1 * y0) = -(RND (x1 * y0) - x1 * y0)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hz01m : Rabs (RND (x0 * y1 - RND (x0 * y1))) <= 2 * (u * u).
  rewrite round_generic; first by apply: (z01m_bound Nx' Ny').
  rewrite (_ : x0 * y1 - RND (x0 * y1) = -(RND (x0 * y1) - x0 * y1)); last by
    ring.
  by apply: generic_format_opp; exact: format_err_mul.
have Hx0y2 := x0y2_bound Nx' Ny'.
have Hx2y0 := x2y0_bound Nx' Ny'.
have Hx1y1 := x1y1_bound Nx' Ny'.
have Hz31 := z31_bound Hz10m Hx0y2.
have Hz32 := z32_bound Hz01m Hx2y0.
have Hb2 : Rabs (nth 0 bb 2) <= 4 * (u * u).
  have Hb2eq : nth 0 bb 2 = RND (x0 * y1) + RND (x1 * y0)
      - RND (RND (x0 * y1) + RND (x1 * y0)).
    rewrite /bb (vecSum3 (generic_format_round _ _ _ _)
      (generic_format_round _ _ _ _) (generic_format_round _ _ _ _)) /=; ring.
  by rewrite Hb2eq; apply: (b2_bound Nx' Ny').
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
have Fno : Fnonoverlap e by rewrite /e /bb; apply: (inner_Fnonoverlap Hc Nx'
  Ny').
have Hle : (Z.of_nat (size e) <= p + 1)%Z by rewrite Hsz5; lia.
have [_ Hsumeq] := @vseb_Pnonoverlap p Hp2 choice choice_sym e Hle Fe Fno.
have Hdecomp := @sumR_e_decomp x0 x1 x2 y0 y1 y2
  (RND (x0 * y0)) (RND (x0 * y0 - RND (x0 * y0)))
  (RND (x0 * y1)) (RND (x0 * y1 - RND (x0 * y1)))
  (RND (x1 * y0)) (RND (x1 * y0 - RND (x1 * y0)))
  bb
  (RND (nth 0 bb 2 + x1 * y1))
  (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2))
  (RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0))
  (RND (RND (RND (x1 * y0 - RND (x1 * y0)) + x0 * y2)
      + RND (RND (x0 * y1 - RND (x0 * y1)) + x2 * y0)))
  Fx0 Fx1 Fy0 Fy1 erefl erefl erefl erefl erefl erefl erefl erefl.
have Hk3 : sumR (vsebK 3 e) = sumR e by rewrite -Hsumeq; lra.
rewrite Hk3.
apply: error_assembly; last by apply: (xy_ge Nx' Ny').
rewrite Rabs_minus_sym /e Hdecomp.
apply: eps04_sum.
- exact: (eps0_bound Nx' Ny').
- exact: (eps1_bound Hz10m Hx0y2).
- exact: (eps2_bound Hz01m Hx2y0).
- exact: (eps3_bound Hz31 Hz32).
- exact: (eps4_bound Hb2 Hx1y1).
Qed.

(* ===========================================================================*)
(*  Theorem 7, part 1: [ThreeProd x y] is a triple-word number (p >= 6).      *)
(*                                                                            *)
(* The general statement reduces to the normalised one [ThreeProd_isTW_norm]  *)
(* (paper WLOG [1 <= x0, y0 < 2]) using scale-invariance [ThreeProd_scale] /  *)
(* [isTW_scale] and sign-invariance [ThreeProd_opp]/[_opp_r] / [isTW_opp]; a  *)
(* zero factor is the degenerate [ThreeProd_0l]/[_0r] case.                   *)
(* ===========================================================================*)
Lemma ThreeProd_isTW x y :
  ties_to_even choice ->
  isTW x -> isTW y -> isTW (ThreeProd x y).
Proof.
move=> Hc Hx Hy.
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  by rewrite (isTW_zero_lead Hx x0z) ThreeProd_0l; exact: isTW_TWR000.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  by rewrite (isTW_zero_lead Hy y0z) ThreeProd_0r; exact: isTW_TWR000.
have [cx _ [Hxp Hxn]] := isTW_normalize Hx x0n.
have [cy _ [Hyp Hyn]] := isTW_normalize Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
case: Hxsg => Hxs; case: Hysg => Hys.
- rewrite -(isTW_scale (cx + cy)) -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxp | apply: Hyp].
- rewrite -(isTW_opp (ThreeProd x y)) -(isTW_scale (cx + cy)).
  rewrite -ThreeProd_opp_r -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxp | apply: Hyn].
- rewrite -(isTW_opp (ThreeProd x y)) -(isTW_scale (cx + cy)).
  rewrite -ThreeProd_opp -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxn | apply: Hyp].
- rewrite -(isTW_scale (cx + cy)).
  have <- : ThreeProd (negTW x) (negTW y) = ThreeProd x y.
    by rewrite ThreeProd_opp ThreeProd_opp_r negTW_id.
  rewrite -ThreeProd_scale.
  by apply: ThreeProd_isTW_norm => //; [apply: Hxn | apply: Hyn].
Qed.

(* A relative-error bound is invariant under a common [pow s] scaling.        *)
Lemma error_scale_transfer (s : Z) (r rxy C : R) :
  Rabs (r * pow s - rxy * pow s) <= C * Rabs (rxy * pow s) ->
  Rabs (r - rxy) <= C * Rabs rxy.
Proof.
have ps : 0 < pow s by apply: bpow_gt_0.
rewrite -Rmult_minus_distr_r !Rabs_mult (Rabs_pos_eq (pow s)); last by lra.
rewrite -Rmult_assoc => H.
by apply: (Rmult_le_reg_r (pow s) _ _ ps).
Qed.

(* ===========================================================================*)
(*  Theorem 7, part 2: relative error of [ThreeProd] is [<= 28u^3+107u^4].    *)
(*  Proof plan (paper Section 6.2, part 2; see doc/thm7.md): the six error    *)
(*  sources [eps0..eps5] (the last is the Theorem-3 truncation bound at       *)
(*  k = 3), divided by [x*y >= 1 - 4u].                                       *)
(* ===========================================================================*)
Lemma ThreeProd_error x y :
  ties_to_even choice ->
  isTW x -> isTW y ->
  Rabs (TWval (ThreeProd x y) - TWval x * TWval y) <=
     (28 * (u * u * u) + 107 * (u * u * u * u)) * Rabs (TWval x * TWval y).
Proof.
move=> Hc Hx Hy.
set C := (28 * _ + _).
case: (Req_dec (tw0 x) 0) => [x0z | x0n].
  rewrite (isTW_zero_lead Hx x0z) ThreeProd_0l.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_l Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
case: (Req_dec (tw0 y) 0) => [y0z | y0n].
  rewrite (isTW_zero_lead Hy y0z) ThreeProd_0r.
  have -> : TWval (TWR 0 0 0) = 0 by rewrite /TWval; ring.
  by rewrite Rmult_0_r Rminus_0_r Rabs_R0 Rmult_0_r; apply: Rle_refl.
have [cx _ [Hxp Hxn]] := isTW_normalize Hx x0n.
have [cy _ [Hyp Hyn]] := isTW_normalize Hy y0n.
have Hxsg : 0 < tw0 x \/ tw0 x < 0 by lra.
have Hysg : 0 < tw0 y \/ tw0 y < 0 by lra.
apply: (@error_scale_transfer (cx + cy)%Z (TWval (ThreeProd x y))
                              (TWval x * TWval y) C).
case: Hxsg => Hxs; case: Hysg => Hys.
- have Hn := ThreeProd_error_norm Hc (Hxp Hxs) (Hyp Hys).
  rewrite ThreeProd_scale !TWval_scale in Hn.
  rewrite (_ : TWval x * pow cx * (TWval y * pow cy) = TWval x * TWval y * pow
    (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
- have Hn := ThreeProd_error_norm Hc (Hxp Hxs) (Hyn Hys).
  rewrite ThreeProd_scale ThreeProd_opp_r !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : TWval x * pow cx * (- TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProd x y) * pow (cx + cy) - - (TWval x * TWval y * pow
    (cx + cy)) = - (TWval (ThreeProd x y) * pow (cx + cy) - TWval x * TWval y *
    pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProd_error_norm Hc (Hxn Hxs) (Hyp Hys).
  rewrite ThreeProd_scale ThreeProd_opp !TWval_scale !TWval_opp in Hn.
  move: Hn.
  have E : - TWval x * pow cx * (TWval y * pow cy) = - (TWval x * TWval y * pow
    (cx + cy)) by rewrite bpow_plus; ring.
  rewrite E.
  have E2 : - TWval (ThreeProd x y) * pow (cx + cy) - - (TWval x * TWval y * pow
    (cx + cy)) = - (TWval (ThreeProd x y) * pow (cx + cy) - TWval x * TWval y *
    pow (cx + cy)) by ring.
  by rewrite E2 !Rabs_Ropp.
- have Hn := ThreeProd_error_norm Hc (Hxn Hxs) (Hyn Hys).
  have Hxy : ThreeProd (negTW x) (negTW y) = ThreeProd x y.
    by rewrite ThreeProd_opp ThreeProd_opp_r negTW_id.
  rewrite ThreeProd_scale Hxy !TWval_scale !TWval_opp in Hn.
  rewrite (_ : - TWval x * pow cx * (- TWval y * pow cy) = TWval x * TWval y *
    pow (cx + cy)) in Hn; last by rewrite bpow_plus; ring.
  exact Hn.
Qed.

End SecThreeProd.
