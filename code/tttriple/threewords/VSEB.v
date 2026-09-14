(* ---------------------------------------------------------------------------*)
(* Algorithm 5 (VecSumErrBranch, VSEB) and the paper's Theorem 2 (its output  *)
(* is P-nonoverlapping).  A general round-to-nearest building block, generic  *)
(* over the precision [p] alone -- FLX (binary64 is fixed only in            *)
(* only when instantiated ([p = 53] = binary64)); built on [TwoSum] and [Nonoverlap].                 *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim TwoSum.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecVSEB.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.

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
Local Notation ulp := (ulp beta fexp).
Local Notation uls := (uls p).
Local Notation TwoSum_correct_RN :=
  (@TwoSum_correct p choice Hp2 choice_sym).

Local Notation TwoSum := (TwoSum p choice).
Local Notation TwoSum_hi := (TwoSum_hi p choice).
Local Notation formatDWR := (formatDWR p).
Local Notation magnitudeDWR := (magnitudeDWR p).
Local Notation format_TwoSum := (format_TwoSum Hp2 choice).
Local Notation TwoSum_correct_loc :=
  (TwoSum_correct_loc Hp2 choice_sym).
Local Notation dwh_TwoSum_r0 := (@dwh_TwoSum_r0 p choice).
Local Notation dwl_TwoSum_r0 := 
  (dwl_TwoSum_r0 Hp2 choice_sym).
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
Local Notation Fnonoverlap_imm := (Fnonoverlap_imm Hp2).
Local Notation Fnonoverlap_TwoSum_merge :=
  (Fnonoverlap_TwoSum_merge Hp2 choice_sym).
Local Notation Fnonoverlap_TwoSum_err :=
  (Fnonoverlap_TwoSum_err Hp2 choice_sym).

(* ===========================================================================*)
(*  Algorithm 5: VecSumErrBranch (VSEB)                                       *)
(*  Returns the full normalised output; zero error terms are dropped.         *)
(* ===========================================================================*)
Fixpoint vsebAux (eps : R) (l : seq R) : seq R :=
  match l with
  | [::]       => [:: eps]
  | [:: elast] => let: DWR y0 y1 := TwoSum eps elast in [:: y0; y1]
  | e :: l'    => let: DWR r et := TwoSum eps e in
                  if Req_EM_T et 0 then vsebAux r l'
                  else r :: vsebAux et l'
  end.

Lemma format_vsebAux e l :
  format e -> {in l, forall z, format z} -> 
   {in vsebAux e l, forall z, format z}.
Proof.
move=> eF lF /= z.
elim: l z e eF lF => /= [z e eF lF|a [| b l] IH z e eF lF].
- by rewrite !inE => /eqP->.
- by rewrite !inE => /orP[/eqP->|/eqP->]; apply: generic_format_round.
case: Req_EM_T => HH.
  apply: IH; first by apply: generic_format_round.
  by move=> z1 z1Ibl; apply: lF; rewrite inE z1Ibl orbT.
rewrite inE => /orP[/eqP->|]; first by apply: generic_format_round.
apply: IH; first by apply: generic_format_round.
by move=> z1 z1Ibl; apply: lF; rewrite inE z1Ibl orbT.
Qed.

Definition vseb (l : seq R) : seq R :=
  if l is e0 :: l' then vsebAux e0 l' else [::].

Lemma format_vseb l :
  {in l, forall z, format z} -> {in vseb l, forall z, format z}.
Proof.
case: l => //= a l alF; apply: format_vsebAux => [|z zIl].
  by apply: alF; rewrite inE eqxx.
by apply: alF; rewrite inE zIl orbT.
Qed.

(* VSEB(k): keep only the first k terms (the dropped tail is the error).      *)
Definition vsebK (k : nat) (l : seq R) : seq R := take k (vseb l).

Lemma format_vsebK k l :
  {in l, forall z, format z} -> {in vsebK k l, forall z, format z}.
Proof.
move=> lF /= z /mem_take zIl.
by apply: format_vseb lF _ zIl.
Qed.

(* Two definitional unfoldings of [vsebAux] (by reflexivity), mirroring       *)
(* [vecSumAux_cons]: they expose [TwoSum eps e] so the following [case] can   *)
(* capture it in the goal, keeping the low words as the very variables that   *)
(* [TwoSum_correct_loc] talks about (otherwise [simpl] re-expands them to     *)
(* [RND ...] and the correctness fact no longer applies).                     *)
Lemma vsebAux_1 eps e :
  vsebAux eps [:: e] = let: DWR y0 y1 := TwoSum eps e in [:: y0; y1].
Proof. by []. Qed.

Lemma vsebAux_consS eps e e2 l :
  vsebAux eps [:: e, e2 & l] =
  let: DWR r et := TwoSum eps e in
  if Req_EM_T et 0 then vsebAux r (e2 :: l) else r :: vsebAux et (e2 :: l).
Proof. by []. Qed.

(* VSEB is error-free: [vsebAux] preserves the exact sum, prefix [eps]        *)
(* included.  Each step is a [TwoSum] (exact by [TwoSum_correct_loc]); whether*)
(* the error [et] is dropped ([et = 0], so [r = eps + e]) or emitted, the sum *)
(* [eps + sumR l] is preserved.                                               *)
Lemma vsebAux_sum eps l :
  format eps -> {in l, forall z, format z} ->
  sumR (vsebAux eps l) = eps + sumR l.
Proof.
elim: l eps => [|e l IH] eps epsF lF.
  by rewrite /=; lra.
have eF : format e by apply: lF; rewrite inE eqxx.
case: l IH lF => [|e2 l'] IH lF.
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  have Cc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e
    by exact: TwoSum_correct_loc epsF eF.
  rewrite E1 /= in Cc.
  by rewrite /=; lra.
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Cc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e
  by exact: TwoSum_correct_loc epsF eF.
have [rF etF] : format (dwh (TwoSum eps e)) /\ format (dwl (TwoSum eps e))
  by exact: format_TwoSum epsF eF.
rewrite E1 /= in Cc rF etF.
have l'F : {in e2 :: l', forall z, format z}.
  by move=> z zIl; apply: lF; rewrite inE zIl orbT.
case: Req_EM_T => [et0|etn0].
  by rewrite (IH r rF l'F) /=; lra.
by rewrite /= (IH et etF l'F) /=; lra.
Qed.

(* VSEB preserves the exact sum (Theorem 2, sum part): [sumR(vseb l)=sumR l]. *)
Lemma vseb_sum l :
  {in l, forall z, format z} -> sumR (vseb l) = sumR l.
Proof.
case: l => [_|e0 l' e0l'F]; first by rewrite /vseb.
have e0F : format e0 by apply: e0l'F; rewrite inE eqxx.
have l'F : {in l', forall z, format z}.
  by move=> z zIl; apply: e0l'F; rewrite inE zIl orbT.
by rewrite /vseb /= (vsebAux_sum e0F l'F) /=.
Qed.

(* Theorem 2 (VSEB), stated as in the paper: if [e] is F-nonoverlapping (with *)
(* float terms) and the precision is large enough, [size e <= p + 1] (i.e. the*)
(* paper's [p >= n - 1] with [n = size e]; here [n = 6], [p = 53]), then      *)
(* [vseb e] is P-nonoverlapping (Priest, Def. 1) AND has the same exact sum.  *)
(* Informal proof (paper Thm 2): [vseb] walks the sequence with a running     *)
(* remainder, emitting a term only when the [2Sum] error is nonzero (thereby  *)
(* dropping interleaving zeros); it is error-free, whence the sum is          *)
(* preserved. The F-nonoverlap bound [|e_{i+1}| <= 1/2 uls(e_i)] makes every  *)
(* step a Fast2Sum with no rounding, so consecutive emitted terms satisfy the *)
(* STRICT [|y_{i+1}| < ulp(y_i)]; the [size e <= p + 1] hypothesis rules out  *)
(* the carry that could turn [<] into [=].                                    *)
(* Reusable step lemma: a nonzero 2Sum error [et = dwl(2Sum eps e)] is at     *)
(* least as coarse as [e] ([uls e <= uls et], by [TwoSum_err_uls_ge]), so     *)
(* prepending [et] to the tail [l] keeps F-nonoverlap.  This re-establishes   *)
(* the VSEB invariant when a term is emitted.                                 *)
(* Zero absorption - the formal content of the paper's "WLOG the list has no" *)
(* "zeros". A zero next term is an exact [2Sum] ([dwh = eps], [dwl = 0]), so  *)
(* [vsebAux] carries the remainder on and emits nothing: it silently drops the*)
(* zero.  Hence the VSEB analysis may assume a zero-free list.                *)
Lemma vsebAux_cons0 eps e l :
  format eps -> vsebAux eps (0 :: e :: l) = vsebAux eps (e :: l).
Proof.
move=> Feps; rewrite vsebAux_consS; case E : (TwoSum eps 0) => [r et].
have -> : et = 0 by have := dwl_TwoSum_r0 Feps; rewrite E.
have -> : r = eps by have := dwh_TwoSum_r0 Feps; rewrite E.
by case: (Req_EM_T 0 0) => [_|H] //; case: (H erefl).
Qed.

(* Strengthened block bound: for ANY float [B] with [|eps| + sum|tail| <= B], *)
(* the emitted head satisfies [|head| <= B].  The exact merges ([et = 0], so  *)
(* [r = eps + e]) recurse; the rounded emits/terminal use                     *)
(* [abs_round_le_generic] -- a float [B] bounding the exact value bounds its  *)
(* rounding too.  This is the engine behind the paper's block estimate.       *)
Lemma vsebAux_head_leB B eps l :
  format eps -> {in l, forall z, format z} -> format B ->
  Rabs eps + sumRabs l <= B ->
  Rabs (nth 0 (vsebAux eps l) 0) <= B.
Proof.
elim: l eps => [|e l IH] eps epsF lF FB Hb; first by move: Hb; rewrite /=; lra.
have eF : format e by apply: lF; rewrite inE eqxx.
have Hepse : Rabs (eps + e) <= B.
  by apply: Rle_trans Hb; rewrite /=; have := sumRabs_ge0 l; split_Rabs; lra.
have Hr : dwh (TwoSum eps e) = RND (eps + e) by rewrite TwoSum_hi.
case: l IH lF Hb => [|e2 l'] IH lF Hb.
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1] /=.
  have Hy0 : y0 = RND (eps + e) by move: Hr; rewrite E1.
  by rewrite Hy0; apply: abs_round_le_generic.
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Hrr : r = RND (eps + e) by move: Hr; rewrite E1.
case: Req_EM_T => [et0|etn0]; last first.
  by rewrite /= Hrr; apply: abs_round_le_generic.
have re : r = eps + e.
  have Cc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e
    by exact: TwoSum_correct_loc epsF eF.
  by move: Cc; rewrite E1 /= et0 Rplus_0_r.
apply: IH.
- by rewrite Hrr; apply: generic_format_round.
- by move=> z zi; apply: lF; rewrite inE zi orbT.
- exact: FB.
by rewrite re; apply: Rle_trans Hb; rewrite /=; split_Rabs; lra.
Qed.

(* Reusable radix-2 power facts: [/2 = pow (-1)] and [(/2)^n = pow (-n)].     *)
Lemma pow_N1 : / 2 = pow (-1).
Proof. by rewrite /=; lra. Qed.

Lemma pow_halfN (n : nat) : (/ 2) ^ n = pow (- Z.of_nat n).
Proof.
elim: n => [|n IH]; first by [].
rewrite -tech_pow_Rmult IH pow_N1 -bpow_plus Nat2Z.inj_succ.
by congr bpow; lia.
Qed.

(* Reusable block bound (paper Thm 2): the first term emitted by VSEB from a  *)
(* nonzero remainder [eps] over an F-nonoverlap tail has magnitude [< 2|eps|].*)
(* Block bound, stated on the MASS of the tail.  This is all the estimate     *)
(* really needs: the F-nonoverlap hypothesis of [vsebAux_head_lt] below is    *)
(* used ONLY to bound [sumRabs l] by [uls eps] geometrically                  *)
(* ([Fnonoverlap_aux_sumRabs]), never term by term.  Splitting it out gives a *)
(* reusable entry point for callers whose tail is NOT F-nonoverlapping -- in  *)
(* particular a [VecSum] output, which need not be (see [CEThm6.v] on main).  *)
Lemma vsebAux_head_lt_mass eps l :
  (Z.of_nat (size l).+2 <= p + 1)%Z ->
  format eps -> {in l, forall z, format z} -> eps <> 0 ->
  sumRabs l <= uls eps * (1 - (/ 2) ^ (size l)) ->
  Rabs (nth 0 (vsebAux eps l) 0) < 2 * Rabs eps.
Proof.
move=> Hsz epsF lF epsn0 Hsum.
have Hu0 : 0 < uls eps by apply: uls_gt_0.
have Hae : uls eps <= Rabs eps by apply: uls_le_abs.
have He0 : 0 < Rabs eps by apply: Rabs_pos_lt.
have Hd0 : 0 < (/ 2) ^ (size l) by apply: pow_lt; lra.
have HsumLt : sumRabs l < uls eps by nra.
have Hg : uls eps = pow (cexp eps + Z.of_nat (trZ (Ztrunc (mant eps)))).
  by rewrite /uls; case: Req_bool_spec => // eps0; case: (epsn0 eps0).
set g := (cexp eps + Z.of_nat (trZ (Ztrunc (mant eps))))%Z.
have Hhalf : uls eps * (/ 2) ^ (size l) = pow (g - Z.of_nat (size l)).
  by rewrite pow_halfN Hg -bpow_plus; congr bpow; lia.
(* [|eps|]'s integer mantissa is bounded ([< 2^p]), giving the block bound.   *)
have HmB : (Z.abs (Ztrunc (mant eps)) < beta ^ p)%Z.
  apply: lt_IZR; rewrite abs_IZR -scaled_mantissa_generic // IZR_Zpower;
    last lia.
  apply: Rlt_le_trans (_ : pow (mag beta eps - cexp eps) <= _)%R.
    exact: scaled_mantissa_lt_bpow.
  by apply: bpow_le; rewrite /cexp /FLX_exp; lia.
have Heps : Rabs eps = IZR (Z.abs (Ztrunc (mant eps))) * pow (cexp eps).
  by rewrite {1}epsF /F2R /= Rabs_mult -abs_IZR Rabs_pow.
have Hcu : pow (cexp eps) <= uls eps.
  by rewrite Hg; apply: bpow_le; rewrite /g;
     have := Zle_0_nat (trZ (Ztrunc (mant eps))); lia.
suff [B [FB HVB HBlt]] :
    exists B, [/\ format B, Rabs eps + sumRabs l <= B & B < 2 * Rabs eps].
  by apply: Rle_lt_trans (vsebAux_head_leB epsF lF FB HVB) HBlt.
have [HM|HM] := Rle_lt_or_eq_dec _ _ Hae.
- (* [uls eps < Rabs eps] (M > 1): [B = |eps| + uls eps] is format, in range. *)
  exists (Rabs eps + uls eps).
  have Huim : is_imul (uls eps) (pow g) by rewrite Hg; exists 1%Z;
    rewrite Rmult_1_l.
  have Heim : is_imul (Rabs eps) (pow g).
    have Him : is_imul eps (pow g) by rewrite -Hg; exact: uls_imul epsF.
    case: (Rle_lt_dec 0 eps) => He.
      by rewrite Rabs_pos_eq.
    by rewrite Rabs_left //; apply: is_imul_opp.
  split.
  + apply: (imul_format Hp2 (e := g) (b := Rabs eps + uls eps)) => //.
    * by apply: is_imul_add.
    * by rewrite Rabs_pos_eq; lra.
    rewrite bpow_plus.
    have Hub : Rabs eps <= (pow p - 1) * uls eps.
      rewrite Heps.
      apply: Rle_trans (_ : (pow p - 1) * pow (cexp eps) <= _).
        apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
        have -> : pow p - 1 = IZR (beta ^ p - 1).
          by rewrite minus_IZR IZR_Zpower //; lia.
        by apply: IZR_le; lia.
      apply: Rmult_le_compat_l; last exact: Hcu.
      by rewrite -(pow0E beta); have := bpow_le beta 0 p ltac:(lia); lra.
    have -> : pow g = uls eps by rewrite Hg.
    nra.
  + by lra.
  + by lra.
- (* [uls eps = Rabs eps] (M = 1): [2|eps| = pow (g+1)]; B = pred (2|eps|).   *)
  have HgF : pow g = uls eps by rewrite Hg.
  have H3 : pow (g + 1) = 2 * pow g by rewrite bpow_plus bpow_1 /=; lra.
  have H2 : 2 * Rabs eps = pow (g + 1) by rewrite H3 -HM Hg.
  exists (pred beta fexp (2 * Rabs eps)); split.
  + by apply: generic_format_pred; rewrite H2; apply: generic_format_bpow;
       rewrite /FLX_exp; lia.
  + rewrite H2 pred_bpow.
    have Hlow : pow (fexp (g + 1)) <= Rabs eps - sumRabs l.
      rewrite -HM /fexp /FLX_exp.
      have Hle : pow (g + 1 - p) <= pow (g - Z.of_nat (size l)).
        by apply: bpow_le; lia.
      have Hs2 : sumRabs l <= uls eps - pow (g - Z.of_nat (size l)).
        by move: Hsum; rewrite Rmult_minus_distr_l Rmult_1_r Hhalf; lra.
      lra.
    by rewrite -H2; lra.
  + by apply: pred_lt_id; rewrite H2; have := bpow_gt_0 beta (g + 1); lra.
Qed.

(* Reusable block bound (paper Thm 2): the first term emitted by VSEB from a  *)
(* nonzero remainder [eps] over an F-nonoverlap tail has magnitude [< 2|eps|].*)
(* F-nonoverlap enters only through the mass bound it implies.                *)
Lemma vsebAux_head_lt eps l :
  (Z.of_nat (size l).+2 <= p + 1)%Z ->
  format eps -> {in l, forall z, format z} -> Fnonoverlap (eps :: l) ->
  eps <> 0 -> Rabs (nth 0 (vsebAux eps l) 0) < 2 * Rabs eps.
Proof.
move=> Hsz epsF lF Fno epsn0.
apply: vsebAux_head_lt_mass => //.
have H := Fnonoverlap_consE epsn0 Fno.
by apply: Fnonoverlap_aux_sumRabs.
Qed.

(* Core of Thm 2, by induction on the tail [l] of [eps :: l] (paper's running *)
(* remainder [eps] and high words [r_i]).  A step [2Sum(eps, e) = (r, et)]:   *)
(* when [et = 0] the remainder [r] is carried on (no term emitted); when      *)
(* [et <> 0] the high word [r] is emitted and [et] becomes the new remainder. *)
(* Two paper facts drive P-nonoverlap of the emitted [r]'s:                   *)
(*  - divisibility: [r_{i-1}], [eps_i] are multiples of [2^(k_i) = uls e_i];  *)
(*  - a per-block bound giving [ulp(y_j) >= 2 |eps_{i0}|], so the next emitted*)
(*    term [y_{j+1}] has [|y_{j+1}| < 2 |eps_{i0}| <= ulp(y_j)].              *)
(* The [size l < p] hypothesis (paper's [p >= n - 1]) bounds the block length *)
(* so the geometric sum [2 - 2^(i0-i-1)] stays [< 2] and no carry occurs.     *)
Lemma vsebAux_Pnonoverlap eps l :
  (Z.of_nat (size l).+1 <= p + 1)%Z ->
  format eps -> {in l, forall z, format z} -> Fnonoverlap (eps :: l) ->
  Pnonoverlap (vsebAux eps l).
Proof.
elim: l eps => [|e l' IH] eps Hsz epsF lF Fno.
  (* [vsebAux eps [::] = [:: eps]]: a single term is P-nonoverlapping.        *)
  by move=> i; rewrite /= ltnS ltn0.
have Fe : format e by apply: lF; rewrite inE eqxx.
case: l' IH lF Fno Hsz => [|e2 l''] IH lF Fno Hsz.
  (* Last step (paper's final 2Sum): [vsebAux eps [:: e] = [:: y0; y1]] with  *)
  (* [(y0, y1) = 2Sum(eps, e)]; P-nonoverlap is [|y1| < ulp y0], the Fast2Sum *)
  (* bound (no carry, using [p >= n - 1]).                                    *)
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  move=> [|i] /= Hi; last by move: Hi; rewrite ltnS ltnS ltn0.
  (* |y1| < ulp y0: the 2Sum error is <= half an ulp of the high word.        *)
  have Hm := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hm.
  (* Under FLX [ulp 0 = 0], so [0 < ulp y0] is NOT free: [y0 = 0] is real     *)
  (* here ([2Sum(x, -x) = (0, 0)], reached from the legitimate Theorem-6      *)
  (* input [[x; -x]]).  The zero guard covers it, and [Hm] itself decides     *)
  (* which way: if [y0 = 0] then [Hm] reads [Rabs y1 <= 0], so [y1 = 0].      *)
  case: (Req_dec y1 0) => [y10|y1n0]; first by left.
  right.
  have y0n0 : y0 <> 0.
    by move=> y00; apply: y1n0; move: Hm;
       rewrite y00 ulp_FLX_0; split_Rabs; lra.
  have Hy : 0 < ulp y0 by rewrite ulp_neq_0 //; apply: bpow_gt_0.
  by lra.
(* General step: [2Sum(eps, e) = (r, et)].                                    *)
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Hr : r = RND (eps + e) by have := TwoSum_hi eps e; rewrite E1.
case: Req_EM_T => [et0|etn0].
  (* [et = 0]: nothing emitted, remainder [r] carried on; recurse on          *)
  (* [r :: e2 :: l''] once the invariant is re-established.                   *)
  apply: IH.
  - by move: Hsz; rewrite /=; lia.
  - by rewrite Hr; apply: generic_format_round.
  - by move=> z zI; apply: lF; rewrite inE zI orbT.
  (* Fnonoverlap (r :: e2 :: l''): [r] merges [eps, e] exactly (et = 0).      *)
  case: (Req_dec e 0) => [e0|en0]; last first.
    case: (Req_dec r 0) => [r0|rn0]; last first.
      have Hdwh : dwh (TwoSum eps e) <> 0 by rewrite E1; exact: rn0.
      have H := Fnonoverlap_TwoSum_merge epsF Fe en0 Hdwh Fno.
      by rewrite E1 /= in H; apply: H.
    (* [r = eps + e = 0] is impossible: it needs [e = -eps], so [|e| = |eps|],*)
    (* but F-nonoverlap forces [|e| <= 1/2 uls eps <= 1/2 |eps| < |eps|].     *)
    have Hsum : r + et = eps + e.
      have Hcc : dwh (TwoSum eps e) + dwl (TwoSum eps e) = eps + e.
        by exact: TwoSum_correct_loc epsF Fe.
      by move: Hcc; rewrite E1 /=.
    have epsn0 : eps <> 0.
      by move=> eps0; apply: en0; move: Hsum; rewrite r0 et0 eps0; lra.
    have Ee : e = - eps by move: Hsum; rewrite r0 et0; lra.
    have Hb : Rabs e <= / 2 * uls eps by exact: Fnonoverlap_head2 Fno epsn0 en0.
    have Hae : Rabs e = Rabs eps by rewrite Ee Rabs_Ropp.
    have Hule : uls eps <= Rabs eps by apply: uls_le_abs.
    have Hu0 : 0 < Rabs eps by apply: Rabs_pos_lt.
    by exfalso; lra.
  (* [e = 0] interior zero: [r = eps], and the recursive [Fnonoverlap] skips  *)
  (* the zero, so the invariant transfers directly ([Fnonoverlap_aux_cons0]). *)
  have Hre : r = eps by rewrite Hr e0 Rplus_0_r; apply: round_generic.
  rewrite Hre; apply/Fnonoverlap_drop0; rewrite e0 in Fno; exact: Fno.
(* [et <> 0]: emit [r], recurse on the new remainder [et].                    *)
have Fet : format et
  by have H := format_TwoSum epsF Fe; rewrite E1 /= in H; case: H.
have Fl' : {in e2 :: l'', forall z, format z}
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have FnoEt : Fnonoverlap (et :: e2 :: l'').
  have H := Fnonoverlap_TwoSum_err epsF Fe Fno; rewrite E1 /= in H.
  by apply: H.
have Hrec : Pnonoverlap (vsebAux et (e2 :: l'')).
  by apply: IH => //; move: Hsz; rewrite /=; lia.
move=> [|i] /= Hi.
  (* Head: emitted [r = y_j] vs next [y_{j+1}].  [ulp r >= 2 |et|]            *)
  (* ([magnitude_TwoSum]) and [|y_{j+1}| < 2 |et|] ([vsebAux_head_lt]).       *)
  (* The zero guard is not needed here: [et <> 0] forces [ulp r > 0].         *)
  right.
  have Hulp : 2 * Rabs et <= ulp r.
    by have Hm := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hm; lra.
  have Hnext : Rabs (nth 0 (vsebAux et (e2 :: l'')) 0) < 2 * Rabs et.
    by apply: vsebAux_head_lt => //; move: Hsz; rewrite /=; lia.
  by apply: (Rlt_le_trans _ _ _ Hnext Hulp).
(* Tail: P-nonoverlap of the recursive output (index shift).                  *)
by apply: (Hrec i); move: Hi; rewrite ltnS.
Qed.

(* Theorem 2 (paper): [vseb e] is P-nonoverlapping with the same sum, given   *)
(* [e] F-nonoverlapping and [size e <= p + 1].  Sum: [vseb_sum] (VSEB is a    *)
(* chain of exact 2Sums).  Separation: [vsebAux_Pnonoverlap].                 *)
Lemma vseb_Pnonoverlap e :
  (Z.of_nat (size e) <= p + 1)%Z ->
  {in e, forall z, format z} -> Fnonoverlap e ->
  Pnonoverlap (vseb e) /\ sumR (vseb e) = sumR e.
Proof.
move=> Hsz eF eFno.
split; last by apply: vseb_sum.
case: e Hsz eF eFno => [|e0 l'] Hsz eF eFno; first by move=> i; rewrite /= ltn0.
rewrite /vseb.
apply: vsebAux_Pnonoverlap => //.
- by apply: eF; rewrite inE eqxx.
by move=> z zI; apply: eF; rewrite inE zI orbT.
Qed.

End SecVSEB.
