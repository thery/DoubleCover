(* ---------------------------------------------------------------------------*)
(* Paper Theorem 6 = the draft's Theorem 7 (doc/old-triplewors.pdf, 5.1):     *)
(* [VSEB (VecSum x_0 .. x_5)] is P-nonoverlapping, for [p >= 4].              *)
(*                                                                            *)
(* This is the ONE open result of the development.  It needs both [VecSum]    *)
(* and [VSEB] and nothing else, so it lives in its own file rather than in    *)
(* [TWSum.v] -- [Merge]/[TWR] are not on its path.                            *)
(*                                                                            *)
(* THE PROOF TO FOLLOW IS [doc/thm6.md] SECTION 5, not the published sketch.  *)
(* The published paper states Theorem 6 with only a five-line sketch and      *)
(* "for space constraints, the proof is not detailed"; the earlier draft      *)
(* proves the same statement in full as Theorem 7.  Beware: the sketch is not *)
(* a faithful compression of the draft (doc/thm6.md 5.6) -- it uses the wrong *)
(* index ([i] for the draft's [i_1]) and the wrong constant ([1/2 uls(e_j)]   *)
(* for the draft's [5/8 u]).                                                  *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.
Require Import VecSum.
Require Import VSEB.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SecThm6.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.
(* The draft uses [p >= 4] explicitly, in the [|e_{i_1}| > 1/2 u] case of the *)
(* VSEB analysis ("this part uses p >= 4, and ties-to-even for p = 4").       *)
Hypothesis Hp4 : (4 <= p)%Z.

Local Notation beta := radix2.
Local Notation pow e := (bpow beta e).

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Open Scope R_scope.

Local Notation u := (u p beta).
Local Notation uE := (@uE p).

Variable choice : Z -> bool.
Hypothesis choice_sym : forall x, choice x = ~~ choice (- (x + 1))%Z.
Local Notation rnd := (Znearest choice).
Local Instance valid_rnd : Valid_rnd rnd := valid_rnd_N choice.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation cexp := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation uls := (uls p).

Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).

Local Notation vecSum := (vecSum p choice).
Local Notation vecSumAux := (vecSumAux p choice).
Local Notation vseb := (vseb p choice).
Local Notation vsebAux := (vsebAux p choice).
Local Notation vecSum_run_ufp := (vecSum_run_ufp Hp2 choice_sym).
Local Notation vecSum_err_ufp := (vecSum_err_ufp Hp2 choice_sym).

Local Notation RND := (round beta fexp rnd).
Local Notation magnitudeDWR := (magnitudeDWR p).
Local Notation TwoSum := (TwoSum.TwoSum p choice).
Local Notation vecSumAux_cons := (@vecSumAux_cons p choice).
Local Notation vecSumAux_nth1 := (@vecSumAux_nth1 p choice).
Local Notation format_vecSumAux := (@format_vecSumAux p Hp2 choice).
Local Notation dwh_TwoSum_r0 := (@dwh_TwoSum_r0 p choice).
Local Notation dwl_TwoSum_r0 := (@dwl_TwoSum_r0 p Hp2 choice choice_sym).
Local Notation TwoSum_err_uls_ge := (@TwoSum_err_uls_ge p Hp2 choice choice_sym).
Local Notation TwoSum_hi := (@TwoSum_hi p choice).
Local Notation TwoSum_correct_loc := (TwoSum_correct_loc Hp2 choice_sym).
Local Notation TwoSum_err_le_r := (@TwoSum_err_le_r p Hp2 choice choice_sym).
Local Notation format_TwoSum := (@format_TwoSum p Hp2 choice).
Local Notation magnitude_TwoSum := (magnitude_TwoSum Hp2 choice_sym).
Local Notation vsebAux_head_lt_mass := (vsebAux_head_lt_mass Hp2 choice_sym).
Local Notation vsebAux_head_leB := (vsebAux_head_leB Hp2 choice_sym).
Local Notation uls_gt_0 := (@uls_gt_0 p).
Local Notation uls_le_abs := (@uls_le_abs p).
Local Notation format_vecSum := (format_vecSum Hp2).
Local Notation size_vecSum := (@size_vecSum p choice).
Local Notation vecSum_nth0 := (@vecSum_nth0 p choice).
Local Notation vecSumAux_imul := (@vecSumAux_imul p Hp2 choice choice_sym).
Local Notation vecSumAux_split := (@vecSumAux_split p choice).

(* ===========================================================================*)
(*  Theorem 6 / draft Theorem 7.                                              *)
(*                                                                            *)
(*  NOTE what is NOT here, compared with the FLT statement on [main]: there is*)
(*  no no-underflow hypothesis [emin + p <= mag z].  FLX IS the paper's model *)
(*  (unlimited exponent range), so this is the paper's statement, unpatched.  *)
(*  That is not just cosmetic: the draft's proof WLOGs [uls(e_j) = u] and     *)
(*  [uls(e_{i_0}) = u] and states every constant relative to that             *)
(*  normalisation.  Rescaling is invalid under FLT with a real [emin] -- which*)
(*  is why [vecSum_sep] had to be done scaling-free with a symbolic carry.    *)
(*  Under FLX the WLOG is legitimate, so the draft's proof is transcribable.  *)
(*                                                                            *)
(*  ROADMAP (doc/thm6.md 5.1-5.3).  Available (Qed, ported from main):        *)
(*   *1 run bound   [vecSum_run_ufp] : |s_j| <= 4 ufp(x_j), <= 2 ufp(x_{j-1}) *)
(*      err bound   [vecSum_err_ufp] : |e_{i+1}| <= 2u ufp(x_i)               *)
(*      the tie     [RN_midpoint_even], [ties_to_even]                        *)
(*   To do:                                                                   *)
(*   *2 (5.2) Assume [uls(e_j) = u] (WLOG) and [e_i >= 5/8 u] for some j < i. *)
(*      Force: |s_{i-1}| >= 1; then [2u | s_{i-1}] but [2u  |  e_j] gives some*)
(*      i' <= i-2 with [~(2u | x_i')], so |x_{i-2}| < 1; hence |x_i| < u,     *)
(*      |s_i| <= 2u, |x_{i-1}| <= 1-u.  With |s_{i-1} + e_i| >= 1 + 5/8 u this*)
(*      pins [s_{i-1} = 1], [x_{i-1} = 1-u], [s_i = u+e_i], and [2u^2 | e_i]. *)
(*      Then the right-of-i and left-of-i case analyses.                      *)
(*   *3 (5.3) VSEB: take [i_0] with [y_j = r_{i_0-1}] (so [eps_{i_0} <> 0]),  *)
(*      and [i_1] the first nonzero [e_i] after [e_{i_0}]; WLOG               *)
(*      [uls(e_{i_0}) = u], so [|eps_{i_0}| >= u] and [ulp(y_j) >= 2u].  Then *)
(*      three cases: [i_1 <= 3 /\ e_{i_1} >= 5/8 u]; [i_1 >= 4 /\ e_{i_1} >=  *)
(*      5/8 u]; [0 < e_{i_1} < 5/8 u] (itself split on 1/2 u and 1/4 u).      *)
(*                                                                            *)
(*  The [<= 6] bound is paid for in *3, via the counting: "we are adding at   *)
(*  most 3 of them", and the final [|e_4| = |e_3|] / [|e_5| <= uls(e_4)] step.*)
(*  It is necessary: Theorem 6 is FALSE for 7 inputs (doc/thm6.md 3).         *)
(* ===========================================================================*)
(* Paper core tool (doc/thm6.md 5.4): each VecSum error is at most half an    *)
(* ulp of the running high word it is dropped from, [|e_{i+1}| <= 1/2 ulp(s_i)]*)
(* -- directly [magnitude_TwoSum] on the step [2Sum(x_i, s_{i+1}) = (s_i,     *)
(* e_{i+1})].  This is the draft's recurring [|e_i| <= 1/2 ulp(s_{i-1})].     *)
Lemma vecSum_err_le_half_ulp_run (l : seq R) i :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  Rabs (nth 0 (vecSum l) i.+1) <= / 2 * ulp ((vecSumAux (drop i l)).2).
Proof.
move=> Hi Hf.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Fx : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have Hdf : {in drop i.+1 l, forall z, format z}
  by move=> z /mem_drop zI; apply: Hf.
have [Fs _] := format_vecSumAux Hdf.
have -> : nth 0 (vecSum l) i.+1 = nth 0 (vecSumAux l).1 i
  by rewrite /vecSum; case: (vecSumAux l).
rewrite (vecSumAux_nth1 Hi).
have Hs : (vecSumAux (drop i l)).2
        = dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
  rewrite (drop_nth 0 iLl).
  case Hd : (drop i.+1 l) Hdne => [//|b l0] _.
  rewrite vecSumAux_cons; case E : (vecSumAux (b :: l0)) => [es s].
  by case: (TwoSum (nth 0 l i) s).
rewrite Hs; have Hm := magnitude_TwoSum Fx Fs.
by move: Hm;
   case: (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) => hi lo /=;
   lra.
Qed.

(* ===========================================================================*)
(*  Step *2 forcing (doc/thm6.md 5.2), scale-invariant: [uls(e_j)] is kept    *)
(*  symbolic (as [pow k]) instead of the paper's WLOG [uls(e_j) = u], which is*)
(*  the FLX-legal reading of the WLOG rescaling.                              *)
(* ===========================================================================*)

(* An ulp lower bound forces a magnitude lower bound.  From                   *)
(* [5/8 pow k <= 1/2 ulp s] we get [ulp s >= 2 pow k] (the next power of two  *)
(* above [5/4 pow k]) and hence [|s| >= ufp s = 2^(p-1) ulp s >= pow(k+p)].   *)
(* This is the draft's "[|e_i| <= 1/2 ulp(s_{i-1})] gives [|s_{i-1}| >= 1]"   *)
(* (with [1 = 2^p uls(e_j)] after the [uls(e_j) = u] normalisation).          *)
(* The content, stated on the [ulp] itself: a running sum whose [ulp] is      *)
(* strictly coarser than [pow k] has [|s| >= ufp s = 2^(p-1) ulp s >=         *)
(* pow(k+p)].  Stating it this way is what lets the draft's own "similarly    *)
(* to what we saw before" in 5.3 reuse the 5.2 chain: there the threshold on  *)
(* [|e_{i_1}|] is [> 1/2 u], not [>= 5/8 u], and both give [ulp s > pow k].   *)
Lemma abs_ge_of_ulp_gt (s : R) (k : Z) :
  pow k < ulp s -> pow (k + p) <= Rabs s.
Proof.
move=> H.
have Hk : 0 < pow k by apply: bpow_gt_0.
have Hs0 : s <> 0 by move=> s0; move: H; rewrite s0 ulp_FLX_0; lra.
have Hulp : ulp s = pow (cexp s) by rewrite ulp_neq_0.
have Hce : (k < cexp s)%Z by apply: (lt_bpow beta); rewrite -Hulp.
have Hcexp : cexp s = (mag beta s - p)%Z by rewrite /cexp /FLX_exp.
apply: Rle_trans (bpow_mag_le beta s Hs0).
apply: bpow_le; lia.
Qed.

Lemma abs_ge_of_ulp_lb (s : R) (k : Z) :
  5 / 8 * pow k <= / 2 * ulp s -> pow (k + p) <= Rabs s.
Proof.
move=> H; apply: abs_ge_of_ulp_gt.
by have := bpow_gt_0 beta k; lra.
Qed.

(* Dual of [abs_ge_of_ulp_lb]: a magnitude upper bound forces an ulp upper    *)
(* bound.  [|x| < pow m] gives [mag x <= m], so [ulp x = pow(cexp x) =        *)
(* pow(mag x - p) <= pow(m - p)].  Used for the draft's [|x_{i-2}| < 1] giving*)
(* [ulp(x_{i-2}) <= u], hence [|x_i| < u].                                    *)
Lemma ulp_le_of_abs_lt (x : R) (m : Z) :
  Rabs x < pow m -> ulp x <= pow (m - p).
Proof.
move=> Hlt.
case: (Req_dec x 0) => [->|xn0]; first by rewrite ulp_FLX_0; apply: bpow_ge_0.
rewrite ulp_neq_0 //; apply: bpow_le.
have := mag_le_bpow beta x _ xn0 Hlt; rewrite /cexp /FLX_exp; lia.
Qed.

(* Same for [ufp]: [|x| < pow m] gives [ufp x = pow(mag x - 1) <= pow(m - 1)].*)
Lemma ufp_le_of_abs_lt (x : R) (m : Z) :
  x <> 0 -> Rabs x < pow m -> ufp x <= pow (m - 1).
Proof.
move=> xn0 Hlt; rewrite /ufp; apply: bpow_le.
have := mag_le_bpow beta x _ xn0 Hlt; lia.
Qed.

(* A format number strictly below [pow m] is at most its predecessor          *)
(* [pred(pow m) = pow m - pow(m - p)].  The draft's "[|x_{i-1}| <= 1 - u]"    *)
(* ([1 = pow(k+p)], [u = pow k], so [1 - u = pow(k+p) - pow k]).              *)
Lemma abs_le_pred_of_lt (x : R) (m : Z) :
  format x -> Rabs x < pow m -> Rabs x <= pow m - pow (m - p).
Proof.
move=> Fx Hlt.
have Fabs : format (Rabs x) by apply: generic_format_abs.
have Fpow : format (pow m) by apply: generic_format_bpow; rewrite /FLX_exp; lia.
have Hpg : Rabs x <= pred beta fexp (pow m) by apply: pred_ge_gt.
by rewrite pred_bpow in Hpg; exact: Hpg.
Qed.

(* [uls] of a nonzero number is a power of two -- the form its                *)
(* definition takes off the zero branch.  Lets a [uls] be named as            *)
(* [pow k], which is how the whole *2 chain is parameterised.                 *)
Lemma uls_pow (x : R) : x <> 0 -> exists k : Z, uls x = pow k.
Proof.
move=> xn0; rewrite /uls; case: Req_bool_spec => [x0|_]; first by case: xn0.
by exists (cexp x + Z.of_nat (trZ (Ztrunc (mant x))))%Z.
Qed.

(* When [|x|] is exactly a power of two its [ulp] is pinned:                  *)
(* [mag x = e + 1] so [cexp x = e - p + 1].  Turns the pinning                *)
(* conclusion [|s_i| = pow(k+p)] into the exact [ulp(s_i) = pow(k+1)].        *)
Lemma ulp_of_abs_pow (x : R) (e : Z) :
  Rabs x = pow e -> ulp x = pow (e - p + 1).
Proof.
move=> Hx.
have xn0 : x <> 0.
  move=> x0; move: Hx; rewrite x0 Rabs_R0 => H.
  by have := bpow_gt_0 beta e; lra.
have Hmag : mag beta x = (e + 1)%Z :> Z.
  apply: mag_unique; rewrite Hx; split.
    have -> : (e + 1 - 1 = e)%Z by lia.
    lra.
  by apply: bpow_lt; lia.
rewrite ulp_neq_0 // /cexp /FLX_exp Hmag.
by congr bpow; lia.
Qed.

(* Draft 5.2, first step: a violation forces the preceding running sum large. *)
(* If a VecSum error [e_{i+1}] reaches [5/8 uls(e_j)] (with [uls(e_j) = pow k])*)
(* then [|s_i| >= 2^p uls(e_j) = pow(k+p)] -- the draft's [|s_{i-1}| >= 1].   *)
(* Combines [vecSum_err_le_half_ulp_run] ([|e_{i+1}| <= 1/2 ulp(s_i)]) with   *)
(* [abs_ge_of_ulp_lb].                                                        *)
Lemma vecSum_run_ge_of_violation (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  pow (k + p) <= Rabs (vecSumAux (drop i l)).2.
Proof.
move=> Hi Hf Hviol.
apply: abs_ge_of_ulp_lb; apply: Rle_trans Hviol _.
exact: vecSum_err_le_half_ulp_run.
Qed.

(* Draft 5.2, divisibility: since [|s_i| >= 2^p uls(e_j)], the running sum is *)
(* a multiple of [2 uls(e_j) = pow(k+1)] -- the draft's "[2u | s_{i-1}]" (with*)
(* [uls(e_j) = u]).  A float of magnitude [>= pow(k+p)] lies on a grid at     *)
(* least as coarse as [pow(k+1)] ([is_imul_bound_pow_format]).                *)
Lemma vecSum_run_imul_of_run_ge (l : seq R) (i : nat) (k : Z) :
  {in l, forall z, format z} ->
  pow (k + p) <= Rabs (vecSumAux (drop i l)).2 ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)).
Proof.
move=> Hf Hge.
have Fs : format (vecSumAux (drop i l)).2.
  have Hdf : {in drop i l, forall z, format z} by move=> z /mem_drop; apply: Hf.
  by have [Fs _] := format_vecSumAux Hdf.
have H := is_imul_bound_pow_format Hge Fs.
by rewrite (_ : (k + 1 = k + p - p + 1)%Z); last lia.
Qed.

Lemma vecSum_run_imul_of_violation (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)).
Proof.
move=> Hi Hf Hviol.
by apply: vecSum_run_imul_of_run_ge (vecSum_run_ge_of_violation Hi Hf Hviol).
Qed.

(* The draft's 5.3 route to the same divisibility: there the threshold is     *)
(* [|e_{i_1}| > 1/2 u].  Since [ulp] is a power of two, [ulp(s) >= 2|e| >     *)
(* pow k] already forces [ulp(s) >= 2 pow k], hence [|s| >= 1].               *)
Lemma vecSum_run_imul_of_gt_half (l : seq R) (i : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  / 2 * pow k < Rabs (nth 0 (vecSum l) i.+1) ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)).
Proof.
move=> Hi Hf Hviol.
apply: (vecSum_run_imul_of_run_ge Hf).
apply: abs_ge_of_ulp_gt.
have := vecSum_err_le_half_ulp_run Hi Hf.
by lra.
Qed.

(* Draft 5.2, "[~(2u | x_{i'})] so [|x_{i'}| < 1]": a float off the           *)
(* [2 uls(e_j) = pow(k+1)] grid has magnitude below [1 = 2^p uls(e_j) =       *)
(* pow(k+p)].  Contrapositive of [is_imul_bound_pow_format]: a format number  *)
(* of magnitude [>= pow(k+p)] has [cexp >= k+1], so it lies on the [pow(k+1)] *)
(* grid.                                                                      *)
Lemma abs_lt_of_not_imul (x : R) (k : Z) :
  format x -> ~ is_imul x (pow (k + 1)) -> Rabs x < pow (k + p).
Proof.
move=> Fx Hni.
case: (Rlt_le_dec (Rabs x) (pow (k + p))) => [//|Hge]; exfalso.
apply: Hni; have := is_imul_bound_pow_format Hge Fx.
by rewrite (_ : (k + 1 = k + p - p + 1)%Z); last lia.
Qed.

(* Chained magnitude isotony (draft's "by isotony"): on a [sorted_mag] list a *)
(* later entry has no larger magnitude than an earlier one.                   *)
Lemma sorted_mag_le_nth (l : seq R) (i j : nat) :
  sorted_mag l -> (i <= j)%N -> (j < size l)%N ->
  Rabs (nth 0 l j) <= Rabs (nth 0 l i).
Proof.
move=> Hs; elim: j => [|j IH] Hij Hj.
  by move: Hij; rewrite leqn0 => /eqP->; apply: Rle_refl.
move: Hij; rewrite leq_eqVlt ltnS => /orP[/eqP->|Hij]; first exact: Rle_refl.
apply: Rle_trans (Hs j Hj) _.
by apply: IH => //; apply: ltn_trans (ltnSn j) Hj.
Qed.

(* Divisibility propagates from inputs to the VecSum output: if every input   *)
(* lies on the grid [pow g], so does every output ([vecSumAux_imul] packaged  *)
(* for [vecSum]).                                                             *)
Lemma vecSum_imul_forward (l : seq R) (g : Z) :
  {in l, forall z, format z} -> {in l, forall z, is_imul z (pow g)} ->
  {in vecSum l, forall z, is_imul z (pow g)}.
Proof.
move=> Hf Hm z; rewrite /vecSum.
have [H2 H1] := vecSumAux_imul Hf Hm.
case E : (vecSumAux l) => [es s0]; rewrite E /= in H2 H1.
by rewrite inE => /orP[/eqP->//|]; apply: H1.
Qed.

(* Draft 5.2, the propagation step: [2u | s_{i-1}] but [~ 2u | e_j] (j < i)   *)
(* forces some INPUT [x_{i'}] off the grid, with [i' < t] when the offending  *)
(* output sits in the prefix [j <= t] and the running sum [s_t] is on grid.   *)
(* Via [vecSumAux_split]: [vecSum (take t l ++ [s_t])] is the [t+1]-prefix of *)
(* [vecSum l], and its inputs are [x_0..x_{t-1}] plus the (on-grid) [s_t].    *)
Lemma vecSum_not_imul_prefix (l : seq R) (t j : nat) (g : Z) :
  (t < size l)%N -> {in l, forall z, format z} -> (j <= t)%N ->
  is_imul (vecSumAux (drop t l)).2 (pow g) ->
  ~ is_imul (nth 0 (vecSum l) j) (pow g) ->
  exists2 i', (i' < t)%N & ~ is_imul (nth 0 l i') (pow g).
Proof.
move=> Ht Hf Hjt Hs Hnj.
set st := (vecSumAux (drop t l)).2.
set L := take t l ++ [:: st].
have Fst : format st.
  have Hdf : {in drop t l, forall z, format z} by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have HvL : vecSum L = (vecSumAux l).2 :: take t (vecSumAux l).1
  by rewrite /vecSum /L vecSumAux_split.
have Hnthj : nth 0 (vecSum L) j = nth 0 (vecSum l) j.
  rewrite HvL /vecSum; case: (vecSumAux l) => es s0.
  rewrite [(es, s0).1]/= [(es, s0).2]/=.
  by rewrite -[s0 :: take t es]/(take t.+1 (s0 :: es)) nth_take.
have HszL : size L = t.+1.
  by rewrite /L size_cat size_take_min /= addn1 (minn_idPl (ltnW Ht)).
apply: Classical_Prop.NNPP => Hnex.
have Hall : {in L, forall z, is_imul z (pow g)}.
  move=> z; rewrite /L mem_cat inE => /orP[|/eqP->]; last exact: Hs.
  move=> /(nthP 0)[i' Hi' <-].
  move: Hi'; rewrite size_take_min ltn_min => /andP[Hi't _].
  rewrite nth_take //.
  apply: Classical_Prop.NNPP => Hni'.
  by apply: Hnex; exists i'.
have HfL : {in L, forall z, format z}.
  by move=> z; rewrite /L mem_cat inE => /orP[/mem_take/Hf //|/eqP->//].
have Him := vecSum_imul_forward HfL Hall.
apply: Hnj; rewrite -Hnthj; apply: Him; apply: mem_nth.
by rewrite size_vecSum HszL.
Qed.

(* Draft 5.2, "[exists i' <= i-2, ~(2u | x_{i'})]": at a violation, with a    *)
(* reference error [e_j] ([j <= i]) whose [uls(e_j) = pow k] (so [e_j] is an  *)
(* odd multiple of the grid, [~ 2u | e_j] by [not_imul_uls_succ]), some input *)
(* [x_{i'}] with [i' < i] is off the [2 uls(e_j) = pow(k+1)] grid.            *)
Lemma vecSum_exists_offgrid_input_of_imul (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)) ->
  exists2 i', (i' < i)%N & ~ is_imul (nth 0 l i') (pow (k + 1)).
Proof.
move=> Hi Hf Hji Hej0 Huls Him.
have Hilt : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Hjs : (j < size (vecSum l))%N.
  rewrite size_vecSum prednK; last by apply: ltn_trans Hi.
  by apply: leq_ltn_trans Hji Hilt.
have Fej : format (nth 0 (vecSum l) j)
  by apply: (format_vecSum Hf); apply: mem_nth.
have Hnej : ~ is_imul (nth 0 (vecSum l) j) (pow (k + 1))
  by exact: not_imul_uls_succ Fej Hej0 Huls.
exact: (vecSum_not_imul_prefix Hilt Hf Hji Him Hnej).
Qed.

(* Draft 5.2, combining the previous two: at a violation, some input [x_{i'}] *)
(* ([i' < i]) is off the [pow(k+1)] grid, hence [|x_{i'}| < 1 = pow(k+p)], and*)
(* by [sorted_mag] isotony EVERY later input [x_m] ([m >= i']) satisfies      *)
(* [|x_m| < 1].  (The draft's "[|x_{i'}| < 1] so by isotony [|x_{i-2}| < 1]".)*)
Lemma vecSum_inputs_lt_of_imul (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> sorted_mag l ->
  (j <= i)%N -> nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m < size l)%N -> Rabs (nth 0 l m) < pow (k + p).
Proof.
move=> Hi Hf Hsort Hji Hej0 Huls Him.
have [i' Hi'i Hoff] :=
  vecSum_exists_offgrid_input_of_imul Hi Hf Hji Hej0 Huls Him.
have Hi's : (i' < size l)%N by apply: ltn_trans Hi'i (ltn_trans (ltnSn i) Hi).
exists i' => // m Hm Hmsz.
apply: Rle_lt_trans (sorted_mag_le_nth Hsort Hm Hmsz) _.
by apply: (abs_lt_of_not_imul _ Hoff); apply: Hf; apply: mem_nth.
Qed.

Lemma vecSum_inputs_lt_of_violation (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> sorted_mag l ->
  (j <= i)%N -> nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m < size l)%N -> Rabs (nth 0 l m) < pow (k + p).
Proof.
move=> Hi Hf Hsort Hji Hej0 Huls Hviol.
apply: (vecSum_inputs_lt_of_imul Hi Hf Hsort Hji Hej0 Huls).
exact: vecSum_run_imul_of_violation Hi Hf Hviol.
Qed.

(* Draft 5.2, "[|x_{i-1}| <= 1 - u]": each earlier input, being format and    *)
(* [< 1 = pow(k+p)], is [<= 1 - u = pow(k+p) - pow k].                        *)
Lemma vecSum_inputs_le_1mu_of_violation (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} -> sorted_mag l ->
  (j <= i)%N -> nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m < size l)%N ->
      Rabs (nth 0 l m) <= pow (k + p) - pow k.
Proof.
move=> Hi Hf Hsort Hji Hej0 Huls Hviol.
have [i' Hi'i Hlt] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
exists i' => // m Hm Hmsz.
have Fm : format (nth 0 l m) by apply: Hf; apply: mem_nth.
have := abs_le_pred_of_lt Fm (Hlt m Hm Hmsz).
by rewrite (_ : (k + p - p = k)%Z); last lia.
Qed.

(* Draft 5.2, "[|x_i| < u]": with [|x_m| < 1] for the earlier inputs          *)
(* ([m >= i']) we get [ulp(x_m) <= u = pow k] ([ulp_le_of_abs_lt]), so        *)
(* [pairwise_ulp] ([|x_{m+2}| < ulp(x_m)]) yields [|x_{m+2}| < u].            *)
Lemma vecSum_inputs_lt_u_of_imul (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2 < size l)%N -> Rabs (nth 0 l m.+2) < pow k.
Proof.
move=> Hi Hf Hsort Hpair Hji Hej0 Huls Him.
have [i' Hi'i Hlt] :=
  vecSum_inputs_lt_of_imul Hi Hf Hsort Hji Hej0 Huls Him.
exists i' => // m Hm Hmsz.
have Hmsz' : (m < size l)%N.
  by apply: ltn_trans Hmsz; apply: ltn_trans (ltnSn m) (ltnSn m.+1).
have Hulp : ulp (nth 0 l m) <= pow k.
  have := ulp_le_of_abs_lt (Hlt m Hm Hmsz').
  by rewrite (_ : (k + p - p = k)%Z); last lia.
have [Hz|Hlt2] := Hpair m Hmsz; first by rewrite Hz Rabs_R0; apply: bpow_gt_0.
exact: Rlt_le_trans Hlt2 Hulp.
Qed.

Lemma vecSum_inputs_lt_u_of_violation (l : seq R) (i j : nat) (k : Z) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2 < size l)%N -> Rabs (nth 0 l m.+2) < pow k.
Proof.
move=> Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
apply: (vecSum_inputs_lt_u_of_imul Hi Hf Hsort Hpair Hji Hej0 Huls).
exact: vecSum_run_imul_of_violation Hi Hf Hviol.
Qed.

(* Draft 5.2, "[|s_i| <= 2u]": with [|x_i| < u] and the *1 running-sum bound  *)
(* [|s_i| <= 4 ufp(x_i)] we get [|s_i| <= 4 ufp(x_i) <= 4 pow(k-1) = pow(k+1) *)
(* = 2u].                                                                     *)
Lemma vecSum_run_le_2u_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2 < size l)%N ->
      Rabs (vecSumAux (drop m.+2 l)).2 <= pow (k + 1).
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [i' Hi'i Hxlt] :=
  vecSum_inputs_lt_u_of_violation Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
exists i' => // m Hm Hmsz.
have Hxn0 : nth 0 l m.+2 <> 0 by apply: Hnz.
have Hufp : ufp (nth 0 l m.+2) <= pow (k - 1)
  by apply: ufp_le_of_abs_lt Hxn0 (Hxlt _ Hm Hmsz).
have [Hrun _] := vecSum_run_ufp Heven Hf Hnz Hsort Hpair Hmsz.
apply: Rle_trans Hrun _.
have -> : pow (k + 1) = 4 * pow (k - 1).
  have E4 : (4 : R) = pow 2 by rewrite /= /Z.pow_pos /=; lra.
  by rewrite (_ : (k + 1 = 2 + (k - 1))%Z) ?bpow_plus -?E4; [|lia].
by apply: Rmult_le_compat_l; [lra | exact: Hufp].
Qed.

(* Draft 5.2, "at the right of i": "[|x_i| < u] so [forall i' >= i+1,         *)
(* |e_{i'}| <= u^2]".  Each later error [e = dwl(2Sum(x, s))] with a small    *)
(* input [|x| < u = pow k] has [|e| <= 2u ufp(x) <= 2u pow(k-1) = pow(k-p) =  *)
(* u^2] ([vecSum_err_ufp] + [ufp_le_of_abs_lt]).  This is the block-mass      *)
(* content feeding the block bound; it does NOT need the pinning.             *)
Lemma vecSum_tail_err_le_u2_of_imul (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  is_imul (vecSumAux (drop i l)).2 (pow (k + 1)) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2.+1 < size l)%N ->
      Rabs (nth 0 (vecSum l) m.+2.+1) <= pow (k - p).
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Him.
have [i' Hi'i Hxlt] :=
  vecSum_inputs_lt_u_of_imul Hi Hf Hsort Hpair Hji Hej0 Huls Him.
exists i' => // m Hm Hmsz.
have Hmsz2 : (m.+2 < size l)%N by apply: ltn_trans (ltnSn _) Hmsz.
have Hxn0 : nth 0 l m.+2 <> 0 by apply: Hnz.
have Hufp : ufp (nth 0 l m.+2) <= pow (k - 1)
  by apply: ufp_le_of_abs_lt Hxn0 (Hxlt m Hm Hmsz2).
have Herr := vecSum_err_ufp Heven Hf Hnz Hsort Hpair Hmsz.
apply: Rle_trans Herr _.
have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
have -> : pow (k - p) = 2 * u * pow (k - 1).
  by rewrite H2u -bpow_plus; congr bpow; lia.
by apply: Rmult_le_compat_l; [have := bpow_ge_0 beta (1 - p); lra | exact: Hufp].
Qed.

Lemma vecSum_tail_err_le_u2_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  exists2 i', (i' < i)%N &
    forall m, (i' <= m)%N -> (m.+2.+1 < size l)%N ->
      Rabs (nth 0 (vecSum l) m.+2.+1) <= pow (k - p).
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
apply: (vecSum_tail_err_le_u2_of_imul Heven Hi Hf Hnz Hsort Hpair Hji Hej0
                                      Huls).
exact: vecSum_run_imul_of_violation Hi Hf Hviol.
Qed.

(* ===========================================================================*)
(*  Draft 5.2, the "close to equality" PINNING (the draft's only gap -- it    *)
(*  says "by an easy case study" without detail).  Written top-down: the pure *)
(*  interval/divisibility core [interval_pin] is isolated (and, for now,      *)
(*  admitted), and [vecSum_pinning_of_violation] gathers the bounds -- all    *)
(*  proved by the *2 lemmas above -- and applies it.                          *)
(*                                                                            *)
(*  Notation ([K] plays [uls(e_j)]'s exponent, so [pow K = u], [pow(K+p) = 1],*)
(*  [pow(K+1) = 2u], [pow(K-p) = u^2]): with [a = s_i], [b = e_{i+1}],        *)
(*  [c = x_i], [d = s_{i+1}] and the exact 2Sum identity [a + b = c + d],     *)
(*   - [a] is a multiple of [2u] with [|a| >= 1] and [|a+b| <= 1+u], so [a] is*)
(*     pinned to [|a| = 1];                                                   *)
(*   - [c] is a float trapped in [(1 - 11/8 u, 1 - u]], so [|c| = 1 - u];     *)
(*   - hence [|d| = u + |b|] and [2u^2 | b].                                  *)
(* ===========================================================================*)
(* Conclusion 1 -- [|a| = 1] -- the tie-exclusion, PROVED.  [a] is a multiple *)
(* of [2u] with [1 <= |a|], and [|a| <= 1 + u + 1/2 ulp a] pins [mag a] (using*)
(* [p >= 4]), so [ulp a = 2u] and [|a| <= 1 + 2u]: [|a| in {1, 1+2u}].  The   *)
(* boundary [1+2u] is excluded because there [c+d = +-(1 + u)] is exactly the *)
(* midpoint [pow(K+p) + pow((K+p)-p)], which round-to-nearest-EVEN sends to   *)
(* [pow(K+p)] ([RN_midpoint_even]), not to [1+2u].                            *)
Lemma interval_pin_abs (a b c d : R) (K : Z) :
  ties_to_even choice ->
  format c -> a = RND (c + d) ->
  is_imul a (pow (K + 1)) -> pow (K + p) <= Rabs a ->
  Rabs c <= pow (K + p) - pow K -> Rabs d <= pow (K + 1) ->
  a + b = c + d -> 5 / 8 * pow K <= Rabs b -> Rabs b <= / 2 * ulp a ->
  Rabs a = pow (K + p).
Proof.
move=> Heven Fc Ha_rnd [za Hza] Ha_ge Hc_le Hd_le Hid Hb_lo Hb_hi.
have HG : 0 < pow K by apply: bpow_gt_0.
have HA : 0 < pow (K + p) by apply: bpow_gt_0.
have H2G : pow (K + 1) = 2 * pow K by rewrite bpow_plus bpow_1 /=; lra.
have HAG : pow (K + p) = pow p * pow K by rewrite -bpow_plus; congr bpow; lia.
have Hb_eq : b = c + d - a by lra.
have an0 : a <> 0 by move=> a0; move: Ha_ge; rewrite a0 Rabs_R0; lra.
have Hulp_le : / 2 * ulp a <= Rabs a * pow (- p).
  rewrite ulp_neq_0 //.
  have Hmg : pow (mag beta a - 1) <= Rabs a by apply: bpow_mag_le.
  have -> : cexp a = (mag beta a - 1 + (1 - p))%Z by rewrite /cexp /FLX_exp; lia.
  rewrite bpow_plus.
  have -> : pow (1 - p) = 2 * pow (- p) by rewrite bpow_plus bpow_1 /=; lra.
  have := bpow_gt_0 beta (- p); nra.
have Hpp : pow 4 <= pow p by apply: bpow_le.
have Hp16 : (16 : R) <= pow p by move: Hpp; rewrite /= /Z.pow_pos /=; lra.
have Hpn : 0 < pow (- p) by apply: bpow_gt_0.
have Hpu : pow (- p) <= / 16.
  have hp4 : (- p <= -4)%Z by lia.
  by have := bpow_le beta (- p) (-4) hp4; rewrite /= /Z.pow_pos /=; lra.
have Ha_lt2A : Rabs a < 2 * pow (K + p).
  have Hchain : Rabs a <= pow (K + p) - pow K + pow (K + 1) + / 2 * ulp a.
    have := Rabs_triang (c + d) (- a); rewrite Rabs_Ropp.
    have -> : c + d + - a = b by lra.
    have := Rabs_triang c d; split_Rabs; lra.
  rewrite H2G HAG in Hchain *; nra.
have HKp1 : pow (K + p + 1) = 2 * pow (K + p) by rewrite bpow_plus bpow_1 /=; lra.
have Hmag : mag beta a = (K + p + 1)%Z :> Z.
  apply: mag_unique.
  rewrite (_ : (K + p + 1 - 1 = K + p)%Z); last lia.
  by rewrite HKp1; split; lra.
have Hulpa : ulp a = 2 * pow K.
  rewrite ulp_neq_0 // /cexp /FLX_exp Hmag.
  by rewrite (_ : (K + p + 1 - p = K + 1)%Z) ?H2G //; lia.
have Hb_le_G : Rabs b <= pow K by move: Hb_hi; rewrite Hulpa; lra.
have Ha_le : Rabs a <= pow (K + p) + 2 * pow K.
  have := Rabs_triang (c + d) (- a); rewrite Rabs_Ropp.
  have -> : c + d + - a = b by lra.
  have := Rabs_triang c d; rewrite Hulpa in Hb_hi; split_Rabs; lra.
have Hpow1 : pow (p - 1) = IZR (2 ^ (p - 1))
  by rewrite -IZR_Zpower; [congr IZR|lia].
have HAeq : pow (K + p) = IZR (2 ^ (p - 1)) * pow (K + 1)
  by rewrite -Hpow1 -bpow_plus; congr bpow; lia.
have Hza' : Rabs a = IZR (Z.abs za) * pow (K + 1).
  by rewrite Hza Rabs_mult abs_IZR (Rabs_pos_eq (pow _)) //; apply: bpow_ge_0.
have Hzge : (2 ^ (p - 1) <= Z.abs za)%Z.
  apply: le_IZR; apply: (Rmult_le_reg_r (pow (K + 1))); first by apply: bpow_gt_0.
  by rewrite -HAeq -Hza'.
have Hzle : (Z.abs za <= 2 ^ (p - 1) + 1)%Z.
  apply: le_IZR; apply: (Rmult_le_reg_r (pow (K + 1))); first by apply: bpow_gt_0.
  rewrite -Hza' plus_IZR Rmult_plus_distr_r Rmult_1_l -HAeq.
  by move: Ha_le; rewrite H2G.
have HKpe : pow (K + p) + pow K = pow (K + p) + pow (K + p - p)
  by congr (_ + _); congr bpow; lia.
have HRmid := @RN_midpoint_even p Hp2 choice (K + p) Heven.
rewrite -HKpe in HRmid.
have Hcase : (Z.abs za = 2 ^ (p - 1) \/ Z.abs za = 2 ^ (p - 1) + 1)%Z by lia.
case: Hcase => Hcase; first by rewrite Hza' Hcase HAeq.
exfalso.
have HRaeq : Rabs a = pow (K + p) + 2 * pow K.
  by rewrite Hza' Hcase plus_IZR Rmult_plus_distr_r Rmult_1_l -HAeq H2G.
have Hcd_le : Rabs (c + d) <= pow (K + p) + pow K
  by have := Rabs_triang c d; lra.
case: (Rle_lt_dec 0 a) => Ha0.
  have Hapos : a = pow (K + p) + 2 * pow K by rewrite -HRaeq Rabs_pos_eq.
  have Hcd : c + d = pow (K + p) + pow K.
    move: Hid Hb_le_G Hcd_le; rewrite Hapos; split_Rabs; lra.
  by move: HRmid; rewrite -Hcd -Ha_rnd Hapos; lra.
have Haneg : a = - (pow (K + p) + 2 * pow K).
  by have := Rabs_left _ Ha0; rewrite HRaeq; lra.
have Hcd : c + d = - (pow (K + p) + pow K).
  move: Hid Hb_le_G Hcd_le; rewrite Haneg; split_Rabs; lra.
have Hopp := @RN_opp_sym p choice choice_sym (pow (K + p) + pow (K + p - p)).
have Haval : a = - pow (K + p)
  by rewrite Ha_rnd Hcd HKpe Hopp -HKpe HRmid.
move: Haneg Haval; lra.
Qed.

(* Conclusion 2 -- [|c| = 1 - u] -- and the extra [|d| >= u], given [|a| = 1].*)
(* The rounding fact [a = RN(c+d)] makes [a] a NEAREST float to [c+d], so with*)
(* [g = 1 - u] we get [-b <= u/2], hence (with the violation) [b in [5/8u, u]]; *)
(* then [c] is a multiple of [u] trapped in [(1 - 11/8 u, 1 - u]], so [c = 1-u],*)
(* and [d = b + u >= 13/8 u >= u].  ([2u^2 | e_i] is NOT provable here -- it  *)
(* needs the 2Sum structure -- so it moves to [vecSum_pinning_of_violation].) *)
Lemma interval_pin_rest (a b c d : R) (K : Z) :
  ties_to_even choice ->
  format c -> a = RND (c + d) ->
  is_imul a (pow (K + 1)) -> Rabs a = pow (K + p) ->
  Rabs c <= pow (K + p) - pow K -> Rabs d <= pow (K + 1) ->
  a + b = c + d -> 5 / 8 * pow K <= Rabs b -> Rabs b <= / 2 * ulp a ->
  [/\ Rabs c = pow (K + p) - pow K,
      pow K <= Rabs d &
      Rabs (d - b) = pow K ].
Proof.
move=> Heven Fc Hr Hai Hae Hcl Hdl Hi Hbl Hbh.
have HG : 0 < pow K by apply: bpow_gt_0.
have HA : 0 < pow (K + p) by apply: bpow_gt_0.
have HAG : pow (K + p) = pow p * pow K by rewrite -bpow_plus; congr bpow; lia.
have Hp16 : (16 : R) <= pow p.
  have h4p : (4 <= p)%Z by lia.
  by have := bpow_le beta 4 p h4p; rewrite /= /Z.pow_pos /=; lra.
have an0 : a <> 0 by move=> a0; move: Hae; rewrite a0 Rabs_R0; lra.
have Hmaga : mag beta a = (K + p + 1)%Z :> Z.
  apply: mag_unique; rewrite Hae (_ : (K + p + 1 - 1 = K + p)%Z); last lia.
  by split; [lra | apply: bpow_lt; lia].
have HulpA : ulp a = 2 * pow K.
  rewrite ulp_neq_0 // /cexp /FLX_exp Hmaga.
  by rewrite (_ : (K + p + 1 - p = K + 1)%Z) ?bpow_plus ?bpow_1 /=; [lra|lia].
have Hb_G : Rabs b <= pow K by move: Hbh; rewrite HulpA; lra.
have [Fa Hnear] := round_N_pt beta fexp choice (c + d).
rewrite -Hr in Fa Hnear.
have HpredAG : pred beta fexp (pow (K + p)) = pow (K + p) - pow K
  by rewrite pred_bpow /fexp /FLX_exp (_ : (K + p - p = K)%Z) //; lia.
have FAG : format (pow (K + p) - pow K)
  by rewrite -HpredAG; apply: generic_format_pred; apply: generic_format_bpow;
     rewrite /FLX_exp; lia.
have Hce : c = a + b - d by lra.
have Hd2G : Rabs d <= 2 * pow K by move: Hdl; rewrite bpow_plus bpow_1 /=; lra.
have Hc_lo : pow (K + p) - 3 * pow K <= Rabs c
  by move: Hi Hae Hb_G Hd2G; split_Rabs; lra.
have HKm1 : pow (K + p) = 2 * pow (K + p - 1)
  by rewrite (_ : (K + p = K + p - 1 + 1)%Z) ?bpow_plus ?bpow_1 /=; [lra|lia].
have HKpm1 : pow (K + p - 1) = pow K * pow (p - 1)
  by rewrite -bpow_plus; congr bpow; lia.
have Hpm1 : (8 : R) <= pow (p - 1).
  have h3p : (3 <= p - 1)%Z by lia.
  by have := bpow_le beta 3 (p - 1) h3p; rewrite /= /Z.pow_pos /=; lra.
have cn0 : c <> 0 by move=> c0; move: Hc_lo; rewrite c0 Rabs_R0; nra.
have Hmagc : mag beta c = (K + p)%Z :> Z.
  apply: mag_unique; split; last by apply: Rle_lt_trans Hcl _; lra.
  by apply: Rle_trans Hc_lo; nra.
have Hcimul : is_imul c (pow K).
  have := format_imul_cexp Fc; rewrite /cexp /FLX_exp Hmagc.
  by rewrite (_ : (K + p - p = K)%Z) //; lia.
have [mc Hmc] := Hcimul.
have Hpp2 : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
case: (Rle_lt_dec 0 a) => Ha0.
  have HaA : a = pow (K + p) by move: Hae; rewrite Rabs_pos_eq.
  have Hnb := Hnear _ FAG.
  have Hbge : - pow K / 2 <= b by move: Hnb; rewrite -Hi HaA; split_Rabs; lra.
  have Hbpos : 5 / 8 * pow K <= b by move: Hbl Hbge Hb_G; split_Rabs; lra.
  have Hcpos : 0 < c by rewrite Hce HaA; move: Hbpos Hd2G; split_Rabs; nra.
  have Hc_up : c <= pow (K + p) - pow K by move: Hcl; rewrite Rabs_pos_eq //; lra.
  have Hc_lo2 : pow (K + p) - 11 / 8 * pow K <= c
    by rewrite Hce HaA; move: Hbpos Hd2G; split_Rabs; lra.
  have Hmc_ge : (2 ^ p - 2 < mc)%Z.
    apply: lt_IZR; rewrite minus_IZR -Hpp2.
    by move: Hc_lo2; rewrite Hmc HAG; nra.
  have Hmc_le : (mc <= 2 ^ p - 1)%Z.
    apply: le_IZR; rewrite minus_IZR -Hpp2.
    by move: Hc_up; rewrite Hmc HAG; nra.
  have Hmceq : mc = (2 ^ p - 1)%Z by lia.
  have Hcval : c = pow (K + p) - pow K
    by rewrite Hmc Hmceq minus_IZR -Hpp2 HAG; ring.
  have Hdval : d = b + pow K by lra.
  have Hdb : d - b = pow K by rewrite Hdval; ring.
  split.
  - by rewrite Rabs_pos_eq //; lra.
  - by rewrite Rabs_pos_eq; rewrite Hdval; move: Hbpos; lra.
  by rewrite Hdb Rabs_pos_eq //; lra.
have HaA : a = - pow (K + p) by move: Hae; rewrite (Rabs_left _ Ha0); lra.
have FnAG : format (- (pow (K + p) - pow K)) by apply: generic_format_opp.
have Hnb := Hnear _ FnAG.
have Hble : b <= pow K / 2 by move: Hnb; rewrite -Hi HaA; split_Rabs; lra.
have Hbneg : b <= - (5 / 8 * pow K) by move: Hbl Hble Hb_G; split_Rabs; lra.
have Hcneg : c < 0 by rewrite Hce HaA; move: Hbneg Hd2G; split_Rabs; nra.
have Hc_up : - (pow (K + p) - pow K) <= c
  by move: Hcl; rewrite (Rabs_left _ Hcneg); lra.
have Hc_lo2 : c <= - (pow (K + p) - 11 / 8 * pow K)
  by rewrite Hce HaA; move: Hbneg Hd2G; split_Rabs; lra.
have Hmc_le : (mc < - (2 ^ p - 2))%Z.
  apply: lt_IZR; rewrite opp_IZR minus_IZR -Hpp2.
  by move: Hc_lo2; rewrite Hmc HAG; nra.
have Hmc_ge : (- (2 ^ p - 1) <= mc)%Z.
  apply: le_IZR; rewrite opp_IZR minus_IZR -Hpp2.
  by move: Hc_up; rewrite Hmc HAG; nra.
have Hmceq : mc = (- (2 ^ p - 1))%Z by lia.
have Hcval : c = - (pow (K + p) - pow K)
  by rewrite Hmc Hmceq opp_IZR minus_IZR -Hpp2 HAG; ring.
have Hdval : d = b - pow K by lra.
have Hdb : d - b = - pow K by rewrite Hdval; ring.
have Hdneg : d < 0 by rewrite Hdval; move: Hbneg; lra.
split.
- by rewrite (Rabs_left _ Hcneg) Hcval; lra.
- by rewrite (Rabs_left _ Hdneg) Hdval; move: Hbneg; lra.
by rewrite Hdb Rabs_Ropp Rabs_pos_eq //; lra.
Qed.

Lemma interval_pin (a b c d : R) (K : Z) :
  ties_to_even choice ->
  format c -> a = RND (c + d) ->
  is_imul a (pow (K + 1)) -> pow (K + p) <= Rabs a ->
  Rabs c <= pow (K + p) - pow K -> Rabs d <= pow (K + 1) ->
  a + b = c + d -> 5 / 8 * pow K <= Rabs b -> Rabs b <= / 2 * ulp a ->
  [/\ Rabs a = pow (K + p),
      Rabs c = pow (K + p) - pow K,
      pow K <= Rabs d &
      Rabs (d - b) = pow K ].
Proof.
move=> Heven Fc Hr Hai Hge Hcl Hdl Hi Hbl Hbh.
have HRa := interval_pin_abs Heven Fc Hr Hai Hge Hcl Hdl Hi Hbl Hbh.
have [HC HD HDB] := interval_pin_rest Heven Fc Hr Hai HRa Hcl Hdl Hi Hbl Hbh.
by split.
Qed.

Lemma vecSum_pinning_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  [/\ Rabs (vecSumAux (drop i l)).2 = pow (k + p),
      Rabs (nth 0 l i) = pow (k + p) - pow k,
      is_imul (nth 0 (vecSum l) i.+1) (pow (k - p + 1)),
      pow k <= Rabs (vecSumAux (drop i.+1 l)).2 &
      (* the draft's "[s_i = u + e_i]", in signed form                        *)
      Rabs ((vecSumAux (drop i.+1 l)).2 - nth 0 (vecSum l) i.+1) = pow k ].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Ha_imul := vecSum_run_imul_of_violation Hi Hf Hviol.
have Ha_ge := vecSum_run_ge_of_violation Hi Hf Hviol.
have Hb_hi := vecSum_err_le_half_ulp_run Hi Hf.
have Fc : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have [i'c Hi'c Hc] :=
  vecSum_inputs_le_1mu_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hc_le : Rabs (nth 0 l i) <= pow (k + p) - pow k
  by apply: Hc (ltnW Hi'c) iLl.
have Hi1 : (0 < i)%N by apply: leq_ltn_trans (leq0n i'c) Hi'c.
have [i'd Hi'd Hd] :=
  vecSum_run_le_2u_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have Hi1eq : (i.-1.+2 = i.+1)%N by rewrite prednK.
have Hle : (i'd <= i.-1)%N by rewrite -ltnS (prednK Hi1).
have Hd_sz : (i.-1.+2 < size l)%N by rewrite Hi1eq.
have Hd_le := Hd i.-1 Hle Hd_sz; rewrite Hi1eq in Hd_le.
have He : nth 0 (vecSum l) i.+1 =
          dwl (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  by rewrite -(vecSumAux_nth1 Hi) /vecSum; case: (vecSumAux l).
have Hsdwh : (vecSumAux (drop i l)).2 =
             dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
  have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
  rewrite (drop_nth 0 iLl).
  case Hd0 : (drop i.+1 l) Hdne => [//|b0 l0] _.
  rewrite vecSumAux_cons; case E : (vecSumAux (b0 :: l0)) => [es s].
  by case: (TwoSum (nth 0 l i) s).
have Fs1 : format (vecSumAux (drop i.+1 l)).2.
  have Hdf : {in drop i.+1 l, forall z, format z}
    by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have Hcorr : dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) +
             dwl (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2) =
             nth 0 l i + (vecSumAux (drop i.+1 l)).2
  by exact: TwoSum_correct_loc Fc Fs1.
have Hid : (vecSumAux (drop i l)).2 + nth 0 (vecSum l) i.+1 =
           nth 0 l i + (vecSumAux (drop i.+1 l)).2
  by rewrite He Hsdwh.
have Ha_rnd : (vecSumAux (drop i l)).2 =
              RND (nth 0 l i + (vecSumAux (drop i.+1 l)).2)
  by rewrite Hsdwh TwoSum_hi.
have [HRs HRc HDd HDB] :=
  interval_pin Heven Fc Ha_rnd Ha_imul Ha_ge Hc_le Hd_le Hid Hviol Hb_hi.
split=> //.
(* [2u^2 | e_{i+1}]: the 2Sum error is a multiple of                          *)
(* [pow(min(cexp x_i, cexp s_{i+1}))], and both cexps are [>= k - p + 1]      *)
(* -- [cexp x_i = k] (from [|x_i| = 1 - u]) and [cexp s_{i+1} >= k-p+1] (from *)
(* [|s_{i+1}| >= u]).                                                         *)
have Hmx : mag beta (nth 0 l i) = (k + p)%Z :> Z.
  apply: mag_unique; rewrite HRc; split; last by have := bpow_gt_0 beta k; lra.
  have -> : pow (k + p) = 2 * pow (k + p - 1)
    by rewrite (_ : (k + p = k + p - 1 + 1)%Z) ?bpow_plus ?bpow_1 /=; [lra|lia].
  have : pow k <= pow (k + p - 1) by apply: bpow_le; lia.
  lra.
have Hms1 : (k + 1 <= mag beta (vecSumAux (drop i.+1 l)).2)%Z.
  apply: mag_ge_bpow; have -> : (k + 1 - 1 = k)%Z by lia.
  exact: HDd.
rewrite He.
apply: is_imul_pow_le
  (@TwoSum_err_imul p Hp2 choice choice_sym _ _ Fc Fs1) _.
apply: Z.min_glb; rewrite /cexp /FLX_exp; [rewrite Hmx | ]; lia.
Qed.


(* Draft 5.2/5.3 workhorse: EVERY later error is bounded by the [uls]         *)
(* of any earlier nonzero one.  This is the paper's repeated step             *)
(* "[uls(e_i1)] <= 1/8 u, so [|e_{i1+1}|, ..., |e_5|] <= 1/8 u".              *)
(* Proof: with [uls(e_j) = pow K], either [|e_m| < 5/8 pow K] and there       *)
(* is nothing to do, or [|e_m|] reaches the violation threshold, the *2       *)
(* pinning applies and fixes [|s_{m-1}| = pow(K+p)], so                       *)
(* [ulp(s_{m-1}) = pow(K+1)] and the core tool                                *)
(* [|e_m| <= 1/2 ulp(s_{m-1})] gives exactly [|e_m| <= pow K].  Note          *)
(* [e_m] is NOT required to be nonzero, and no [size l <= 6] is needed.       *)
Lemma vecSum_tail_le_uls (l : seq R) (j m : nat) :
  ties_to_even choice ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  (j < m)%N -> (m < size (vecSum l))%N ->
  nth 0 (vecSum l) j <> 0 ->
  Rabs (nth 0 (vecSum l) m) <= uls (nth 0 (vecSum l) j).
Proof.
move=> Heven Hfmt Hnz Hsort Hpair Hjm Hm Hnj.
have [K HK] := uls_pow Hnj.
have HpK := bpow_gt_0 beta K.
rewrite HK.
case: m Hjm Hm => [//|m'] Hjm Hm.
case: (Rle_lt_dec (5 / 8 * pow K) (Rabs (nth 0 (vecSum l) m'.+1))) =>
      [Hviol|Hsmall]; last by lra.
(* the violation case: the pinning fixes [ulp(s_{m-1})] exactly               *)
have Hszl : (m'.+1 < size l)%N.
  move: Hm; rewrite size_vecSum ltnS => Hm'.
  have H0 : (0 < size l)%N by case: (size l) Hm'.
  by rewrite -(prednK H0) ltnS.
have Hji : (j <= m')%N by rewrite -ltnS.
have [HRs _ _] :=
  vecSum_pinning_of_violation Heven Hszl Hfmt Hnz Hsort Hpair Hji Hnj HK
                              Hviol.
have Hulp := vecSum_err_le_half_ulp_run Hszl Hfmt.
rewrite (ulp_of_abs_pow HRs) in Hulp.
have Hee : (K + p - p + 1 = K + 1)%Z by lia.
rewrite Hee bpow_plus bpow_1 /= in Hulp.
lra.
Qed.


(* Draft 5.2, "at the right of i", the CASE LIST.  There the violating        *)
(* error satisfies [2u^2 | e_i] (the pinning) and [e_i <= u]                  *)
(* ([vecSum_tail_le_uls]), and the proof splits on [e_i = u],                 *)
(* [e_i = u - 2u^2], or [e_i <= u - 4u^2].  Scale-invariantly, with           *)
(* [t = pow K] for [u] and [g = pow(K-p+1)] for [2u^2]: a multiple of         *)
(* [g] bounded by [t] is [t], [t - g], or at most [t - 2g], because           *)
(* [t / g = pow(p-1)] is an integer, so the multiples of [g] below [t]        *)
(* step down by [g] from [t] itself.                                          *)
Lemma imul_case_split (x : R) (K : Z) :
  is_imul x (pow (K - p + 1)) -> Rabs x <= pow K ->
  [\/ Rabs x = pow K,
      Rabs x = pow K - pow (K - p + 1) |
      Rabs x <= pow K - 2 * pow (K - p + 1) ].
Proof.
move=> [n Hn] Hle.
have Hg := bpow_gt_0 beta (K - p + 1).
(* [t = pow(p-1) * g]: the number of [g]-steps up to [t] is an integer        *)
have Hpm : pow (p - 1) = IZR (2 ^ (p - 1))
  by rewrite -IZR_Zpower; [congr IZR|lia].
have Ht : pow K = IZR (2 ^ (p - 1)) * pow (K - p + 1).
  by rewrite -Hpm -bpow_plus; congr bpow; lia.
have HN : (0 < 2 ^ (p - 1))%Z by apply: Z.pow_pos_nonneg; lia.
have Hgp : 0 <= pow (K - p + 1) by apply: bpow_ge_0.
have Hxa : Rabs x = IZR (Z.abs n) * pow (K - p + 1).
  by rewrite Hn Rabs_mult abs_IZR (Rabs_pos_eq _ Hgp).
(* [|n| <= 2^(p-1)] from [|x| <= t]                                           *)
have Hn_le : (Z.abs n <= 2 ^ (p - 1))%Z.
  apply: le_IZR; apply: (Rmult_le_reg_r (pow (K - p + 1))) => //.
  by rewrite -Hxa -Ht.
(* three cases on how far [|n|] sits below [2^(p-1)]                          *)
case: (Z.eq_dec (Z.abs n) (2 ^ (p - 1))) => [Heq|Hne].
  by apply: Or31; rewrite Hxa Heq Ht.
case: (Z.eq_dec (Z.abs n) (2 ^ (p - 1) - 1)) => [Heq1|Hne1].
  apply: Or32; rewrite Hxa Heq1 Ht minus_IZR.
  by rewrite Rmult_minus_distr_r Rmult_1_l.
apply: Or33; rewrite Hxa Ht.
have Hn2 : (Z.abs n <= 2 ^ (p - 1) - 2)%Z by lia.
have := IZR_le _ _ Hn2; rewrite minus_IZR => Hle2.
have -> : IZR (2 ^ (p - 1)) * pow (K - p + 1) -
          2 * pow (K - p + 1) =
          (IZR (2 ^ (p - 1)) - 2) * pow (K - p + 1) by lra.
by apply: Rmult_le_compat_r; lra.
Qed.


(* Draft 5.2 "at the right of i", instantiated at a violation: the            *)
(* violating error is [e_i = u], [e_i = u - 2u^2], or [e_i <= u - 4u^2].      *)
(* The divisibility [2u^2 | e_i] comes from the pinning and the ceiling       *)
(* [e_i <= u] from [vecSum_tail_le_uls]; [imul_case_split] then splits.       *)
Lemma vecSum_err_case_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  [\/ Rabs (nth 0 (vecSum l) i.+1) = pow k,
      Rabs (nth 0 (vecSum l) i.+1) = pow k - pow (k - p + 1) |
      Rabs (nth 0 (vecSum l) i.+1) <= pow k - 2 * pow (k - p + 1) ].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [_ _ Him _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
have H0 : (0 < size l)%N by case: (size l) Hi.
have Hsz : (i.+1 < size (vecSum l))%N by rewrite size_vecSum prednK.
have Hle := vecSum_tail_le_uls Heven Hf Hnz Hsort Hpair (leq_ltn_trans Hji
                               (ltnSn i)) Hsz Hej0.
rewrite Huls in Hle.
exact: imul_case_split Him Hle.
Qed.


(* If [s] sits at signed distance exactly [G] from [e], is itself at          *)
(* least [G] away from 0, and [e] is smaller than [2G], then [s] lies on      *)
(* the FAR side of [e]: [|s| = |e| + G].  (The near side would put [s]        *)
(* strictly inside [(-G, G)], contradicting [G <= |s|].)  This is what        *)
(* turns the draft's [s_i = u + e_i] into its per-case values.                *)
Lemma abs_pin_add (s e G : R) :
  Rabs (s - e) = G -> G <= Rabs s -> 0 < Rabs e -> Rabs e < 2 * G ->
  Rabs s = Rabs e + G.
Proof. by move=> Hse Hsg He0 He2; move: Hse Hsg He0 He2; split_Rabs; lra. Qed.

(* Draft 5.2, "[s_i = u + e_i]": at a violation, as soon as the error         *)
(* stays below [2u] the running sum is pushed to [|e_i| + u].  Both of        *)
(* the draft's named cases ([e_i = u] and [e_i = u - 2u^2]) satisfy that      *)
(* bound, so this one lemma yields both of their [s_i] values.                *)
Lemma vecSum_run_val_of_violation (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 (vecSum l) i.+1) < 2 * pow k ->
  Rabs (vecSumAux (drop i.+1 l)).2 =
    Rabs (nth 0 (vecSum l) i.+1) + pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hlt.
have Hpk := bpow_gt_0 beta k.
have [_ _ _ HDd HDB] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
by apply: abs_pin_add HDB HDd _ Hlt; lra.
Qed.

(* Draft 5.2 "at the right of i", COMPLETE: the three cases together          *)
(* with the running-sum value each forces.  Cases 1 and 2 are the             *)
(* draft's [e_i = u, s_i = 2u] and [e_i = u - 2u^2, s_i = 2u - 2u^2];         *)
(* case 3 is its [e_i <= u - 4u^2] remainder.                                 *)
Lemma vecSum_right_of_i_cases (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  [\/ Rabs (nth 0 (vecSum l) i.+1) = pow k /\
      Rabs (vecSumAux (drop i.+1 l)).2 = 2 * pow k,
      Rabs (nth 0 (vecSum l) i.+1) = pow k - pow (k - p + 1) /\
      Rabs (vecSumAux (drop i.+1 l)).2 = 2 * pow k - pow (k - p + 1) |
      Rabs (nth 0 (vecSum l) i.+1) <= pow k - 2 * pow (k - p + 1) ].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have Hpk := bpow_gt_0 beta k.
have Hg : pow (k - p + 1) < pow k by apply: bpow_lt; lia.
have Hgp := bpow_gt_0 beta (k - p + 1).
have Hval := vecSum_run_val_of_violation Heven Hi Hf Hnz Hsort Hpair Hji
                                         Hej0 Huls Hviol.
case: (vecSum_err_case_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0
                                    Huls Hviol) => [He|He|He].
- by apply: Or31; split=> //; rewrite Hval ?He; lra.
- by apply: Or32; split=> //; rewrite Hval ?He; lra.
by apply: Or33.
Qed.


(* The VecSum step at index [i], as reusable facts: the exact 2Sum            *)
(* identity [s_i + e_{i+1} = x_i + s_{i+1}] and [s_i = RND(x_i +              *)
(* s_{i+1})].  Both were derived inline inside                                *)
(* [vecSum_pinning_of_violation]; the counting argument needs them at         *)
(* other indices, so they are factored out here.                              *)
Lemma vecSum_run_dwh (l : seq R) (i : nat) :
  (i.+1 < size l)%N ->
  (vecSumAux (drop i l)).2 =
    dwh (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
Proof.
move=> Hi.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Hdne : (0 < size (drop i.+1 l))%N by rewrite size_drop subn_gt0.
rewrite (drop_nth 0 iLl).
case Hd0 : (drop i.+1 l) Hdne => [//|b0 l0] _.
rewrite vecSumAux_cons; case E : (vecSumAux (b0 :: l0)) => [es s].
by case: (TwoSum (nth 0 l i) s).
Qed.

Lemma vecSum_run_dwl (l : seq R) (i : nat) :
  (i.+1 < size l)%N ->
  nth 0 (vecSum l) i.+1 =
    dwl (TwoSum (nth 0 l i) (vecSumAux (drop i.+1 l)).2).
Proof.
by move=> Hi; rewrite -(vecSumAux_nth1 Hi) /vecSum; case: (vecSumAux l).
Qed.

Lemma vecSum_run_step (l : seq R) (i : nat) :
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (vecSumAux (drop i l)).2 + nth 0 (vecSum l) i.+1 =
    nth 0 l i + (vecSumAux (drop i.+1 l)).2.
Proof.
move=> Hi Hf.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have Fc : format (nth 0 l i) by apply: Hf; apply: mem_nth.
have Fs1 : format (vecSumAux (drop i.+1 l)).2.
  have Hdf : {in drop i.+1 l, forall z, format z}
    by move=> z /mem_drop; apply: Hf.
  by have [F _] := format_vecSumAux Hdf.
have Hcorr := TwoSum_correct_loc Fc Fs1.
by rewrite (vecSum_run_dwl Hi) (vecSum_run_dwh Hi).
Qed.

Lemma vecSum_run_rnd (l : seq R) (i : nat) :
  (i.+1 < size l)%N ->
  (vecSumAux (drop i l)).2 =
    RND (nth 0 l i + (vecSumAux (drop i.+1 l)).2).
Proof. by move=> Hi; rewrite (vecSum_run_dwh Hi) TwoSum_hi. Qed.

(* At the last index the running sum IS the input.                            *)
Lemma vecSum_run_last (l : seq R) (i : nat) :
  size l = i.+1 -> (vecSumAux (drop i l)).2 = nth 0 l i.
Proof.
move=> Hsz.
have iLl : (i < size l)%N by rewrite Hsz ltnSn.
rewrite (drop_nth 0 iLl).
have -> : drop i.+1 l = [::] by apply: drop_oversize; rewrite Hsz.
by [].
Qed.

(* Draft 5.2, "so we must have s_{i+1} >= u": from [|s_i| >= 2u], the         *)
(* input bound [|x_i| <= u - u^2] and the tail error [|e_{i+1}| <= u^2],      *)
(* the exact step identity [s_{i+1} = s_i + e_{i+1} - x_i] leaves at          *)
(* least [2u - u^2 - (u - u^2) = u].                                          *)
Lemma vecSum_run_ge_next_gen (l : seq R) (i : nat) (k : Z) (S : R) :
  (i.+2 < size l)%N -> {in l, forall z, format z} ->
  S <= Rabs (vecSumAux (drop i.+1 l)).2 ->
  Rabs (nth 0 l i.+1) <= pow k - pow (k - p) ->
  Rabs (nth 0 (vecSum l) i.+2) <= pow (k - p) ->
  S - pow k <= Rabs (vecSumAux (drop i.+2 l)).2.
Proof.
move=> Hsz Hf Hs Hx He.
have Hst := vecSum_run_step Hsz Hf.
by move: Hst Hs Hx He; split_Rabs; lra.
Qed.

(* The draft's [e_i = u] instance: [s_i = 2u] leaves [s_{i+1} >= u].          *)
Lemma vecSum_run_ge_next (l : seq R) (i : nat) (k : Z) :
  (i.+2 < size l)%N -> {in l, forall z, format z} ->
  2 * pow k <= Rabs (vecSumAux (drop i.+1 l)).2 ->
  Rabs (nth 0 l i.+1) <= pow k - pow (k - p) ->
  Rabs (nth 0 (vecSum l) i.+2) <= pow (k - p) ->
  pow k <= Rabs (vecSumAux (drop i.+2 l)).2.
Proof.
move=> Hsz Hf Hs Hx He.
have H := vecSum_run_ge_next_gen Hsz Hf Hs Hx He.
by lra.
Qed.

(* The draft's [e_i = u - 2u^2] instance: [s_i = 2u - 2u^2] leaves only       *)
(* [s_{i+1} >= u - 2u^2].  That is BELOW the [u - u^2] ceiling on the next    *)
(* input, which is exactly why the draft's conclusion in this case is the     *)
(* weaker "either there is no more non-zero e_{i'} or i <= 3" rather than     *)
(* the outright [i <= 3] of the [e_i = u] case.                               *)
Lemma vecSum_run_ge_next_1m2u (l : seq R) (i : nat) (k : Z) :
  (i.+2 < size l)%N -> {in l, forall z, format z} ->
  2 * pow k - pow (k - p + 1) <= Rabs (vecSumAux (drop i.+1 l)).2 ->
  Rabs (nth 0 l i.+1) <= pow k - pow (k - p) ->
  Rabs (nth 0 (vecSum l) i.+2) <= pow (k - p) ->
  pow k - pow (k - p + 1) <= Rabs (vecSumAux (drop i.+2 l)).2.
Proof.
move=> Hsz Hf Hs Hx He.
have H := vecSum_run_ge_next_gen Hsz Hf Hs Hx He.
by lra.
Qed.


Lemma leq6_of_gt2 (n : nat) : (2 < n)%N -> (6 <= n.+3)%N.
Proof. by case: n => [|[|[|n]]]. Qed.

(* Draft 5.2, case [e_i = u], THE COUNTING: "so we must have                  *)
(* s_{i+1} >= u with x_{i+1} < u, so s_{i+2} <> 0.  In particular,            *)
(* i <= 3."  (Our [i] is the draft's [i-1], so the conclusion reads           *)
(* [i <= 2].)  The running sum two steps on is still at least [u],            *)
(* while every input from there on is below [u]; a running sum that has       *)
(* run off the end of the list is [0], and one sitting at the very last       *)
(* index IS that input -- either way it cannot reach [u].  So the list        *)
(* must extend at least to [i+3], and [size l <= 6] caps [i].                 *)
Lemma vecSum_right_of_i_count (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (size l <= 6)%N -> (i.+1 < size l)%N ->
  {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 (vecSum l) i.+1) = pow k ->
  (i <= 2)%N.
Proof.
move=> Heven Hsz6 Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Heq.
have Hpk := bpow_gt_0 beta k.
have Hpkp := bpow_gt_0 beta (k - p).
have Hlt2 : Rabs (nth 0 (vecSum l) i.+1) < 2 * pow k by rewrite Heq; lra.
(* the draft's [s_i = 2u]                                                     *)
have Hs1 : Rabs (vecSumAux (drop i.+1 l)).2 = 2 * pow k.
  rewrite (vecSum_run_val_of_violation Heven Hi Hf Hnz Hsort Hpair Hji
                                       Hej0 Huls Hviol Hlt2) Heq.
  by lra.
have [ix Hix Hxlt] :=
  vecSum_inputs_lt_u_of_violation Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n ix) Hix.
have Hpred : (i.-1.+2 = i.+1)%N by rewrite prednK.
have Hixle : (ix <= i.-1)%N by rewrite -ltnS prednK.
(* the list must reach i+2: otherwise s_{i+1} would BE x_{i+1} < u            *)
have HA : (i.+2 < size l)%N.
  case: (ltnP i.+2 (size l)) => [//|Hge].
  have Hszeq : size l = i.+2 by apply/eqP; rewrite eqn_leq Hge Hi.
  have Hx1 : Rabs (nth 0 l i.+1) < pow k.
    have H := Hxlt i.-1 Hixle; rewrite Hpred in H.
    by apply: H; rewrite Hszeq.
  by move: Hs1; rewrite (vecSum_run_last Hszeq) => H2; move: Hx1; lra.
(* the draft's [x_{i+1} <= u - u^2] and [|e_{i+2}| <= u^2]                    *)
have Hx1 : Rabs (nth 0 l i.+1) < pow k.
  have H := Hxlt i.-1 Hixle; rewrite Hpred in H; exact: H Hi.
have Hx1p : Rabs (nth 0 l i.+1) <= pow k - pow (k - p).
  have Fx : format (nth 0 l i.+1) by apply: Hf; apply: mem_nth.
  by have := abs_le_pred_of_lt Fx Hx1.
have [ie Hie Hetail] :=
  vecSum_tail_err_le_u2_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0
                                     Huls Hviol.
have Hiele : (ie <= i.-1)%N by rewrite -ltnS prednK.
have He2 : Rabs (nth 0 (vecSum l) i.+2) <= pow (k - p).
  have H := Hetail i.-1 Hiele.
  rewrite (_ : (i.-1.+2.+1 = i.+2)%N) in H; last by rewrite prednK.
  exact: H HA.
(* the draft's [s_{i+1} >= u]                                                 *)
have Hs1' : 2 * pow k <= Rabs (vecSumAux (drop i.+1 l)).2
  by rewrite Hs1; lra.
have HB := vecSum_run_ge_next HA Hf Hs1' Hx1p He2.
(* [i >= 3] would strand that running sum at or past the last index           *)
rewrite leqNgt; apply/negP => Hi3.
have H36 := leq6_of_gt2 Hi3.
have Hszeq : size l = i.+3.
  by apply/eqP; rewrite eqn_leq HA andbT; apply: leq_trans Hsz6 H36.
have Hx2 : Rabs (nth 0 l i.+2) < pow k.
  by apply: (Hxlt i (ltnW Hix)); rewrite Hszeq.
by move: HB; rewrite (vecSum_run_last Hszeq); lra.
Qed.




(* The MIRROR of [VecSum.RN_midpoint_even]: the tie just BELOW a power of     *)
(* two.  [pow e - pow(e-p-1)] is halfway between [pow e - pow(e-p)]           *)
(* (mantissa [2^p - 1], odd) and [pow e] (mantissa [2^p], even), so           *)
(* ties-to-even sends it UP to [pow e].  This is what makes the draft's       *)
(* "case x_{i-2} = 1-u ... s_{i-2} = 2" come out exact.                       *)
Lemma RN_midpoint_even_lo (e : Z) : ties_to_even choice ->
  RND (pow e - pow (e - p - 1)) = pow e.
Proof.
move=> Heven.
have Hpe := bpow_gt_0 beta e.
have Hpep := bpow_gt_0 beta (e - p - 1).
have Hlt1 : pow (e - p - 1) < pow (e - 1) by apply: bpow_lt; lia.
have Haux1 : pow ((e - 1) + 1)%Z = 2 * pow (e - 1).
  by rewrite bpow_plus bpow_1 /=; lra.
have He1 : pow e = 2 * pow (e - 1).
  by rewrite -Haux1; congr bpow; lia.
have Hx0 : 0 < pow e - pow (e - p - 1) by lra.
have Hmagx : mag beta (pow e - pow (e - p - 1)) = e :> Z.
  by apply: mag_unique_pos; split; lra.
have Hcexp : cexp (pow e - pow (e - p - 1)) = (e - p)%Z.
  by rewrite /cexp Hmagx /FLX_exp.
have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
have Hpp : pow p = IZR (2 ^ p).
  have -> : (2 = radix2 :> Z)%Z by [].
  by rewrite IZR_Zpower //; lia.
have Hppg := bpow_gt_0 beta p.
have Hsm : mant (pow e - pow (e - p - 1)) = pow p - / 2.
  rewrite /scaled_mantissa Hcexp Rmult_minus_distr_r -!bpow_plus.
  have -> : (e + - (e - p) = p)%Z by lia.
  have -> : (e - p - 1 + - (e - p) = -1)%Z by lia.
  by rewrite Hpm1.
have Hfloor : Zfloor (mant (pow e - pow (e - p - 1))) = (2 ^ p - 1)%Z.
  rewrite Hsm; apply: Zfloor_imp.
  have -> : (2 ^ p - 1 + 1 = 2 ^ p)%Z by lia.
  by rewrite minus_IZR -Hpp; lra.
have Hceil : Zceil (mant (pow e - pow (e - p - 1))) = (2 ^ p)%Z.
  rewrite Hsm; apply: Zceil_imp.
  by rewrite minus_IZR -Hpp; lra.
have HRD : round beta fexp Zfloor (pow e - pow (e - p - 1)) =
           pow e - pow (e - p).
  rewrite /round Hfloor Hcexp /F2R /= minus_IZR -Hpp Rmult_minus_distr_r.
  by rewrite -bpow_plus Rmult_1_l; congr (_ - _); congr bpow; lia.
have HRU : round beta fexp Zceil (pow e - pow (e - p - 1)) = pow e.
  rewrite /round Hceil Hcexp /F2R /= -Hpp -bpow_plus.
  by congr bpow; lia.
have Haux2 : pow ((e - p - 1) + 1)%Z = 2 * pow (e - p - 1).
  by rewrite bpow_plus bpow_1 /=; lra.
have Hhalf : pow (e - p) = 2 * pow (e - p - 1).
  by rewrite -Haux2; congr bpow; lia.
have Hmid :
  (pow e - pow (e - p - 1)) -
    round beta fexp Zfloor (pow e - pow (e - p - 1)) =
  round beta fexp Zceil (pow e - pow (e - p - 1)) -
    (pow e - pow (e - p - 1)).
  by rewrite HRD HRU Hhalf; lra.
rewrite (@round_N_middle beta fexp choice _ Hmid) Hfloor.
have Heven2p : Z.even (2 ^ p) = true.
  have -> : (2 ^ p = 2 * 2 ^ (p - 1))%Z.
    by rewrite -Z.pow_succ_r; [congr (_ ^ _)%Z; lia | lia].
  by rewrite Z.even_mul.
have -> : choice (2 ^ p - 1) = true.
  by rewrite Heven Z.even_sub Heven2p.
exact: HRU.
Qed.

(* Draft 5.3's "thus we must have [eps_{i_0} = -u]", in its general form.     *)
(* If [g] sits on the [pow a] grid and [|d|] is the grid step [pow (a-p)]     *)
(* below it, the rounding of [g + d] can NEVER land on [g + 2d] -- i.e. the   *)
(* error can never come back with the OPPOSITE sign.  [g + 2d] would be a     *)
(* multiple of [2 pow (a-p)] but not of [4 pow (a-p)], which caps its [uls],  *)
(* hence its magnitude, at [pow (a+1)]; being a multiple of [pow a], [g] is   *)
(* then [pow a] or [pow (a+1)] in absolute value, and each of the four        *)
(* sign combinations is settled by a tie that ties-to-even breaks TOWARDS     *)
(* [g] ([RN_midpoint_even], [RN_midpoint_even_lo]), by exactness, or by the   *)
(* [uls] cap itself.                                                          *)
Lemma RN_imul_no_tie (g d : R) (a : Z) :
  ties_to_even choice -> format g -> g <> 0 -> is_imul g (pow a) ->
  Rabs d = pow (a - p) -> RND (g + d) <> g + 2 * d.
Proof.
move=> Heven Fg gn0 Himg Hd Heq.
have HGp := bpow_gt_0 beta (a - p).
have HAp := bpow_gt_0 beta a.
have HA1 := bpow_gt_0 beta (a + 1).
have Hpa0 : 0 <= pow a by lra.
have HGA : 16 * pow (a - p) <= pow a.
  have -> : 16 * pow (a - p) = pow (a - p + 4).
    by rewrite bpow_plus /= /Z.pow_pos /=; lra.
  by apply: bpow_le; lia.
have Hdn0 : d <> 0 by move: Hd; split_Rabs; lra.
have Hpm : d = pow (a - p) \/ d = - pow (a - p) by move: Hd; split_Rabs; lra.
have Hgge : pow a <= Rabs g by apply: is_imul_pow_le_abs.
have Hstep2 : pow (a - p + 1) = 2 * pow (a - p).
  have H2 : (2 = pow 1) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite H2 -bpow_plus; congr bpow; lia.
have Hstep4 : pow (a - p + 2) = 4 * pow (a - p).
  have H4 : (4 = pow 2) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite H4 -bpow_plus; congr bpow; lia.
(* [g + 2d] is on the [2 pow (a-p)] grid but not on the [4 pow (a-p)] one     *)
have Ff : format (g + 2 * d) by rewrite -Heq; apply: generic_format_round.
have Hfn0 : g + 2 * d <> 0 by move: Hd Hgge HGA; split_Rabs; lra.
have H2d : is_imul (2 * d) (pow (a - p + 1))
  by case: Hpm => ->; rewrite Hstep2; [exists 1%Z | exists (-1)%Z]; lra.
have Hnot4 : ~ is_imul (g + 2 * d) (pow (a - p + 2)).
  move=> Him4.
  have Himg4 : is_imul g (pow (a - p + 2))
    by apply: is_imul_pow_le Himg _; lia.
  have Him2d : is_imul (2 * d) (pow (a - p + 2)).
    have -> : 2 * d = (g + 2 * d) - g by lra.
    by apply: is_imul_minus.
  have H2dn0 : 2 * d <> 0 by lra.
  have Hge := is_imul_pow_le_abs Him2d H2dn0.
  by move: Hge Hd; rewrite Hstep4; split_Rabs; lra.
(* which caps its [uls], hence its [ulp], hence its magnitude                 *)
have Hulscap : uls (g + 2 * d) < pow (a - p + 2).
  case: (Rle_lt_dec (pow (a - p + 2)) (uls (g + 2 * d))) => [Hle|//].
  case: Hnot4.
  have [c Hc] := uls_pow Hfn0.
  have Him := uls_imul Ff; rewrite Hc in Him Hle.
  by apply: is_imul_pow_le Him _; apply: (le_bpow beta).
have Hmagcap : Rabs (g + 2 * d) < pow (a + 1).
  have Hulp : ulp (g + 2 * d) < pow (a - p + 2)
    by apply: Rle_lt_trans (ulp_le_ulps _) Hulscap.
  rewrite ulp_neq_0 // /cexp /FLX_exp in Hulp.
  have Hmg := lt_bpow _ _ _ Hulp.
  apply: Rlt_le_trans (bpow_mag_gt beta (g + 2 * d)) _.
  by apply: bpow_le; lia.
have Hstepa : pow (a + 1) = 2 * pow a.
  have H2 : (2 = pow 1) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite H2 -bpow_plus; congr bpow; lia.
(* being a multiple of [pow a], [g] is then [pow a] or [pow (a+1)]            *)
have Hgcases : Rabs g = pow a \/ Rabs g = pow (a + 1).
  case: Himg Hgge Hmagcap => m -> Hgge Hmagcap.
  have Hb : Rabs (IZR m) * pow a < 3 * pow a.
    have Hb1 : Rabs (IZR m * pow a) < 2 * pow a + 2 * pow (a - p)
      by move: Hmagcap Hd; rewrite Hstepa; split_Rabs; lra.
    by move: Hb1; rewrite Rabs_mult [Rabs (pow a)]Rabs_pos_eq //; lra.
  have Hb2 : pow a <= Rabs (IZR m) * pow a
    by move: Hgge; rewrite Rabs_mult [Rabs (pow a)]Rabs_pos_eq //.
  have Hm3 : (Z.abs m < 3)%Z by apply: lt_IZR; rewrite abs_IZR; nra.
  have Hm1 : (1 <= Z.abs m)%Z by apply: le_IZR; rewrite abs_IZR; nra.
  have HX : Rabs (IZR m) = 1 \/ Rabs (IZR m) = 2.
    rewrite -abs_IZR.
    have Hm : (Z.abs m = 1 \/ Z.abs m = 2)%Z by lia.
    by case: Hm => ->; [left | right]; lra.
  rewrite Rabs_mult [Rabs (pow a)]Rabs_pos_eq //.
  by case: HX => ->; [left | right]; lra.
have Hopp := @RN_opp_sym p choice choice_sym.
(* [pow a - pow (a-p)] is a float, so the step DOWN from [pow a] is exact     *)
have Fpred : format (pow a - pow (a - p)).
  have Fpow : format (pow a) by apply: format_pow.
  have := generic_format_pred beta fexp _ Fpow.
  by rewrite pred_bpow /FLX_exp; apply; apply: FLX_exp_valid; lia.
have Hmide := @RN_midpoint_even p Hp2 choice a Heven.
have Hmidlo : RND (pow (a + 1) - pow (a - p)) = pow (a + 1).
  have -> : (a - p = a + 1 - p - 1)%Z by lia.
  by apply: RN_midpoint_even_lo.
case: Hgcases => Hg.
  have Hgpm : g = pow a \/ g = - pow a by move: Hg; split_Rabs; lra.
  case: Hgpm => Hgv; case: Hpm => Hdv; rewrite Hgv Hdv in Heq.
  - by move: Heq; rewrite Hmide; lra.
  - move: Heq.
    have -> : pow a + - pow (a - p) = pow a - pow (a - p) by lra.
    by rewrite round_generic //; lra.
  - move: Heq.
    have -> : - pow a + pow (a - p) = - (pow a - pow (a - p)) by lra.
    by rewrite round_generic; [lra | apply: generic_format_opp].
  move: Heq.
  have -> : - pow a + - pow (a - p) = - (pow a + pow (a - p)) by lra.
  by rewrite Hopp Hmide; lra.
(* [|g| = pow (a+1)]: the tie one notch up, and the [uls] cap kills the rest  *)
have Hgpm : g = pow (a + 1) \/ g = - pow (a + 1) by move: Hg; split_Rabs; lra.
case: Hgpm => Hgv; case: Hpm => Hdv; rewrite Hgv Hdv in Heq Hmagcap.
- by move: Hmagcap; split_Rabs; lra.
- move: Heq.
  have -> : pow (a + 1) + - pow (a - p) = pow (a + 1) - pow (a - p) by lra.
  by rewrite Hmidlo; lra.
- move: Heq.
  have -> : - pow (a + 1) + pow (a - p) = - (pow (a + 1) - pow (a - p))
    by lra.
  by rewrite Hopp Hmidlo; lra.
by move: Hmagcap; split_Rabs; lra.
Qed.

Lemma RN_imul_no_flip (g d : R) (a : Z) :
  ties_to_even choice -> format g -> g <> 0 -> is_imul g (pow a) ->
  Rabs d = pow (a - p) ->
  RND (g + d) = g \/ RND (g + d) = g + d.
Proof.
move=> Heven Fg gn0 Himg Hd.
have HGp := bpow_gt_0 beta (a - p).
have Hnt := RN_imul_no_tie Heven Fg gn0 Himg Hd.
have [_ Hnear] := round_N_pt beta fexp choice (g + d).
have H1 : Rabs (RND (g + d) - (g + d)) <= pow (a - p).
  have := Hnear _ Fg.
  by rewrite (_ : g - (g + d) = - d); [rewrite Rabs_Ropp Hd | lra].
have Hpm : d = pow (a - p) \/ d = - pow (a - p) by move: Hd; split_Rabs; lra.
have Himd : is_imul d (pow (a - p))
  by case: Hpm => ->; [exists 1%Z | exists (-1)%Z]; lra.
have Himg' : is_imul g (pow (a - p)) by apply: is_imul_pow_le Himg _; lia.
have Himdiff : is_imul (RND (g + d) - g) (pow (a - p)).
  apply: is_imul_minus => //.
  by apply: is_imul_pow_round; apply: is_imul_add.
case: Himdiff => m Hm.
have Hm2 : (Z.abs m <= 2)%Z.
  apply: le_IZR; rewrite abs_IZR.
  have Hb : Rabs (IZR m) * pow (a - p) <= 2 * pow (a - p).
    have -> : Rabs (IZR m) * pow (a - p) = Rabs (RND (g + d) - g)
      by rewrite Hm Rabs_mult [Rabs (pow _)]Rabs_pos_eq //; lra.
    by move: H1 Hd; split_Rabs; lra.
  by nra.
have Hmc : (m = -2 \/ m = -1 \/ m = 0 \/ m = 1 \/ m = 2)%Z by lia.
set r := RND (g + d) in Hnt H1 Hm *.
by case: Hpm => Hdv; rewrite Hdv in H1 Hnt *;
   case: Hmc => [Hmv|[Hmv|[Hmv|[Hmv|Hmv]]]]; rewrite Hmv in Hm;
   first [ by left; move: H1 Hm; split_Rabs; lra
         | by right; move: H1 Hm; split_Rabs; lra
         | by case: Hnt; move: H1 Hm; split_Rabs; lra ].
Qed.


(* ---- 5.2, "at the left of i" -------------------------------------------*)

(* Draft 5.2: "we saw that x_{i-1} = 1-u and x_{i-2} < 1, so                  *)
(* |x_{i-2}| = 1-u".  The pinning gives [|x_i| = A - G] (our index [i] is     *)
(* the draft's [i-1]); [sorted_mag] pushes that up to the previous input,     *)
(* while being a float below [A] pushes it back down -- so the previous       *)
(* input has exactly the same magnitude.                                      *)
Lemma vecSum_left_x_eq (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1) = pow (k + p) - pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have [_ HRc _ _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
have [i' Hi'i Hlt] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n i') Hi'i.
have Hi'le : (i' <= i.-1)%N by rewrite -ltnS prednK.
have Hi1Ll : (i.-1 < size l)%N by apply: leq_ltn_trans (leq_pred i) iLl.
(* a float strictly below [A] is at most its predecessor [A - G]              *)
have Hup : Rabs (nth 0 l i.-1) <= pow (k + p) - pow k.
  have Fx : format (nth 0 l i.-1) by apply: Hf; apply: mem_nth.
  have H := abs_le_pred_of_lt Fx (Hlt i.-1 Hi'le Hi1Ll).
  by rewrite (_ : (k + p - p = k)%Z) in H; [|lia].
(* and isotony keeps it at least [|x_i| = A - G]                              *)
have Hlo : Rabs (nth 0 l i) <= Rabs (nth 0 l i.-1).
  by apply: sorted_mag_le_nth Hsort (leq_pred i) iLl.
by move: Hlo; rewrite HRc; lra.
Qed.


(* Draft 5.2's split "case x_{i-2} = -1+u" / "case x_{i-2} = 1-u": with       *)
(* [|x_{i-1}| = A - G] and [|s_i| = A], the pair either cancels (sum [G],     *)
(* the draft's [-1+u] case) or reinforces (sum [2A - G], its [1-u]            *)
(* case).  Stated on the SUM, so no sign bookkeeping leaks out.               *)
Lemma vecSum_left_sum_cases (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) = pow k \/
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have HX :=
  vecSum_left_x_eq Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [HRs _ _ _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                              Hviol.
have HG := bpow_gt_0 beta k.
have HA := bpow_gt_0 beta (k + p).
have HGA : pow k < pow (k + p) by apply: bpow_lt; lia.
have H1 : nth 0 l i.-1 = pow (k + p) - pow k \/
          nth 0 l i.-1 = - (pow (k + p) - pow k).
  by move: HX; split_Rabs; lra.
have H2 : (vecSumAux (drop i l)).2 = pow (k + p) \/
          (vecSumAux (drop i l)).2 = - pow (k + p).
  by move: HRs; split_Rabs; lra.
by case: H1 => ->; case: H2 => ->; [right|left|left|right];
   split_Rabs; lra.
Qed.

(* Draft 5.2, case [x_{i-2} = -1+u]: "then e_{i-1} = 0 and s_{i-2} = u".      *)
(* The cancelling sum is [+/- G], already a float, so the 2Sum at that        *)
(* step is EXACT: the running sum takes the value and the error is [0].       *)
Lemma vecSum_left_opp (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) = pow k ->
  Rabs (vecSumAux (drop i.-1 l)).2 = pow k /\ nth 0 (vecSum l) i = 0.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hsum.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have [i' Hi'i _] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n i') Hi'i.
have Hpk : (i.-1.+1 = i)%N by rewrite prednK.
have Hsz : (i.-1.+1 < size l)%N by rewrite Hpk.
(* the cancelling sum is a float, so the step rounds exactly                  *)
have HG := bpow_gt_0 beta k.
have Fsum : format (nth 0 l i.-1 + (vecSumAux (drop i l)).2).
  have H : nth 0 l i.-1 + (vecSumAux (drop i l)).2 = pow k \/
           nth 0 l i.-1 + (vecSumAux (drop i l)).2 = - pow k.
    by move: Hsum; split_Rabs; lra.
  case: H => ->; first by apply: format_pow.
  by apply/generic_format_opp/format_pow.
have Hrnd := vecSum_run_rnd Hsz.
have Hstep := vecSum_run_step Hsz Hf.
rewrite Hpk in Hrnd Hstep.
have Hs : (vecSumAux (drop i.-1 l)).2 =
          nth 0 l i.-1 + (vecSumAux (drop i l)).2.
  by rewrite Hrnd round_generic.
split; first by rewrite Hs.
by move: Hstep; rewrite Hs; lra.
Qed.


(* Draft 5.2, case [x_{i-2} = 1-u]: "then e_{i-1} = -u and s_{i-2} = 2".      *)
(* Here the pair reinforces, giving the sum [2A - G] -- exactly the tie       *)
(* just below [2A], which ties-to-even sends UP to [2A]                       *)
(* ([RN_midpoint_even_lo]).  The 2Sum error is then the discarded [G].        *)
(* The SIGNED form, which is what 5.3 needs: the draft writes this case as    *)
(* "[e_{i-1} = -u] and [s_{i-2} = 2]", and the two signs are not              *)
(* independent -- the discarded [G] is taken AWAY from the running sum, so    *)
(* [e_i] always carries the sign OPPOSITE to [s_{i-1}].  5.3's cancellation   *)
(* [|eps_{i_0} + e_{i_1}| <= 3/8 u] rests on exactly this.                    *)
Lemma vecSum_left_same_signed (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k ->
  [/\ (vecSumAux (drop i.-1 l)).2 = 2 * pow (k + p),
      (vecSumAux (drop i l)).2 = pow (k + p) &
      nth 0 (vecSum l) i = - pow k] \/
  [/\ (vecSumAux (drop i.-1 l)).2 = - (2 * pow (k + p)),
      (vecSumAux (drop i l)).2 = - pow (k + p) &
      nth 0 (vecSum l) i = pow k].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hsum.
have iLl : (i < size l)%N by apply: ltn_trans (ltnSn i) Hi.
have [i' Hi'i _] :=
  vecSum_inputs_lt_of_violation Hi Hf Hsort Hji Hej0 Huls Hviol.
have Hi0 : (0 < i)%N by apply: leq_ltn_trans (leq0n i') Hi'i.
have Hpk : (i.-1.+1 = i)%N by rewrite prednK.
have Hsz : (i.-1.+1 < size l)%N by rewrite Hpk.
(* [2A = pow(k+p+1)] and [G = pow((k+p+1) - p - 1)]                           *)
have H2A : 2 * pow (k + p) = pow (k + p + 1).
  have -> : pow (k + p + 1) = pow (k + p) * pow 1.
    by rewrite -bpow_plus; congr bpow; lia.
  by rewrite bpow_1 /=; lra.
have HG : pow k = pow (k + p + 1 - p - 1).
  by congr bpow; lia.
(* the tie rounds up, in either sign                                          *)
have Hmid : RND (2 * pow (k + p) - pow k) = 2 * pow (k + p).
  by rewrite H2A HG; apply: RN_midpoint_even_lo.
have Hmidn : RND (- (2 * pow (k + p) - pow k)) = - (2 * pow (k + p)).
  by rewrite (@RN_opp_sym p choice choice_sym) Hmid.
have Hrnd := vecSum_run_rnd Hsz.
have Hstep := vecSum_run_step Hsz Hf.
rewrite Hpk in Hrnd Hstep.
have HA := bpow_gt_0 beta (k + p).
have HGp := bpow_gt_0 beta k.
have H : nth 0 l i.-1 + (vecSumAux (drop i l)).2 =
         2 * pow (k + p) - pow k \/
         nth 0 l i.-1 + (vecSumAux (drop i l)).2 =
         - (2 * pow (k + p) - pow k).
  by move: Hsum; split_Rabs; lra.
(* the pair REINFORCES, so [s_i] carries the sign of the sum: the other       *)
(* sign would need [|x_{i-1}| = 3A - G], well past its own bound.             *)
have HX := vecSum_left_x_eq Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have [HRs _ _ _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
case: H => HE; rewrite HE in Hrnd Hstep.
  rewrite Hmid in Hrnd; left; split => //.
    by move: HX HRs HE; split_Rabs; lra.
  by move: Hstep; rewrite Hrnd; lra.
rewrite Hmidn in Hrnd; right; split => //.
  by move: HX HRs HE; split_Rabs; lra.
by move: Hstep; rewrite Hrnd; lra.
Qed.

(* The magnitudes alone, as the rest of 5.2 consumes them.                    *)
Lemma vecSum_left_same (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k ->
  Rabs (vecSumAux (drop i.-1 l)).2 = 2 * pow (k + p) /\
  Rabs (nth 0 (vecSum l) i) = pow k.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hsum.
have HA := bpow_gt_0 beta (k + p).
have HGp := bpow_gt_0 beta k.
case: (vecSum_left_same_signed Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol
                               Hsum) => [] [Hs _ He]; rewrite Hs He;
  by split; split_Rabs; lra.
Qed.

(* Draft 5.2/5.3 bridge: in the reinforcing case the two errors around the    *)
(* violation are TIED TOGETHER.  The pinning leaves [x_i] no choice of sign   *)
(* (the opposite one would put [|e_{i+1}|] near [2A]), so the exact step      *)
(* [s_i + e_{i+1} = x_i + s_{i+1}] collapses to [e_{i+1} = e_i + s_{i+1}].    *)
(* With [|s_{i+1}| <= 2u] and [5/8 u <= |e_{i+1}| <= u] that forces           *)
(* [e_{i+1}] to have the sign OPPOSITE to [e_i = -u], and the two of them     *)
(* to cancel down to the draft's [3/8 u].                                     *)
Lemma vecSum_left_same_err_opp (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k ->
  [/\ nth 0 (vecSum l) i.+1 =
        nth 0 (vecSum l) i + (vecSumAux (drop i.+1 l)).2,
      nth 0 (vecSum l) i * nth 0 (vecSum l) i.+1 < 0 &
      Rabs (nth 0 (vecSum l) i + nth 0 (vecSum l) i.+1) <= 3 / 8 * pow k].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Hsum.
have HG := bpow_gt_0 beta k.
have HA := bpow_gt_0 beta (k + p).
(* [A >= 16u] is the slack that kills the wrong sign of [x_i]                 *)
have HAG : 16 * pow k <= pow (k + p).
  have H16 : 16 * pow k = pow (k + 4).
    by rewrite bpow_plus /= /Z.pow_pos /=; lra.
  by rewrite H16; apply: bpow_le; lia.
have [HRs HRc _ HS2ge HP5] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
have Hstep := vecSum_run_step Hi Hf.
(* every error to the right of [i] is at most [u]                             *)
have HE1le : Rabs (nth 0 (vecSum l) i.+1) <= pow k.
  have Hgp := bpow_gt_0 beta (k - p + 1).
  case: (vecSum_right_of_i_cases Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                                 Hviol);
    by [case=> -> _; lra | case=> -> _; lra | lra].
have HS2le : Rabs (vecSumAux (drop i.+1 l)).2 <= 2 * pow k
  by move: HP5 HE1le; split_Rabs; lra.
case: (vecSum_left_same_signed Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol
                               Hsum) => [] [_ HS1 HE].
  (* [s_i = A], so [x_i = A - u] and [e_{i+1} = s_{i+1} - u]                  *)
  have HXv : nth 0 l i = pow (k + p) - pow k.
    by move: HRc HS1 HS2le HE1le Hstep HAG; split_Rabs; lra.
  have HE1v : nth 0 (vecSum l) i.+1 = (vecSumAux (drop i.+1 l)).2 - pow k
    by move: Hstep; rewrite HS1 HXv; lra.
  have HS2g : pow k <= (vecSumAux (drop i.+1 l)).2
    by move: HS2ge HE1le; rewrite HE1v; split_Rabs; lra.
  have HE1pos : 5 / 8 * pow k <= nth 0 (vecSum l) i.+1
    by move: Hviol; rewrite HE1v; split_Rabs; lra.
  split; first by rewrite HE1v HE; lra.
    by rewrite HE; nra.
  by rewrite HE HE1v; split_Rabs; lra.
(* the mirror image                                                           *)
have HXv : nth 0 l i = - (pow (k + p) - pow k).
  by move: HRc HS1 HS2le HE1le Hstep HAG; split_Rabs; lra.
have HE1v : nth 0 (vecSum l) i.+1 = (vecSumAux (drop i.+1 l)).2 + pow k
  by move: Hstep; rewrite HS1 HXv; lra.
have HS2g : (vecSumAux (drop i.+1 l)).2 <= - pow k
  by move: HS2ge HE1le; rewrite HE1v; split_Rabs; lra.
have HE1neg : nth 0 (vecSum l) i.+1 <= - (5 / 8 * pow k)
  by move: Hviol; rewrite HE1v; split_Rabs; lra.
split; first by rewrite HE1v HE; lra.
  by rewrite HE; nra.
by rewrite HE HE1v; split_Rabs; lra.
Qed.

(* Draft 5.2/5.3, the reinforcing case again: "all the [e_i],                 *)
(* [i <= i_1-2], are divisible by 1".  With [i = 2] that is [s_0] and         *)
(* [e_1], and the source of the divisibility is [pairwise_ulp] at             *)
(* [(x_0, x_2)]: [|x_2| = A - u] pushes [ulp(x_0)] past [A/2], so [x_0] is    *)
(* a multiple of [A]; so is [s_1 = +/- 2A], hence so are their rounded sum    *)
(* [s_0] and its error [e_1].  This is what pins the walk's remainder to      *)
(* the [A] grid, and so (5.3) what stops a tie from flipping                  *)
(* [eps_{i_0}]: a multiple of [A] has an EVEN mantissa at scale [2u].         *)
Lemma vecSum_left_same_imul (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N -> i = 2%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k ->
  [/\ is_imul (nth 0 l 0) (pow (k + p)),
      is_imul (vecSumAux (drop 1 l)).2 (pow (k + p)),
      is_imul (nth 0 (vecSum l) 0) (pow (k + p)) &
      is_imul (nth 0 (vecSum l) 1) (pow (k + p))].
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hji Heqi Hej0 Huls Hviol Hsum.
have HG := bpow_gt_0 beta k.
have HA := bpow_gt_0 beta (k + p).
have HAG : 16 * pow k <= pow (k + p).
  have H16 : 16 * pow k = pow (k + 4).
    by rewrite bpow_plus /= /Z.pow_pos /=; lra.
  by rewrite H16; apply: bpow_le; lia.
have Hhalf : 2 * pow (k + p - 1) = pow (k + p).
  have H2 : (2 = pow 1) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite H2 -bpow_plus; congr bpow; lia.
have Hsz2 : (0.+2 < size l)%N by rewrite -Heqi; apply: ltnW.
have Hsz1 : (0.+1 < size l)%N by apply: ltnW.
have [_ HRc _ _ _] :=
  vecSum_pinning_of_violation Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol.
rewrite Heqi in HRc.
(* [s_1 = +/- 2A] is a multiple of [A]                                        *)
have HS1imul : is_imul (vecSumAux (drop 1 l)).2 (pow (k + p)).
  case: (vecSum_left_same_signed Heven Hi Hf Hnz Hsort Hpair Hji Hej0 Huls
                                 Hviol Hsum) => [] [HS0 _ _];
    rewrite Heqi /= in HS0.
    by exists 2%Z; rewrite HS0.
  by exists (-2)%Z; rewrite HS0; lra.
(* and so is [x_0], because [pairwise_ulp] must clear [|x_2| = A - u]         *)
have Fx0 : format (nth 0 l 0) by apply: Hf; apply: mem_nth; apply: ltnW.
have Hx2n0 : nth 0 l 2 <> 0 by apply: Hnz.
have Hulpx0 : pow (k + p) - pow k < ulp (nth 0 l 0).
  case: (Hpair 0%N Hsz2) => [Hzz|Hlt]; first by case: Hx2n0.
  by move: Hlt; rewrite HRc.
have Hx0 : pow (k + p - 1 + p) <= Rabs (nth 0 l 0).
  case: (Rle_lt_dec (pow (k + p - 1 + p)) (Rabs (nth 0 l 0))) => // Hlt.
  by have := bound_ulp_FLX Hp2 Hlt; lra.
have Hmag : (k + 2 * p <= mag beta (nth (0:R) l 0))%Z.
  apply: mag_ge_bpow.
  by have -> : (k + 2 * p - 1 = k + p - 1 + p)%Z by lia.
have Hcexp : (k + p <= cexp (nth (0:R) l 0))%Z
  by rewrite /cexp /FLX_exp; lia.
have Himx0 : is_imul (nth 0 l 0) (pow (k + p))
  by apply: is_imul_pow_le (format_imul_cexp Fx0) Hcexp.
(* so are the rounded sum [s_0] and the error [e_1] it discards               *)
have Hstep := vecSum_run_step Hsz1 Hf.
have Hrnd := vecSum_run_rnd Hsz1.
rewrite drop0 in Hstep Hrnd.
have Hims0 : is_imul (nth 0 (vecSum l) 0) (pow (k + p)).
  rewrite vecSum_nth0 Hrnd.
  by apply: is_imul_pow_round; apply: is_imul_add.
have He1 : nth 0 (vecSum l) 1 =
           (nth 0 l 0 + (vecSumAux (drop 1 l)).2) -
           RND (nth 0 l 0 + (vecSumAux (drop 1 l)).2) by lra.
have Hime1 : is_imul (nth 0 (vecSum l) 1) (pow (k + p)).
  rewrite He1; apply: is_imul_minus; first by apply: is_imul_add.
  by apply: is_imul_pow_round; apply: is_imul_add.
by split.
Qed.

(* Hence [i_0 = i_1 - 1] in this case: an [e_j] with [j <= i_1-2] would be a  *)
(* multiple of [A], so its [uls] would be at least [A], not the normalising   *)
(* [u].  With [i <= 2] the only offending pair is [j = 1, i = 2].             *)
Lemma vecSum_left_same_i0 (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (i.+1 < size l)%N -> {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (0 < j)%N -> (j < i)%N -> (i <= 2)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 l i.-1 + (vecSumAux (drop i l)).2) =
    2 * pow (k + p) - pow k ->
  False.
Proof.
move=> Heven Hi Hf Hnz Hsort Hpair Hj0 Hji Hi2 Hej0 Huls Hviol Hsum.
have Hji' : (j <= i)%N by apply: ltnW.
have Heqi : i = 2%N.
  apply/eqP; rewrite eqn_leq Hi2 /=.
  by move: Hj0 Hji; case: (i) => [|[|i']] //; case: (j).
have Heqj : j = 1%N by move: Hj0 Hji; rewrite Heqi; case: (j) => [|[|j']].
have [_ _ _ Hime1] :=
  vecSum_left_same_imul Heven Hi Hf Hnz Hsort Hpair Hji' Heqi Hej0 Huls Hviol
                        Hsum.
have Hsz2 : (0.+2 < size l)%N by rewrite -Heqi; apply: ltnW.
have Hsz1 : (0.+1 < size l)%N by apply: ltnW.
have Fe1 : format (nth 0 (vecSum l) 1).
  apply: (format_vecSum Hf); apply: mem_nth.
  by rewrite size_vecSum prednK //; apply: ltnW; apply: ltnW.
move: Hej0 Huls; rewrite Heqj => Hej0 Huls.
have := is_imul_uls_ge Fe1 Hej0 Hime1; rewrite Huls => Hle.
by have := le_bpow _ _ _ Hle; lia.
Qed.

(* ===========================================================================*)
(*  Step *3 (doc/thm6.md 5.3): the VSEB part.                                 *)
(*                                                                            *)
(*  The draft fixes [i_0] with [y_j = r_{i_0-1}] (so [eps_{i_0} <> 0]), lets  *)
(*  [i_1] the index of the first nonzero [e_i] after [e_{i_0}], normalises    *)
(*  [uls(e_{i_0}) = u], and records the two opening facts                     *)
(*  [|eps_{i_0}| >= u] and [ulp(y_j) >= 2 |eps_{i_0}|].  Every subsequent     *)
(*  estimate then has the SAME shape: bound [|e_{i_1}|] by a multiple of      *)
(*  [|eps_{i_0}|], add, and round.                                            *)
(* ===========================================================================*)

(* Draft 5.3, the recurring estimate.  With [ulp(y_j) >= 2|eps|] (the         *)
(* opening fact) and [|e| <= c * |eps|], the next emitted word                *)
(* [r = RND(eps + e)] obeys [|r| <= (1+c)/2 * ulp(y_j)].  Instantiating       *)
(* [c] reproduces the draft's constants: [c = 5/8] gives the 13/16            *)
(* bound, [c = 1/2] gives 3/4, [c = 1/4] gives 5/8.                           *)
Lemma vseb_next_le (yj eps e : R) (c : R) :
  2 * Rabs eps <= ulp yj ->
  Rabs e <= c * Rabs eps ->
  0 <= c ->
  format ((1 + c) / 2 * ulp yj) ->
  Rabs (RND (eps + e)) <= (1 + c) / 2 * ulp yj.
Proof.
move=> Hulp He Hc FB.
apply: Rabs_round_le_r => //.
have Habs : Rabs (eps + e) <= Rabs eps + Rabs e by apply: Rabs_triang.
have Hpe : 0 <= Rabs eps by apply: Rabs_pos.
by nra.
Qed.


(* Draft 5.3 opening, first fact: "[|eps_{i_0}| >= u]".  Scale-free, with     *)
(* the draft's normalisation [uls(e_{i_0}) = u] kept symbolic: the emitted    *)
(* remainder has [uls] at least that of the error consumed                    *)
(* ([TwoSum_err_uls_ge]), and [uls] is below the absolute value.              *)
Lemma vseb_emit_abs_ge (eps e : R) :
  format eps -> format e -> eps <> 0 -> e <> 0 ->
  uls e <= uls eps -> dwl (TwoSum eps e) <> 0 ->
  uls e <= Rabs (dwl (TwoSum eps e)).
Proof.
move=> Feps Fe epsn0 en0 Hle Hn0.
apply: Rle_trans (TwoSum_err_uls_ge Feps Fe epsn0 en0 Hle Hn0) _.
apply: uls_le_abs; last exact: Hn0.
have := format_TwoSum Feps Fe.
by case: (TwoSum eps e) => r et /= [_ Fet].
Qed.

(* Draft 5.3 opening, second fact: "[ulp(y_j) >= 2 |eps_{i_0}|]".  This is    *)
(* just the 2Sum magnitude property [|err| <= ulp(hi)/2].                     *)
Lemma vseb_emit_ulp_ge (eps e : R) :
  format eps -> format e ->
  2 * Rabs (dwl (TwoSum eps e)) <= ulp (dwh (TwoSum eps e)).
Proof.
move=> Feps Fe.
have := magnitude_TwoSum Feps Fe.
by case: (TwoSum eps e) => r et /=; lra.
Qed.


(* [p >= 4] in the form the constant bounds need it: 13, 5 and 3 all fit      *)
(* in [p] bits because [2^p >= 16].                                           *)
Lemma pow2_ge_16 : (16 <= 2 ^ p)%Z.
Proof.
have -> : (16 = 2 ^ 4)%Z by [].
by apply: Z.pow_le_mono_r; lia.
Qed.

(* A scaled integer with fewer than [p] bits is a float.                      *)
Lemma format_mult_pow (m e : Z) :
  (Z.abs m < 2 ^ p)%Z -> format (IZR m * pow e).
Proof.
move=> Hm.
have Hp2p : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
apply: (@imul_format beta p Hp2 (IZR m * pow e) e (pow (p + e))).
- by exists m.
- rewrite Rabs_mult (Rabs_pos_eq (pow e)); last by apply: bpow_ge_0.
  rewrite bpow_plus; apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
  by rewrite -abs_IZR Hp2p; apply: IZR_le; lia.
by apply: Rle_refl.
Qed.

(* The draft's constants (13/16, 3/4, 5/8, 1-u, 1-2u) times an [ulp] are      *)
(* floats: each is a short integer scaled by a power of two.                  *)
Lemma format_frac_ulp (m e : Z) (y : R) :
  (Z.abs m < 2 ^ p)%Z -> format (IZR m * pow e * ulp y).
Proof.
move=> Hm.
case: (Req_dec y 0) => [->|yn0].
  by rewrite ulp_FLX_0 Rmult_0_r; apply: generic_format_0.
rewrite ulp_neq_0 // Rmult_assoc -bpow_plus.
exact: format_mult_pow.
Qed.

(* Draft 5.3, the estimate in the form the case study actually uses: the      *)
(* draft always bounds [|e_{i_1}|] by a multiple of [u] and then leans on     *)
(* the opening fact [|eps_{i_0}| >= u].  Here [t] plays [u] (kept             *)
(* symbolic), so [|e| <= c t <= c |eps|] and [vseb_next_le] applies.          *)
Lemma vseb_next_le_uls (yj eps e t c : R) :
  0 <= c -> t <= Rabs eps ->
  2 * Rabs eps <= ulp yj ->
  Rabs e <= c * t ->
  format ((1 + c) / 2 * ulp yj) ->
  Rabs (RND (eps + e)) <= (1 + c) / 2 * ulp yj.
Proof.
move=> Hc Ht Hulp He FB.
apply: vseb_next_le => //.
by apply: Rle_trans He _; apply: Rmult_le_compat_l.
Qed.

(* ---- the draft's five constants, instantiated ---------------------------*)


(* [1 - k u] times an [ulp] is a float ([= (2^p - k) * pow(-p) * ulp]);       *)
(* this covers the draft's [1 - u] and [1 - 2u] bounds.                       *)
Lemma format_1_sub_ku_ulp (k : Z) (y : R) :
  (1 <= k)%Z -> (k < 2 ^ p)%Z -> format ((1 - IZR k * u) * ulp y).
Proof.
move=> Hk1 Hk2.
have Hpp2 : pow p = IZR (2 ^ p) by rewrite -IZR_Zpower; [congr IZR|lia].
have Hu : u = pow (- p).
  have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
  have H1p : pow (1 - p) = 2 * pow (- p).
    have -> : (1 - p = 1 + - p)%Z by lia.
    by rewrite bpow_plus bpow_1 /=; lra.
  by lra.
have Hpm : pow p * pow (- p) = 1.
  by rewrite -bpow_plus (_ : (p + - p = 0)%Z) ?(pow0E beta); [|lia].
have -> : (1 - IZR k * u) * ulp y = IZR (2 ^ p - k) * pow (- p) * ulp y.
  rewrite minus_IZR -Hpp2 Hu.
  by rewrite -{1}Hpm; ring.
by apply: format_frac_ulp; rewrite Z.abs_eq; lia.
Qed.

(* Draft 5.3, case [i_1 >= 4]: "[|eps_{i_0}| + |e_{i_1}| <=                   *)
(* |eps_{i_0}| + (u - 2u^2) <= (2 - 2u)|eps_{i_0}|], so                       *)
(* [|r_{i_1-1}| <= (1 - u) ulp(y_j)]".                                        *)
Lemma vseb_next_1mu (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= (1 - 2 * u) * t ->
  Rabs (RND (eps + e)) <= (1 - u) * ulp yj.
Proof.
move=> Ht Hulp He.
have Hu0 : 0 < u by apply: u_gt_0.
have H12u : 0 <= 1 - 2 * u.
  have -> : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
  have h1p : (1 - p <= 0)%Z by lia.
  by have := bpow_le beta (1 - p) 0 h1p; rewrite (pow0E beta); lra.
have -> : (1 - u) * ulp yj = (1 + (1 - 2 * u)) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + (1 - 2 * u)) / 2 * ulp yj = (1 - IZR 1 * u) * ulp yj.
  by rewrite /=; lra.
by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
Qed.

(* Draft 5.3, case [i_1 >= 4], sub-case [|e_{i_1}| <= u - 4u^2]: "then we     *)
(* have the stronger estimate [|r_{i_1-1}| <= (1 - 2u) ulp(y_j)]".            *)
Lemma vseb_next_1m2u (yj eps e t : R) :
  t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= (1 - 4 * u) * t ->
  Rabs (RND (eps + e)) <= (1 - 2 * u) * ulp yj.
Proof.
move=> Ht Hulp He.
have Hu0 : 0 < u by apply: u_gt_0.
have H14u : 0 <= 1 - 4 * u.
  have H4u : 4 * u = pow (2 - p).
    have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
    have Hsp : pow (2 - p) = 2 * pow (1 - p).
      have -> : (2 - p = 1 + (1 - p))%Z by lia.
      by rewrite bpow_plus bpow_1 /=; lra.
    by rewrite Hsp; lra.
  rewrite H4u.
  have h2p : (2 - p <= 0)%Z by lia.
  by have := bpow_le beta (2 - p) 0 h2p; rewrite (pow0E beta); lra.
have -> : (1 - 2 * u) * ulp yj = (1 + (1 - 4 * u)) / 2 * ulp yj by lra.
apply: vseb_next_le_uls Ht Hulp He _; first by lra.
have -> : (1 + (1 - 4 * u)) / 2 * ulp yj = (1 - IZR 2 * u) * ulp yj.
  by rewrite /=; lra.
by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
Qed.


(* ---- 5.3, case [i_1 >= 4] ----------------------------------------------*)

(* Draft 5.3, case [i_1 >= 4], sub-case [|e_{i_1}| = u - 2u^2]: "then         *)
(* y_{j+1} = r_{i_1-1} < ulp(y_j)".  The [(1-u)] bound already sits           *)
(* strictly below [ulp(y_j)]; the [ulp] is positive because it dominates      *)
(* [2|eps_{i_0}| >= 2t > 0].                                                  *)
Lemma vseb_next_lt_of_1mu (yj eps e t : R) :
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= (1 - 2 * u) * t ->
  Rabs (RND (eps + e)) < ulp yj.
Proof.
move=> Ht0 Ht Hulp He.
have Hu0 : 0 < u by apply: u_gt_0.
have Hulp0 : 0 < ulp yj by lra.
have H := vseb_next_1mu Ht Hulp He.
by nra.
Qed.

(* Draft 5.3, case [i_1 >= 4], sub-case [|e_{i_1}| <= u - 4u^2]: after the    *)
(* [(1-2u)] estimate the draft absorbs one more error,                        *)
(* [|e_{i_1+1}| <= u^2 <= u/2 ulp(y_j)], and concludes                        *)
(* [|y_{j+1}| < ulp(y_j)].  The sum is at most [(1 - 3u/2) ulp(y_j)],         *)
(* hence at most the FLOAT [(1-u) ulp(y_j)], which rounding cannot            *)
(* escape -- and that is still strictly below [ulp(y_j)].                     *)
Lemma vseb_merge_lt (yj r e' : R) :
  0 < ulp yj ->
  Rabs r <= (1 - 2 * u) * ulp yj ->
  Rabs e' <= / 2 * u * ulp yj ->
  Rabs (RND (r + e')) < ulp yj.
Proof.
move=> Hulp0 Hr He.
have Hu0 : 0 < u by apply: u_gt_0.
have Hsum : Rabs (r + e') <= (1 - IZR 1 * u) * ulp yj.
  apply: Rle_trans (Rabs_triang _ _) _.
  by rewrite /=; nra.
have HF : format ((1 - IZR 1 * u) * ulp yj).
  by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
have H : Rabs (RND (r + e')) <= (1 - 1 * u) * ulp yj.
  by apply: Rabs_round_le_r.
by nra.
Qed.


(* ---- 5.3, "adding at most 3 of them" ------------------------------------*)

(* The counting: a block of at most [n] further errors, each below [d],       *)
(* adds at most [n * d] to the mass carried past the head.                    *)
Lemma sumRabs_le_count (l : seq R) (n : nat) (d : R) :
  (size l <= n)%N -> 0 <= d -> (forall z, z \in l -> Rabs z <= d) ->
  sumRabs l <= INR n * d.
Proof.
elim: l n => [|a l IH] n Hsz Hd Hall /=.
  by have := pos_INR n; nra.
case: n Hsz => [//|n] Hsz.
have Ha : Rabs a <= d by apply: Hall; rewrite inE eqxx.
have Hrec : sumRabs l <= INR n * d.
  by apply: IH => // z zl; apply: Hall; rewrite inE zl orbT.
by rewrite S_INR; nra.
Qed.

(* Draft 5.3's block estimate, packaged: the emitted word [y_{j+1}] is the    *)
(* head of the continued VSEB walk, and [VSEB.vsebAux_head_leB] bounds it     *)
(* by any FLOAT [B] dominating [|eps_{i_0}|] plus the mass of the errors      *)
(* still to come.  So a [B] strictly below [ulp(y_j)] closes the case --      *)
(* this is the engine behind every "we are adding at most 3 of them".         *)
Lemma vseb_head_lt_of_mass (yj eps B : R) (l : seq R) :
  format eps -> {in l, forall z, format z} -> format B ->
  Rabs eps + sumRabs l <= B -> B < ulp yj ->
  Rabs (nth 0 (vsebAux eps l) 0) < ulp yj.
Proof.
move=> Feps Hl FB Hmass HB.
by apply: Rle_lt_trans (vsebAux_head_leB Feps Hl FB Hmass) HB.
Qed.

(* The same with the draft's split of the mass: the first error               *)
(* [e_{i_1}] is handled by the [(1+c)/2] estimate and the at-most-[n]         *)
(* later ones by [d] each, so [B = ((1+c)/2 + n d) ulp(y_j)] serves.          *)
Lemma vseb_head_lt_split (yj eps e B : R) (l : seq R) (n : nat) (d : R) :
  format eps -> format e -> {in l, forall z, format z} -> format B ->
  (size l <= n)%N -> 0 <= d -> (forall z, z \in l -> Rabs z <= d) ->
  Rabs eps + Rabs e + INR n * d <= B -> B < ulp yj ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl FB Hsz Hd Hall Hmass HB.
apply: vseb_head_lt_of_mass Feps _ FB _ HB.
  by move=> z; rewrite inE => /orP[/eqP->|zl]; [|apply: Hl].
have Hrec := sumRabs_le_count Hsz Hd Hall.
by rewrite /=; lra.
Qed.


(* ---- 5.3, case [0 < e_{i_1} < 5/8 u] -----------------------------------*)

(* [u] as a power of two, and the [p >= 4] consequence [u <= 1/16] that       *)
(* every sub-case below needs.                                                *)
Lemma uE_pow : u = pow (- p).
Proof.
have H2u : 2 * u = pow (1 - p) by rewrite /Fmore.u; lra.
have H1p : pow (1 - p) = 2 * pow (- p).
  have -> : (1 - p = 1 + - p)%Z by lia.
  by rewrite bpow_plus bpow_1 /=; lra.
by lra.
Qed.

Lemma u_le_inv16 : u <= / 16.
Proof.
have H16 : pow 4 = 16 by rewrite /= /Z.pow_pos /=; lra.
have Hle : pow (- p) <= pow (-4) by apply: bpow_le; lia.
have Hmul : pow 4 * pow (-4) = 1.
  by rewrite -bpow_plus (_ : (4 + -4 = 0)%Z) ?(pow0E beta); [|lia].
have H4 : 0 < pow (-4) by apply: bpow_gt_0.
rewrite uE_pow; nra.
Qed.

(* The sub-case shape at the level the draft actually argues at: what         *)
(* matters is the total MASS [M ulp(y_j)] of the errors after                 *)
(* [e_{i_1}], however it was obtained.  Three of the four sub-cases get       *)
(* it by counting ([M = 3d]); the [1/4 u] one needs the draft's sharper       *)
(* [|e_5| <= uls(e_4)] step, which only changes [M].                          *)
Lemma vseb_subcase_mass_lt (yj eps e : R) (l : seq R) (t c M : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  0 <= c -> Rabs e <= c * t ->
  sumRabs l <= M * ulp yj ->
  (1 + c) / 2 + M <= 1 - u ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp Hc He Hmass Hbound.
have Hu0 : 0 < u by apply: u_gt_0.
have HU : 0 < ulp yj by lra.
have HB : format ((1 - IZR 1 * u) * ulp yj).
  by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
apply: (vseb_head_lt_of_mass Feps _ HB).
- by move=> z; rewrite inE => /orP[/eqP->|zl]; [|apply: Hl].
- have Hec : Rabs e <= c * Rabs eps by apply: Rle_trans He _; nra.
  by rewrite /=; nra.
by nra.
Qed.
(* The shape shared by the sub-cases of [0 < e_{i_1} < 5/8 u]: the head       *)
(* pair contributes [(1+c)/2 ulp(y_j)] and the at most 3 later errors [d]     *)
(* each, so as soon as [(1+c)/2 + 3d <= 1 - u] the FLOAT [(1-u) ulp(y_j)]     *)
(* dominates the whole block and the emitted word lands below                 *)
(* [ulp(y_j)].  Instantiating [c] and [d] reproduces the draft's cases.       *)
Lemma vseb_subcase_lt (yj eps e : R) (l : seq R) (t c d : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  0 <= c -> Rabs e <= c * t ->
  (size l <= 3)%N -> 0 <= d ->
  (forall z, z \in l -> Rabs z <= d * ulp yj) ->
  (1 + c) / 2 + 3 * d <= 1 - u ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp Hc He Hsz Hd Hall Hbound.
have HU : 0 < ulp yj by lra.
have Hd0 : 0 <= d * ulp yj by nra.
have Htail := sumRabs_le_count Hsz Hd0 Hall.
have H3 : INR 3 = 3 by rewrite /=; lra.
rewrite H3 in Htail.
have Hmass : sumRabs l <= (3 * d) * ulp yj by lra.
apply: (vseb_subcase_mass_lt Feps Fe Hl Ht0 Ht Hulp Hc He Hmass).
by lra.
Qed.

(* Draft 5.3, sub-case [|e_{i_1}| > 1/2 u]: the tail errors are               *)
(* [<= u^2 <= u/2 ulp(y_j)], and "we are adding at most 3 of them".           *)
Lemma vseb_subcase_gt_half (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= 5 / 8 * t ->
  (size l <= 3)%N ->
  (forall z, z \in l -> Rabs z <= / 2 * u * ulp yj) ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hsz Hall.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
apply: vseb_subcase_lt Feps Fe Hl Ht0 Ht Hulp _ He Hsz _ Hall _; try lra.
Qed.

(* Draft 5.3, sub-case [1/2 u > |e_{i_1}|] and [|e_{i_1}| <> 1/4 u]: there    *)
(* [uls(e_{i_1}) <= 1/8 u], so the tail errors are [<= 1/8 u <= 1/16          *)
(* ulp(y_j)].  The count is exactly [3/4 + 3/16 = 15/16 <= 1 - u], tight      *)
(* at [p = 4].                                                                *)
Lemma vseb_subcase_lt_half (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= / 2 * t ->
  (size l <= 3)%N ->
  (forall z, z \in l -> Rabs z <= / 16 * ulp yj) ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hsz Hall.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
apply: vseb_subcase_lt Feps Fe Hl Ht0 Ht Hulp _ He Hsz _ Hall _; try lra.
Qed.


(* Draft 5.3, sub-case [|e_{i_1}| = 1/4 u].  Counting alone does NOT          *)
(* close here: [5/8 + 3*(1/8) = 1] exactly.  The draft repairs it with        *)
(* "we can not have |e_4| = |e_3| ... so |e_5| <= uls(e_4) <= 1/16            *)
(* ulp(y_j)", i.e. the last of the three is half the size, giving a tail      *)
(* mass of [1/8 + 1/8 + 1/16 = 5/16] and the total [5/8 + 5/16 = 15/16].      *)
(* The refined tail mass is taken as a hypothesis: establishing it is         *)
(* the draft's index-level argument about positions 3, 4 and 5.               *)
Lemma vseb_subcase_quarter (yj eps e : R) (l : seq R) (t : R) :
  format eps -> format e -> {in l, forall z, format z} ->
  0 < t -> t <= Rabs eps -> 2 * Rabs eps <= ulp yj ->
  Rabs e <= / 4 * t ->
  sumRabs l <= 5 / 16 * ulp yj ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl Ht0 Ht Hulp He Hmass.
have Hu16 := u_le_inv16.
by apply: vseb_subcase_mass_lt Feps Fe Hl Ht0 Ht Hulp _ He Hmass _; lra.
Qed.

(* ===========================================================================*)
(*  THE ASSEMBLY (doc/thm6.md 5.3): the draft's own route to the theorem.     *)
(*                                                                            *)
(*  The draft proves P-nonoverlap by showing, at every emit of the VSEB walk, *)
(*  that the NEXT emitted word falls below [ulp] of the one just emitted --   *)
(*  and it gets there by bounding [|eps| + (mass of the errors still to come)]*)
(*  by a float under that [ulp].  [vsebBlock] records exactly that per-emit   *)
(*  obligation along the walk, and [vsebAux_Pnonoverlap_block] turns it into  *)
(*  the conclusion.  Every 5.3 case lemma above produces such a bound, with   *)
(*  [B = (1 - u) ulp(y_j)].                                                   *)
(* ===========================================================================*)

Fixpoint vsebBlock (eps : R) (l : seq R) : Prop :=
  match l with
  | [::]    => True
  | [:: _]  => True
  | e :: l' =>
      let: DWR r et := TwoSum eps e in
      if Req_EM_T et 0 then vsebBlock r l'
      else Rabs (nth 0 (vsebAux et l') 0) < ulp r /\ vsebBlock et l'
  end.

(* One-step unfolding (by reflexivity), as for [vsebAux_consS].               *)
Lemma vsebBlock_consS eps e e2 l :
  vsebBlock eps [:: e, e2 & l] =
  (let: DWR r et := TwoSum eps e in
   if Req_EM_T et 0 then vsebBlock r (e2 :: l)
   else Rabs (nth 0 (vsebAux et (e2 :: l)) 0) < ulp r
        /\ vsebBlock et (e2 :: l)).
Proof. by []. Qed.

(* The driver: the per-emit float bound gives P-nonoverlap.  Same walk        *)
(* induction as [vsebAux_Pnonoverlap_mass], with [vsebAux_head_leB]           *)
(* supplying the emitted head bound instead of the mass machinery.            *)
Lemma vsebAux_Pnonoverlap_block eps l :
  format eps -> {in l, forall z, format z} ->
  vsebBlock eps l -> Pnonoverlap (vsebAux eps l).
Proof.
elim: l eps => [|e l' IH] eps epsF lF Hb.
  by move=> i; rewrite /= ltnS ltn0.
have Fe : format e by apply: lF; rewrite inE eqxx.
case: l' IH lF Hb => [|e2 l''] IH lF Hb.
  rewrite vsebAux_1; case E1 : (TwoSum eps e) => [y0 y1].
  move=> [|i] /= Hi; last by move: Hi; rewrite ltnS ltnS ltn0.
  have Hmag := magnitude_TwoSum epsF Fe; rewrite E1 /= in Hmag.
  case: (Req_dec y1 0) => [y10|y1n0]; first by left.
  right.
  have y0n0 : y0 <> 0.
    by move=> y00; apply: y1n0; move: Hmag;
       rewrite y00 ulp_FLX_0; split_Rabs; lra.
  have Hy : 0 < ulp y0 by rewrite ulp_neq_0 //; apply: bpow_gt_0.
  by lra.
rewrite vsebAux_consS; case E1 : (TwoSum eps e) => [r et].
have Hr : r = RND (eps + e) by have := TwoSum_hi eps e; rewrite E1.
move: Hb; rewrite vsebBlock_consS E1.
case: (Req_EM_T et 0) => [et0|etn0] Hb.
  apply: IH => //.
  - by rewrite Hr; apply: generic_format_round.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have Fet : format et
  by have H := format_TwoSum epsF Fe; rewrite E1 /= in H; case: H.
have Fl' : {in e2 :: l'', forall z, format z}
  by move=> z zI; apply: lF; rewrite inE zI orbT.
case: Hb => [Hnext Hbrec].
have Hrec : Pnonoverlap (vsebAux et (e2 :: l'')) by apply: IH.
move=> [|i] /= Hi.
  by right; exact: Hnext.
by apply: (Hrec i); move: Hi; rewrite ltnS.
Qed.



(* ---- carrying the draft's normalisation along the walk -----------------*)

(* [uls] is non-increasing along the nonzero VecSum errors.  (I had this      *)
(* as [vecSum_ulsMono] and deleted it with the scaffolding in PR #97 --       *)
(* wrongly: it is not scaffolding, it is what lets the draft's                *)
(* normalisation [uls(e_{i_0}) = u] survive from one emit to the next.)       *)
(* Immediate from [vecSum_tail_le_uls] and [uls z <= |z|].                    *)
Lemma vecSum_uls_le (l : seq R) (i m : nat) :
  ties_to_even choice -> {in l, forall z, format z} ->
  (forall k, (k < size l)%N -> nth 0 l k <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  (i < m)%N -> (m < size (vecSum l))%N ->
  nth 0 (vecSum l) i <> 0 -> nth 0 (vecSum l) m <> 0 ->
  uls (nth 0 (vecSum l) m) <= uls (nth 0 (vecSum l) i).
Proof.
move=> Heven Hfmt Hnz Hsort Hpair Him Hm Hni Hnm.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
apply: Rle_trans (uls_le_abs _ Hnm) _; first by apply/HfV/mem_nth.
exact: vecSum_tail_le_uls Heven Hfmt Hnz Hsort Hpair Him Hm Hni.
Qed.

(* Discharging one [vsebBlock] obligation from a MASS bound.  The draft's     *)
(* per-emit estimates are always of the form "the errors still to come are    *)
(* small next to the remainder": with [sumRabs tail <= (1 - 2u)|et|] and      *)
(* the free [2|et| <= ulp r] ([magnitude_TwoSum]), the block sits under       *)
(* [(2 - 2u)|et| <= (1 - u) ulp r], a float strictly below [ulp r], so        *)
(* [vsebAux_head_leB] puts the next emitted word there too.                   *)
Lemma vsebBlock_obligation (r et : R) (tail : seq R) :
  format et -> {in tail, forall z, format z} ->
  et <> 0 -> 2 * Rabs et <= ulp r ->
  sumRabs tail <= (1 - 2 * u) * Rabs et ->
  Rabs (nth 0 (vsebAux et tail) 0) < ulp r.
Proof.
move=> Fet Ftail etn0 Hulp Hmass.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Het : 0 < Rabs et by apply: Rabs_pos_lt.
have HU : 0 < ulp r by lra.
have FB : format ((1 - IZR 1 * u) * ulp r).
  by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
have Hb : Rabs et + sumRabs tail <= (1 - IZR 1 * u) * ulp r
  by rewrite /=; nra.
have Hhead := vsebAux_head_leB Fet Ftail FB Hb.
by move: Hhead; rewrite /=; nra.
Qed.

(* ---- locating the draft's [i_1] ----------------------------------------*)

(* An all-zero block carries no mass.                                         *)
Lemma sumRabs_eq0 (l : seq R) :
  (forall z, z \in l -> z = 0) -> sumRabs l = 0.
Proof.
elim: l => [//|a l IH] Hall /=.
have -> : a = 0 by apply: Hall; rewrite inE eqxx.
rewrite Rabs_R0 IH ?Rplus_0_l //.
by move=> z zl; apply: Hall; rewrite inE zl orbT.
Qed.

(* If nothing is left but zeros the obligation is free: the walk emits        *)
(* the remainder itself, and [|et| <= ulp r / 2 < ulp r].                     *)
Lemma vsebBlock_obligation_zeros (r et : R) (tail : seq R) :
  format et -> {in tail, forall z, format z} ->
  et <> 0 -> 2 * Rabs et <= ulp r ->
  (forall z, z \in tail -> z = 0) ->
  Rabs (nth 0 (vsebAux et tail) 0) < ulp r.
Proof.
move=> Fet Ftail etn0 Hulp Hall.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Het : 0 < Rabs et by apply: Rabs_pos_lt.
apply: vsebBlock_obligation => //.
by rewrite (sumRabs_eq0 Hall); nra.
Qed.


(* When the next step is EXACT the walk merges, and the block bound may       *)
(* be taken on the COMBINED value [eps + e] rather than on                    *)
(* [|eps| + |e|].  The draft needs exactly this in its [i_1 <= 3] case,       *)
(* where [eps_{i_0} = -u] and [e_{i_1} >= 5/8 u] cancel down to               *)
(* [|eps_{i_0} + e_{i_1}| <= 3/8 u] -- a bound the triangle inequality        *)
(* cannot see.                                                                *)
Lemma vsebAux_head_leB_merge (B eps e : R) (l : seq R) :
  format eps -> format e -> {in l, forall z, format z} -> format B ->
  dwl (TwoSum eps e) = 0 -> (0 < size l)%N ->
  Rabs (eps + e) + sumRabs l <= B ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) <= B.
Proof.
move=> Feps Fe Hl FB Het0 Hl0 Hmass.
case: l Hl0 Hl Hmass => [//|b l'] _ Hl Hmass.
have Hc := TwoSum_correct_loc Feps Fe.
have HF := format_TwoSum Feps Fe.
rewrite vsebAux_consS.
case E : (TwoSum eps e) => [r et].
have Het : et = 0 by move: Het0; rewrite E.
have Hc2 : r + et = eps + e by move: Hc; case: E => <- <-.
have Fr : format r by move: HF; rewrite E; case.
have Hr : r = eps + e by lra.
rewrite Het.
have Htrue : is_left (Req_EM_T (0:R) 0) = true.
  by case: (Req_EM_T (0:R) 0) => [//|H]; case: (H erefl).
rewrite Htrue.
apply: vsebAux_head_leB => //.
by rewrite Hr.
Qed.
(* The walk skips a run of zeros: this is how the draft's "let i_1 be the     *)
(* index of the first e_i after e_{i_0} that is non-zero" is realised.        *)
(* Iterates [VSEB.vsebAux_cons0].                                             *)
Lemma vsebAux_drop0s (eps : R) (l : seq R) (k : nat) :
  format eps -> (k < size l)%N ->
  (forall m, (m < k)%N -> nth 0 l m = 0) ->
  vsebAux eps l = vsebAux eps (drop k l).
Proof.
elim: k l => [|k IH] l Feps Hk Hz; first by rewrite drop0.
case: l Hk Hz => [//|a l'] Hk Hz.
have Ha : a = 0 by have := Hz 0%N isT.
have Hk' : (k < size l')%N by move: Hk; rewrite /= ltnS.
have Hl' : (0 < size l')%N by apply: leq_ltn_trans (leq0n k) Hk'.
case: l' Hl' Hk Hk' Hz => [//|b l''] _ Hk Hk' Hz.
rewrite Ha vsebAux_cons0 //.
rewrite (IH (b :: l'')) //.
by move=> m Hm; have := Hz m.+1 Hm.
Qed.
(* ---- the walk position, as an INDEX of the VecSum output ------------------*)
(*                                                                            *)
(*  The draft's whole case study (5.2 and 5.3 alike) is keyed on INDICES of   *)
(*  the error sequence: [i_0] is the index of the error consumed at the emit  *)
(*  under study, [i_1] the index of the first non-zero error after it.  The   *)
(*  VSEB walk, on the other hand, is a fold that has forgotten where it is.   *)
(*  The bridge is to run the walk on the SUFFIX [drop k (vecSum l)] and to    *)
(*  carry [k] through the induction: then the element consumed at that step   *)
(*  is literally [nth 0 (vecSum l) k], and [j := k] is the [i_0] the *2       *)
(*  lemmas ask for.                                                           *)
(* ===========================================================================*)

(* The list is [uls]-decreasing along its non-zero entries.                   *)
Definition ulsChain (V : seq R) : Prop :=
  forall i m, (i < m)%N -> (m < size V)%N ->
    nth 0 V i <> 0 -> nth 0 V m <> 0 ->
    uls (nth 0 V m) <= uls (nth 0 V i).

Lemma vecSum_ulsChain (l : seq R) :
  ties_to_even choice -> {in l, forall z, format z} ->
  (forall k, (k < size l)%N -> nth (0:R) l k <> 0) ->
  sorted_mag l -> pairwise_ulp l -> ulsChain (vecSum l).
Proof.
move=> Heven Hfmt Hnz Hsort Hpair i m Him Hm Hni Hnm.
exact: vecSum_uls_le Heven Hfmt Hnz Hsort Hpair Him Hm Hni Hnm.
Qed.

(* The walk invariant.  The remainder [eps] is at least as COARSE as every    *)
(* error still to be consumed -- this is the draft's normalisation            *)
(* "[uls(e_{i_0}) = u]" read symbolically, and it is what keeps               *)
(* [vseb_emit_abs_ge] applicable at every emit.  A remainder of [0] carries   *)
(* no grid at all and is allowed: the walk can cancel completely, and the     *)
(* next merge restores the invariant.                                         *)
Definition vsebDom (V : seq R) (k : nat) (eps : R) : Prop :=
  eps = 0 \/
  (forall m, (k <= m)%N -> (m < size V)%N -> nth 0 V m <> 0 ->
             uls (nth 0 V m) <= uls eps).

Lemma vsebDom_wk (V : seq R) (k1 k2 : nat) (eps : R) :
  (k1 <= k2)%N -> vsebDom V k1 eps -> vsebDom V k2 eps.
Proof.
move=> Hk [->|H]; first by left.
by right=> m Hm; apply: H; apply: leq_trans Hk Hm.
Qed.

(* An EMIT carries the invariant: the 2Sum error inherits the grid of the     *)
(* term just consumed ([TwoSum_err_uls_ge]), and that term dominates all      *)
(* the later ones ([ulsChain]).                                               *)
Lemma vsebDom_emit (V : seq R) (k : nat) (eps r et : R) :
  {in V, forall z, format z} -> ulsChain V ->
  format eps -> eps <> 0 -> (k < size V)%N -> vsebDom V k eps ->
  TwoSum eps (nth 0 V k) = DWR r et -> et <> 0 ->
  vsebDom V k.+1 et.
Proof.
move=> HfV Hch Feps epsn0 Hk Hdom E etn0.
have Fe : format (nth 0 V k) by apply: HfV; apply: mem_nth.
have en0 : nth 0 V k <> 0.
  move=> H0; apply: etn0.
  by have := dwl_TwoSum_r0 Feps; rewrite -H0 E.
have Hle : uls (nth 0 V k) <= uls eps.
  by case: Hdom => [H0|H]; [case: epsn0|apply: H].
have Hetn0 : dwl (TwoSum eps (nth 0 V k)) <> 0 by rewrite E.
have Hinh := TwoSum_err_uls_ge Feps Fe epsn0 en0 Hle Hetn0.
rewrite E /= in Hinh.
right=> m Hm Hmsz Hnm.
by apply: Rle_trans Hinh; apply: Hch.
Qed.

(* A MERGE carries the invariant too.  The new remainder is the EXACT sum     *)
(* [eps + e], which lies on the grid of [e] (both summands do), so its [uls]  *)
(* is at least [uls e] ([is_imul_uls_ge]) -- unless it cancels to [0], the    *)
(* case the invariant explicitly allows.                                      *)
Lemma vsebDom_merge (V : seq R) (k : nat) (eps r : R) :
  {in V, forall z, format z} -> ulsChain V ->
  format eps -> (k < size V)%N -> vsebDom V k eps ->
  TwoSum eps (nth 0 V k) = DWR r 0 ->
  vsebDom V k.+1 r.
Proof.
move=> HfV Hch Feps Hk Hdom E.
have Fe : format (nth 0 V k) by apply: HfV; apply: mem_nth.
have Hc : r + 0 = eps + nth 0 V k.
  move: E (TwoSum_correct_loc Feps Fe).
  by case: (TwoSum eps (nth 0 V k)) => s e [-> ->] /= H; lra.
have Hr : r = eps + nth 0 V k by lra.
case: (Req_EM_T (nth 0 V k) 0) => [Hz|en0].
  have -> : r = eps by rewrite Hr Hz; lra.
  by apply: vsebDom_wk Hdom.
case: (Req_EM_T r 0) => [->|rn0]; first by left.
have Hulse : uls (nth 0 V k) <= uls r.
  have [K HK] := uls_pow en0.
  have Hie : is_imul (nth 0 V k) (pow K) by rewrite -HK; apply: uls_imul.
  have Hieps : is_imul eps (pow K).
    case: Hdom => [H0|H].
      by exists 0%Z; rewrite H0; lra.
    have Hle : pow K <= uls eps by rewrite -HK; apply: H.
    have Feps' : is_imul eps (pow (cexp eps)) by apply: format_imul_cexp.
    case: (Req_EM_T eps 0) => [->|epsn0]; first by exists 0%Z; lra.
    have [K' HK'] := uls_pow epsn0.
    have HKK' : (K <= K')%Z by apply: (le_bpow beta); rewrite -HK'.
    by apply: (is_imul_pow_le _ HKK'); rewrite -HK'; apply: uls_imul.
  have Fr : format r.
    by have := format_TwoSum Feps Fe; rewrite E; case.
  by rewrite HK; apply: is_imul_uls_ge => //; rewrite Hr; apply: is_imul_add.
right=> m Hm Hmsz Hnm.
by apply: Rle_trans Hulse; apply: Hch.
Qed.

(* The draft's "let [i_1] be the index of the first [e_i] after [e_{i_0}]     *)
(* that is non-zero": either the rest of the list is all zeros, or there is   *)
(* a FIRST non-zero, with everything strictly before it zero.                 *)
Lemma seq_first_nonzero (V : seq R) (k n : nat) :
  (size V - k <= n)%N ->
  (forall m, (k <= m)%N -> (m < size V)%N -> nth 0 V m = 0) \/
  (exists2 q, ((k <= q) && (q < size V))%N &
     nth 0 V q <> 0 /\
     forall m, (k <= m)%N -> (m < q)%N -> nth 0 V m = 0).
Proof.
elim: n k => [|n IH] k Hn.
  left=> m Hm Hmsz.
  have Hge : (size V <= k)%N.
    by rewrite -subn_eq0; apply/eqP; case: (size V - k)%N Hn.
  by move: Hmsz; rewrite ltnNge (leq_trans Hge Hm).
case: (ltnP k (size V)) => [Hk|Hk]; last first.
  by left=> m Hm Hmsz; move: Hmsz; rewrite ltnNge (leq_trans Hk Hm).
case: (Req_EM_T (nth 0 V k) 0) => [Hz|Hnz]; last first.
  by right; exists k; [rewrite leqnn Hk|split=> // m Hm; rewrite ltnNge Hm].
have Hn' : (size V - k.+1 <= n)%N
  by rewrite subnS; move: Hn; case: (size V - k)%N => [|m] //=.
case: (IH k.+1 Hn') => [Hall|[q /andP[Hq1 Hq2] [Hqn0 Hqz]]].
  by left=> m; rewrite leq_eqVlt => /orP[/eqP<-|Hm] Hmsz; [|apply: Hall].
right; exists q; first by rewrite (leq_trans (leqnSn k) Hq1) Hq2.
split=> // m; rewrite leq_eqVlt => /orP[/eqP<-|Hm] Hmq; [by []|by apply: Hqz].
Qed.

(* THE remaining core, at ONE emit: the draft's 5.3 case study.  [k] is the   *)
(* draft's [i_0] -- the index of the error just consumed -- and the tail      *)
(* [drop k.+1 (vecSum l)] is what the draft's [i_1] is looked for in.  Every  *)
(* case lemma above discharges one branch; what is admitted here is the       *)
(* dispatch plus the two branches doc/thm6.md still owes ([i_1 <= 3] and      *)
(* the [|e_4| = |e_3|] index argument).                                       *)
(* The draft's "[uls(e_{i_1}) <= 1/8 u]" in its sub-case [1/2 u > |e_{i_1}|]  *)
(* and [|e_{i_1}| <> 1/4 u].  [uls x] is a power of two at most [|x|], so     *)
(* here it is at most [1/4 u]; and AT [1/4 u] the bound [|x| < 2 uls x]       *)
(* pins [|x| = uls x = 1/4 u] ([abs_eq_uls_of_lt_2uls]) -- exactly the value  *)
(* the sub-case excludes.  So the boundary is unreachable and [uls x] drops   *)
(* a further notch.                                                           *)
Lemma uls_le_eighth (x : R) (K : Z) :
  format x -> x <> 0 -> Rabs x < / 2 * pow K -> Rabs x <> / 4 * pow K ->
  uls x <= / 8 * pow K.
Proof.
move=> Fx xn0 Hlt Hne.
have Hpk := bpow_gt_0 beta K.
have E1 : 2 * pow (K - 1) = pow K.
  by rewrite -(bpow_plus beta 1 (K - 1)) (_ : (1 + (K - 1) = K)%Z) //; lia.
have E2 : 4 * pow (K - 2) = pow K.
  by rewrite -(bpow_plus beta 2 (K - 2)) (_ : (2 + (K - 2) = K)%Z) //; lia.
have E3 : 8 * pow (K - 3) = pow K.
  by rewrite -(bpow_plus beta 3 (K - 3)) (_ : (3 + (K - 3) = K)%Z) //; lia.
have [J HJ] := uls_pow xn0.
have Hux : uls x <= Rabs x by apply: uls_le_abs.
have HJ1 : (J <= K - 2)%Z.
  have Hp1 : pow J < pow (K - 1) by rewrite -HJ in E1 *; lra.
  by move: (lt_bpow beta _ _ Hp1); lia.
case: (Z_le_gt_dec J (K - 3)) => [HJ3|HJ2].
  have Hle := bpow_le beta _ _ HJ3.
  by rewrite HJ; lra.
have HJeq : J = (K - 2)%Z by lia.
have Hu2 : Rabs x < 2 * uls x by rewrite HJ HJeq; lra.
by case: Hne; rewrite (abs_eq_uls_of_lt_2uls Fx xn0 Hu2) HJ HJeq; lra.
Qed.

(* A float whose magnitude IS a power of two has that power as its [uls]:     *)
(* it is a multiple of [pow m] ([is_imul_uls_ge] gives [pow m <= uls x]) and  *)
(* [uls x <= |x| = pow m].                                                    *)
Lemma uls_eq_of_abs_pow (x : R) (m : Z) :
  format x -> Rabs x = pow m -> uls x = pow m.
Proof.
move=> Fx Habs.
have Hpm := bpow_gt_0 beta m.
have xn0 : x <> 0 by move=> H0; move: Habs; rewrite H0 Rabs_R0; lra.
have Hge : pow m <= uls x.
  apply: is_imul_uls_ge => //.
  case: (Rle_dec 0 x) => Hx.
    by exists 1%Z; move: Habs; split_Rabs; lra.
  by exists (-1)%Z; move: Habs; split_Rabs; lra.
by have := uls_le_abs Fx xn0; rewrite Habs; lra.
Qed.

(* A float strictly below [pow m] has [uls] at most [pow (m-1)]: [uls] is a   *)
(* power of two at most [|x|].                                                *)
Lemma uls_le_pred_of_lt (x : R) (m : Z) :
  format x -> x <> 0 -> Rabs x < pow m -> uls x <= pow (m - 1).
Proof.
move=> Fx xn0 Hlt.
have [J HJ] := uls_pow xn0.
have Hux : uls x <= Rabs x by apply: uls_le_abs.
have HJm : (J <= m - 1)%Z.
  have Hp : pow J < pow m by rewrite -HJ; lra.
  by have := lt_bpow beta _ _ Hp; lia.
by rewrite HJ; apply: bpow_le.
Qed.

(* The draft's 5.3 sub-case [1/2 u > |e_{i_1}|], [|e_{i_1}| <> 1/4 u],        *)
(* discharged from purely LOCAL data: no [vecSum] index reasoning is needed   *)
(* here, because the tail bound comes from [uls]-domination alone (the        *)
(* [>= 1/2 u] sub-cases are the ones that must go back through 5.2).          *)
Lemma vseb_emit_lt_half (e et r : R) (tail : seq R) (K : Z) :
  format et -> format e -> {in tail, forall z, format z} ->
  e <> 0 -> pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  Rabs e < / 2 * pow K -> Rabs e <> / 4 * pow K ->
  (size tail <= 3)%N ->
  (forall z, z \in tail -> Rabs z <= uls e) ->
  Rabs (nth 0 (vsebAux et (e :: tail)) 0) < ulp r.
Proof.
move=> Fet Fe Ftail en0 Ht Hulp Hlt Hne Hsz Hdom.
have Hpk := bpow_gt_0 beta K.
have Huls := uls_le_eighth Fe en0 Hlt Hne.
apply: (vseb_subcase_lt_half (t := pow K)) => // [|z zt]; first by lra.
by apply: Rle_trans (Hdom z zt) _; lra.
Qed.

(* The draft's 5.3 sub-cases [|e_{i_1}| > 1/2 u] and [|e_{i_1}| = 1/2 u].     *)
(* Both read "similarly to what we saw before, we deduce [|x_{i_1-2}| < 1],   *)
(* so [|x_{i_1}| < u] so [|e_{i_1+1}|, ..., |e_5| <= u^2]" -- i.e. both go    *)
(* back through the 5.2 chain, which is exactly why that chain is stated on   *)
(* the divisibility ([..._of_imul]) rather than on the [5/8] threshold.  The  *)
(* two sub-cases differ ONLY in how they obtain it, so both land here; and    *)
(* the head bound [<= 5/8 u] covers the [= 1/2 u] one a fortiori, so the      *)
(* draft's separate [1/2] constant buys nothing once the tail bound is the    *)
(* same.                                                                      *)
Lemma vseb_emit_of_imul (l : seq R) (k q : nat) (r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format et -> (0 < k)%N -> (k < q)%N -> (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  is_imul (vecSumAux (drop q.-1 l)).2 (pow (K + 1)) ->
  Rabs (nth 0 (vecSum l) q) <= 5 / 8 * pow K ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq Hq en0 HK Ht Hulp Him He.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hpk := bpow_gt_0 beta K.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Hpred : (q.-1.+1 = q)%N by rewrite prednK //; apply: ltnW.
have Hqsz : (q.-1.+1 < size l)%N by rewrite Hpred -Hszl.
have Hkq' : (k <= q.-1)%N by rewrite -ltnS Hpred.
(* the draft's "[|x_i| < u], so [forall i' >= i+1, |e_{i'}| <= u^2]"          *)
have [i' Hi'q Htail] :=
  vecSum_tail_err_le_u2_of_imul Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0
    (etrans HK (erefl _)) Him.
have Hn2 : ((q - 2).+2 = q)%N by rewrite -addn2 subnK //.
have Htail' : forall z, z \in drop q.+1 (vecSum l) -> Rabs z <= pow (K - p).
  move=> z /(nthP 0)[j Hj <-].
  rewrite nth_drop.
  have Hjs : (q.+1 + j < size l)%N
    by move: Hj; rewrite size_drop Hszl ltn_subRL addnC.
  have Hm3 : ((q - 2 + j).+3 = q.+1 + j)%N by rewrite -{2}Hn2 !addSn.
  have Hi'm : (i' <= q - 2 + j)%N.
    apply: leq_trans (leq_addr j _).
    by move: Hi'q; rewrite -{1}Hn2 /= ltnS.
  by rewrite -Hm3; apply: Htail => //; rewrite Hm3.
have Fq : format (nth 0 (vecSum l) q) by apply: HfV; apply: mem_nth.
have Ftail : {in drop q.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
(* "we are adding at most 3 of them" -- this is where [size l <= 6] is paid   *)
have Hszt : (size (drop q.+1 (vecSum l)) <= 3)%N.
  rewrite size_drop Hszl leq_subLR.
  apply: leq_trans Hsz6 _.
  by rewrite addSn addnC; move: Hq2; rewrite -addn1 -(leq_add2l 3) addnCA.
have Hu2 : pow (K - p) = u * pow K
  by rewrite uE_pow -bpow_plus; congr bpow; lia.
apply: (vseb_subcase_gt_half (t := pow K)) => // z zt.
apply: Rle_trans (Htail' z zt) _.
rewrite Hu2; have Hu0 : 0 < u by apply: u_gt_0.
by nra.
Qed.

(* ---- the three branches doc/thm6.md 5.3 still owes ---------------------*)

(* What the walk's FIRST step contributes to the emitted head.  Either the    *)
(* step is inexact -- and then the head is [RND(eps + e)] no matter what      *)
(* follows, which is why the draft can write "[y_{j+1} = r_{i_1-1}]" and stop *)
(* -- or it is exact, and the walk carries on from the exact sum.  This is    *)
(* the structural reason the [i_1 >= 4] case needs no mass argument on the    *)
(* inexact side.                                                              *)
Lemma vsebAux_head_step (eps e : R) (l : seq R) :
  nth 0 (vsebAux eps (e :: l)) 0 = RND (eps + e) \/
  (dwl (TwoSum eps e) = 0 /\
   nth 0 (vsebAux eps (e :: l)) 0 = nth 0 (vsebAux (RND (eps + e)) l) 0).
Proof.
case: l => [|e2 l].
  left; rewrite vsebAux_1.
  by case E : (TwoSum eps e) => [y0 y1] /=; have := TwoSum_hi eps e; rewrite E.
rewrite vsebAux_consS.
case E : (TwoSum eps e) => [r et].
have Hr : r = RND (eps + e) by have := TwoSum_hi eps e; rewrite E.
case: (Req_EM_T et 0) => [Het0|Hetn0]; last by left; rewrite /= Hr.
change (nth 0 (vsebAux r (e2 :: l)) 0 = RND (eps + e) \/
        et = 0 /\ nth 0 (vsebAux r (e2 :: l)) 0
                  = nth 0 (vsebAux (RND (eps + e)) (e2 :: l)) 0).
by right; rewrite Hr.
Qed.

(* Ties-to-even, in the form the draft's "[2u | s_{i_1-1}]" needs: a rounding *)
(* whose error is EXACTLY [1/2 pow K] lands on the [pow (K+1)] grid.  Write   *)
(* [c] for [cexp v]; the error is [|m - Znearest m| pow c] with               *)
(* [|m - Znearest m| <= 1/2], so [pow K <= pow c].  If [K < c] the result is  *)
(* a multiple of [pow c] already.  If [K = c] the error is exactly half a     *)
(* unit, so by [Znearest_N_strict] the scaled mantissa sits at [.5] -- a TIE  *)
(* -- and ties-to-even returns [Zfloor] when that is even and [Zceil =        *)
(* Zfloor + 1] when it is odd: EITHER WAY an even integer, i.e. a multiple    *)
(* of [2 pow c = pow (K+1)].                                                  *)
Lemma RN_err_half_imul (v : R) (K : Z) :
  ties_to_even choice ->
  Rabs (v - RND v) = / 2 * pow K -> is_imul (RND v) (pow (K + 1)).
Proof.
move=> Heven Herr.
set c := cexp v.
set m := scaled_mantissa beta (FLX_exp p) v.
have Hv : m * pow c = v by apply: scaled_mantissa_mult_bpow.
have HR : RND v = IZR (Znearest choice m) * pow c by rewrite /round /F2R /=.
have Hpc := bpow_gt_0 beta c.
have Hpk := bpow_gt_0 beta K.
have Herr' : Rabs (m - IZR (rnd m)) * pow c = / 2 * pow K.
  rewrite -Herr -{1}Hv HR -(Rabs_pos_eq (pow c) (Rlt_le _ _ Hpc)) -Rabs_mult.
  by rewrite (Rabs_pos_eq (pow c) (Rlt_le _ _ Hpc)); congr Rabs; ring.
case: (Req_EM_T (m - IZR (Zfloor m)) (/ 2)) => [Htie|Hntie]; last first.
  (* not a tie: the error is STRICTLY under half a unit, so [K < c] and the   *)
  (* result already sits on the [pow c] grid                                  *)
  have Hlt := Znearest_N_strict choice m Hntie.
  have HKc : pow K < pow c by nra.
  have HKc' : (K + 1 <= c)%Z by have := lt_bpow beta _ _ HKc; lia.
  apply: (is_imul_pow_le _ HKc').
  by exists (rnd m); rewrite HR.
(* a tie: ties-to-even returns [Zfloor] when even and [Zfloor + 1] when odd   *)
have Hnint : IZR (Zfloor m) <> m by lra.
have Hceil : Zceil m = (Zfloor m + 1)%Z by apply: Zceil_floor_neq.
have Hrnd : rnd m = (if choice (Zfloor m) then Zceil m else Zfloor m)
  by rewrite /Znearest (Rcompare_Eq _ _ Htie).
have Habs : Rabs (m - IZR (rnd m)) = / 2.
  case: (Znearest_DN_or_UP choice m) => ->; first by split_Rabs; lra.
  by rewrite Hceil plus_IZR; split_Rabs; lra.
have HcK : c = K by apply: (bpow_inj beta); move: Herr'; rewrite Habs; lra.
have Hev : Z.even (rnd m).
  rewrite Hrnd Heven; case E : (Z.even (Zfloor m)) => //=.
  by rewrite Hceil Z.even_add E.
have /Z.even_spec [n Hn] := Hev.
exists n; rewrite HR Hn HcK mult_IZR.
have -> : pow (K + 1) = pow K * 2 by rewrite bpow_plus bpow_1 /=; lra.
by lra.
Qed.

(* Draft 5.3, sub-case [|e_{i_1}| = 1/2 u]: "thanks to ties-to-even,          *)
(* [2u | s_{i_1-1}]".  Here [|e| = 1/2 u] and [|e| <= 1/2 ulp(s)] give        *)
(* [ulp(s) >= u]; if [ulp(s) >= 2u] the divisibility is free, and if          *)
(* [ulp(s) = u] then [e] sits at EXACTLY half an ulp -- a tie -- so           *)
(* round-to-nearest-EVEN returns an even multiple of [u], i.e. a multiple     *)
(* of [2u].  Feeding [vseb_emit_of_imul] then closes the sub-case.            *)
Lemma vecSum_run_imul_of_half (l : seq R) (i : nat) (K : Z) :
  ties_to_even choice ->
  (i.+1 < size l)%N -> {in l, forall z, format z} ->
  Rabs (nth 0 (vecSum l) i.+1) = / 2 * pow K ->
  is_imul (vecSumAux (drop i l)).2 (pow (K + 1)).
Proof.
move=> Heven Hi Hf Herr.
set v := (nth 0 l i + (vecSumAux (drop i.+1 l)).2).
have Hrnd : (vecSumAux (drop i l)).2 = RND v by apply: vecSum_run_rnd.
have Hstep := vecSum_run_step Hi Hf.
rewrite Hrnd; apply: RN_err_half_imul => //.
have Heq : v - RND v = nth 0 (vecSum l) i.+1
  by move: Hstep; rewrite Hrnd /v; lra.
by rewrite Heq.
Qed.

(* Peeling one term off a suffix mass.  Needed because the [i_1 = 2] tail     *)
(* must be bounded term BY TERM (the draft's [1/8 + 1/8 + 1/16]) rather than  *)
(* by a uniform count.                                                        *)
Lemma sumRabs_drop_cons (s : seq R) (n : nat) :
  sumRabs (drop n s) <= Rabs (nth 0 s n) + sumRabs (drop n.+1 s).
Proof.
case: (ltnP n (size s)) => [Hn|Hn]; first by rewrite (drop_nth 0 Hn) /=; lra.
rewrite drop_oversize // nth_default // drop_oversize; last exact: leqW.
by rewrite /= Rabs_R0; lra.
Qed.

(* Draft 5.3, sub-case [|e_{i_1}| = 1/4 u], at [i_1 = 2] -- the ONLY place    *)
(* the draft's refinement is needed.  Counting there gives exactly            *)
(* [5/8 + 3*(1/8) = 1], which does NOT close, and the draft repairs it with   *)
(* "we can not have [|e_4| = |e_3|] (because this can not happen for          *)
(* [i >= 4]) so [|e_5| <= uls(e_4)]": the last of the three tail errors is    *)
(* half the size, giving tail mass [1/8 + 1/8 + 1/16 = 5/16] and the total    *)
(* [5/8 + 5/16 = 15/16 <= 1 - u].  [vseb_subcase_quarter] takes that refined  *)
(* mass as its hypothesis; what is missing is the index argument about        *)
(* positions 3, 4 and 5 -- which is exactly why the draft names them.         *)
Lemma vseb_emit_quarter_i1_2 (l : seq R) (k q : nat) (r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format et -> (0 < k)%N -> (k < q)%N -> (q <= 2)%N ->
  (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  Rabs (nth 0 (vecSum l) q) = / 4 * pow K ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq Hq2' Hq en0 Hqn0 HK Ht Hulp
       Heq4.
have Hpk := bpow_gt_0 beta K.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Hulp0 : 0 < ulp r by have := Rabs_pos et; lra.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hqeq : q = 2%N by apply/eqP; rewrite eqn_leq Hq2' Hq2.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Fq : format (nth 0 (vecSum l) q) by apply: HfV; apply: mem_nth.
have Ftail : {in drop q.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
have Hp2K : / 4 * pow K = pow (K - 2).
  have -> : (K - 2 = - (2) + K)%Z by lia.
  by rewrite bpow_plus /= /Z.pow_pos /=; lra.
(* [|e_{i_1}| = 1/4 u] is a POWER OF TWO, so it IS its own [uls]              *)
have Huls2 : uls (nth 0 (vecSum l) q) = pow (K - 2)
  by apply: uls_eq_of_abs_pow => //; rewrite Heq4 Hp2K.
have Hp3K : pow (K - 3) = / 8 * pow K.
  have -> : (K - 3 = - (3) + K)%Z by lia.
  by rewrite bpow_plus /= /Z.pow_pos /=; lra.
have Hp2gt := bpow_gt_0 beta (K - 2).
have Hp3gt := bpow_gt_0 beta (K - 3).
have Hq3 : (q <= 3)%N by rewrite Hqeq.
(* THE DRAFT'S "we can not have [|e_4| = |e_3|] (because this can not         *)
(* happen for [i >= 4])": [|e_4| = uls(e_2)] would itself be a VIOLATION at   *)
(* [j := 2], [i := 3] -- and 5.2's counting then forces [3 <= 2].             *)
have He4ne : Rabs (nth 0 (vecSum l) 3.+1) <> pow (K - 2).
  move=> Habs4.
  have H4sz : (3.+1 < size l)%N.
    case: (ltnP 3.+1 (size l)) => [//|Hge].
    suff : False by [].
    by move: Habs4; rewrite nth_default ?Hszl // Rabs_R0; lra.
  have Hviol4 : 5 / 8 * pow (K - 2) <= Rabs (nth 0 (vecSum l) 3.+1)
    by rewrite Habs4; lra.
  by have := vecSum_right_of_i_count Heven Hsz6 H4sz Hfmt Hnz Hsort Hpair Hq3
                                     Hqn0 Huls2 Hviol4 Habs4.
have Hb : forall m, (2 < m)%N -> Rabs (nth 0 (vecSum l) m) <= pow (K - 2).
  move=> m Hm.
  case: (ltnP m (size (vecSum l))) => [Hlt|Hge]; last first.
    by rewrite nth_default ?Rabs_R0 //; lra.
  rewrite -Huls2; apply: vecSum_tail_le_uls => //.
  by rewrite Hqeq.
have H3 := Hb 3%N isT.
have H4 := Hb 4%N isT.
have H5 := Hb 5%N isT.
(* the draft's [1/8 + 1/8 + 1/16]: with [|e_4| < uls(e_2)] the last error     *)
(* drops a notch, [|e_5| <= uls(e_4) <= 1/8 u]                                *)
have Hsum : Rabs (nth 0 (vecSum l) 3) + Rabs (nth 0 (vecSum l) 4)
              + Rabs (nth 0 (vecSum l) 5) <= 2 * pow (K - 2) + pow (K - 3).
  case: (Req_EM_T (nth 0 (vecSum l) 4) 0) => [Hz4|Hn4].
    by rewrite Hz4 Rabs_R0; lra.
  have Hlt4 : Rabs (nth 0 (vecSum l) 4) < pow (K - 2) by lra.
  have F4 : format (nth 0 (vecSum l) 4).
    case: (ltnP 4 (size (vecSum l))) => [Hlt|Hge]; last first.
      by rewrite nth_default //; apply: generic_format_0.
    by apply: HfV; apply: mem_nth.
  have Huls4 := uls_le_pred_of_lt F4 Hn4 Hlt4.
  have HKK : (K - 2 - 1 = K - 3)%Z by lia.
  rewrite HKK in Huls4.
  case: (ltnP 5 (size (vecSum l))) => [Hlt5|Hge5]; last first.
    by rewrite [nth 0 (vecSum l) 5]nth_default ?Rabs_R0 //; lra.
  have H45 := vecSum_tail_le_uls Heven Hfmt Hnz Hsort Hpair (_ : (4 < 5)%N)
                                 Hlt5 Hn4.
  have H45' := H45 isT.
  by lra.
have Hd6 : drop 6 (vecSum l) = [::] by apply: drop_oversize; rewrite Hszl.
have Hmass : sumRabs (drop q.+1 (vecSum l)) <= 5 / 16 * ulp r.
  have E1 := sumRabs_drop_cons (vecSum l) 3.
  have E2 := sumRabs_drop_cons (vecSum l) 4.
  have E3 := sumRabs_drop_cons (vecSum l) 5.
  rewrite Hd6 /= in E3.
  have Hq1 : q.+1 = 3%N by rewrite Hqeq.
  rewrite Hq1.
  have Hfin : sumRabs (drop 3 (vecSum l)) <= 2 * pow (K - 2) + pow (K - 3)
    by lra.
  rewrite -Hp2K in Hfin.
  by rewrite Hp3K in Hfin; lra.
apply: (vseb_subcase_quarter (t := pow K)) => //.
by rewrite Heq4; lra.
Qed.

(* Draft 5.3, sub-case [|e_{i_1}| = 1/4 u].  The draft's tail-mass refinement *)
(* is needed ONLY at [i_1 = 2]: with [i_1 >= 3] and [size l <= 6] at most     *)
(* TWO errors follow, and plain counting gives                                *)
(* [5/8 + 2*(1/8) = 7/8 <= 1 - u].  The tail bound itself is free -- every    *)
(* later error is [<= uls(e_{i_1}) <= |e_{i_1}| = 1/4 u <= 1/8 ulp(y_j)].     *)
Lemma vseb_emit_quarter (l : seq R) (k q : nat) (r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format et -> (0 < k)%N -> (k < q)%N -> (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  Rabs (nth 0 (vecSum l) q) = / 4 * pow K ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq Hq en0 Hqn0 HK Ht Hulp Heq4.
have Hpk := bpow_gt_0 beta K.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Hulp0 : 0 < ulp r by have := Rabs_pos et; lra.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Fq : format (nth 0 (vecSum l) q) by apply: HfV; apply: mem_nth.
have Ftail : {in drop q.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
(* every later error is [<= uls(e_{i_1}) <= |e_{i_1}| = 1/4 u]                *)
have Ht4 : uls (nth 0 (vecSum l) q) <= / 4 * pow K
  by rewrite -Heq4; apply: uls_le_abs.
have Hdomt : forall z, z \in drop q.+1 (vecSum l) ->
                        Rabs z <= / 8 * ulp r.
  move=> z /(nthP 0)[j Hj <-]; rewrite nth_drop.
  apply: Rle_trans (_ : uls (nth 0 (vecSum l) q) <= _); last by lra.
  apply: vecSum_tail_le_uls => //; first by rewrite addSn ltnS leq_addr.
  by move: Hj; rewrite size_drop ltn_subRL addnC.
case: (leqP q 2) => [Hq2'|Hq3].
  by apply: (vseb_emit_quarter_i1_2 Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq
                                    Hq2' Hq en0 Hqn0 HK Ht Hulp Heq4).
(* [i_1 >= 3]: at most TWO errors left, and plain counting closes             *)
have Hszt : (size (drop q.+1 (vecSum l)) <= 2)%N.
  rewrite size_drop Hszl leq_subLR.
  apply: leq_trans Hsz6 _.
  by rewrite addSn addnC.
have Hd0 : 0 <= / 8 * ulp r by lra.
have Hmass := sumRabs_le_count Hszt Hd0 Hdomt.
have H2 : INR 2 = 2 by rewrite /=; lra.
rewrite H2 in Hmass.
apply: (vseb_subcase_mass_lt (t := pow K) (c := / 4) (M := / 4)) => //;
  try lra.
Qed.

(* The head bound when the FIRST step cancels: what survives is               *)
(* [|eps + e|], not [|eps| + |e|].  Either the step is inexact and the head   *)
(* IS [RND(eps + e)], or it is exact and the walk carries on from it -- and   *)
(* then the mass argument applies with [eps + e] in place of [eps].  Draft    *)
(* 5.3's [|eps_{i_0} + e_{i_1}| <= 3/8 u] is used exactly here.               *)
Lemma vseb_head_lt_of_merge_mass (yj eps e B : R) (l : seq R) :
  format eps -> format e -> {in l, forall z, format z} -> format B ->
  Rabs (eps + e) + sumRabs l <= B -> B < ulp yj ->
  Rabs (nth 0 (vsebAux eps (e :: l)) 0) < ulp yj.
Proof.
move=> Feps Fe Hl FB Hmass HB.
have Hs0 := sumRabs_ge0 l.
case: (vsebAux_head_step eps e l) => [Hhd|[Hex Hhd]]; rewrite Hhd.
  apply: Rle_lt_trans HB.
  by apply: Rabs_round_le_r => //; lra.
have Hexact : RND (eps + e) = eps + e.
  move: Hex (TwoSum_correct_loc Feps Fe) (TwoSum_hi eps e).
  case: (TwoSum eps e) => s et H1 H2 H3.
  by rewrite /= in H1 H2 H3; lra.
apply: Rle_lt_trans HB.
by apply: vsebAux_head_leB => //;
   [apply: generic_format_round | rewrite Hexact; lra].
Qed.

(* Draft 5.3, case [i_1 <= 3], sub-case [x_{i_1-2} = -1+u].  The cancelling   *)
(* pair kills [e_{i_1-1}], so [i_0 < i_1 - 1] forces [i_1 = 3] and            *)
(* [i_0 = 1]: this emit is the FIRST one of the walk, so [eps] is [s_0]       *)
(* itself.  The draft's "[|y_j| = |s_0| >= 1/2 u^{-1}]" is [pairwise_ulp]     *)
(* at [(x_0, x_2)]: [|s_2| = 1] pushes [|x_2|] up to [1/4] (5.1's             *)
(* [|s_i| <= 4 ufp(x_i)]), so [ulp(x_0) > 1/4] and [|x_0| >= 2^{p-2}] --      *)
(* whence [ulp(y_j) >= 4u], while the whole remaining mass                    *)
(* [|eps_{i_0}| + |e_3| + |e_4| + |e_5|] is at most [2u + 2u^2].              *)
Lemma vseb_emit_viol_le3_opp (l : seq R) (k q : nat) (eps r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format eps -> TwoSum eps (nth 0 (vecSum l) k) = DWR r et ->
  ((k = 1)%N -> eps = nth 0 (vecSum l) 0) ->
  eps <> 0 ->
  (forall gg : Z, (forall m, (m < k)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul eps (pow gg)) ->
  format et -> (0 < k)%N -> (k < q)%N -> (q <= 3)%N ->
  (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q) ->
  nth 0 (vecSum l) q.-1 = 0 ->
  Rabs (vecSumAux (drop q.-1.-1 l)).2 = pow K ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd epsn0 Hgrid Fet Hk Hkq Hq3
       Hq en0 Hqn0 HK Ht Hulp Hviol Hz Hs1.
have Hpk := bpow_gt_0 beta K.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Hulp0 : 0 < ulp r by have := Rabs_pos et; lra.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Hpred : (q.-1.+1 = q)%N by rewrite prednK //; apply: ltnW.
have Hqsz : (q.-1.+1 < size l)%N by rewrite Hpred -Hszl.
have Hkq' : (k <= q.-1)%N by rewrite -ltnS Hpred.
have Hviol' : 5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q.-1.+1) by rewrite Hpred.
(* [e_{i_1-1} = 0] puts [i_0] STRICTLY left of [i_1-1], which with            *)
(* [1 <= i_0] and [i_1 <= 3] pins [i_1 = 3] and [i_0 = 1].                    *)
have Hkq1 : (k < q.-1)%N.
  rewrite ltn_neqAle Hkq' andbT; apply/eqP => Hkeq.
  by apply: en0; rewrite Hkeq.
have Hq3' : (3 <= q)%N.
  have H2 : (1 < q.-1)%N by apply: leq_ltn_trans Hk Hkq1.
  by move: H2; case: (q) => [|q'].
have Heqq : q = 3%N by apply/eqP; rewrite eqn_leq Hq3 Hq3'.
have Heqk : k = 1%N.
  by move: Hk Hkq1; rewrite Heqq /=; case: (k) => [|[|k']].
rewrite Heqq /= in Hs1.
have Hsz4 : (3 < size l)%N by rewrite -Hszl -Heqq.
(* [e_1] is the 2Sum error of [x_0] against [s_1], so [|e_1| <= |s_1| = u];   *)
(* [eps_{i_0}] is the 2Sum error of [s_0] against [e_1], so it is smaller     *)
(* still -- and it is [>= u].  Everything collapses to [= u].                 *)
have F0 : format (nth 0 l 0) by apply: Hfmt; apply: mem_nth.
have Fs1 : format (vecSumAux (drop 1 l)).2.
  have Hdf : {in drop 1 l, forall z, format z}
    by move=> z /mem_drop; apply: Hfmt.
  by have [F _] := format_vecSumAux Hdf.
have Hsz1 : (0.+1 < size l)%N by apply: leq_trans Hsz4.
have Fe1 : format (nth 0 (vecSum l) 1)
  by apply: HfV; apply: mem_nth; rewrite Hszl; apply: leq_trans Hsz4.
have He1 : nth 0 (vecSum l) 1 =
           dwl (TwoSum (nth 0 l 0) (vecSumAux (drop 1 l)).2)
  by apply: vecSum_run_dwl.
have He1le : Rabs (nth 0 (vecSum l) 1) <= pow K.
  by rewrite He1 -Hs1; apply: TwoSum_err_le_r.
have HE' : TwoSum eps (nth 0 (vecSum l) 1) = DWR r et by rewrite -Heqk.
have [Hcorr Herr] : r + et = eps + nth 0 (vecSum l) 1 /\
                    Rabs et <= Rabs (nth 0 (vecSum l) 1).
  move: HE' (TwoSum_correct_loc Feps Fe1) (TwoSum_err_le_r Feps Fe1).
  case: (TwoSum eps (nth 0 (vecSum l) 1)) => s e [-> ->] H1 H2.
  by rewrite /= in H1 H2; split; lra.
have Hetv : Rabs et = pow K by lra.
have He1v : Rabs (nth 0 (vecSum l) 1) = pow K by lra.
(* [eps = s_0 = x_0 + s_1 - e_1], so [|r| >= |x_0| - 4u]                      *)
have Heps : eps = (vecSumAux l).2 by rewrite Hhd // vecSum_nth0.
have Hstep : (vecSumAux l).2 + nth 0 (vecSum l) 1 =
             nth 0 l 0 + (vecSumAux (drop 1 l)).2.
  by have := vecSum_run_step Hsz1 Hfmt; rewrite drop0.
have Hrlow : Rabs (nth 0 l 0) - 4 * pow K <= Rabs r.
  move: Hcorr Hstep Hetv He1v Hs1; rewrite Heps; split_Rabs; lra.
(* the draft's [|s_0| >= 1/2 u^{-1}], via [pairwise_ulp] at [(x_0, x_2)]      *)
have [HRs _ _ _ _] :=
  vecSum_pinning_of_violation Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0 HK
                              Hviol'.
rewrite Heqq /= in HRs.
have Hx2n0 : nth 0 l 2 <> 0 by apply: Hnz; apply: ltnW.
have Hpow2 : pow (K + p) = 4 * pow (K + p - 2).
  have H4 : (4 = pow 2) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite H4 -bpow_plus; congr bpow; lia.
have Hx2 : pow (K + p - 2) <= Rabs (nth 0 l 2).
  have [Hufp _] := vecSum_run_ufp Heven Hfmt Hnz Hsort Hpair (ltnW Hsz4).
  have Hle := ufp_le_abs Hx2n0.
  by lra.
have Hulpx0 : pow (K + p - 2) < ulp (nth 0 l 0).
  case: (Hpair 0%N (ltnW Hsz4)) => [Hzz|Hlt]; first by case: Hx2n0.
  by lra.
have Hx0 : pow (K + p - 2 + p) <= Rabs (nth 0 l 0).
  case: (Rle_lt_dec (pow (K + p - 2 + p)) (Rabs (nth 0 l 0))) => // Hlt.
  by have := bound_ulp_FLX Hp2 Hlt; lra.
(* [ulp(y_j) >= 4u]                                                           *)
have H4u : 4 * pow K = pow (K + 2).
  by rewrite bpow_plus /= /Z.pow_pos /=; lra.
have Hbig : pow (K + p - 3 + p) <= Rabs r.
  have Hhalf : 2 * pow (K + p - 3 + p) = pow (K + p - 2 + p).
    have H2 : (2 = pow 1) by rewrite /= /Z.pow_pos /=; lra.
    by rewrite H2 -bpow_plus; congr bpow; lia.
  have Hsm : pow (K + 2) <= pow (K + p - 3 + p) by apply: bpow_le; lia.
  by rewrite -H4u in Hsm; lra.
have Hulpr : pow (K + 2) <= ulp r.
  have Hu4 : pow (K + 2) <= pow (K + p - 2) by apply: bpow_le; lia.
  apply: Rle_trans Hu4 _.
  have <- : ulp (pow (K + p - 3 + p)) = pow (K + p - 2).
    by rewrite ulp_bpow /FLX_exp; congr bpow; lia.
  apply: (ulp_le beta fexp).
  by rewrite [Rabs (pow _)]Rabs_pos_eq //; apply: bpow_ge_0.
(* the mass: [|e_{i_1}| <= u] and at most two later errors, each [<= u^2]     *)
have Heqle : Rabs (nth 0 (vecSum l) q) <= pow K.
  have Hgp := bpow_gt_0 beta (K - p + 1).
  case: (vecSum_right_of_i_cases Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0 HK
                                 Hviol'); rewrite Hpred;
    by [case=> -> _; lra | case=> -> _; lra | lra].
have Hszt : (size (drop q.+1 (vecSum l)) <= 2)%N.
  rewrite size_drop Hszl leq_subLR.
  apply: leq_trans Hsz6 _.
  by rewrite Heqq addnC.
have Hd0 : 0 <= pow (K - p) by apply: bpow_ge_0.
have Hdom : forall z, z \in drop q.+1 (vecSum l) -> Rabs z <= pow (K - p).
  move=> z /(nthP 0)[m Hm <-]; rewrite nth_drop.
  have [i' Hi' Htail] :=
    vecSum_tail_err_le_u2_of_violation Heven Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                       en0 HK Hviol'.
  have Hi'1 : (i' <= m.+1)%N.
    have Hi'2 : (i' <= 1)%N by move: Hi'; rewrite Heqq /=.
    by apply: leq_trans Hi'2 (ltn0Sn m).
  have -> : (q.+1 + m = m.+1.+2.+1)%N by rewrite Heqq /=.
  apply: Htail => //; rewrite -Hszl.
  by move: Hm; rewrite size_drop ltn_subRL Heqq /=.
(* the draft's counting, with [(1 - u) ulp(y_j)] as the format witness        *)
have HB : format ((1 - IZR 1 * u) * ulp r).
  by apply: format_1_sub_ku_ulp; move: pow2_ge_16; lia.
have H1 : IZR 1 = 1 by [].
have Hup : pow (K - p) = u * pow K
  by rewrite uE_pow -bpow_plus; congr bpow; lia.
have Fq : format (nth 0 (vecSum l) q) by apply: HfV; apply: mem_nth.
have Ftail : {in drop q.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
apply: (vseb_head_lt_split Fet Fq Ftail HB Hszt Hd0 Hdom);
    last by rewrite ?H1; nra.
have H2 : INR 2 = 2 by rewrite /=; lra.
rewrite -H4u in Hulpr.
rewrite H2 ?H1.
by nra.
Qed.

(* Draft 5.3, case [i_1 <= 3], sub-case [x_{i_1-2} = 1-u].  Here the pair     *)
(* reinforces: [|e_{i_1-1}| = u] and [|s_{i_1-2}| = 2].  The draft pins       *)
(* [eps_{i_0} = -u] against [e_{i_1} >= 5/8 u] -- the CANCELLATION            *)
(* [|eps_{i_0} + e_{i_1}| <= 3/8 u] -- after which the at most 3 remaining    *)
(* errors are [<= u^2].                                                       *)
Lemma vseb_emit_viol_le3_same (l : seq R) (k q : nat) (eps r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format eps -> TwoSum eps (nth 0 (vecSum l) k) = DWR r et ->
  ((k = 1)%N -> eps = nth 0 (vecSum l) 0) ->
  eps <> 0 ->
  (forall gg : Z, (forall m, (m < k)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul eps (pow gg)) ->
  format et -> (0 < k)%N -> (k < q)%N -> (q <= 3)%N ->
  (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q) ->
  Rabs (nth 0 l q.-1.-1 + (vecSumAux (drop q.-1 l)).2) =
    2 * pow (K + p) - pow K ->
  Rabs (nth 0 (vecSum l) q.-1) = pow K ->
  Rabs (vecSumAux (drop q.-1.-1 l)).2 = 2 * pow (K + p) ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd epsn0 Hgrid Fet Hk Hkq Hq3
       Hq en0 Hqn0 HK Ht Hulp Hviol Hsum He Hs0.
have Hpk := bpow_gt_0 beta K.
have HAp := bpow_gt_0 beta (K + p).
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Hulp0 : 0 < ulp r by have := Rabs_pos et; lra.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Hpred : (q.-1.+1 = q)%N by rewrite prednK //; apply: ltnW.
have Hqsz : (q.-1.+1 < size l)%N by rewrite Hpred -Hszl.
have Hkq' : (k <= q.-1)%N by rewrite -ltnS Hpred.
have Hviol' : 5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q.-1.+1) by rewrite Hpred.
have Hq12 : (q.-1 <= 2)%N by rewrite -ltnS Hpred.
(* the draft's [i_0 = i_1 - 1]: anything further left is a multiple of [1]    *)
have Heqk : k = q.-1.
  case: (ltnP k q.-1) => [Hlt|Hge]; last by apply/eqP; rewrite eqn_leq Hkq' Hge.
  by case: (vecSum_left_same_i0 Heven Hqsz Hfmt Hnz Hsort Hpair Hk Hlt Hq12 en0
                                HK Hviol' Hsum).
have Hq23 : q = 2%N \/ q = 3%N.
  by move: Hq2 Hq3; case: (q) => [|[|[|[|q']]]] // _ _; [left | right].
(* "all the [e_i], [i <= i_1-2], are divisible by 1", so the walk's           *)
(* remainder [eps] entering this emit is itself on the [1] grid               *)
have Himeps : is_imul eps (pow (K + p)).
  apply: Hgrid => m Hm.
  case: Hq23 => Hqv.
    have Hm0 : m = 0%N by move: Hm; rewrite Heqk Hqv /=; case: (m).
    rewrite Hm0 vecSum_nth0.
    move: Hs0; rewrite Hqv /= drop0 => Hs0'.
    have Hpm : (vecSumAux l).2 = 2 * pow (K + p) \/
               (vecSumAux l).2 = - (2 * pow (K + p))
      by move: Hs0'; split_Rabs; lra.
    by case: Hpm => ->; [exists 2%Z | exists (-2)%Z]; lra.
  have Hi2 : q.-1 = 2%N by rewrite Hqv.
  have [_ _ Him0 Him1] :=
    vecSum_left_same_imul Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' Hi2 en0 HK
                          Hviol' Hsum.
  have Hm01 : m = 0%N \/ m = 1%N.
    by move: Hm; rewrite Heqk Hqv /=; case: (m) => [|[|m']] // _;
       [left | right].
  by case: Hm01 => ->.
(* hence the draft's "thus we must have [eps_{i_0} = -u]": no tie can flip    *)
(* the sign, and an exact step would leave nothing to emit                    *)
have Hek : Rabs (nth 0 (vecSum l) k) = pow (K + p - p).
  have -> : (K + p - p = K)%Z by lia.
  by rewrite Heqk.
have Hr : r = RND (eps + nth 0 (vecSum l) k)
  by have := TwoSum_hi eps (nth 0 (vecSum l) k); rewrite HE.
have Hc : r + et = eps + nth 0 (vecSum l) k.
  have Hklt : (k < size (vecSum l))%N by apply: ltn_trans Hkq Hq.
  have Fek : format (nth 0 (vecSum l) k) by apply: HfV; apply: mem_nth.
  move: HE (TwoSum_correct_loc Feps Fek).
  case: (TwoSum eps (nth 0 (vecSum l) k)) => s e [-> ->] H.
  by rewrite /= in H; lra.
have Hetv : et = nth 0 (vecSum l) k.
  case: (RN_imul_no_flip Heven Feps epsn0 Himeps Hek) => Hflip;
    rewrite Hflip in Hr; first by lra.
  have Het0 : et = 0 by lra.
  by move: Ht; rewrite Het0 Rabs_R0; lra.
(* the CANCELLATION [|eps_{i_0} + e_{i_1}| <= 3/8 u]                          *)
have [_ _ Hcancel] :=
  vecSum_left_same_err_opp Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0 HK Hviol'
                           Hsum.
rewrite Hpred in Hcancel.
have Hetabs : Rabs et = pow K by rewrite Hetv Heqk He.
have Hcan : Rabs (et + nth 0 (vecSum l) q) <= 3 / 8 * pow K
  by rewrite Hetv Heqk.
(* and the at most 3 remaining errors are [<= u^2]                            *)
have Hszt : (size (drop q.+1 (vecSum l)) <= 3)%N.
  rewrite size_drop Hszl leq_subLR.
  apply: leq_trans Hsz6 _.
  by rewrite addSn addnC; move: Hq2; rewrite -addn1 -(leq_add2l 3) addnCA.
have Hd0 : 0 <= pow (K - p) by apply: bpow_ge_0.
have Hdom : forall z, z \in drop q.+1 (vecSum l) -> Rabs z <= pow (K - p).
  move=> z /(nthP 0)[m Hm <-]; rewrite nth_drop.
  have [i' Hi' Htail] :=
    vecSum_tail_err_le_u2_of_violation Heven Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                       en0 HK Hviol'.
  have Hidx : (q.+1 + m = (q - 2 + m).+2.+1)%N by case: Hq23 => ->.
  rewrite Hidx; apply: Htail.
    by apply: leq_trans (leq_addr m _); move: Hi'; case: Hq23 => ->.
  rewrite -Hidx -Hszl.
  by move: Hm; rewrite size_drop ltn_subRL addnC.
have Hmass := sumRabs_le_count Hszt Hd0 Hdom.
have H3 : INR 3 = 3 by rewrite /=; lra.
rewrite H3 in Hmass.
have Hup : pow (K - p) = u * pow K
  by rewrite uE_pow -bpow_plus; congr bpow; lia.
have Fq : format (nth 0 (vecSum l) q) by apply: HfV; apply: mem_nth.
have Ftail : {in drop q.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
have FB : format (pow K) by apply: format_pow.
apply: (vseb_head_lt_of_merge_mass (B := pow K)) => //; last by lra.
by rewrite Hup in Hmass; nra.
Qed.

(* Draft 5.3, case [i_1 <= 3] (with [e_{i_1} >= 5/8 u]).  Splits on 5.2's     *)
(* "at the left of [i]": in the [x_{i_1-2} = -1+u] case [e_{i_1-1} = 0]       *)
(* forces [i_1 = 3] and then [|y_j| = |s_0| >= 1/2 u^{-1}], so                *)
(* [ulp(y_j) >= 1] while [|y_{j+1}| < 1]; in the [x_{i_1-2} = 1-u] case all   *)
(* the [e_i], [i <= i_1-2], are divisible by 1, which pins                    *)
(* [eps_{i_0} = -u] and gives the CANCELLATION                                *)
(* [|eps_{i_0} + e_{i_1}| <= 3/8 u] ([vsebAux_head_leB_merge] is built for    *)
(* it), after which the at most 3 remaining errors are [<= u^2].              *)
Lemma vseb_emit_viol_le3 (l : seq R) (k q : nat) (eps r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format eps -> TwoSum eps (nth 0 (vecSum l) k) = DWR r et ->
  ((k = 1)%N -> eps = nth 0 (vecSum l) 0) ->
  eps <> 0 ->
  (forall gg : Z, (forall m, (m < k)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul eps (pow gg)) ->
  format et -> (0 < k)%N -> (k < q)%N -> (q <= 3)%N ->
  (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q) ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd epsn0 Hgrid Fet Hk Hkq Hq3
       Hq en0 Hqn0 HK Ht Hulp Hviol.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Hpred : (q.-1.+1 = q)%N by rewrite prednK //; apply: ltnW.
have Hqsz : (q.-1.+1 < size l)%N by rewrite Hpred -Hszl.
have Hkq' : (k <= q.-1)%N by rewrite -ltnS Hpred.
have Hviol' : 5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q.-1.+1) by rewrite Hpred.
case: (vecSum_left_sum_cases Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0 HK
                             Hviol') => Hsum.
  have [Hs1 Hz] := vecSum_left_opp Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0 HK
                                   Hviol' Hsum.
  by apply: (vseb_emit_viol_le3_opp Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd
                                    epsn0 Hgrid Fet Hk Hkq Hq3 Hq en0 Hqn0 HK
                                    Ht Hulp Hviol Hz Hs1).
have [Hs0 He] := vecSum_left_same Heven Hqsz Hfmt Hnz Hsort Hpair Hkq' en0 HK
                                  Hviol' Hsum.
by apply: (vseb_emit_viol_le3_same Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd
                                   epsn0 Hgrid Fet Hk Hkq Hq3 Hq en0 Hqn0 HK Ht
                                   Hulp Hviol Hsum He Hs0).
Qed.

(* The THIRD tie the proof needs, and the only one that rounds DOWN.          *)
(* [pow e - pow(e-p) - pow(e-p-1)] is halfway between [pow e - 2 pow(e-p)]    *)
(* (mantissa [2^p - 2], EVEN) and [pow e - pow(e-p)] (mantissa [2^p - 1],     *)
(* odd), so ties-to-even sends it DOWN.  Same shape as                        *)
(* [RN_midpoint_even_lo], one notch lower; it is what excludes the mixed      *)
(* pair [(u-u^2, u-2u^2)] in the [u-2u^2] counting.                           *)
Lemma RN_midpoint_even_lo2 (e : Z) : ties_to_even choice ->
  RND (pow e - pow (e - p) - pow (e - p - 1)) = pow e - 2 * pow (e - p).
Proof.
move=> Heven.
have Hpe := bpow_gt_0 beta e.
have Hpep := bpow_gt_0 beta (e - p).
have Hpep1 := bpow_gt_0 beta (e - p - 1).
have Hhalf : pow (e - p) = 2 * pow (e - p - 1).
  have Haux : pow ((e - p - 1) + 1)%Z = 2 * pow (e - p - 1)
    by rewrite bpow_plus bpow_1 /=; lra.
  by rewrite -Haux; congr bpow; lia.
have He1 : pow e = 2 * pow (e - 1).
  have Haux : pow ((e - 1) + 1)%Z = 2 * pow (e - 1)
    by rewrite bpow_plus bpow_1 /=; lra.
  by rewrite -Haux; congr bpow; lia.
have H8 : pow (e - 1) = 8 * pow (e - 4).
  have -> : (e - 1 = 3 + (e - 4))%Z by lia.
  by rewrite bpow_plus /= /Z.pow_pos /=; lra.
have Hle4 : pow (e - p) <= pow (e - 4) by apply: bpow_le; lia.
have Hx0 : 0 < pow e - pow (e - p) - pow (e - p - 1) by lra.
have Hmagx : mag beta (pow e - pow (e - p) - pow (e - p - 1)) = e :> Z.
  by apply: mag_unique_pos; split; lra.
have Hcexp : cexp (pow e - pow (e - p) - pow (e - p - 1)) = (e - p)%Z.
  by rewrite /cexp Hmagx /FLX_exp.
have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
have Hpp : pow p = IZR (2 ^ p).
  have -> : (2 = radix2 :> Z)%Z by [].
  by rewrite IZR_Zpower //; lia.
have Hppg := bpow_gt_0 beta p.
have Hsm : mant (pow e - pow (e - p) - pow (e - p - 1)) = pow p - 1 - / 2.
  rewrite /scaled_mantissa Hcexp !Rmult_minus_distr_r -!bpow_plus.
  have -> : (e + - (e - p) = p)%Z by lia.
  have -> : (e - p + - (e - p) = 0)%Z by lia.
  have -> : (e - p - 1 + - (e - p) = -1)%Z by lia.
  by rewrite Hpm1 (pow0E beta).
have Hfloor : Zfloor (mant (pow e - pow (e - p) - pow (e - p - 1)))
                = (2 ^ p - 2)%Z.
  rewrite Hsm; apply: Zfloor_imp.
  have -> : (2 ^ p - 2 + 1 = 2 ^ p - 1)%Z by lia.
  by rewrite !minus_IZR -Hpp /=; lra.
have Hceil : Zceil (mant (pow e - pow (e - p) - pow (e - p - 1)))
               = (2 ^ p - 1)%Z.
  rewrite Hsm; apply: Zceil_imp.
  have -> : (2 ^ p - 1 - 1 = 2 ^ p - 2)%Z by lia.
  by rewrite !minus_IZR -Hpp /=; lra.
have HRD : round beta fexp Zfloor (pow e - pow (e - p) - pow (e - p - 1)) =
           pow e - 2 * pow (e - p).
  rewrite /round Hfloor Hcexp /F2R /= !minus_IZR -Hpp !Rmult_minus_distr_r.
  have -> : pow p * pow (e - p) = pow e by rewrite -bpow_plus; congr bpow; lia.
  by lra.
have HRU : round beta fexp Zceil (pow e - pow (e - p) - pow (e - p - 1)) =
           pow e - pow (e - p).
  rewrite /round Hceil Hcexp /F2R /= !minus_IZR -Hpp !Rmult_minus_distr_r.
  have -> : pow p * pow (e - p) = pow e by rewrite -bpow_plus; congr bpow; lia.
  by lra.
have Hmid :
  (pow e - pow (e - p) - pow (e - p - 1)) -
    round beta fexp Zfloor (pow e - pow (e - p) - pow (e - p - 1)) =
  round beta fexp Zceil (pow e - pow (e - p) - pow (e - p - 1)) -
    (pow e - pow (e - p) - pow (e - p - 1)).
  by rewrite HRD HRU; lra.
rewrite (@round_N_middle beta fexp choice _ Hmid) Hfloor.
have Heven2p : Z.even (2 ^ p) = true.
  have -> : (2 ^ p = 2 * 2 ^ (p - 1))%Z.
    by rewrite -Z.pow_succ_r; [congr (_ ^ _)%Z; lia | lia].
  by rewrite Z.even_mul.
have -> : choice (2 ^ p - 2) = false.
  by rewrite Heven Z.even_sub Heven2p.
exact: HRD.
Qed.

(* The PINNING behind the [u - 2u^2] counting, as pure arithmetic (the        *)
(* [interval_pin] pattern).  Two inputs of magnitude at most [u - u^2] whose  *)
(* rounded sum has magnitude exactly [2u - 2u^2] must sum EXACTLY.            *)
(*                                                                            *)
(* The rounded sum sits in [[u, 2u)], where the grid is [2u^2], so the error  *)
(* is at most [u^2] and [|a + b| >= 2u - 3u^2].  Each input is then at least  *)
(* [u - 2u^2 > u/2], hence lies on the [u^2] grid, so [|a|, |b| in            *)
(* {u - 2u^2, u - u^2}]; and opposite signs are impossible because they       *)
(* would leave [|a + b| <= u^2].  That leaves three sums: [2u - 4u^2] and     *)
(* [2u - 3u^2] round to themselves resp. DOWN ([RN_midpoint_even_lo2]), both  *)
(* missing [2u - 2u^2]; only [2u - 2u^2] survives, and it is a float.         *)
Lemma pair_pin_1m2u (a b : R) (k : Z) :
  ties_to_even choice ->
  format a -> format b ->
  Rabs a <= pow k - pow (k - p) ->
  Rabs b <= pow k - pow (k - p) ->
  Rabs (RND (a + b)) = 2 * pow k - pow (k - p + 1) ->
  RND (a + b) = a + b.
Proof.
move=> Heven Fa Fb Ha Hb Hs.
have HG := bpow_gt_0 beta k.
have Hg := bpow_gt_0 beta (k - p).
have H2g : pow (k - p + 1) = 2 * pow (k - p).
  have -> : (k - p + 1 = 1 + (k - p))%Z by lia.
  by rewrite bpow_plus bpow_1 /=; lra.
have H16 : 16 * pow (k - p) <= pow k.
  have Hle : pow (k - p) <= pow (k - 4) by apply: bpow_le; lia.
  have H16' : pow k = 16 * pow (k - 4).
    have Hp16 : (16 : R) = pow 4 by rewrite /= /Z.pow_pos /=; lra.
    by rewrite Hp16 -bpow_plus; congr bpow; lia.
  by lra.
have Hk1 : pow (k + 1) = 2 * pow k by rewrite bpow_plus bpow_1 /=; lra.
have Hkm1 : pow (k - 1) = / 2 * pow k.
  have Hp2' : (/ 2 : R) = pow (-1) by rewrite /= /Z.pow_pos /=; lra.
  by rewrite Hp2' -bpow_plus; congr bpow; lia.
have Hpp : pow k = IZR (2 ^ p) * pow (k - p).
  have Hpp' : pow p = IZR (2 ^ p).
    have -> : (2 = radix2 :> Z)%Z by [].
    by rewrite IZR_Zpower //; lia.
  by rewrite -Hpp' -bpow_plus; congr bpow; lia.
(* an input in [[u - 2u^2, u - u^2]] sits above [u/2], hence on the [u^2]     *)
(* grid, and only two multiples of [u^2] lie in that range                    *)
have Hpin : forall x : R, format x -> Rabs x <= pow k - pow (k - p) ->
              pow k - 2 * pow (k - p) <= Rabs x ->
              Rabs x = pow k - 2 * pow (k - p) \/
              Rabs x = pow k - pow (k - p).
  move=> x Fx Hxle Hxge.
  have xn0 : x <> 0 by move=> H0; move: Hxge; rewrite H0 Rabs_R0; lra.
  have Hmagx : mag beta x = k :> Z.
    by apply: mag_unique; split; [rewrite Hkm1|]; lra.
  have Hcx : cexp x = (k - p)%Z by rewrite /cexp Hmagx /FLX_exp.
  have [z Hz] : is_imul x (pow (k - p))
    by have := format_imul_cexp Fx; rewrite Hcx.
  have Habsz : Rabs x = IZR (Z.abs z) * pow (k - p).
    by rewrite Hz Rabs_mult (Rabs_pos_eq (pow (k - p))) ?abs_IZR //; lra.
  have Hz1 : IZR (2 ^ p) - 2 <= IZR (Z.abs z) by nra.
  have Hz2 : IZR (Z.abs z) <= IZR (2 ^ p) - 1 by nra.
  have Hzi : (Z.abs z = 2 ^ p - 2 \/ Z.abs z = 2 ^ p - 1)%Z.
    have H1 : (2 ^ p - 2 <= Z.abs z)%Z
      by apply: le_IZR; rewrite minus_IZR; lra.
    have H2 : (Z.abs z <= 2 ^ p - 1)%Z
      by apply: le_IZR; rewrite minus_IZR; lra.
    by lia.
  by case: Hzi => Hzi; [left|right]; rewrite Habsz Hzi !minus_IZR; nra.
(* the rounded sum lies in [[u, 2u)], so the grid there is [2u^2] and the     *)
(* rounding error is at most [u^2]                                            *)
have Hsn0 : RND (a + b) <> 0
  by move=> H0; move: Hs; rewrite H0 Rabs_R0; lra.
have Hmags : mag beta (RND (a + b)) = (k + 1)%Z :> Z.
  apply: mag_unique; rewrite (_ : (k + 1 - 1 = k)%Z); last by lia.
  by rewrite Hs H2g Hk1; split; lra.
have Hulps : ulp (RND (a + b)) = pow (k + 1 - p)
  by rewrite ulp_neq_0 // /cexp /FLX_exp Hmags.
have Hg1 : pow (k + 1 - p) = 2 * pow (k - p) by rewrite -H2g; congr bpow; lia.
have Herr : Rabs (RND (a + b) - (a + b)) <= / 2 * ulp (RND (a + b))
  by apply: error_le_half_ulp_round.
rewrite Hulps Hg1 in Herr.
have Hvge : 2 * pow k - 3 * pow (k - p) <= Rabs (a + b)
  by move: Herr Hs; rewrite H2g; split_Rabs; lra.
have Hage : pow k - 2 * pow (k - p) <= Rabs a
  by move: Hvge Hb; have := Rabs_triang a b; lra.
have Hbge : pow k - 2 * pow (k - p) <= Rabs b
  by move: Hvge Ha; have := Rabs_triang a b; lra.
(* opposite signs would leave [|a + b| <= u^2], far below [2u - 3u^2]         *)
have Hsign : Rabs (a + b) = Rabs a + Rabs b.
  case: (Rle_lt_dec 0 (a * b)) => [Hab|Hab]; first by split_Rabs; nra.
  by move: Hvge Ha Hb; split_Rabs; lra.
have Hg2 : pow (k + 1 - p - 1) = pow (k - p) by congr bpow; lia.
have Htie : RND (2 * pow k - 3 * pow (k - p)) = 2 * pow k - 4 * pow (k - p).
  have H := RN_midpoint_even_lo2 (k + 1) Heven.
  rewrite Hk1 Hg1 Hg2 in H.
  have -> : 2 * pow k - 3 * pow (k - p)
          = 2 * pow k - 2 * pow (k - p) - pow (k - p) by lra.
  by rewrite H; lra.
case: (Hpin a Fa Ha Hage) => Ha'; case: (Hpin b Fb Hb Hbge) => Hb'.
- (* [(u-2u^2, u-2u^2)]: the sum is [2u - 4u^2], below the error floor        *)
  by move: Hvge; rewrite Hsign Ha' Hb'; lra.
- (* the MIXED pairs sum to the tie [2u - 3u^2], which rounds DOWN            *)
  have Hv : Rabs (a + b) = 2 * pow k - 3 * pow (k - p)
    by rewrite Hsign Ha' Hb'; lra.
  suff : False by [].
  move: Hs; case: (Rle_lt_dec 0 (a + b)) => Hab.
    have -> : a + b = 2 * pow k - 3 * pow (k - p) by move: Hv; split_Rabs; lra.
    by rewrite Htie; split_Rabs; lra.
  have -> : a + b = - (2 * pow k - 3 * pow (k - p))
    by move: Hv; split_Rabs; lra.
  by rewrite (@RN_opp_sym p choice choice_sym) Htie; split_Rabs; lra.
- have Hv : Rabs (a + b) = 2 * pow k - 3 * pow (k - p)
    by rewrite Hsign Ha' Hb'; lra.
  suff : False by [].
  move: Hs; case: (Rle_lt_dec 0 (a + b)) => Hab.
    have -> : a + b = 2 * pow k - 3 * pow (k - p) by move: Hv; split_Rabs; lra.
    by rewrite Htie; split_Rabs; lra.
  have -> : a + b = - (2 * pow k - 3 * pow (k - p))
    by move: Hv; split_Rabs; lra.
  by rewrite (@RN_opp_sym p choice choice_sym) Htie; split_Rabs; lra.
(* [(u-u^2, u-u^2)]: equal magnitudes and equal signs, so [a + b = 2a]        *)
have Hba : b = a by move: Hsign Ha' Hb'; split_Rabs; lra.
apply: round_generic.
rewrite Hba.
have -> : a + a = a * pow 1 by rewrite bpow_1 /=; lra.
by apply: mult_bpow_exact_FLX.
Qed.

(* Draft 5.2, "at the right of [i]", case [e_i = u - 2u^2]: "so we must have  *)
(* [s_{i+1} >= u-u^2] with [x_{i+1} <= u-u^2], so either there is no more     *)
(* non-zero [e_{i'}] or [i <= 3]" -- here on the [i >= 3] side, where the     *)
(* disjunction must resolve to "no more non-zero [e_{i'}]".                   *)
(*                                                                            *)
(* Unlike the [e_i = u] case ([vecSum_right_of_i_count]) this does NOT close  *)
(* by the running-sum contradiction: [vecSum_run_ge_next_1m2u] only reaches   *)
(* [u - 2u^2], which sits BELOW the input ceiling [u - u^2], so a stranded    *)
(* running sum is not absurd.  What closes it is a PINNING: with [i >= 3]     *)
(* and [size l <= 6] the only live case is [size l = 6], [i = 3], where the   *)
(* running sum [|s_3| = 2u - 2u^2] is [RND(x_4 + x_5)] with                   *)
(* [|x_4|, |x_5| <= u - u^2].  The midpoint [2u - 3u^2] is a TIE that         *)
(* ties-to-even sends DOWN (its lower neighbour [2u - 4u^2] has the even      *)
(* mantissa), so [x_4 + x_5 > 2u - 3u^2]; both inputs then sit on the [u^2]   *)
(* grid inside [(u - 2u^2, u - u^2]], forcing [x_4 = x_5 = +-(u - u^2)] and   *)
(* hence [x_4 + x_5 = +-(2u - 2u^2)] EXACTLY, i.e. [e_5 = 0].                 *)
Lemma vecSum_no_more_err_of_1m2u (l : seq R) (i j : nat) (k : Z) :
  ties_to_even choice -> (size l <= 6)%N -> (i.+1 < size l)%N ->
  {in l, forall z, format z} ->
  (forall m, (m < size l)%N -> nth 0 l m <> 0) ->
  sorted_mag l -> pairwise_ulp l -> (j <= i)%N ->
  nth 0 (vecSum l) j <> 0 -> uls (nth 0 (vecSum l) j) = pow k ->
  5 / 8 * pow k <= Rabs (nth 0 (vecSum l) i.+1) ->
  Rabs (nth 0 (vecSum l) i.+1) = pow k - pow (k - p + 1) ->
  (2 < i)%N ->
  forall m, (i.+1 < m)%N -> nth 0 (vecSum l) m = 0.
Proof.
move=> Heven Hsz6 Hi Hf Hnz Hsort Hpair Hji Hej0 Huls Hviol Heq Hi3 m Hm.
have Hpk := bpow_gt_0 beta k.
have Hgk := bpow_gt_0 beta (k - p + 1).
have Hszl : size (vecSum l) = size l
  by rewrite size_vecSum prednK //; apply: ltn_trans Hi.
case: (ltnP m (size (vecSum l))) => [Hmsz|Hge]; last by rewrite nth_default.
have Hmlt : (m < size l)%N by rewrite -Hszl.
(* [i >= 3] and [size l <= 6] leave exactly one live configuration            *)
have Hm5 : m = 5%N.
  have H1 : (5 <= m)%N by apply: leq_trans Hm; rewrite !ltnS.
  have H2 : (m <= 5)%N by rewrite -ltnS; apply: leq_trans Hmlt _.
  by apply/eqP; rewrite eqn_leq H2 H1.
have Hieq : i = 3%N.
  apply/eqP; rewrite eqn_leq Hi3 andbT.
  by move: Hm; rewrite Hm5 !ltnS.
have Hsz : size l = 6%N.
  by apply/eqP; rewrite eqn_leq Hsz6 /=; move: Hmlt; rewrite Hm5.
rewrite Hm5.
(* the running sum is [RND(x_4 + x_5)] and [e_5] is its error                 *)
have H5sz : (4.+1 < size l)%N by rewrite Hsz.
have Hrnd := vecSum_run_rnd H5sz.
have Hlast : (vecSumAux (drop 5 l)).2 = nth 0 l 5
  by apply: vecSum_run_last; rewrite Hsz.
rewrite Hlast in Hrnd.
have F4 : format (nth 0 l 4) by apply: Hf; apply: mem_nth; rewrite Hsz.
have F5 : format (nth 0 l 5) by apply: Hf; apply: mem_nth; rewrite Hsz.
have Hstep := vecSum_run_step H5sz Hf.
rewrite Hlast in Hstep.
(* [Heq] picks 5.2's case 2, which pins [|s_3| = 2u - 2u^2]                   *)
have Hcases := vecSum_right_of_i_cases Heven Hi Hf Hnz Hsort Hpair Hji Hej0
                                       Huls Hviol.
rewrite Hieq in Hcases.
rewrite Hieq in Heq.
have Hs : Rabs (RND (nth 0 l 4 + nth 0 l 5)) = 2 * pow k - pow (k - p + 1).
  rewrite -Hrnd.
  case: Hcases => [[He _]|[_ Hs2]|He]; last 1 first.
  - by move: Heq He; have := bpow_gt_0 beta (k - p + 1); lra.
  - by move: Heq He; lra.
  by [].
(* the draft's [x_{i+1} <= u - u^2] for both inputs                           *)
have [i' Hi'i Hxlt] :=
  vecSum_inputs_lt_u_of_violation Hi Hf Hsort Hpair Hji Hej0 Huls Hviol.
rewrite Hieq in Hi'i.
have Hi'2 : (i' <= 2)%N by rewrite -ltnS.
have Hi'3 : (i' <= 3)%N by apply: leq_trans Hi'2 _.
have Ha4 : Rabs (nth 0 l 4) <= pow k - pow (k - p)
  by apply: abs_le_pred_of_lt => //; apply: (Hxlt 2%N Hi'2); rewrite Hsz.
have Ha5 : Rabs (nth 0 l 5) <= pow k - pow (k - p)
  by apply: abs_le_pred_of_lt => //; apply: (Hxlt 3%N Hi'3); rewrite Hsz.
have Hexact := pair_pin_1m2u Heven F4 F5 Ha4 Ha5 Hs.
by move: Hstep; rewrite Hrnd Hexact; lra.
Qed.

(* Draft 5.3, case [i_1 >= 4] (with [e_{i_1} >= 5/8 u]): "in particular       *)
(* there is no need to consider beyond [r_{i_1}]".  5.2's                     *)
(* [vecSum_right_of_i_count] kills the [|e_{i_1}| = u] case here (it forces   *)
(* [i <= 3]); [|e_{i_1}| = u - 2u^2] needs 5.2's OTHER counting -- "either    *)
(* there is no more non-zero [e_{i'}] or [i <= 3]" -- and then                *)
(* [vseb_next_lt_of_1mu]; [|e_{i_1}| <= u - 4u^2] uses the stronger           *)
(* [vseb_next_1m2u] estimate plus one more error [<= u^2].                    *)
Lemma vseb_emit_viol_ge4 (l : seq R) (k q : nat) (r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format et -> (0 < k)%N -> (k < q)%N -> (3 < q)%N ->
  (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q) ->
  Rabs (nth 0 (vsebAux et (nth 0 (vecSum l) q :: drop q.+1 (vecSum l))) 0)
    < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq Hq4 Hq en0 Hqn0 HK Ht Hulp
       Hviol.
have Hpk := bpow_gt_0 beta K.
have Hu0 : 0 < u by apply: u_gt_0.
have Hu16 := u_le_inv16.
have Hulp0 : 0 < ulp r by have := Rabs_pos et; lra.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Hpred : (q.-1.+1 = q)%N by rewrite prednK //; apply: ltnW.
have Hqsz : (q.-1.+1 < size l)%N by rewrite Hpred -Hszl.
have Hkq' : (k <= q.-1)%N by rewrite -ltnS Hpred.
have Hviol' : 5 / 8 * pow K <= Rabs (nth 0 (vecSum l) q.-1.+1) by rewrite Hpred.
have Hi3 : (2 < q.-1)%N by rewrite -ltnS Hpred.
have Hp0 : pow (K - p) = u * pow K
  by rewrite uE_pow -bpow_plus; congr bpow; lia.
have Hp1 : pow (K - p + 1) = 2 * u * pow K.
  have -> : (K - p + 1 = 1 + (K - p))%Z by lia.
  by rewrite bpow_plus bpow_1 Hp0 /=; lra.
(* [i_1 >= 4] with [size l <= 6]: at most ONE error is left after [e_{i_1}]   *)
(* -- the draft's "no need to consider beyond [r_{i_1}]".                     *)
have Hszt : (size (drop q.+1 (vecSum l)) <= 1)%N.
  rewrite size_drop Hszl leq_subLR.
  apply: leq_trans Hsz6 _.
  by rewrite addSn addnC; move: Hq4; rewrite -addn1 -(leq_add2l 1) addnCA.
have Hmerge : forall (x : R) (tl : seq R), format x -> (size tl <= 1)%N ->
    nth 0 (vsebAux x tl) 0 = RND (x + nth 0 tl 0).
  by move=> x [|a [|b tl]] //= Fx _; rewrite Rplus_0_r round_generic.
have Fq : format (nth 0 (vecSum l) q)
  by apply: (format_vecSum Hfmt); apply: mem_nth.
have Frnd : format (RND (et + nth 0 (vecSum l) q))
  by apply: generic_format_round.
case: (vsebAux_head_step et (nth 0 (vecSum l) q) (drop q.+1 (vecSum l)))
      => [Hhd|[Hex Hhd]]; rewrite Hhd.
  (* INEXACT step: the head is [RND(eps + e_{i_1})], whatever follows         *)
  have Hcases := vecSum_right_of_i_cases Heven Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                         en0 HK Hviol'.
  rewrite Hpred in Hcases.
  case: Hcases => [[Heq _]|[Heq _]|Hle].
  - (* [|e_{i_1}| = u] is excluded here: 5.2's counting forces [i <= 3]       *)
    have := vecSum_right_of_i_count Heven Hsz6 Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                    en0 HK Hviol'.
    by rewrite Hpred => /(_ Heq); rewrite leqNgt Hi3.
  - apply: (vseb_next_lt_of_1mu (t := pow K)) => //.
    by rewrite Heq Hp1; lra.
  have H := vseb_next_1m2u (yj := r) (t := pow K) Ht Hulp.
  have Hb : Rabs (nth 0 (vecSum l) q) <= (1 - 4 * u) * pow K
    by move: Hle; rewrite Hp1; lra.
  by have := H _ Hb; nra.
(* EXACT step: the walk carries on from [eps + e_{i_1}], with one term left   *)
rewrite (Hmerge _ _ Frnd Hszt) nth_drop addn0.
have Htl : Rabs (nth 0 (vecSum l) (q.+1 + 0)) <= / 2 * u * ulp r.
  rewrite addn0.
  case: (ltnP q.+1 (size (vecSum l))) => [Hlt1|Hge1]; last first.
    by rewrite nth_default // Rabs_R0; nra.
  have [i' Hi'q Htail] :=
    vecSum_tail_err_le_u2_of_violation Heven Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                       en0 HK Hviol'.
  have Hn2 : ((q - 2).+2 = q)%N by rewrite -addn2 subnK //.
  have Hm3 : ((q - 2).+3 = q.+1)%N by rewrite -{2}Hn2.
  have Hi'm : (i' <= q - 2)%N by move: Hi'q; rewrite -{1}Hn2 -Hpred /= ltnS.
  have Hb := Htail _ Hi'm.
  rewrite Hm3 -Hszl in Hb.
  have Hb2 := Hb Hlt1.
  rewrite Hp0 in Hb2.
  by nra.
rewrite addn0 in Htl.
have Hcases := vecSum_right_of_i_cases Heven Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                       en0 HK Hviol'.
rewrite Hpred in Hcases.
case: Hcases => [[Heq _]|[Heq _]|Hle].
- have := vecSum_right_of_i_count Heven Hsz6 Hqsz Hfmt Hnz Hsort Hpair Hkq'
                                  en0 HK Hviol'.
  by rewrite Hpred => /(_ Heq); rewrite leqNgt Hi3.
- (* [|e_{i_1}| = u - 2u^2]: the draft's OTHER counting says nothing          *)
  (* non-zero is left, and then the merged word IS the emitted head           *)
  have Heq' : Rabs (nth 0 (vecSum l) q.-1.+1) = pow K - pow (K - p + 1)
    by rewrite Hpred.
  have Hz : nth 0 (vecSum l) q.+1 = 0.
    apply: (vecSum_no_more_err_of_1m2u Heven Hsz6 Hqsz Hfmt Hnz Hsort Hpair
                                       Hkq' en0 HK Hviol' Heq' Hi3).
    by rewrite Hpred ltnSn.
  rewrite Hz Rplus_0_r round_generic //.
  have H := vseb_next_1mu (yj := r) (t := pow K) Ht Hulp.
  have Hb : Rabs (nth 0 (vecSum l) q) <= (1 - 2 * u) * pow K
    by move: Heq; rewrite Hp1; lra.
  by have := H _ Hb; nra.
have H := vseb_next_1m2u (yj := r) (t := pow K) Ht Hulp.
have Hb : Rabs (nth 0 (vecSum l) q) <= (1 - 4 * u) * pow K
  by move: Hle; rewrite Hp1; lra.
by apply: vseb_merge_lt => //; apply: (H _ Hb).
Qed.

(* The draft's 5.3 CASE STUDY, with both of its indices in hand: [k] is       *)
(* [i_0] (the error consumed at this emit, whose [uls] is the draft's         *)
(* normalising [u = pow K]) and [q] is [i_1] (the first non-zero error        *)
(* after it).  [et] is [eps_{i_0}], [r] is [y_j].  The three inequalities     *)
(* are the draft's opening: [|eps_{i_0}| >= u] and [ulp(y_j) >= 2|eps_{i_0}|].*)
Lemma vseb_emit_cases (l : seq R) (k q : nat) (eps r et : R) (K : Z) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format eps -> TwoSum eps (nth 0 (vecSum l) k) = DWR r et ->
  ((k = 1)%N -> eps = nth 0 (vecSum l) 0) ->
  eps <> 0 ->
  (forall gg : Z, (forall m, (m < k)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul eps (pow gg)) ->
  format et -> (0 < k)%N -> (k < q)%N -> (q < size (vecSum l))%N ->
  nth 0 (vecSum l) k <> 0 -> nth 0 (vecSum l) q <> 0 ->
  uls (nth 0 (vecSum l) k) = pow K ->
  pow K <= Rabs et -> 2 * Rabs et <= ulp r ->
  Rabs (nth 0 (vsebAux et (drop q (vecSum l))) 0) < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd epsn0 Hgrid Fet Hk Hkq Hq
       en0 Hqn0 HK Ht Hulp.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hpk := bpow_gt_0 beta K.
have Hq2 : (1 < q)%N by apply: leq_ltn_trans Hk Hkq.
have Hl0 : (0 < size l)%N.
  move: Hq Hq2; rewrite size_vecSum.
  by case: (size l) => [|n] //= H1 H2; have := leq_ltn_trans H2 H1.
have Hszl : size (vecSum l) = size l by rewrite size_vecSum prednK.
have Hpred : (q.-1.+1 = q)%N by rewrite prednK //; apply: ltnW.
have Hqsz : (q.-1.+1 < size l)%N by rewrite Hpred -Hszl.
rewrite (drop_nth 0 Hq).
case: (Rle_lt_dec (5 / 8 * pow K) (Rabs (nth 0 (vecSum l) q))) => [Hviol|Hlt].
  (* the draft's *2 violation; split on [i_1 <= 3] vs [i_1 >= 4]              *)
  case: (leqP q 3) => [Hq3|Hq4].
    by apply: (vseb_emit_viol_le3 Heven Hsz6 Hfmt Hnz Hsort Hpair Feps HE Hhd
                                  epsn0 Hgrid Fet Hk Hkq Hq3 Hq en0 Hqn0 HK Ht
                                  Hulp Hviol).
  by apply: (vseb_emit_viol_ge4 Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq
                                Hq4 Hq en0 Hqn0 HK Ht Hulp Hviol).
case: (Rlt_le_dec (Rabs (nth 0 (vecSum l) q)) (/ 2 * pow K)) => [Hlt2|Hge2];
    last first.
  (* [1/2 u <= |e_{i_1}| < 5/8 u]: both draft sub-cases at once, via the *2   *)
  (* divisibility -- from the ulp when [> 1/2 u], from ties-to-even when      *)
  (* [= 1/2 u].                                                               *)
  apply: (vseb_emit_of_imul Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq Hq en0
                            HK Ht Hulp _ (Rlt_le _ _ Hlt)).
  case: (Rle_lt_or_eq_dec _ _ Hge2) => [Hgt|Heq].
    by apply: (vecSum_run_imul_of_gt_half Hqsz Hfmt); rewrite Hpred.
  by apply: (vecSum_run_imul_of_half Heven Hqsz Hfmt); rewrite Hpred.
have Fq : format (nth 0 (vecSum l) q) by apply: HfV; apply: mem_nth.
have Ftail : {in drop q.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
(* "we are adding at most 3 of them" -- where [size l <= 6] is paid           *)
have Hszt : (size (drop q.+1 (vecSum l)) <= 3)%N.
  rewrite size_drop Hszl leq_subLR.
  apply: leq_trans Hsz6 _.
  by rewrite addSn addnC; move: Hq2; rewrite -addn1 -(leq_add2l 3) addnCA.
have Hdomt : forall z, z \in drop q.+1 (vecSum l) ->
                        Rabs z <= uls (nth 0 (vecSum l) q).
  move=> z /(nthP 0)[j Hj <-]; rewrite nth_drop.
  apply: vecSum_tail_le_uls => //; first by rewrite addSn ltnS leq_addr.
  by move: Hj; rewrite size_drop ltn_subRL addnC.
case: (Req_EM_T (Rabs (nth 0 (vecSum l) q)) (/ 4 * pow K)) => [Heq4|Hne4].
  by apply: (vseb_emit_quarter Heven Hsz6 Hfmt Hnz Hsort Hpair Fet Hk Hkq Hq
                               en0 Hqn0 HK Ht Hulp Heq4).
by apply: (vseb_emit_lt_half (K := K) Fet Fq Ftail Hqn0 Ht Hulp Hlt2 Hne4
                             Hszt Hdomt).
Qed.

(* THE per-emit obligation, reduced to the case study: locate the draft's     *)
(* [i_1] ([seq_first_nonzero]), skip the zeros in between                     *)
(* ([vsebAux_drop0s]), and hand over.  If nothing non-zero is left the walk   *)
(* emits the remainder itself and [vsebBlock_obligation_zeros] closes it.     *)
Lemma vecSum_emit_obligation (l : seq R) (k : nat) (eps r et : R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  format eps -> eps <> 0 -> (0 < k)%N -> (k < size (vecSum l))%N ->
  ((k = 1)%N -> eps = nth 0 (vecSum l) 0) ->
  (forall gg : Z, (forall m, (m < k)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul eps (pow gg)) ->
  vsebDom (vecSum l) k eps ->
  TwoSum eps (nth 0 (vecSum l) k) = DWR r et -> et <> 0 ->
  Rabs (nth 0 (vsebAux et (drop k.+1 (vecSum l))) 0) < ulp r.
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair Feps epsn0 Hk Hk0 Hhd Hgrid Hdom E
       Hetn0.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Fe : format (nth 0 (vecSum l) k) by apply: HfV; apply: mem_nth.
have Fet : format et by have := format_TwoSum Feps Fe; rewrite E; case.
have Hftail : {in drop k.+1 (vecSum l), forall z, format z}
  by move=> z /mem_drop; apply: HfV.
have en0 : nth 0 (vecSum l) k <> 0.
  by move=> H0; apply: Hetn0; have := dwl_TwoSum_r0 Feps; rewrite -H0 E.
have Hle : uls (nth 0 (vecSum l) k) <= uls eps
  by case: Hdom => [H0|H]; [case: epsn0|apply: H].
have Hulp : 2 * Rabs et <= ulp r
  by have := vseb_emit_ulp_ge Feps Fe; rewrite E.
have Ht : uls (nth 0 (vecSum l) k) <= Rabs et.
  have := vseb_emit_abs_ge Feps Fe epsn0 en0 Hle.
  by rewrite E /=; apply.
have [K HK] := uls_pow en0.
case: (seq_first_nonzero (leq_subr k.+1 (size (vecSum l)))) => [Hall|].
  (* nothing non-zero is left: the walk emits the remainder itself            *)
  apply: vsebBlock_obligation_zeros => // z.
  move=> /(nthP 0)[m Hm <-].
  rewrite nth_drop; apply: Hall; first exact: leq_addr.
  by move: Hm; rewrite size_drop ltn_subRL addnC.
move=> [q /andP[Hq1 Hq2] [Hqn0 Hqz]].
have Hdd : drop (q - k.+1) (drop k.+1 (vecSum l)) = drop q (vecSum l)
  by rewrite drop_drop subnK.
rewrite (vsebAux_drop0s Fet (k := (q - k.+1)%N)); first last.
- move=> m Hm; rewrite nth_drop; apply: Hqz; first exact: leq_addr.
  by move: Hm; rewrite ltn_subRL addnC.
- rewrite size_drop; apply: ltn_sub2r => //.
  exact: leq_ltn_trans Hq1 Hq2.
rewrite Hdd.
by apply: (vseb_emit_cases Heven Hsz6 Hfmt Hnz Hsort Hpair Feps E Hhd epsn0
                           Hgrid Fet Hk Hq1 Hq2 en0 Hqn0 HK); rewrite -?HK.
Qed.

(* The walk, by induction on the SUFFIX.  Merges are handled by               *)
(* [vsebDom_merge] and recursion; emits split into the draft's per-emit       *)
(* obligation ([vecSum_emit_obligation]) and the recursion.                   *)
Lemma vecSum_vsebBlock_gen (l : seq R) (n k : nat) (eps : R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  (size (vecSum l) - k <= n)%N -> format eps -> (0 < k)%N ->
  ((k = 1)%N -> eps = nth 0 (vecSum l) 0) ->
  (forall gg : Z, (forall m, (m < k)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul eps (pow gg)) ->
  vsebDom (vecSum l) k eps ->
  vsebBlock eps (drop k (vecSum l)).
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hch := vecSum_ulsChain Heven Hfmt Hnz Hsort Hpair.
elim: n k eps => [|n IH] k eps Hn Feps Hk Hhd Hgrid Hdom.
  have Hge : (size (vecSum l) <= k)%N.
    by rewrite -subn_eq0; apply/eqP; case: (size (vecSum l) - k)%N Hn.
  by rewrite drop_oversize.
case: (ltnP k.+1 (size (vecSum l))) => [Hk1|Hk1]; last first.
  have Hsz1 : (size (drop k (vecSum l)) <= 1)%N
    by rewrite size_drop leq_subLR addnC.
  by case: (drop k (vecSum l)) Hsz1 => [|a [|b tl]].
have Hk0 : (k < size (vecSum l))%N by apply: ltn_trans (ltnSn k) Hk1.
have Hn' : (size (vecSum l) - k.+1 <= n)%N
  by rewrite subnS; move: Hn; case: (size (vecSum l) - k)%N => [|m] //=.
rewrite (drop_nth 0 Hk0).
have Hdrop : (0 < size (drop k.+1 (vecSum l)))%N by rewrite size_drop subn_gt0.
have [e2 [tl Hdr]] : exists e2 tl, drop k.+1 (vecSum l) = e2 :: tl.
  by case: (drop k.+1 (vecSum l)) Hdrop => [//|a s] _; exists a, s.
rewrite Hdr vsebBlock_consS.
have Fe : format (nth 0 (vecSum l) k) by apply: HfV; apply: mem_nth.
case E : (TwoSum eps (nth 0 (vecSum l) k)) => [r et].
have [Fr Fet] : format r /\ format et
  by have := format_TwoSum Feps Fe; rewrite E.
case: (Req_EM_T et 0) => [Het0|Hetn0].
  change (vsebBlock r (e2 :: tl)); rewrite -Hdr; apply: IH => //.
      by move: Hk; case: (k) => // n' _ [].
    move=> gg Hall.
    have Hr : r = RND (eps + nth 0 (vecSum l) k)
      by have := TwoSum_hi eps (nth 0 (vecSum l) k); rewrite E.
    rewrite Hr; apply: is_imul_pow_round; apply: is_imul_add;
      last by apply: Hall.
    by apply: Hgrid => m Hm; apply: Hall; apply: leqW.
  by apply: (vsebDom_merge HfV Hch Feps Hk0 Hdom); rewrite E Het0.
change (Rabs (nth 0 (vsebAux et (e2 :: tl)) 0) < ulp r
        /\ vsebBlock et (e2 :: tl)).
(* [eps = 0] would make the step EXACT, so this emit forces [eps <> 0] --     *)
(* the draft's "[eps_{i_0} <> 0]".                                            *)
have epsn0 : eps <> 0.
  move=> Heps0; apply: Hetn0.
  have Hhi : r = nth 0 (vecSum l) k.
    have := TwoSum_hi eps (nth 0 (vecSum l) k).
    by rewrite E /= Heps0 Rplus_0_l round_generic.
  move: E (TwoSum_correct_loc Feps Fe).
  case: (TwoSum eps (nth 0 (vecSum l) k)) => s e [-> ->] /= H.
  by move: H Hhi; rewrite Heps0; lra.
have Hdom' : vsebDom (vecSum l) k.+1 et
  by apply: (vsebDom_emit HfV Hch Feps epsn0 Hk0 Hdom E Hetn0).
have Hgrid' : forall gg : Z, (forall m, (m < k.+1)%N ->
       is_imul (nth 0 (vecSum l) m) (pow gg)) -> is_imul et (pow gg).
  move=> gg Hall.
  have Heps' : is_imul eps (pow gg)
    by apply: Hgrid => m Hm; apply: Hall; apply: leqW.
  have Hek := Hall k (ltnSn k).
  have Hc : r + et = eps + nth 0 (vecSum l) k.
    move: E (TwoSum_correct_loc Feps Fe).
    case: (TwoSum eps (nth 0 (vecSum l) k)) => s e [-> ->] H.
    by rewrite /= in H; lra.
  have -> : et = (eps + nth 0 (vecSum l) k) - r by lra.
  apply: is_imul_minus; first by apply: is_imul_add.
  have Hr : r = RND (eps + nth 0 (vecSum l) k)
    by have := TwoSum_hi eps (nth 0 (vecSum l) k); rewrite E.
  by rewrite Hr; apply: is_imul_pow_round; apply: is_imul_add.
split; last first.
  rewrite -Hdr; apply: IH => //.
  by move: Hk; case: (k) => // n' _ [].
rewrite -Hdr.
by apply: (vecSum_emit_obligation Heven Hsz6 Hfmt Hnz Hsort Hpair Feps
                                  epsn0 Hk Hk0 Hhd Hgrid Hdom E Hetn0).
Qed.

(* THE remaining core, assembled: the VecSum error sequence satisfies the     *)
(* draft's per-emit block bound.                                              *)
Lemma vecSum_vsebBlock (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  vsebBlock (head 0 (vecSum l)) (behead (vecSum l)).
Proof.
move=> Heven Hsz6 Hfmt Hnz Hsort Hpair.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have Hch := vecSum_ulsChain Heven Hfmt Hnz Hsort Hpair.
have Hhd : head 0 (vecSum l) = nth 0 (vecSum l) 0 by case: (vecSum l).
have -> : behead (vecSum l) = drop 1 (vecSum l) by rewrite drop1.
apply: (vecSum_vsebBlock_gen (n := size (vecSum l))) => //.
- exact: leq_subr.
- rewrite Hhd; case: (vecSum l) HfV => [|a tl] HfV;
    first by apply: generic_format_0.
  by apply: HfV; rewrite inE eqxx.
- by move=> gg Hall; rewrite Hhd; apply: Hall.
rewrite Hhd.
case: (Req_EM_T (nth 0 (vecSum l) 0) 0) => [Hz|Hn0]; first by left.
by right=> m Hm Hmsz Hnm; apply: Hch.
Qed.

(* ===========================================================================*)
(*  LAYER 2 (the draft's Theorem 7 proper): the ZERO-FREE case.               *)
(*                                                                            *)
(*  This is what doc/thm6.md 5.1-5.3 actually proves.  The draft's [x_i] are  *)
(*  nonzero throughout -- it takes [uls(e_j)] and divides by it -- and our    *)
(*  [vecSum_run_ufp] / [vecSum_err_ufp] likewise need [Hnz].  Zeros are OUR   *)
(*  obligation, discharged in layer 1 below.                                  *)
(* ===========================================================================*)
Lemma vecSum_vseb_Pnonoverlap_nz (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  Pnonoverlap (vseb (vecSum l)).
Proof.
move=> Heven Hsz Hfmt Hnz Hsort Hpair.
have HfV : {in vecSum l, forall z, format z} by apply: format_vecSum.
have HM := vecSum_vsebBlock Heven Hsz Hfmt Hnz Hsort Hpair.
rewrite /vseb; case E : (vecSum l) HfV HM => [|e0 tl] HfV HM.
  by move=> i; rewrite /= ltn0.
apply: vsebAux_Pnonoverlap_block => //.
- by apply: HfV; rewrite inE eqxx.
by move=> z zI; apply: HfV; rewrite inE zI orbT.
Qed.

(* ===========================================================================*)
(*  LAYER 1: zeros.  Under [sorted_mag] the zeros of [l] form a SUFFIX, so a  *)
(*  list is either zero-free (layer 2) or ends in a zero, which we peel.      *)
(* ===========================================================================*)

(* [sorted_mag] makes the zeros a suffix: a nonzero LAST entry forces every   *)
(* entry nonzero, since [|nth i| >= |last| > 0] along the chain.              *)
Lemma sorted_mag_last_nz (m : seq R) (x : R) :
  sorted_mag (rcons m x) -> x <> 0 ->
  forall i, (i < size (rcons m x))%N -> nth (0:R) (rcons m x) i <> 0.
Proof.
move=> Hsort xn0 i Hi.
have Hlast : nth (0:R) (rcons m x) (size m) = x by rewrite nth_rcons ltnn eqxx.
have Hsz : size (rcons m x) = (size m).+1 by rewrite size_rcons.
(* Walk down from the last index, using one [sorted_mag] step at a time.      *)
have Hdown : forall d, (d <= size m)%N ->
    nth (0:R) (rcons m x) (size m - d) <> 0.
  elim=> [_|d IH Hd]; first by rewrite subn0 Hlast.
  have Hd' : (d <= size m)%N by apply: ltnW.
  have Hlt : (size m - d.+1).+1 = (size m - d)%N by rewrite subnSK.
  have Hin : ((size m - d.+1).+1 < size (rcons m x))%N.
    by rewrite Hlt Hsz ltnS leq_subr.
  move=> Hz; apply: (IH Hd').
  have := Hsort _ Hin; rewrite Hlt Hz Rabs_R0 => Habs.
  by apply/Rabs_eq_R0/Rle_antisym => //; apply: Rabs_pos.
have -> : i = (size m - (size m - i))%N by rewrite subKn // -ltnS -Hsz.
by apply: Hdown; apply: leq_subr.
Qed.

(* [vecSumAux] on a list with a trailing zero: the deepest step is            *)
(* [2Sum(x_{n-1}, 0) = (x_{n-1}, 0)] (exact, since [x_{n-1}] is a float), so  *)
(* the running sum is unchanged and the emitted error is a trailing zero.     *)
Lemma vecSumAux_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSumAux (rcons m 0) =
    (rcons (vecSumAux m).1 0, (vecSumAux m).2).
Proof.
case: m => [//|a m _]; elim: m a => [a aF|b m IH a abF].
  have Fa : format a by apply: aF; rewrite inE eqxx.
  have -> : rcons [:: a] 0 = [:: a, 0 & [::]] by [].
  rewrite vecSumAux_cons.
  have E0 : vecSumAux [:: 0] = ([::], 0) by [].
  have Ea : vecSumAux [:: a] = ([::], a) by [].
  rewrite E0 Ea; case E : (TwoSum a 0) => [si ei1].
  have := dwh_TwoSum_r0 Fa; rewrite E /= => ->.
  by have := dwl_TwoSum_r0 Fa; rewrite E /= => ->.
have Hbm : {in b :: m, forall z, format z}.
  by move=> z zI; apply: abF; rewrite inE zI orbT.
have IH' := IH b Hbm; rewrite rcons_cons in IH'.
rewrite rcons_cons vecSumAux_cons rcons_cons vecSumAux_cons IH'.
by case: (vecSumAux (b :: m)) => es s /=; case: (TwoSum a s).
Qed.

(* VecSum carries a trailing zero through untouched: the running sum entering *)
(* the last step is [s = 0], so [2Sum(x_{n-2}, 0) = (x_{n-2}, 0)] and the     *)
(* emitted error is [0].                                                      *)
Lemma vecSum_rcons0 (m : seq R) :
  (0 < size m)%N -> {in m, forall z, format z} ->
  vecSum (rcons m 0) = rcons (vecSum m) 0.
Proof.
move=> Hs Hf; rewrite /vecSum vecSumAux_rcons0 //.
by case: (vecSumAux m) => es s /=.
Qed.

(* VSEB absorbs a trailing zero at the [vsebAux] level: the terminal step is  *)
(* [2Sum(_, 0) = (_, 0)], whose zero error either is dropped (output          *)
(* unchanged) or, at the very last position, emitted as a trailing zero.      *)
Lemma vsebAux_rcons0 (l : seq R) (eps : R) :
  format eps -> {in l, forall z, format z} ->
  vsebAux eps (rcons l 0) = vsebAux eps l \/
  vsebAux eps (rcons l 0) = rcons (vsebAux eps l) 0.
Proof.
(* [vsebAux w [:: 0] = [:: w; 0]]: a trailing zero is an exact merge.         *)
have vseb0 : forall w : R, format w -> vsebAux w [:: 0] = [:: w; 0].
  move=> w wF; rewrite vsebAux_1; case Ew : (TwoSum w 0) => [z0 z1].
  have := dwh_TwoSum_r0 wF; rewrite Ew /= => ->.
  by have := dwl_TwoSum_r0 wF; rewrite Ew /= => ->.
elim: l eps => [|e l' IH] eps epsF lF.
  by right; rewrite (vseb0 _ epsF).
have eF : format e by apply: lF; rewrite inE eqxx.
have Fl' : {in l', forall z, format z}.
  by move=> z zI; apply: lF; rewrite inE zI orbT.
have [rF etF] : format (dwh (TwoSum eps e)) /\
                format (dwl (TwoSum eps e))
  by apply: format_TwoSum.
rewrite rcons_cons.
case: l' IH lF Fl' rF etF => [|e2 l2] IH lF Fl' rF etF.
  (* One remaining term: the trailing zero is either dropped or emitted last. *)
  have -> : e :: rcons [::] 0 = [:: e, 0 & [::]] by [].
  rewrite vsebAux_consS vsebAux_1.
  case E : (TwoSum eps e) => [r et].
  have rF' : format r by move: rF; rewrite E.
  have etF' : format et by move: etF; rewrite E.
  case: (Req_EM_T et 0) => [et0|etn0].
    by left; rewrite [is_left _]/= (vseb0 r rF') et0.
  by right; rewrite [is_left _]/= (vseb0 et etF').
(* Two or more terms: recurse, the zero travelling to the tail.               *)
have -> : e :: rcons (e2 :: l2) 0 = [:: e, e2 & rcons l2 0] by rewrite rcons_cons.
rewrite !vsebAux_consS.
case E : (TwoSum eps e) => [r et].
have rF' : format r by move: rF; rewrite E.
have etF' : format et by move: etF; rewrite E.
case: (Req_EM_T et 0) => [et0|etn0]; rewrite [is_left _]/= -rcons_cons.
  exact: (IH r rF' Fl').
have [->|->] := IH et etF' Fl'; first by left.
by right; rewrite rcons_cons.
Qed.

(* VSEB absorbs a trailing zero: [2Sum(eps, 0) = (eps, 0)] has zero error, so *)
(* nothing is emitted and the remainder is carried.  The output therefore     *)
(* either is unchanged or gains a single trailing zero.                       *)
Lemma vseb_rcons0 (X : seq R) :
  (0 < size X)%N -> {in X, forall z, format z} ->
  vseb (rcons X 0) = vseb X \/ vseb (rcons X 0) = rcons (vseb X) 0.
Proof.
case: X => [//|e0 l'] _ Hf.
have e0F : format e0 by apply: Hf; rewrite inE eqxx.
have l'F : {in l', forall z, format z}.
  by move=> z zI; apply: Hf; rewrite inE zI orbT.
rewrite rcons_cons /vseb.
exact: vsebAux_rcons0.
Qed.

(* ===========================================================================*)
(*  Theorem 6 / draft Theorem 7 -- the target.                                *)
(* ===========================================================================*)
Lemma vecSum_vseb_Pnonoverlap (l : seq R) :
  ties_to_even choice ->
  (size l <= 6)%N ->
  {in l, forall z, format z} -> sorted_mag l -> pairwise_ulp l ->
  Pnonoverlap (vseb (vecSum l)).
Proof.
elim/last_ind: l => [_ _ _ _ _ i|m x IH Heven Hsz Hfmt Hsort Hpair].
  by rewrite /vseb /vecSum /= ltnS ltn0.
(* A nonzero last entry means the whole list is zero-free: layer 2 applies.   *)
case: (Req_dec x 0) => [x0|xn0]; last first.
  apply: vecSum_vseb_Pnonoverlap_nz => //.
  exact: sorted_mag_last_nz Hsort xn0.
(* Otherwise peel the trailing zero: VecSum passes it through, VSEB absorbs   *)
(* it, and the guard makes whatever trailing zero survives harmless.          *)
case: (posnP (size m)) => [/eqP|Hm].
  by rewrite size_eq0 => /eqP-> i; rewrite x0 /vseb /vecSum /= ltnS ltn0.
have Hfm : {in m, forall z, format z}.
  by move=> z zIm; apply: Hfmt; rewrite mem_rcons inE zIm orbT.
have Hrec : Pnonoverlap (vseb (vecSum m)).
  apply: IH => //.
  - by apply: leq_trans Hsz; rewrite size_rcons leqW.
  - exact: sorted_mag_rcons Hsort.
  exact: pairwise_ulp_rcons Hpair.
rewrite x0 vecSum_rcons0 //.
have Hsz0 : (0 < size (vecSum m))%N by rewrite size_vecSum.
have HfV : {in vecSum m, forall z, format z} by apply: format_vecSum.
have [->|->] := vseb_rcons0 Hsz0 HfV; first exact: Hrec.
exact: Pnonoverlap_rcons0.
Qed.

End SecThm6.
