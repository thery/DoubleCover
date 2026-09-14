(* ---------------------------------------------------------------------------*)
(* Algorithm 4 (VecSum) and the paper's Theorem 1 (its output is              *)
(* F-nonoverlapping).  A general round-to-nearest building block, generic     *)
(* over the precision [p] alone -- FLX (binary64 is fixed only in            *)
(* only when instantiated ([p = 53] = binary64)); built on [TwoSum] and [Nonoverlap].                 *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Uls.
Require Import TwoSum.
Require Import Nonoverlap.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Round-to-nearest TIES-TO-EVEN, as a condition on the tie-breaking [choice]:*)
(* on a tie, keep the even mantissa.  Strictly stronger than the symmetry     *)
(* [choice_sym] the rest of the development assumes; paper Theorem 6 genuinely*)
(* needs it (the same-binade running-sum bound lands on an exact rounding     *)
(* midpoint).  The paper's [RN] means ties-to-even (Section 1), so this is    *)
(* the paper's own assumption, not a strengthening of it -- it is the         *)
(* development that was more general.                                         *)
Definition ties_to_even (choice : Z -> bool) :=
  forall z : Z, choice z = ~~ Z.even z.

Section SecVecSum.

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

(* [p] is symbolic here (concrete only when instantiated ([p = 53] = binary64)), so the base-2 power  *)
(* identity that used to hold by computation needs [IZR_Zpower] ([0 <= p]).   *)
Lemma IZR_2powp : IZR (2 ^ p) = pow p.
Proof.
have -> : (2 = radix2 :> Z)%Z by [].
by rewrite IZR_Zpower //; lia.
Qed.

(* ===========================================================================*)
(*  Algorithm 4: VecSum                                                       *)
(*  On [x0; ...; x_{n-1}] returns [e0; ...; e_{n-1}] with the same            *)
(*  exact sum, processing from the least significant term.                    *)
(* ===========================================================================*)
Fixpoint vecSumAux (l : seq R) : seq R * R :=
  match l with
  | [::]    => ([::], 0)
  | [:: x]  => ([::], x)
  | x :: l' => let: (es, s) := vecSumAux l' in
               let: DWR si ei1 := TwoSum x s in
               (ei1 :: es, si)
  end.

Definition vecSum (l : seq R) : seq R :=
  let: (es, s0) := vecSumAux l in s0 :: es.

Lemma format_vecSum l :
  {in l, forall z, format z} -> {in vecSum l, forall z, format z}.
Proof.
move=> Hl /= z.
suff Hf ll a : vecSumAux l = (ll, a) -> 
                {in ll, forall z, format z}  /\ format a.
  case E : (vecSumAux l) => [ll a].
  have [llF aF] := Hf _ _ E.
  by rewrite /vecSum E inE => /orP[/eqP->|zIll] //; apply: llF.
elim: l ll a Hl => /= [ll a _ [<- <-]| b [| c l] IH ll a blF].
- split; first by move=> ?; rewrite in_nil.
  by apply: generic_format_0.
- case => <- <-; split; first by move=> ?; rewrite in_nil.
  by apply: blF; rewrite inE eqxx.
case E1 : (vecSumAux (c :: l)) => [ll1 d].
case => <- <-; split; last by apply: generic_format_round.
move=> z1; rewrite inE => /orP[/eqP->|z1Ill1].
  by apply: generic_format_round.
have cF : format c by apply: blF; rewrite !inE eqxx orbT.
case: (IH ll1 d) => // [z2 z2Icl|].
  by apply: blF; rewrite inE z2Icl orbT.
by move=> ll1F dF; apply: ll1F.
Qed.

(* The head of the output IS the final running sum [s_0].                     *)
Lemma vecSum_nth0 l : nth 0 (vecSum l) 0 = (vecSumAux l).2.
Proof. by rewrite /vecSum; case: (vecSumAux l). Qed.

Lemma vecSumAux_cons a b l :
  vecSumAux [::a, b & l] =
  let '(es, s) := vecSumAux (b :: l) in 
  let 'DWR si ei1 := TwoSum a s in (ei1 :: es, si).
Proof. by []. Qed.

Lemma size_vecSumAux l : size (vecSumAux l).1 = (size l).-1.
Proof.
elim: l => // a [//| b l].
rewrite vecSumAux_cons.
case : vecSumAux => c l1.
by case TwoSum => a3 b3 /= ->.
Qed.

Lemma size_vecSum l : size (vecSum l) = (size l).-1.+1.
Proof.
case: l => //= a l.
rewrite /vecSum.
by case: vecSumAux (size_vecSumAux (a :: l)) => ? ? /= ->.
Qed.

Lemma format_vecSumAux l : 
  {in l, forall z, format z} ->
  format (vecSumAux l).2 /\ {in (vecSumAux l).1, forall z, format z}.
Proof.
elim: l => [_|a [|b l] // IH ablF]; split => //.
- by apply: generic_format_0.
- by apply: ablF; rewrite inE eqxx.
- rewrite vecSumAux_cons.
  have /IH[] :  {in b :: l,  forall z : R, format z}.
    by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  case E : vecSumAux => [es s].
  case E1 : (TwoSum a s) => [si ei1] => sF esF.
  have Fa : format a by apply: ablF; rewrite inE eqxx.
  have [Hsi Hei1] : format (dwh (TwoSum a s)) /\ format (dwl (TwoSum a s))
    by exact: format_TwoSum Fa sF.
  rewrite E1 /= in Hsi Hei1.
  by first [exact: Hsi | exact: Hei1].
have /IH[] :  {in b :: l,  forall z : R, format z}.
  by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  rewrite vecSumAux_cons.
case E : vecSumAux => [es s].
case E1 : (TwoSum a s) => [si ei1] => sF esF.
move=> z; rewrite inE => /orP[/eqP->|zIes].
  have Fa : format a by apply: ablF; rewrite inE eqxx.
  have [Hsi Hei1] : format (dwh (TwoSum a s)) /\ format (dwl (TwoSum a s))
    by exact: format_TwoSum Fa sF.
  rewrite E1 /= in Hsi Hei1.
  by first [exact: Hsi | exact: Hei1].
by apply: esF.
Qed.

Lemma vecSum_sum l : 
  {in l, forall z, format z} -> sumR (vecSum l) = sumR l.
Proof.
rewrite /vecSum; elim: l => [|a [|b l] // IH ablF]; first by rewrite /=; lra.
rewrite vecSumAux_cons.
have : sumR (let '(es, s0) := vecSumAux (b :: l) in s0 :: es) = sumR (b :: l).
  by apply: IH => z zIl; apply: ablF; rewrite inE zIl orbT.
case E : vecSumAux => [es s] ssE; rewrite /= in ssE.
case E1 : (TwoSum a s) => [si ei1] /=.
have Fa : format a by apply: ablF; rewrite inE eqxx.
have Fs : format s.
  have [Hs _] :
      format (vecSumAux (b :: l)).2 /\
      {in (vecSumAux (b :: l)).1, forall z, format z}.
    by apply: format_vecSumAux => z zIl; apply: ablF; rewrite inE zIl !orbT.
  by move: Hs; rewrite E.
have Hc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s
  by exact: TwoSum_correct_loc Fa Fs.
rewrite E1 /= in Hc.
lra.
Qed.

(* Divisibility propagation -- the induction step of paper Thm 1 ("if"        *)
(* "2^k | s_i, x_{i-1}, ..., x_0 then 2^k | e_i, ..., e_0"). If every input   *)
(* lies on the grid [pow e], so does the running high word and every error:   *)
(* [2Sum] preserves it, the rounded sum via [is_imul_pow_round] and the exact *)
(* error via [is_imul_minus].  [format] is only used for the error identity.  *)
Lemma vecSumAux_imul e l :
  {in l, forall z, format z} -> {in l, forall z, is_imul z (pow e)} ->
  is_imul (vecSumAux l).2 (pow e) /\
  {in (vecSumAux l).1, forall z, is_imul z (pow e)}.
Proof.
elim: l => [_ _|a [|b l] // IH ablF ablM]; split => //.
- by exists 0%Z; rewrite Rmult_0_l.
- by apply: ablM; rewrite inE eqxx.
- rewrite vecSumAux_cons.
  have Ma : is_imul a (pow e) by apply: ablM; rewrite inE eqxx.
  have [sM _] : is_imul (vecSumAux (b :: l)).2 (pow e) /\
                {in (vecSumAux (b :: l)).1, forall z, is_imul z (pow e)}.
    apply: IH.
      by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
    by move=> z zIl; apply: ablM; rewrite inE zIl orbT.
  move: sM; case E : vecSumAux => [es s] sM.
  case E1 : (TwoSum a s) => [si ei1] /=.
  have := TwoSum_hi a s; rewrite E1 /= => ->.
  by apply: is_imul_pow_round; apply: is_imul_add.
rewrite vecSumAux_cons.
have Ma : is_imul a (pow e) by apply: ablM; rewrite inE eqxx.
have Fa : format a by apply: ablF; rewrite inE eqxx.
have [sM esM] : is_imul (vecSumAux (b :: l)).2 (pow e) /\
                {in (vecSumAux (b :: l)).1, forall z, is_imul z (pow e)}.
  apply: IH.
    by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
  by move=> z zIl; apply: ablM; rewrite inE zIl orbT.
have [Fs _] : format (vecSumAux (b :: l)).2 /\
              {in (vecSumAux (b :: l)).1, forall z, format z}.
  apply: format_vecSumAux.
  by move=> z zIl; apply: ablF; rewrite inE zIl orbT.
move: sM esM Fs; case E : vecSumAux => [es s] sM esM Fs.
case E1 : (TwoSum a s) => [si ei1] /=.
move=> z; rewrite inE => /orP[/eqP->|zIes]; last by apply: esM.
have Hsi : si = RND (a + s) by have := TwoSum_hi a s; rewrite E1.
have Hc : si + ei1 = a + s.
  have Hcc : dwh (TwoSum a s) + dwl (TwoSum a s) = a + s
    by exact: TwoSum_correct_loc Fa Fs.
  by move: Hcc; rewrite E1 /= => ->.
have -> : ei1 = (a + s) - si by lra.
apply: is_imul_minus; first by apply: is_imul_add.
by rewrite Hsi; apply: is_imul_pow_round; apply: is_imul_add.
Qed.

(* [ufp x] -- "unit in the first place": the weight [2^(mag x - 1)] of the    *)
(* leftmost bit, i.e. the largest power of two <= |x| (for x <> 0).  Paper    *)
(* Theorem 1 / Corollary 1 (p.3) state the VecSum input conditions with it.   *)
Definition repr (k : Z) (x : R) : Prop :=
  exists2 M : Z, (Z.abs M < 2 ^ p)%Z & x = IZR M * pow (k - p + 1)%Z.

(* Being [repr]-esentable at [k] makes [x] a float: it is [F2R] of the       *)
(* integer float [Float M (k-p+1)], whose mantissa is < 2^p (under FLX there  *)
(* is no constraint on the exponent).                                        *)
Lemma repr_format k x : repr k x -> format x.
Proof.
move=> [M Mlt ->].
apply: generic_format_FLX; exists (Float beta M (k - p + 1)%Z).
- by rewrite /F2R.
by exact: Mlt.
Qed.

(* Hypotheses of Theorem 1 on inputs [l] with a chosen exponent map [k]:      *)
(*  - every [x_i] is representable at exponent [k_i];                         *)
(*  - [k_{i-1} >= k_i + 1] for every pair but the last (strict exponent gap); *)
(*  - [k_{n-2} >= k_{n-1}] for the last pair (weak gap: allowed overlap).     *)
Definition Thm1_hyp (k : nat -> Z) (l : seq R) : Prop :=
  [/\ forall i, (i < size l)%N -> repr (k i) (nth 0 l i),
      forall i, (i.+2 < size l)%N -> (k i.+1 + 1 <= k i)%Z &
      forall i, i.+2 = size l -> (k i.+1 <= k i)%Z ].

(* "Firstly": the running high word [s_{i+1} = (vecSumAux (drop i.+1 l)).2]   *)
(* is bounded by [(2-2u) 2^(k_i)].  (paper: |s_i| <= (2-2u)2^(k_{i-1});       *)
(* we index by the *previous* position [i] to avoid [k_{-1}], which is exactly*)
(* the induction-hypothesis form used in the proof.)                          *)
Lemma VecSum_run_bound k l : Thm1_hyp k l ->
  forall i, (i.+1 < size l)%N ->
  Rabs (vecSumAux (drop i.+1 l)).2 <= (2 - 2 * u) * pow (k i).
Proof.
case=> Hrepr Hgap Hlast.
(* Each input is bounded: |x_j| = |M_j| 2^(k_j-p+1) <= (2^p-1) 2^(k_j-p+1)    *)
(*                              = (2 - 2u) 2^(k_j).                           *)
have Hx : forall j, (j < size l)%N ->
  Rabs (nth 0 l j) <= (2 - 2 * u) * pow (k j).
  move=> j jLs; have [M Mlt ->] := Hrepr j jLs.
  rewrite Rabs_mult (Rabs_pos_eq _ (bpow_ge_0 _ _)) -abs_IZR.
  have I2p := IZR_2powp.
  have Hkj : pow (k j) = pow (p - 1) * pow (k j - p + 1)
    by rewrite -bpow_plus; congr bpow; lia.
  have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
  have H2u : u * pow (p - 1) = / 2
    by rewrite uE -bpow_plus (_ : (- p + (p - 1))%Z = (-1)%Z);
       [exact: Hpm1 | lia].
  have Hpp : pow p = 2 * pow (p - 1).
    have H := bpow_plus beta 1 (p - 1); rewrite bpow_1 in H.
    rewrite (_ : (1 + (p - 1))%Z = p) in H; last by lia.
    by rewrite H /= /Z.pow_pos /=; lra.
  rewrite Hkj -Rmult_assoc; apply: Rmult_le_compat_r; first exact: bpow_ge_0.
  have -> : (2 - 2 * u) * pow (p - 1) = IZR (2 ^ p - 1)
    by rewrite minus_IZR I2p Hpp; nra.
  by apply: IZR_le; lia.
(* Downward induction on the suffix.  [s_{i+1} = (vecSumAux (drop i.+1 l)).2]:*)
(*  - base [i.+2 = size l]: [s_{i+1} = x_{i+1}], and                          *)
(*      |x_{i+1}| <= (2-2u) 2^(k_{i+1}) <= (2-2u) 2^(k_i)                     *)
(*    by the weak gap [k_i >= k_{i+1}] (Hlast);                               *)
(*  - step [i.+2 < size l]: [s_{i+1} = RN(x_{i+1} + s_{i+2})]; with the IH    *)
(*      |s_{i+2}| <= (2-2u) 2^(k_{i+1}) and |x_{i+1}| <= (2-2u) 2^(k_{i+1}),  *)
(*      |x_{i+1}| + |s_{i+2}| <= (4-4u) 2^(k_{i+1}) <= (2-2u) 2^(k_i)         *)
(*    by the strict gap [k_i >= k_{i+1} + 1] (Hgap), and rounding to nearest  *)
(*    preserves the bound.                                                    *)
move=> i iLs; have [d le_d] := ubnP (size l - i.+2).
elim: d i iLs le_d => // d IHd i iLs; rewrite ltnS => le_d.
have [Hi2|Hi2] := eqVneq i.+2 (size l).
- (* base: the suffix is the singleton [x_{i+1}], so s_{i+1} = x_{i+1}.       *)
  have Hdrop : drop i.+1 l = [:: nth 0 l i.+1]
    by rewrite (drop_nth 0) // Hi2 drop_size.
  rewrite Hdrop /=.
  apply: Rle_trans (Hx i.+1 iLs) _.
  apply: Rmult_le_compat_l; last by apply: bpow_le; exact: (Hlast i Hi2).
  have u_le_1 : u <= 1 by rewrite uE -(pow0E beta); apply: bpow_le; lia.
  lra.
(* step: the suffix has >= 2 elements, so s_{i+1} = RN(x_{i+1} + s_{i+2}).    *)
have iLs' : (i < size l)%N := ltn_trans (ltnSn i) iLs.
have Hi2lt : (i.+2 < size l)%N by rewrite ltn_neqAle Hi2 iLs.
have Hd1 : drop i.+1 l = nth 0 l i.+1 :: drop i.+2 l by rewrite (drop_nth 0).
have Hd2 : drop i.+2 l = nth 0 l i.+2 :: drop i.+3 l
  by rewrite (drop_nth 0) // Hi2lt.
have Hs : (vecSumAux (drop i.+1 l)).2
            = RND (nth 0 l i.+1 + (vecSumAux (drop i.+2 l)).2).
  rewrite Hd1 Hd2 vecSumAux_cons -Hd2.
  by case: (vecSumAux (drop i.+2 l)) => es s /=; rewrite /TwoSum.
rewrite Hs.
(* the tight bound B = (2 - 2u) 2^{k_i} is itself a float.                    *)
have Meq : (2 - 2 * u) * pow (k i) = IZR (2 ^ p - 1) * pow (k i - p + 1).
  have I2p := IZR_2powp.
  have Hki : pow (k i) = pow (p - 1) * pow (k i - p + 1)
    by rewrite -bpow_plus; congr bpow; lia.
  have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
  have Hu2 : u * pow (p - 1) = / 2
    by rewrite uE -bpow_plus (_ : (- p + (p - 1))%Z = (-1)%Z);
       [exact: Hpm1 | lia].
  have Hpp : pow p = 2 * pow (p - 1).
    have H := bpow_plus beta 1 (p - 1); rewrite bpow_1 in H.
    rewrite (_ : (1 + (p - 1))%Z = p) in H; last by lia.
    by rewrite H /= /Z.pow_pos /=; lra.
  rewrite Hki -Rmult_assoc; congr (_ * _).
  by rewrite minus_IZR I2p Hpp; nra.
have FB : format ((2 - 2 * u) * pow (k i)).
  rewrite Meq; apply: generic_format_FLX.
  exists (Float beta (2 ^ p - 1) (k i - p + 1)); first by rewrite /F2R /=.
  rewrite [Fnum _]/=; have h : (0 < 2 ^ p)%Z by apply: Z.pow_pos_nonneg; lia.
  rewrite Z.abs_eq; last by lia.
  by change (2 ^ p - 1 < 2 ^ p)%Z; lia.
(* the strict gap [k_i >= k_{i+1} + 1] gives [2 . 2^{k_{i+1}} <= 2^{k_i}].    *)
have Hgk : (k i.+1 + 1 <= k i)%Z by apply: Hgap.
have Hpowgap : 2 * pow (k i.+1) <= pow (k i).
  have E1 : pow (k i.+1 + 1) = 2 * pow (k i.+1)
    by rewrite bpow_plus bpow_1 /=; lra.
  by rewrite -E1; apply: bpow_le.
(* the tail running sum is bounded by the IH at [i.+1].                       *)
have s2_bnd : Rabs (vecSumAux (drop i.+2 l)).2 <= (2 - 2 * u) * pow (k i.+1).
  apply: IHd => //.
  by apply: (leq_trans _ le_d); rewrite subnS prednK ?subn_gt0 //.
have u_le_1 : u <= 1 by rewrite uE -(pow0E beta); apply: bpow_le; lia.
have HX := Hx i.+1 iLs.
(* rounding to nearest preserves the bound B, which is a float.               *)
apply: abs_round_le_generic; first exact: FB.
(* |x_{i+1}| + |s_{i+2}| <= (4 - 4u) 2^{k_{i+1}} <= (2 - 2u) 2^{k_i}.         *)
apply: Rle_trans (Rabs_triang _ _) _.
nra.
Qed.

(* The running high word [(vecSumAux m).2] of a VecSum is a float.            *)
Lemma format_vecSumAux2 m :
  {in m, forall z, format z} -> format (vecSumAux m).2.
Proof.
elim: m => [|a [|b m] IH] Hf.
- exact: generic_format_0.
- by have -> : (vecSumAux [:: a]).2 = a by []; apply: Hf; rewrite inE eqxx.
rewrite vecSumAux_cons.
case E : (vecSumAux (b :: m)) => [es s].
have -> :
  (let: DWR si ei1 := TwoSum a s in (ei1 :: es, si)).2 = dwh (TwoSum a s)
  by case: (TwoSum a s).
by rewrite TwoSum_hi; apply: generic_format_round.
Qed.

(* The [i]-th VecSum error [nth 0 (vecSumAux m).1 i] is the low word of the   *)
(* 2Sum combining [x_i] with the running sum [s_{i+1}] of the tail.           *)
Lemma vecSumAux_nth1 m i : (i.+1 < size m)%N ->
  nth 0 (vecSumAux m).1 i =
  dwl (TwoSum (nth 0 m i) (vecSumAux (drop i.+1 m)).2).
Proof.
elim: m i => [|a m' IH] i Hi.
  by move: Hi; rewrite /= ltn0.
case: m' IH Hi => [|b m] IH Hi.
  by move: Hi; rewrite /= ltnS ltn0.
rewrite vecSumAux_cons.
case E : (vecSumAux (b :: m)) => [es s].
case: i Hi => [|i] Hi.
  have -> : nth 0 [:: a, b & m] 0 = a by [].
  have -> : drop 1 [:: a, b & m] = b :: m by [].
  rewrite E [(es, s).2]/=.
  by case: (TwoSum a s).
rewrite ltnS in Hi.
have -> : nth 0 [:: a, b & m] i.+1 = nth 0 (b :: m) i by [].
have -> : drop i.+2 [:: a, b & m] = drop i.+1 (b :: m) by [].
by rewrite -(IH i) // E.
Qed.

(* The two LEADING limbs of a VecSum output are the two words of ONE 2Sum --  *)
(* the last one performed, [TwoSum x_0 s_1] -- so they are separated by a     *)
(* genuine HALF ulp, [2|e_1| <= ulp e_0].  This is strictly better than the   *)
(* P-nonoverlap [|e_1| < ulp e_0] of Theorem 1, and the factor 2 is exactly   *)
(* what a head argument needs: [(1 + 2u, -2u + 2u^2, ...)] is a legal         *)
(* P-nonoverlapping triple summing to [1 + O(u^2)], so no property of the     *)
(* OUTPUT alone can ever pin the leading limb (Algorithm 13, Section 8.3).    *)
Lemma vecSum_head_sep l :
  {in l, forall z, format z} -> (1 < size l)%N ->
  2 * Rabs (nth 0 (vecSum l) 1) <= ulp (nth 0 (vecSum l) 0).
Proof.
case: l => [|a [|b m]] // Hfmt _.
rewrite /vecSum vecSumAux_cons.
case E : (vecSumAux (b :: m)) => [es s].
have Fa : format a by apply: Hfmt; rewrite inE eqxx.
have Fs : format s.
  have Hf : format (vecSumAux (b :: m)).2.
    by apply: format_vecSumAux2 => z zI; apply: Hfmt; rewrite inE zI orbT.
  by move: Hf; rewrite E.
have Hm := magnitude_TwoSum Fa Fs.
move: Hm; rewrite /magnitudeDWR.
by case: (TwoSum a s) => h low /=; lra.
Qed.

(* Two crude, hypothesis-free size bounds on a VecSum, for callers that have  *)
(* absolute bounds on the inputs rather than the [Thm1_hyp] exponent          *)
(* representation.  They are what a head argument needs on the LOW part of a  *)
(* VecSum (Algorithm 13, Section 8.3): there the entries below the leading    *)
(* one are all [O(u)], so their accumulated rounding error is [O(u^2)] and    *)
(* becomes negligible against the half-ulp of the head.                       *)

(* The running sum never exceeds the total mass, up to one rounding per step. *)
Lemma vecSumAux_run_le l : {in l, forall z, format z} ->
  Rabs (vecSumAux l).2 <= (1 + u) ^ (size l) * sumRabs l.
Proof.
elim: l => [|x [|b l] IH] Hf.
- by rewrite /= Rabs_R0; lra.
- have -> : (vecSumAux [:: x]).2 = x by [].
  have Hu0 := u_gt_0; have := Rabs_pos x.
  by rewrite /=; nra.
rewrite vecSumAux_cons.
case E : (vecSumAux (b :: l)) => [es s].
have E2 : (let: DWR si ei1 := TwoSum x s in (ei1 :: es, si)).2 = RND (x + s).
  by rewrite -TwoSum_hi; case: (TwoSum x s).
rewrite E2.
have Hs : Rabs s <= (1 + u) ^ size (b :: l) * sumRabs (b :: l).
  have H : {in b :: l, forall z : R, format z}
    by move=> z zI; apply: Hf; rewrite inE zI orbT.
  by have := IH H; rewrite E.
have Hrel := @relative_error_le p beta Hp2 choice (x + s).
have Ht := Rabs_triang x s.
have Hu0 := u_gt_0.
have Hsr := sumRabs_ge0 (b :: l).
have Hx := Rabs_pos x.
have Hpow1 : 1 + u <= (1 + u) ^ size [:: x, b & l].
  have H1 : (1 + u) ^ 1 <= (1 + u) ^ size [:: x, b & l]
    by apply: Rle_pow; [lra | apply/leP; rewrite /=].
  by move: H1; rewrite /= Rmult_1_r.
have Hps : (1 + u) ^ size [:: x, b & l] = (1 + u) * (1 + u) ^ size (b :: l)
  by rewrite /=; ring.
have Hsum : sumRabs [:: x, b & l] = Rabs x + sumRabs (b :: l)
  by rewrite /=; ring.
have Hab := Rabs_pos (RND (x + s)).
have Hxs := Rabs_pos (x + s).
rewrite Hsum Hps.
have H4 : Rabs (RND (x + s)) <= (1 + u) * Rabs (x + s) by split_Rabs; lra.
by nra.
Qed.

(* VecSum is exact as a SUM ([vecSum_sum]); what the head alone loses is the  *)
(* accumulated rounding error, at most one [u] per step, against the total    *)
(* mass.  Since [sumR (vecSum l) = sumR l], this is also the total mass of    *)
(* the limbs BELOW the head.                                                  *)
Lemma vecSumAux_err_le l : {in l, forall z, format z} ->
  Rabs (sumR l - (vecSumAux l).2) <=
    INR (size l) * u * ((1 + u) ^ (size l) * sumRabs l).
Proof.
elim: l => [|x [|b l] IH] Hf.
- by rewrite /= Rminus_0_r Rabs_R0; lra.
- have -> : (vecSumAux [:: x]).2 = x by [].
  have -> : sumR [:: x] - x = 0 by rewrite /=; ring.
  rewrite Rabs_R0.
  have Hu0 := u_gt_0; have := Rabs_pos x.
  have Hp1 : 0 <= INR (size [:: x]) by apply: pos_INR.
  by rewrite /=; nra.
have Fx : format x by apply: Hf; rewrite inE eqxx.
have Fs0 : format (vecSumAux (b :: l)).2.
  by apply: format_vecSumAux2 => z zI; apply: Hf; rewrite inE zI orbT.
have Hhead : (vecSumAux [:: x, b & l]).2 = RND (x + (vecSumAux (b :: l)).2).
  rewrite vecSumAux_cons; case E : (vecSumAux (b :: l)) => [es s].
  by rewrite [(es, s).2]/= -TwoSum_hi; case: (TwoSum x s).
set s := (vecSumAux (b :: l)).2.
(* The head is one 2Sum away from [x + s]: its error is the low word.         *)
have Hc : dwh (TwoSum x s) + dwl (TwoSum x s) = x + s
  by exact: TwoSum_correct_loc Fx Fs0.
have Hm : Rabs (dwl (TwoSum x s)) <= ulp (dwh (TwoSum x s)) / 2.
  by have := magnitude_TwoSum Fx Fs0; rewrite /magnitudeDWR;
     case: (TwoSum x s).
rewrite TwoSum_hi in Hc Hm.
have Herr : Rabs (x + s - RND (x + s)) <= u * Rabs (RND (x + s)).
  have -> : x + s - RND (x + s) = dwl (TwoSum x s) by lra.
  by have := @ulp_2u p beta Hp2 (RND (x + s)); lra.
have Hrun : Rabs (RND (x + s)) <=
    (1 + u) ^ size [:: x, b & l] * sumRabs [:: x, b & l].
  by have := vecSumAux_run_le Hf; rewrite Hhead -/s.
have HIH : Rabs (sumR (b :: l) - s) <=
    INR (size (b :: l)) * u * ((1 + u) ^ size (b :: l) * sumRabs (b :: l)).
  have H : {in b :: l, forall z : R, format z}
    by move=> z zI; apply: Hf; rewrite inE zI orbT.
  by exact: IH H.
have Hsplit : Rabs (sumR [:: x, b & l] - RND (x + s))
    <= Rabs (x + s - RND (x + s)) + Rabs (sumR (b :: l) - s).
  have -> : sumR [:: x, b & l] - RND (x + s)
      = (x + s - RND (x + s)) + (sumR (b :: l) - s) by rewrite /=; ring.
  by apply: Rabs_triang.
rewrite Hhead -/s.
have Hu0 := u_gt_0.
have Hsr := sumRabs_ge0 (b :: l).
have Hx := Rabs_pos x.
have Hn0 : 0 <= INR (size (b :: l)) by apply: pos_INR.
have Hpow0 : 0 < (1 + u) ^ size (b :: l) by apply: pow_lt; lra.
have Hpn : INR (size [:: x, b & l]) = INR (size (b :: l)) + 1
  by rewrite -S_INR.
have Hps : (1 + u) ^ size [:: x, b & l] = (1 + u) * (1 + u) ^ size (b :: l)
  by [].
have Hsum : sumRabs [:: x, b & l] = Rabs x + sumRabs (b :: l) by [].
move: Hrun; rewrite Hps Hsum => Hrun.
rewrite Hpn.
have HA : Rabs (x + s - RND (x + s)) <=
    u * ((1 + u) * (1 + u) ^ size (b :: l) * (Rabs x + sumRabs (b :: l))).
  by apply: Rle_trans Herr _; apply: Rmult_le_compat_l; [lra | exact: Hrun].
have HB : Rabs (sumR (b :: l) - s) <= INR (size (b :: l)) * u *
    ((1 + u) * (1 + u) ^ size (b :: l) * (Rabs x + sumRabs (b :: l))).
  apply: Rle_trans HIH _; apply: Rmult_le_compat_l; first by nra.
  have Hid : (1 + u) * (1 + u) ^ size (b :: l) * (Rabs x + sumRabs (b :: l))
      - (1 + u) ^ size (b :: l) * sumRabs (b :: l)
      = (1 + u) ^ size (b :: l)
        * (Rabs x + u * Rabs x + u * sumRabs (b :: l)) by ring.
  have Hnn : 0 <= (1 + u) ^ size (b :: l)
      * (Rabs x + u * Rabs x + u * sumRabs (b :: l))
    by apply: Rmult_le_pos; nra.
  lra.
have Hexp : (INR (size (b :: l)) + 1) * u *
      ((1 + u) * (1 + u) ^ size (b :: l) * (Rabs x + sumRabs (b :: l)))
    = INR (size (b :: l)) * u *
      ((1 + u) * (1 + u) ^ size (b :: l) * (Rabs x + sumRabs (b :: l)))
    + u * ((1 + u) * (1 + u) ^ size (b :: l) * (Rabs x + sumRabs (b :: l)))
  by ring.
by lra.
Qed.

(* What a head argument needs about a VecSum, in one statement: the leading   *)
(* limb approximates the WHOLE sum to within half an ulp of itself, plus the  *)
(* accumulated rounding error of the limbs below.  The half-ulp is exact      *)
(* ([vecSum_head_sep]); the second term is negligible whenever the entries    *)
(* below the leading one are small, which is the situation of Algorithm 13,   *)
(* Section 8.3 (there they are [O(u)] against a leading [O(1)]).              *)
Lemma vecSum_head_tail_le l : {in l, forall z, format z} -> (1 < size l)%N ->
  Rabs (sumR l - nth 0 (vecSum l) 0) <=
    / 2 * ulp (nth 0 (vecSum l) 0)
    + INR (size l).-1 * u * ((1 + u) ^ (size l).-1 * sumRabs (behead l)).
Proof.
case: l => [|x L] // Hf _.
have Fx : format x by apply: Hf; rewrite inE eqxx.
have HL : {in L, forall z : R, format z}
  by move=> z zI; apply: Hf; rewrite inE zI orbT.
have Fs0 : format (vecSumAux L).2 by apply: format_vecSumAux2.
have Hhead : nth 0 (vecSum (x :: L)) 0 = RND (x + (vecSumAux L).2).
  rewrite vecSum_nth0; case: L Hf HL Fs0 => [|b l] Hf HL Fs0.
    by rewrite [(vecSumAux [::]).2]/= Rplus_0_r round_generic.
  rewrite vecSumAux_cons; case E : (vecSumAux (b :: l)) => [es s].
  by rewrite [(es, s).2]/= -TwoSum_hi; case: (TwoSum x s).
set s := (vecSumAux L).2.
have Hc : dwh (TwoSum x s) + dwl (TwoSum x s) = x + s
  by exact: TwoSum_correct_loc Fx Fs0.
have Hm : Rabs (dwl (TwoSum x s)) <= ulp (dwh (TwoSum x s)) / 2.
  by have := magnitude_TwoSum Fx Fs0; rewrite /magnitudeDWR;
     case: (TwoSum x s).
rewrite TwoSum_hi in Hc Hm.
have Herr : Rabs (x + s - RND (x + s)) <= / 2 * ulp (RND (x + s)).
  have -> : x + s - RND (x + s) = dwl (TwoSum x s) by lra.
  by lra.
have HIH := vecSumAux_err_le HL.
have Hsplit : Rabs (sumR (x :: L) - RND (x + s))
    <= Rabs (x + s - RND (x + s)) + Rabs (sumR L - s).
  have -> : sumR (x :: L) - RND (x + s)
      = (x + s - RND (x + s)) + (sumR L - s) by rewrite /=; ring.
  by apply: Rabs_triang.
rewrite Hhead.
have -> : (size (x :: L)).-1 = size L by [].
have -> : behead (x :: L) = L by [].
move: HIH; rewrite -/s => HIH.
by lra.
Qed.

(* The engine of a head argument, in the form its callers meet it: a value    *)
(* [v] known to within [D] of the exact sum of the VecSum inputs is known to  *)
(* within half an ulp (plus small change) of the LEADING LIMB.  Callers       *)
(* supply [D] (their own error decomposition) and [B] (the mass of the        *)
(* entries below the leading one); everything else is generic.                *)
Lemma vecSum_head_gap l v D B :
  {in l, forall z, format z} -> (1 < size l)%N ->
  Rabs (v - sumR l) <= D -> sumRabs (behead l) <= B ->
  Rabs (v - nth 0 (vecSum l) 0) <=
    / 2 * ulp (nth 0 (vecSum l) 0)
    + (D + INR (size l).-1 * u * ((1 + u) ^ (size l).-1 * B)).
Proof.
move=> Hf Hsz HD HB.
have Hgap := vecSum_head_tail_le Hf Hsz.
have Ht : Rabs (v - nth 0 (vecSum l) 0)
    <= Rabs (v - sumR l) + Rabs (sumR l - nth 0 (vecSum l) 0).
  have -> : v - nth 0 (vecSum l) 0
      = (v - sumR l) + (sumR l - nth 0 (vecSum l) 0) by ring.
  by apply: Rabs_triang.
have Hu0 := u_gt_0.
have Hn0 : 0 <= INR (size l).-1 by apply: pos_INR.
have Hpow0 : 0 < (1 + u) ^ (size l).-1 by apply: pow_lt; lra.
have Hmono : INR (size l).-1 * u * ((1 + u) ^ (size l).-1 * sumRabs (behead l))
          <= INR (size l).-1 * u * ((1 + u) ^ (size l).-1 * B).
  apply: Rmult_le_compat_l; first by nra.
  by apply: Rmult_le_compat_l; [lra | exact: HB].
by lra.
Qed.

(* The low word of a 2Sum [TwoSum x s] is small: its magnitude is at most     *)
(* [2 u 2^e0], provided [|x| < 2^(e0+1)] and [|s| <= (2-2u) 2^e0] (so the     *)
(* exact sum has magnitude below [2^(e0+2)]).  This is the tight per-step     *)
(* error bound behind [Herr] (the paper's [2 u^2 2^(k_{i-1})] would be a      *)
(* factor [2^p] too small: a single 2Sum error can reach [~u 2^(k_i)]).       *)
(* The running-sum hypothesis is [|s| <= 2 pow e0], NOT [(2-2u) pow e0]: the  *)
(* Theorem-6 run bound [vecSum_run_ufp] only delivers the former, and the     *)
(* slack is not needed ([Rabs x < pow (e0+1)] is already strict).             *)
Lemma magnitude_vecSum_err x s e0 : format x -> format s ->
  Rabs x < pow (e0 + 1) -> Rabs s <= 2 * pow e0 ->
  Rabs (dwl (TwoSum x s)) <= 2 * u * pow e0.
Proof.
move=> Fx Fs Hx Hs.
have Hc : dwh (TwoSum x s) + dwl (TwoSum x s) = x + s
  by exact: TwoSum_correct_loc Fx Fs.
rewrite TwoSum_hi in Hc.
have -> : dwl (TwoSum x s) = - (RND (x + s) - (x + s)) by lra.
rewrite Rabs_Ropp.
have Hz : Rabs (x + s) < pow (e0 + 2).
  apply: Rle_lt_trans (Rabs_triang _ _) _.
  have Hs1 : Rabs s <= pow (e0 + 1).
    apply: Rle_trans Hs _.
    by rewrite bpow_plus bpow_1 /=; lra.
  have -> : pow (e0 + 2) = pow (e0 + 1) + pow (e0 + 1)
    by rewrite !bpow_plus /= /Z.pow_pos /=; lra.
  lra.
have Hulp : ulp (x + s) <= pow (e0 + 2 - p).
  have [z0|z0] := Req_dec (x + s) 0.
    by rewrite z0 ulp_FLX_0; apply: bpow_ge_0.
  rewrite ulp_neq_0 //; apply: bpow_le; rewrite /cexp /FLX_exp.
  have Hm : (mag beta (x + s) <= e0 + 2)%Z by apply: mag_le_bpow.
  by rewrite /fexp; lia.
apply: (Rle_trans _ (/ 2 * ulp (x + s))).
  by apply: error_le_half_ulp.
apply: Rle_trans (_ : / 2 * pow (e0 + 2 - p) <= _).
  by apply: Rmult_le_compat_l; [lra | exact: Hulp].
have -> : 2 * u * pow e0 = / 2 * pow (e0 + 2 - p).
  rewrite uE.
  have -> : / 2 = pow (-1) by rewrite /= /Z.pow_pos /=; lra.
  have -> : (2 : R) = pow 1 by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -!bpow_plus; congr bpow; lia.
by lra.
Qed.

(* The tight per-step error bound (paper: [|e_i| <= 2u 2^(k_{i-1})]), here    *)
(* indexed by the previous position: [|e_{i+1}| <= 2u 2^(k_i)].  Each error is*)
(* the low word of the 2Sum combining [x_i] with the running tail sum         *)
(* ([vecSumAux_nth1]); [magnitude_vecSum_err] bounds it from the input bound  *)
(* [|x_i| < 2^(k_i+1)] and the running-sum bound [VecSum_run_bound].          *)
Lemma vecSum_err_bound k l : Thm1_hyp k l ->
  forall i, (i.+1 < size l)%N ->
    Rabs (nth 0 (vecSum l) i.+1) <= 2 * u * pow (k i).
Proof.
move=> Hk.
have Hfmt : {in l, forall z, format z}.
  case: Hk => Hrepr _ _ z /(nthP 0)[i iLs <-].
  exact: repr_format (Hrepr i iLs).
have Hrun := VecSum_run_bound Hk.
have [Hrepr _ _] := Hk.
move=> j jLs.
have jLl : (j < size l)%N := ltn_trans (ltnSn j) jLs.
have [M HM Hxeq] := Hrepr j jLl.
have -> : nth 0 (vecSum l) j.+1 = nth 0 (vecSumAux l).1 j
  by rewrite /vecSum; case: (vecSumAux l).
rewrite vecSumAux_nth1 //.
apply: magnitude_vecSum_err.
- by apply: Hfmt; apply: mem_nth.
- apply: format_vecSumAux2 => z zIn.
  by apply: Hfmt; rewrite -(cat_take_drop j.+1 l) mem_cat zIn orbT.
- rewrite Hxeq Rabs_mult (Rabs_pos_eq _ (bpow_ge_0 _ _)) -abs_IZR.
  have -> : pow (k j + 1) = pow p * pow (k j - p + 1)
    by rewrite -bpow_plus; congr bpow; lia.
  apply: Rmult_lt_compat_r; first exact: bpow_gt_0.
  have -> : pow p = IZR (2 ^ p) by rewrite IZR_2powp.
  by apply: IZR_lt.
(* [VecSum_run_bound] gives the sharper [(2-2u) pow (k j)]; relax it to the   *)
(* [2 pow (k j)] that [magnitude_vecSum_err] now asks for.                    *)
apply: Rle_trans (Hrun j jLs) _.
have Hu : 0 < u by rewrite uE; apply: bpow_gt_0.
have := bpow_gt_0 beta (k j); nra.
Qed.

(* Prefix/suffix split of the VecSum walk (paper: "e_i, ..., e_0 and s_0      *)
(* depend only on x_{i-1}, ..., x_0 and s_i").  Running [vecSumAux] on the    *)
(* first [m] inputs with the tail's running sum [(vecSumAux (drop m l)).2]    *)
(* appended reproduces the first [m] output errors and the final high word.   *)
(* This is what lets [vecSumAux_imul] be applied to the prefix in the         *)
(* divisibility step of [vecSum_sep].                                         *)
Lemma vecSumAux_split m l : (m < size l)%N ->
  vecSumAux (take m l ++ [:: (vecSumAux (drop m l)).2]) =
  (take m (vecSumAux l).1, (vecSumAux l).2).
Proof.
elim: m l => [|m IH] [|a l] //= Hs; first by rewrite take0.
rewrite (IH l Hs).
case E : (take m l ++ [:: (vecSumAux (drop m l)).2]) => [|c Q'].
  by move: E => /(congr1 size); rewrite size_cat /= addn1.
case: l Hs {IH E} => [//|b l'] _.
by case: (vecSumAux (b :: l')) => es ss; case: (TwoSum a ss) => si ei /=.
Qed.

(* The paper's separation estimate, in pure index form (the whole content of  *)
(* Theorem 1 once the [Fnonoverlap] recursion is peeled off by                *)
(* [Fnonoverlap_allpairs]): for the VecSum output [e_0 = s_0, e_1, ...], every*)
(* term is at most [1/2 uls] of every earlier nonzero term.  Proof (paper     *)
(* Section 2.1, by contradiction): an overlap [|e_i| > 1/2 uls(e_{i'})],      *)
(* [i' < i], WLOG [uls(e_{i'}) = u] (scale invariance).  By backward          *)
(* divisibility ([vecSumAux_imul]: [2^k | s_i, x_{i-1}, .., x_0 =>            *)
(* 2^k | e_i, .., e_0]), since [s_{i-1}] is a multiple of [2u] (from          *)
(* [|s_{i-1}| >= 1]) some input [x_j], [j <= i-2], is off the [2u]-grid, so   *)
(* [2^(k_j) <= 1/2], whence [2^(k_{i-1}) <= 1/4], contradicting the error     *)
(* bound [|e_i| <= 2u 2^(k_i)].                                               *)
Lemma vecSum_sep k l : Thm1_hyp k l ->
  (forall i, (i.+1 < size l)%N ->
     Rabs (nth 0 (vecSum l) i.+1) <= 2 * u * pow (k i)) ->
  (forall i, (i.+1 < size l)%N ->
     Rabs (vecSumAux (drop i.+1 l)).2 <= (2 - 2 * u) * pow (k i)) ->
  forall i j, (i < j)%N -> (j < size (vecSum l))%N ->
    nth 0 (vecSum l) i <> 0 ->
    Rabs (nth 0 (vecSum l) j) <= / 2 * uls (nth 0 (vecSum l) i).
Proof.
move=> Hk Herr Hrun i j ltij Hj Hni.
have j0 : (0 < j)%N by apply: leq_ltn_trans (leq0n i) ltij.
have Hgt1 : (1 < size (vecSum l))%N by apply: leq_ltn_trans j0 Hj.
have Hsl : (1 < size l)%N.
  by move: Hgt1; rewrite size_vecSum; case: (size l) => [|[|n]].
have Hsz : size (vecSum l) = size l.
  by rewrite size_vecSum; case: (size l) Hsl => [|[|n]].
rewrite Hsz in Hj.
case: Hk => Hrepr Hgap Hlast.
have gap : forall r, (r.+2 < size l)%N -> (k r.+1 < k r)%Z.
  by move=> r Hr; have := Hgap r Hr; lia.
have kdec : forall a b, (a < b)%N -> (b.+1 < size l)%N -> (k b < k a)%Z.
  move=> a b; elim: b a => [//|b IHb] a.
  rewrite ltnS leq_eqVlt => /orP[/eqP->|aLb] Hb1; first by apply: gap.
  by apply: Z.lt_trans (gap b Hb1) (IHb a aLb (ltn_trans (ltnSn _) Hb1)).
have HvcS : forall m, nth 0 (vecSum l) m.+1 = nth 0 (vecSumAux l).1 m.
  by move=> m; rewrite /vecSum; case: (vecSumAux l) => es s.
move: ltij Hj Hni; case: j j0 => [//|t] _ ltit Ht Hni.
have Ht' : (t < size l)%N by apply: ltn_trans (ltnSn t) Ht.
have Hej : nth 0 (vecSum l) t.+1 =
    dwl (TwoSum (nth 0 l t) (vecSumAux (drop t.+1 l)).2).
  by rewrite HvcS vecSumAux_nth1.
set x := nth 0 l t; set s := (vecSumAux (drop t.+1 l)).2.
set e := dwl (TwoSum x s); set r := dwh (TwoSum x s).
have Fx : format x by apply: repr_format (Hrepr t Ht').
have Hfmt : {in l, forall z, format z}.
  by move=> z /(nthP 0)[a aLs <-]; apply: repr_format (Hrepr a aLs).
have Fs : format s.
  apply: format_vecSumAux2 => z zI.
  by apply: Hfmt; rewrite -(cat_take_drop t.+1 l) mem_cat zI orbT.
have Fr : format r by rewrite /r TwoSum_hi; apply: generic_format_round.
have Fe : format e by have [_ Hl] := format_TwoSum Fx Fs; exact: Hl.
have Hmag : Rabs e <= / 2 * ulp r.
  have := magnitude_TwoSum Fx Fs.
  by rewrite /magnitudeDWR /e /r; case: (TwoSum x s) => h low /=; lra.
rewrite Hej -/x -/s -/e.
set xi := nth 0 (vecSum l) i.
have Fxi : format xi.
  apply: (format_vecSum Hfmt); apply: mem_nth.
  by rewrite Hsz; apply: ltn_trans ltit Ht.
have gE : uls xi = pow (cexp xi + Z.of_nat (trZ (Ztrunc (mant xi)))).
  by rewrite /uls; case: Req_bool_spec => // xi0; case: (Hni xi0).
set g := (cexp xi + Z.of_nat (trZ (Ztrunc (mant xi))))%Z.
case: (Rle_lt_dec (Rabs e) (/ 2 * uls xi)) => [//|Hgt]; exfalso.
have Hur : uls xi < ulp r by lra.
have rn0 : r <> 0.
  move=> r0; move: Hur; rewrite r0 ulp_FLX_0.
  suff : 0 < uls xi by lra.
  by rewrite gE; apply: bpow_gt_0.
have Hur2 : ulp r = pow (cexp r) by rewrite ulp_neq_0.
have Hcexp : (g + 1 <= cexp r)%Z.
  suff : (g < cexp r)%Z by lia.
  by apply: (lt_bpow radix2); rewrite -gE -Hur2.
have Hr2 : is_imul r (pow (g + 1)).
  by apply: is_imul_pow_le (format_imul_cexp Fr) Hcexp.
have Hni2 : ~ is_imul xi (pow (g + 1)).
  move=> Hc; have H := is_imul_uls_ge Fxi Hni Hc.
  rewrite gE bpow_plus bpow_1 /= in H.
  by rewrite -/g in H; move: (bpow_gt_0 radix2 g); lra.
have Hdt : drop t l = x :: drop t.+1 l by rewrite (drop_nth 0 Ht').
have Hrr : (vecSumAux (drop t l)).2 = r.
  have Hnn : (0 < size (drop t.+1 l))%N by rewrite size_drop subn_gt0.
  rewrite Hdt /r /s.
  case Ed : (drop t.+1 l) Hnn => [//|b rest] _.
  rewrite vecSumAux_cons.
  by case: (vecSumAux (b :: rest)) => es ss; case: (TwoSum x ss).
have Hex : exists2 w, (w < t)%N & ~ is_imul (nth 0 l w) (pow (g + 1)).
  apply: Classical_Prop.NNPP => Hnex.
  have Hall : forall w, (w < t)%N -> is_imul (nth 0 l w) (pow (g + 1)).
    by move=> w wLt; apply: Classical_Prop.NNPP => Hns; apply: Hnex; exists w.
  have HPimul : {in take t l ++ [:: r], forall z, is_imul z (pow (g + 1))}.
    move=> z; rewrite mem_cat inE => /orP[|/eqP->]; last exact: Hr2.
    move=> /(nthP 0)[idx]; rewrite size_take_min ltn_min => /andP[idxLt _] <-.
    by rewrite nth_take //; apply: Hall.
  have HPf : {in take t l ++ [:: r], forall z, format z}.
    by move=> z; rewrite mem_cat inE => /orP[/mem_take/Hfmt //|/eqP->//].
  have [H2 Hes] := vecSumAux_imul HPf HPimul.
  have Hsp : vecSumAux (take t l ++ [:: r]) =
      (take t (vecSumAux l).1, (vecSumAux l).2).
    by rewrite -Hrr vecSumAux_split.
  rewrite Hsp /= in H2 Hes.
  apply: Hni2; move: Hni; rewrite /xi.
  case: (i) ltit => [|i'] ltit' _.
    by rewrite /vecSum; move: H2; case: (vecSumAux l) => es ss.
  have i'Lt : (i' < t)%N by rewrite -ltnS.
  have sl0 : (0 < size l)%N by apply: ltnW.
  have i'Sz : (i' < size (vecSumAux l).1)%N.
    rewrite size_vecSumAux; apply: leq_trans i'Lt _.
    by rewrite -ltnS prednK.
  rewrite HvcS -(nth_take 0 i'Lt); apply: Hes; apply: mem_nth.
  by rewrite size_take_min ltn_min i'Lt i'Sz.
have [w wLt Hw] := Hex.
have Hkw : (k w <= g + p - 1)%Z.
  have [M HM HxM] := Hrepr w (ltn_trans wLt Ht').
  case: (Z_le_gt_dec (k w) (g + p - 1)) => // Hgtw.
  case: Hw.
  apply: is_imul_pow_le (_ : is_imul (nth 0 l w) (pow (k w - p + 1))) _;
    last by lia.
  by exists M; rewrite HxM.
have Hkt : (g <= k t + 1 - p)%Z.
  have Het : Rabs e <= 2 * u * pow (k t).
    by move: (Herr t Ht); rewrite Hej -/x -/s -/e.
  suff Hlt : pow (g - 1) < pow (k t + 1 - p).
    by have := lt_bpow radix2 _ _ Hlt; lia.
  have HA : pow (g - 1) = / 2 * pow g.
    have hg : (g - 1 = g + -1)%Z by lia.
    by rewrite hg bpow_plus /=; lra.
  have HB : pow (k t + 1 - p) = 2 * u * pow (k t).
    have hk : (k t + 1 - p = (1 + - p) + k t)%Z by lia.
    by rewrite hk !bpow_plus bpow_1 uE /=; lra.
  by rewrite HA HB -gE; lra.
have := kdec w t wLt Ht.
lia.
Qed.

(* Core of paper Theorem 1: the VecSum output is F-nonoverlapping, given the  *)
(* running-sum and per-step error bounds.  With the paper-faithful (wIZ)      *)
(* [Fnonoverlap], this is exactly the all-pairs separation [vecSum_sep] fed   *)
(* through [Fnonoverlap_allpairs].                                            *)
Lemma vecSum_Fnonoverlap_core k l : Thm1_hyp k l ->
  (forall i, (i.+1 < size l)%N ->
     Rabs (nth 0 (vecSum l) i.+1) <= 2 * u * pow (k i)) ->
  (forall i, (i.+1 < size l)%N ->
     Rabs (vecSumAux (drop i.+1 l)).2 <= (2 - 2 * u) * pow (k i)) ->
  Fnonoverlap (vecSum l).
Proof.
move=> Hk Herr Hrun; apply: Fnonoverlap_allpairs.
exact: vecSum_sep Hk Herr Hrun.
Qed.

(* Theorem 1.  [VecSum l] is F-nonoverlapping (wIZ) with the same sum,        *)
(* assembling the running-sum bound [VecSum_run_bound], the per-step error    *)
(* bound [vecSum_err_bound] and the divisibility core [vecSum_Fnonoverlap_    *)
(* core].  The sum conjunct is [vecSum_sum] (a chain of error-free 2Sums).    *)
Lemma VecSum_Thm1 k l : Thm1_hyp k l ->
  Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> Hk.
have Hfmt : {in l, forall z, format z}.
  case: Hk => Hrepr _ _ z /(nthP 0)[i iLs <-].
  exact: repr_format (Hrepr i iLs).
split; last by apply: vecSum_sum.
apply: (vecSum_Fnonoverlap_core Hk).
  exact: vecSum_err_bound Hk.
exact: VecSum_run_bound Hk.
Qed.

(* Relaxed exponent hypothesis (paper Corollary 1): magnitude-sorted floats  *)
(* with a designated overlap set [I] on which one equal-magnitude overlap is  *)
(* tolerated (never two in a row), bounded by [ufp(x_{i+1}) <= 2^(p-2)        *)
(* uls(x_i)].  These are the paper's hypotheses; [sorted_mag] + [pairwise_ulp]*)
(* alone do NOT imply the overlap bound (counterexample [15;15;0.5] at p=4),  *)
(* and dropping it is false ([CEThm6]).  See doc/thm1.md.                     *)
Definition Cor1_hyp (l : seq R) : Prop :=
  [/\ {in l, forall z, format z},
      (forall i, (i < size l)%N -> nth 0 l i <> 0) &
   exists inI : nat -> bool,
    [/\ (forall i, inI i -> (0 < i)%N /\ (i.+1 < size l)%N),
        (forall i, inI i -> ~~ inI i.+1),
        (forall i, (i.+1 < size l)%N -> ~~ inI i ->
           2 * ufp (nth 0 l i.+1) <= ufp (nth 0 l i)),
        (forall i, inI i ->
           ufp (nth 0 l i.+1) <= pow (p - 2) * uls (nth 0 l i)) &
        (forall i, inI i -> 4 * ufp (nth 0 l i.+1) <= ufp (nth 0 l i.-1)) ]].

(* Paper Corollary 1, main step: the bumped exponent map exists and meets the *)
(* strict-gap hypothesis [Thm1_hyp] of Theorem 1.  [k_i = e_{x_i}] off [I],   *)
(* [max(e_{x_i}, e_{x_{i+1}}+1)] on [I].  This is old [main]'s FLT proof with *)
(* the [emin] bookkeeping removed: under FLX [cexp = mag - p] definitionally  *)
(* and [repr] has no exponent lower bound.  See doc/thm1.md.                  *)
Lemma Cor1_bump_Thm1_hyp l : Cor1_hyp l -> exists k, Thm1_hyp k l.
Proof.
move=> [Hfmt Hnz [inI [HI Hcons Hoff Hon1 Hon2]]].
pose ex := fun i => (cexp (nth (0:R) l i) + p - 1)%Z.
pose k := fun i => if inI i then Z.max (ex i) (ex i.+1 + 1) else ex i.
have Fnth : forall i, (i < size l)%N -> format (nth (0:R) l i).
  by move=> i Hi; apply: Hfmt; apply: mem_nth.
have Hcx : forall i, (i < size l)%N ->
    cexp (nth (0:R) l i) = (mag beta (nth (0:R) l i) - p)%Z.
  by move=> i Hi; rewrite /cexp /FLX_exp.
have Hufp : forall i, (i < size l)%N -> ufp (nth (0:R) l i) = pow (ex i).
  by move=> i Hi; rewrite /ufp /ex (Hcx i Hi); congr bpow; lia.
exists k.
have Hoff' : forall i, (i.+1 < size l)%N -> ~~ inI i -> (ex i.+1 + 1 <= ex i)%Z.
  move=> i Hi HnI; have iLs : (i < size l)%N by apply: ltnW.
  apply: (le_bpow beta); rewrite bpow_plus bpow_1 /=.
  by have := Hoff i Hi HnI; rewrite (Hufp _ Hi) (Hufp _ iLs); lra.
have Hon2' : forall i, inI i -> (ex i.+1 + 2 <= ex i.-1)%Z.
  move=> i HiI; have [i0 i1s] := HI i HiI.
  have iLs : (i < size l)%N by apply: ltn_trans (ltnSn i) i1s.
  have im1 : (i.-1 < size l)%N by apply: leq_ltn_trans (leq_pred i) iLs.
  apply: (le_bpow beta).
  have E4 : pow 2 = 4 by rewrite /= /Z.pow_pos /=; lra.
  rewrite bpow_plus E4.
  by have := Hon2 i HiI; rewrite (Hufp _ i1s) (Hufp _ im1); lra.
have Hdiv : forall i, inI i ->
    is_imul (nth (0:R) l i) (pow (cexp (nth (0:R) l i.+1) + 1)).
  move=> i HiI; have [i0 i1s] := HI i HiI.
  have iLs : (i < size l)%N by apply: ltn_trans (ltnSn i) i1s.
  have Fxi := Fnth i iLs.
  have xin0 : nth (0:R) l i <> 0 by apply: Hnz.
  have gE : uls (nth (0:R) l i) =
      pow (cexp (nth (0:R) l i)
             + Z.of_nat (trZ (Ztrunc (mant (nth (0:R) l i))))).
    by rewrite /uls; case: Req_bool_spec => // /xin0.
  have Hle : pow (cexp (nth (0:R) l i.+1) + 1) <= uls (nth (0:R) l i).
    have H1 := Hon1 i HiI; rewrite (Hufp _ i1s) in H1.
    have exeq : ex i.+1 = (cexp (nth (0:R) l i.+1) + p - 1)%Z by rewrite /ex.
    rewrite exeq in H1.
    have Hsplit : pow (cexp (nth (0:R) l i.+1) + p - 1) =
        pow (p - 2) * pow (cexp (nth (0:R) l i.+1) + 1).
      by rewrite -bpow_plus; congr bpow; lia.
    rewrite Hsplit in H1; have := bpow_gt_0 beta (p-2); nra.
  apply: is_imul_pow_le.
    by have H := uls_imul Fxi; rewrite gE in H; exact: H.
  by apply: (le_bpow beta); rewrite -gE; exact: Hle.
have Hgap : forall i, (i.+2 < size l)%N -> (k i.+1 + 1 <= k i)%Z.
  move=> i Hi.
  have i1s : (i.+1 < size l)%N by apply: ltn_trans (ltnSn i.+1) Hi.
  rewrite /k.
  case E : (inI i); case E1 : (inI i.+1).
  - by move: (Hcons i E); rewrite E1.
  - by apply: Z.le_max_r.
  - have A := Hoff' i i1s (negbT E).
    have B : (ex i.+2 + 2 <= ex i)%Z := Hon2' i.+1 E1.
    suff H : (Z.max (ex i.+1) (ex i.+2 + 1) <= ex i - 1)%Z by lia.
    by apply: Z.max_lub; lia.
  - by have := Hoff' i i1s (negbT E); lia.
have Hlast : forall i, i.+2 = size l -> (k i.+1 <= k i)%Z.
  move=> i Hi.
  have i1s : (i.+1 < size l)%N by rewrite -Hi; apply: ltnSn.
  have Hn1 : ~~ inI i.+1.
    by apply/negP => Hc; have := (HI _ Hc).2; rewrite -Hi ltnn.
  rewrite /k (negbTE Hn1).
  case E : (inI i).
  - by have := Z.le_max_r (ex i) (ex i.+1 + 1); lia.
  - by have := Hoff' i i1s (negbT E); lia.
split; [ | exact: Hgap | exact: Hlast].
move=> i Hi.
have Fxi := Fnth i Hi.
have Hkge : (ex i <= k i)%Z.
  by rewrite /k; case: (inI i); [apply: Z.le_max_l | apply: Z.le_refl].
have Hisimul : is_imul (nth (0:R) l i) (pow (k i - p + 1)).
  rewrite /k; case E : (inI i); last first.
    have -> : (ex i - p + 1 = cexp (nth (0:R) l i))%Z by rewrite /ex; lia.
    exact: format_imul_cexp Fxi.
  case: (Z.max_spec (ex i) (ex i.+1 + 1)) => [[_ ->]|[_ ->]].
    have -> : (ex i.+1 + 1 - p + 1 = cexp (nth (0:R) l i.+1) + 1)%Z
      by rewrite /ex; lia.
    exact: Hdiv i E.
  have -> : (ex i - p + 1 = cexp (nth (0:R) l i))%Z by rewrite /ex; lia.
  exact: format_imul_cexp Fxi.
have [z Hz] := Hisimul.
exists z; last exact: Hz.
apply: lt_IZR; rewrite abs_IZR IZR_2powp.
have Hb := bpow_mag_gt beta (nth (0:R) l i).
have Hrw : Rabs (nth (0:R) l i) = Rabs (IZR z) * pow (k i - p + 1).
  by rewrite {1}Hz Rabs_mult (Rabs_pos_eq _ (bpow_ge_0 _ _)).
rewrite Hrw in Hb.
have Hmle : pow (mag beta (nth (0:R) l i)) <= pow p * pow (k i - p + 1).
  rewrite -bpow_plus; apply: bpow_le.
  by move: Hkge (Hcx i Hi); rewrite /ex; lia.
have Hpos := bpow_gt_0 beta (k i - p + 1).
nra.
Qed.

(* Paper Corollary 1: [VecSum l] is F-nonoverlapping (wIZ) with the same sum, *)
(* assembled from the bump [Cor1_bump_Thm1_hyp] and Theorem 1.                 *)
Lemma vecSum_Fnonoverlap l :
  Cor1_hyp l -> Fnonoverlap (vecSum l) /\ sumR (vecSum l) = sumR l.
Proof.
move=> Hc; have [k Hk] := Cor1_bump_Thm1_hyp Hc.
have [Hfmt _ _] := Hc.
split; last by apply: vecSum_sum.
apply: (vecSum_Fnonoverlap_core Hk) => //.
  by move=> i Hi; apply: (vecSum_err_bound Hk).
by move=> i Hi; apply: (VecSum_run_bound Hk).
Qed.

Lemma vecSum_Fnonoverlap_sep l : Cor1_hyp l -> Fnonoverlap (vecSum l).
Proof. by move=> Hc; case: (vecSum_Fnonoverlap Hc). Qed.

(* ===========================================================================*)
(*  Toward paper Theorem 6 (ported from the FLT development).                 *)
(*                                                                            *)
(*  NB the [emin] scaffolding of the FLT versions is GONE here: [emin <= e-p] *)
(*  in [RN_midpoint_even], and the no-underflow hypothesis                    *)
(*  [emin + p <= mag (nth l i)] in the two bounds below, all disappear -- FLX *)
(*  IS the paper's model (unlimited exponent range), so these statements are  *)
(*  the paper's, unpatched.                                                   *)
(* ===========================================================================*)

(* FLX analogue of [Pff2Flocq.round_N_opp_sym], which is FLT-only (it is      *)
(* stated for [round_flt]).  A symmetric tie-breaking [choice] makes          *)
(* round-to-nearest odd: [round_N_opp] flips [choice] to                      *)
(* [fun t => ~~ choice (-(t+1))], which [choice_sym] says is [choice] again,  *)
(* pointwise -- so [round_ext] closes it without functional extensionality.   *)
Lemma RN_opp_sym x : RND (- x) = - RND x.
Proof.
rewrite round_N_opp; congr (- _).
apply: round_ext => t.
rewrite /Znearest; case: Rcompare => //.
by rewrite -choice_sym.
Qed.

(* Round-to-nearest ties-to-even sends the exact midpoint [pow e + pow(e-p)]  *)
(* (halfway between the even float [pow e] and its successor) DOWN to [pow e].*)
(* This is the one place paper Theorem 6 needs ties-to-even (see              *)
(* [vecSum_run_ufp]'s same-binade case): a general symmetric [choice] could   *)
(* round it up.                                                               *)
Lemma RN_midpoint_even e : ties_to_even choice ->
  RND (pow e + pow (e - p)) = pow e.
Proof.
move=> Heven.
have Hpe := bpow_gt_0 beta e.
have Hpep := bpow_gt_0 beta (e - p).
have Hmagx : mag beta (pow e + pow (e - p)) = (e + 1)%Z :> Z.
  apply: mag_unique_pos; split.
    have -> : (e + 1 - 1 = e)%Z by lia.
    by lra.
  rewrite bpow_plus bpow_1 /=.
  have : pow (e - p) < pow e by apply: bpow_lt; lia.
  lra.
have Hcexp : cexp (pow e + pow (e - p)) = (e + 1 - p)%Z.
  by rewrite /cexp Hmagx /FLX_exp.
have Hpm1 : pow (-1)%Z = / 2 by rewrite /= /Z.pow_pos /=; lra.
have Hpp1 : pow (p - 1) = IZR (2 ^ (p - 1)).
  have -> : (2 = radix2 :> Z)%Z by [].
  by rewrite IZR_Zpower //; lia.
have Hsm : mant (pow e + pow (e - p)) = pow (p - 1) + / 2.
  rewrite /scaled_mantissa Hcexp Rmult_plus_distr_r -!bpow_plus.
  have -> : (e + - (e + 1 - p) = p - 1)%Z by lia.
  have -> : (e - p + - (e + 1 - p) = -1)%Z by lia.
  by rewrite Hpm1.
have Hfloor : Zfloor (mant (pow e + pow (e - p))) = (2 ^ (p - 1))%Z.
  rewrite Hsm Hpp1; apply: Zfloor_imp.
  rewrite plus_IZR; have := bpow_gt_0 beta (p - 1); rewrite -Hpp1.
  by move=> ?; lra.
have Heven2 : Z.even (2 ^ (p - 1)) = true.
  have -> : (2 ^ (p - 1) = 2 * 2 ^ (p - 2))%Z.
    by rewrite -Z.pow_succ_r; [congr (_ ^ _)%Z; lia | lia].
  by rewrite Z.even_mul.
have HRD : round beta fexp Zfloor (pow e + pow (e - p)) = pow e.
  rewrite /round Hfloor Hcexp /F2R /= -Hpp1 -bpow_plus.
  by congr bpow; lia.
have Hceil : Zceil (mant (pow e + pow (e - p))) = (2 ^ (p - 1) + 1)%Z.
  rewrite Hsm Hpp1; apply: Zceil_imp.
  rewrite minus_IZR plus_IZR; have := bpow_gt_0 beta (p - 1); rewrite -Hpp1.
  by move=> ?; lra.
have HRU : round beta fexp Zceil (pow e + pow (e - p)) =
    pow e + pow (e + 1 - p).
  rewrite /round Hceil Hcexp /F2R /= plus_IZR -Hpp1 Rmult_plus_distr_r.
  rewrite -bpow_plus Rmult_1_l.
  by congr (_ + _); congr bpow; lia.
have Hmid : (pow e + pow (e - p)) - round beta fexp Zfloor (pow e + pow (e - p))
          = round beta fexp Zceil (pow e + pow (e - p)) - (pow e + pow (e - p)).
  rewrite HRD HRU.
  have -> : pow (e + 1 - p) = 2 * pow (e - p).
    by rewrite -[in RHS](bpow_1 beta) -bpow_plus; congr bpow; lia.
  lra.
rewrite (@round_N_middle beta fexp choice (pow e + pow (e - p)) Hmid) Hfloor.
have -> : choice (2 ^ (p - 1)) = false by rewrite Heven Heven2.
exact: HRD.
Qed.

(* Paper Theorem 6, step (a) / the draft's step *1 (see [doc/thm6.md] 5.1):   *)
(* the running high word [s_j = (vecSumAux (drop j l)).2] of a VecSum on a    *)
(* magnitude-sorted, pairwise-ulp separated, zero-free sequence obeys         *)
(* [|s_j| <= 4 ufp(x_j)] and (for [j >= 1]) [|s_j| <= 2 ufp(x_{j-1})], by     *)
(* coupled downward induction.  The same-binade step (no strict exponent      *)
(* drop) uses [pairwise_ulp] to shrink the tail and [RN_midpoint_even] for    *)
(* the boundary tie -- the draft's "after rounding (ties-to-even)".           *)
Lemma vecSum_run_ufp (l : seq R) :
  ties_to_even choice ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  forall j, (j < size l)%N ->
    Rabs (vecSumAux (drop j l)).2 <= 4 * ufp (nth (0:R) l j) /\
    ((0 < j)%N -> Rabs (vecSumAux (drop j l)).2 <= 2 * ufp (nth (0:R) l j.-1)).
Proof.
move=> Heven Hfmt Hnz Hsort Hpair.
have Fnth : forall i, (i < size l)%N -> format (nth (0:R) l i).
  by move=> i Hi; apply: Hfmt; apply: mem_nth.
have ufpE : forall i, ufp (nth (0:R) l i) = pow (mag beta (nth (0:R) l i) - 1).
  by move=> i; rewrite /ufp.
have ulpE : forall i, (i < size l)%N ->
    ulp (nth (0:R) l i) = pow (mag beta (nth (0:R) l i) - p).
  move=> i Hi; rewrite ulp_neq_0; last exact: Hnz.
  by rewrite /cexp /FLX_exp.
have magmon : forall i, (i.+1 < size l)%N ->
    (mag beta (nth (0:R) l i.+1) <= mag beta (nth (0:R) l i))%Z.
  by move=> i Hi; apply: mag_le_abs; [exact: Hnz i.+1 Hi | exact: Hsort i Hi].
have E2 : (2:R) = pow 1 by rewrite /= /Z.pow_pos /=; lra.
have Fufp4 : forall i, (i < size l)%N -> format (4 * ufp (nth (0:R) l i)).
  move=> i Hi.
  have E4 : (4:R) = pow 2 by rewrite /= /Z.pow_pos /=; lra.
  rewrite ufpE E4 -bpow_plus.
  by apply: generic_format_bpow; rewrite /FLX_exp; lia.
move=> j; have [d le_d] := ubnP (size l - j).
elim: d j le_d => // d IHd j; rewrite ltnS => le_d Hj.
have Fx := Fnth j Hj.
have Hx2 : Rabs (nth (0:R) l j) < 2 * ufp (nth (0:R) l j) by apply: abs_lt_2ufp.
have HxN := abs_le_ufp_norm Fx.
have Uj : 0 < ufp (nth (0:R) l j) by apply: ufp_gt_0.
have [Hlast|Hlast] := eqVneq j.+1 (size l).
  have Hdrop : drop j l = [:: nth (0:R) l j]
    by rewrite (drop_nth 0) // Hlast drop_size.
  rewrite Hdrop /=; split; first by lra.
  move=> j0.
  have Hmm : (mag beta (nth (0:R) l j) <= mag beta (nth (0:R) l j.-1))%Z.
    by move: (magmon j.-1); rewrite prednK //; apply.
  apply: Rle_trans (Rlt_le _ _ Hx2) _.
  rewrite !ufpE; apply: Rmult_le_compat_l; first by lra.
  by apply: bpow_le; lia.
have Hj1 : (j.+1 < size l)%N by rewrite ltn_neqAle Hlast Hj.
have Hde : (size l - j.+1 < d)%N.
  by apply: (leq_trans _ le_d); rewrite subnS prednK ?subn_gt0.
have [IHB IHA] := IHd j.+1 Hde Hj1.
have IHA' : Rabs (vecSumAux (drop j.+1 l)).2 <= 2 * ufp (nth (0:R) l j)
  := IHA (ltn0Sn j).
have Hd1 : drop j l = nth (0:R) l j :: drop j.+1 l by rewrite (drop_nth 0).
have Hd2 : drop j.+1 l = nth (0:R) l j.+1 :: drop j.+2 l
  by rewrite (drop_nth 0).
have Hs : (vecSumAux (drop j l)).2
            = RND (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2).
  rewrite Hd1 Hd2 vecSumAux_cons -Hd2.
  by case: (vecSumAux (drop j.+1 l)) => es s /=; rewrite /TwoSum.
rewrite Hs.
have HB : Rabs (RND (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2))
            <= 4 * ufp (nth (0:R) l j).
  apply: abs_round_le_generic; first exact: Fufp4 j Hj.
  apply: Rle_trans (Rabs_triang _ _) _; lra.
split; first exact: HB.
move=> j0.
have Hmm : (mag beta (nth (0:R) l j) <= mag beta (nth (0:R) l j.-1))%Z.
  by move: (magmon j.-1); rewrite prednK //; apply.
have [Hne|Heq] :=
  Z.eq_dec (mag beta (nth (0:R) l j)) (mag beta (nth (0:R) l j.-1)).
  have Hjm1 : (j.-1 < size l)%N by apply: leq_ltn_trans (leq_pred j) Hj.
  have HulpM := ulpE j Hj.
  have Hs1 : Rabs (vecSumAux (drop j.+1 l)).2 <= 2 * ulp (nth (0:R) l j).
    apply: Rle_trans IHB _.
    (* [Hnz] rules out the zero guard on [pairwise_ulp].                      *)
    have Hp1 : Rabs (nth (0:R) l j.+1) < ulp (nth (0:R) l j.-1).
      move: (Hpair j.-1); rewrite (prednK j0) => /(_ Hj1) -[Hz|//].
      by case: (Hnz j.+1 Hj1).
    have Hmg1 : (mag beta (nth (0:R) l j.+1) <= mag beta (nth (0:R) l j) - p)%Z.
      apply: mag_le_bpow; first exact: Hnz j.+1 Hj1.
      apply: Rlt_le_trans Hp1 _.
      by rewrite (ulpE j.-1 Hjm1); apply: bpow_le; lia.
    rewrite (ufpE j.+1) HulpM.
    have E4 : (4:R) = pow 2 by rewrite /= /Z.pow_pos /=; lra.
    by rewrite E4 E2 -!bpow_plus; apply: bpow_le; lia.
  have Hu2u : (2 - 2 * u) * ufp (nth (0:R) l j)
      = pow (mag beta (nth (0:R) l j)) - ulp (nth (0:R) l j).
    rewrite Rmult_minus_distr_r ufpE HulpM uE E2 -!bpow_plus.
    by congr (_ - _); congr bpow; lia.
  have Hv : Rabs (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2)
      <= pow (mag beta (nth (0:R) l j)) + ulp (nth (0:R) l j).
    apply: Rle_trans (Rabs_triang _ _) _.
    by rewrite Hu2u in HxN; lra.
  have Ht : 2 * ufp (nth (0:R) l j.-1) = pow (mag beta (nth (0:R) l j)).
    by rewrite (ufpE j.-1) -Hne E2 -bpow_plus; congr bpow; lia.
  rewrite Ht.
  (* The [(emin <= mag - p)] side condition of the FLT version is gone.       *)
  have Htie := RN_midpoint_even (mag beta (nth (0:R) l j)) Heven.
  rewrite -HulpM in Htie.
  have Hup : RND (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2)
      <= pow (mag beta (nth (0:R) l j)).
    rewrite -Htie; apply: round_le.
    have := Rle_abs (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2); lra.
  have Hlo : - pow (mag beta (nth (0:R) l j))
      <= RND (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2).
    have Hopp := RN_opp_sym (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2).
    suff Hs2 : RND (- (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2))
        <= pow (mag beta (nth (0:R) l j)) by move: Hs2; rewrite Hopp; lra.
    rewrite -Htie; apply: round_le.
    have := Rle_abs (- (nth (0:R) l j + (vecSumAux (drop j.+1 l)).2)).
    rewrite Rabs_Ropp; lra.
  by split_Rabs; lra.
apply: Rle_trans HB _.
rewrite !ufpE.
have E4 : (4:R) = pow 2 by rewrite /= /Z.pow_pos /=; lra.
by rewrite E4 E2 -!bpow_plus; apply: bpow_le; lia.
Qed.

(* Step (b) of Theorem 6 / the draft's "What is more, we still have           *)
(* [|e_i| <= 2u ufp(x_{i-1})]" (see [doc/thm6.md] 5.1).  Each VecSum error    *)
(* [e_i = nth (vecSum l) i.+1] is the low word of the 2Sum of [x_i] with the  *)
(* tail running sum [s_{i+1}]; [magnitude_vecSum_err] bounds it from          *)
(* [|x_i| < 2 ufp(x_i)] and the run bound [|s_{i+1}| <= 2 ufp(x_i)]           *)
(* ([vecSum_run_ufp], second conjunct at [j = i.+1]).                         *)
Lemma vecSum_err_ufp (l : seq R) :
  ties_to_even choice ->
  {in l, forall z, format z} ->
  (forall i, (i < size l)%N -> nth (0:R) l i <> 0) ->
  sorted_mag l -> pairwise_ulp l ->
  forall i, (i.+1 < size l)%N ->
    Rabs (nth (0:R) (vecSum l) i.+1) <= 2 * u * ufp (nth (0:R) l i).
Proof.
move=> Heven Hfmt Hnz Hsort Hpair i Hi.
have iLl : (i < size l)%N := ltn_trans (ltnSn i) Hi.
have Fx : format (nth (0:R) l i) by apply: Hfmt; apply: mem_nth.
have Hrun := vecSum_run_ufp Heven Hfmt Hnz Hsort Hpair.
have -> : nth (0:R) (vecSum l) i.+1 = nth (0:R) (vecSumAux l).1 i
  by rewrite /vecSum; case: (vecSumAux l).
rewrite vecSumAux_nth1 //.
rewrite /ufp; apply: magnitude_vecSum_err.
- exact: Fx.
- apply: format_vecSumAux2 => z zIn.
  by apply: Hfmt; rewrite -(cat_take_drop i.+1 l) mem_cat zIn orbT.
- have -> : (mag beta (nth (0:R) l i) - 1 + 1 = mag beta (nth (0:R) l i))%Z
    by lia.
  by apply: bpow_mag_gt.
- have [_ /(_ (ltn0Sn i))] := Hrun i.+1 Hi.
  by rewrite /ufp /=.
Qed.

End SecVecSum.
