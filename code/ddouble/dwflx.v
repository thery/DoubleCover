From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dwtwosum DWPlus.

(* The unbounded format, where the double-word theorems live.                 *)
(* Those theorems are all stated for a format with no bottom, and binary64    *)
(* has one.  It turns out to cost nothing: the two formats round every sum    *)
(* of two binary64 numbers alike, above the bottom of the range because       *)
(* the bound on the exponent does not bite there, and below it because such   *)
(* a sum is exact and neither format has anything to round.  Every algorithm  *)
(* here rounds nothing but such sums, so it computes the same numbers in      *)
(* both, and its theorems carry over with no condition at all.                *)

Open Scope R_scope.

(* The smallest normal number.                                                *)
Notation Dnorm := (bpow radix2 (SpecFloat.emin prec emax + prec - 1)).

(* Round to nearest, ties to even, in the format with no bottom.              *)
Notation Xrnd :=
  (round radix2 (FLX_exp prec) (Znearest (fun n => negb (Z.even n)))).
Notation Xformat := (generic_format radix2 (FLX_exp prec)).

(* Round to nearest, ties to even, as the ported development names it.        *)
Notation Dchoice := (fun n : Z => negb (Z.even n)).

(* A sum of two binary64 numbers is rounded alike by both formats.  Above     *)
(* the smallest normal number that is because the bound on the exponent does  *)
(* not bite.  Below it, every binary64 number is a whole multiple of the      *)
(* smallest one there is, so such a sum is one too, and being that small it   *)
(* is itself a binary64 number: neither format has anything to round.  So     *)
(* the bottom of the range needs no case of its own.                          *)
Lemma Drnd_FLX_plus a b :
  generic_format radix2 Dfexp a -> generic_format radix2 Dfexp b ->
  Drnd (a + b) = Xrnd (a + b).
Proof.
move=> Fa Fb.
have [Hn|Hs] := Rle_lt_dec Dnorm (Rabs (a + b)); first by apply: Drnd_FLX.
have F : generic_format radix2 Dfexp (a + b).
  apply: FLT_format_plus_small => //.
  rewrite Z.add_comm; apply/Rlt_le/(Rlt_le_trans _ Dnorm) => //.
  by apply: bpow_le; lia.
by rewrite !round_generic //; apply: generic_format_FLX_FLT F.
Qed.

Lemma Drnd_FLX_minus a b :
  generic_format radix2 Dfexp a -> generic_format radix2 Dfexp b ->
  Drnd (a - b) = Xrnd (a - b).
Proof.
move=> Fa Fb; have -> : a - b = a + - b by lra.
by apply: Drnd_FLX_plus => //; apply: generic_format_opp.
Qed.

(* Every binary64 number is a number of the format with no bottom: the        *)
(* bound below is on the exponent only, and removing it takes nothing away.   *)
Lemma Dformat_FLX x : Xformat (D2R x).
Proof. by apply/generic_format_FLX_FLT/Dformat. Qed.

(* And a pair of them is a double word for both, with nothing asked at all.   *)
Lemma Ddw_FLX xh xl :
  generic_format radix2 Dfexp xh -> generic_format radix2 Dfexp xl ->
  xh = Drnd (xh + xl) -> double_word prec Dchoice xh xl.
Proof.
move=> Fxh Fxl xhE.
split; first by split; [apply: generic_format_FLX_FLT Fxh |
                        apply: generic_format_FLX_FLT Fxl].
by rewrite -(Drnd_FLX_plus _ _ Fxh Fxl).
Qed.

(* TwoSum computes the same two numbers in both formats.  Each development    *)
(* proves its own TwoSum error free, so the pair is pinned by the one         *)
(* rounding that makes the high word, and the two formats agree on that as    *)
(* soon as the sum is normal, or zero.                                        *)
Lemma twoSum_FLX a b :
  Dfin a -> Dfin b ->
  Dfits (D2R a + D2R b) ->
  Dfits (D2R (a + b)%float - D2R b) ->
  Dfits (D2R (a + b)%float - D2R ((a + b) - b)%float) ->
  Dfits (D2R a - D2R ((a + b) - b)%float) ->
  Dfits (D2R b - D2R ((a + b) - ((a + b) - b))%float) ->
  Dfits (D2R (a - ((a + b) - b))%float +
         D2R (b - ((a + b) - ((a + b) - b)))%float) ->
  D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b) /\
  D2R (dwlo (twoSum a b)) = TwoSum_err prec Dchoice (D2R a) (D2R b).
Proof.
move=> Fa Fb Hs Ha' Hb' Hda Hdb He.
have Hp : (1 < prec)%Z by [].
have [Eh _] := twoSumE _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Ex := twoSum_exact _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Hsum : D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b).
  by rewrite Eh TwoSum_sumE (Drnd_FLX_plus _ _ (Dformat a) (Dformat b)).
split=> //.
rewrite (TwoSum_correct Hp eq_refl (Dformat_FLX a) (Dformat_FLX b)).
by rewrite -Hsum; lra.
Qed.

(* And in the form the program can check.                                     *)
Lemma twoSum_FLX_fin a b :
  Dfin a -> Dfin b ->
  DtwoSumFin a b ->
  D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b) /\
  D2R (dwlo (twoSum a b)) = TwoSum_err prec Dchoice (D2R a) (D2R b).
Proof.
move=> Fa Fb [Fs [Fa' [Fb' [Fda [Fdb Fe]]]]].
have [_ Hs] := Dfin_add _ _ Fa Fb Fs.
have [_ Ha'] := Dfin_sub _ _ Fs Fb Fa'.
have [_ Hb'] := Dfin_sub _ _ Fs Fa' Fb'.
have [_ Hda] := Dfin_sub _ _ Fa Fa' Fda.
have [_ Hdb] := Dfin_sub _ _ Fb Fb' Fdb.
have [_ He] := Dfin_add _ _ Fda Fdb Fe.
by apply: twoSum_FLX.
Qed.

(* Fast2Sum computes the same two numbers in both formats.  Here there is no  *)
(* exactness to lean on - it is exactly the thing the preconditions are       *)
(* about - so the three operations are matched one by one, which asks         *)
(* nothing of the arguments.  The preconditions stay where they belong,       *)
(* inside the proof of the development being ported.  The three places where  *)
(* the formats must agree are named by the numbers the program computes, so   *)
(* they are testable too.                                                     *)
Lemma fastTwoSum_FLX a b :
  Dfin a -> Dfin b ->
  Dfits (D2R a + D2R b) ->
  Dfits (D2R (a + b)%float - D2R a) ->
  Dfits (D2R b - D2R ((a + b) - a)%float) ->
  D2R (dwhi (fastTwoSum a b)) =
    fst (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)) /\
  D2R (dwlo (fastTwoSum a b)) =
    snd (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)).
Proof.
move=> Fa Fb Hs Hz Ht.
have [Eh [El _]] := fastTwoSumE _ _ Fa Fb Hs Hz Ht.
have [Es Fs] := D2R_add _ _ Fa Fb Hs.
have [Ez _] := D2R_sub _ _ Fs Fa Hz.
have E1 := Drnd_FLX_plus _ _ (Dformat a) (Dformat b).
have FX : generic_format radix2 Dfexp (Xrnd (D2R a + D2R b)).
  by rewrite -E1 -Es; apply: Dformat.
have E2 := Drnd_FLX_minus _ _ FX (Dformat a).
have FZ : generic_format radix2 Dfexp (Xrnd (Xrnd (D2R a + D2R b) - D2R a)).
  by rewrite -E2 -E1 -Es -Ez; apply: Dformat.
rewrite /F2Sum.Fast2Sum /F2SumFLX.Fast2Sum /=.
split; first by rewrite Eh E1.
by rewrite El E1 E2 (Drnd_FLX_minus _ _ (Dformat b) FZ).
Qed.

(* And in the form the program can check.                                     *)
Lemma fastTwoSum_FLX_fin a b :
  Dfin a -> Dfin b ->
  DfastTwoSumFin a b ->
  D2R (dwhi (fastTwoSum a b)) =
    fst (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)) /\
  D2R (dwlo (fastTwoSum a b)) =
    snd (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)).
Proof.
move=> Fa Fb [Fs [Fz Ft]].
have [_ Hs] := Dfin_add _ _ Fa Fb Fs.
have [_ Hz] := Dfin_sub _ _ Fs Fa Fz.
have [_ Ht] := Dfin_sub _ _ Fb Fz Ft.
by apply: fastTwoSum_FLX.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The sum of two double words                                               *)
(* ---------------------------------------------------------------------------*)

(* What the ported development computes, on the reals.                        *)
Definition XplusDwDw (xh xl yh yl : R) : R * R :=
  let sh := TwoSum_sum prec Dchoice xh yh in
  let sl := TwoSum_err prec Dchoice xh yh in
  let th := TwoSum_sum prec Dchoice xl yl in
  let tl := TwoSum_err prec Dchoice xl yl in
  let c := Xrnd (sl + th) in
  let v := F2Sum.Fast2Sum prec Dchoice sh c in
  let w := Xrnd (tl + snd v) in
  F2Sum.Fast2Sum prec Dchoice (fst v) w.

(* Every number the algorithm computes is finite: the guard, in full.         *)
Definition DplusDwDwFin (xh xl yh yl : PrimFloat.float) :=
  let sh := dwhi (twoSum xh yh) in
  let sl := dwlo (twoSum xh yh) in
  let th := dwhi (twoSum xl yl) in
  let tl := dwlo (twoSum xl yl) in
  let c := (sl + th)%float in
  let v := fastTwoSum sh c in
  let w := (tl + dwlo v)%float in
  Dfin xh /\ Dfin xl /\ Dfin yh /\ Dfin yl /\
  DtwoSumFin xh yh /\ DtwoSumFin xl yl /\
  Dfin c /\ DfastTwoSumFin sh c /\
  Dfin w /\ DfastTwoSumFin (dwhi v) w.

(* The composition, written out: the two calls the program makes last.        *)
Lemma plusDwDwE xh xl yh yl :
  plusDwDw (DWFloat xh xl) (DWFloat yh yl) =
  fastTwoSum
    (dwhi (fastTwoSum (dwhi (twoSum xh yh))
             (dwlo (twoSum xh yh) + dwhi (twoSum xl yl))%float))
    (dwlo (twoSum xl yl) +
     dwlo (fastTwoSum (dwhi (twoSum xh yh))
             (dwlo (twoSum xh yh) + dwhi (twoSum xl yl))%float))%float.
Proof. by []. Qed.

(* The program computes, number for number, what the ported development       *)
(* computes: two TwoSum, two Fast2Sum, and the two lone roundings between     *)
(* them.  Nothing is asked of the values, only that no step overflow.         *)
Lemma plusDwDw_FLX xh xl yh yl :
  DplusDwDwFin xh xl yh yl ->
  D2R (dwhi (plusDwDw (DWFloat xh xl) (DWFloat yh yl))) =
    fst (XplusDwDw (D2R xh) (D2R xl) (D2R yh) (D2R yl)) /\
  D2R (dwlo (plusDwDw (DWFloat xh xl) (DWFloat yh yl))) =
    snd (XplusDwDw (D2R xh) (D2R xl) (D2R yh) (D2R yl)).
Proof.
move=> [Fxh [Fxl [Fyh [Fyl [T1 [T2 [Fc [G1 [Fw G2]]]]]]]]].
have [Esh Esl] := twoSum_FLX_fin _ _ Fxh Fyh T1.
have [Eth Etl] := twoSum_FLX_fin _ _ Fxl Fyl T2.
have [Fsh Fsl] := twoSum_fin _ _ T1.
have [Fth Ftl] := twoSum_fin _ _ T2.
have [Evh Evl] := fastTwoSum_FLX_fin _ _ Fsh Fc G1.
have [Fvh Fvl] := fastTwoSum_fin _ _ G1.
have [Ezh Ezl] := fastTwoSum_FLX_fin _ _ Fvh Fw G2.
have [Ec _] := Dfin_add _ _ Fsl Fth Fc.
have [Ew _] := Dfin_add _ _ Ftl Fvl Fw.
rewrite Ec (Drnd_FLX_plus _ _ (Dformat _) (Dformat _)) Esh Esl Eth in Evh Evl.
rewrite Ew (Drnd_FLX_plus _ _ (Dformat _) (Dformat _)) Etl Evl Evh in Ezh Ezl.
by rewrite plusDwDwE; split; [exact: Ezh | exact: Ezl].
Qed.

(* The unit roundoff, as the ported development writes it.                    *)
Notation Du := (bpow radix2 (- prec)).

(* What the ported development calls the relative error is the one made by    *)
(* XplusDwDw, which is to say by the program.                                 *)
Lemma relative_errorDWDWE xh xl yh yl :
  relative_errorDWDW prec Dchoice xh xl yh yl =
  Rabs ((fst (XplusDwDw xh xl yh yl) + snd (XplusDwDw xh xl yh yl) -
         ((xh + xl) + (yh + yl))) / ((xh + xl) + (yh + yl))).
Proof. by []. Qed.

(* The sum of two double words, on primitive floats, is within three unit     *)
(* roundoffs squared of the exact sum.  Nothing is asked of the numbers but   *)
(* that the two arguments really are double words, that their sum is not      *)
(* zero, and that no step overflows.                                          *)
Theorem plusDwDw_relerr xh xl yh yl :
  DplusDwDwFin xh xl yh yl ->
  D2R xh = Drnd (D2R xh + D2R xl) ->
  D2R yh = Drnd (D2R yh + D2R yl) ->
  (D2R xh + D2R xl) + (D2R yh + D2R yl) <> 0 ->
  Rabs ((D2R (dwhi (plusDwDw (DWFloat xh xl) (DWFloat yh yl))) +
         D2R (dwlo (plusDwDw (DWFloat xh xl) (DWFloat yh yl)))) -
        ((D2R xh + D2R xl) + (D2R yh + D2R yl))) <=
  3 * Du ^ 2 / (1 - 4 * Du) *
  Rabs ((D2R xh + D2R xl) + (D2R yh + D2R yl)).
Proof.
move=> F Ex Ey Hn.
have [Eh El] := plusDwDw_FLX xh xl yh yl F.
have DWx := Ddw_FLX _ _ (Dformat xh) (Dformat xl) Ex.
have DWy := Ddw_FLX _ _ (Dformat yh) (Dformat yl) Ey.
have Hp : (1 < prec)%Z by [].
have Hp3 : (3 <= prec)%Z by [].
have K := DWPlusDW_relerr_bound Hp eq_refl Hp3 DWx DWy Hn.
rewrite relative_errorDWDWE in K.
have HE : forall a b : R, b <> 0 -> Rabs (a - b) = Rabs ((a - b) / b) * Rabs b.
  by move=> a b b0; rewrite -Rabs_mult; congr Rabs; field.
rewrite Eh El (HE _ _ Hn).
by apply: Rmult_le_compat_r; [apply: Rabs_pos | exact: K].
Qed.
