From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dwtwosum DWPlus.

(* The unbounded format, where the double-word theorems live.                 *)
(* Those theorems are all stated for a format with no bottom, and binary64    *)
(* has one.  Above the smallest normal number the two round alike, so a       *)
(* value that stays there is read the same way by either, and a double word   *)
(* that stays there is a double word for both.  That is what carries the      *)
(* theorems over.                                                             *)

Open Scope R_scope.

(* The smallest normal number.                                                *)
Notation Dnorm := (bpow radix2 (SpecFloat.emin prec emax + prec - 1)).

(* Round to nearest, ties to even, in the format with no bottom.              *)
Notation Xrnd :=
  (round radix2 (FLX_exp prec) (Znearest (fun n => negb (Z.even n)))).
Notation Xformat := (generic_format radix2 (FLX_exp prec)).

(* Round to nearest, ties to even, as the ported development names it.        *)
Notation Dchoice := (fun n : Z => negb (Z.even n)).

(* The two formats round this number the same way: it is normal, or it is     *)
(* zero, and zero is the one value below the smallest normal they agree on.   *)
Definition Dsame (r : R) := r = 0 \/ Dnorm <= Rabs r.

(* Zero is the one value below the smallest normal number that the two        *)
(* formats still agree on, and the algorithms do produce it.                  *)
Lemma Drnd_FLX0 r : Dsame r -> Drnd r = Xrnd r.
Proof.
by case=> [->|rge]; [rewrite !round_0 | apply: Drnd_FLX].
Qed.

(* Every binary64 number is a number of the format with no bottom: the        *)
(* bound below is on the exponent only, and removing it takes nothing away.   *)
Lemma Dformat_FLX x : Xformat (D2R x).
Proof. by apply/generic_format_FLX_FLT/Dformat. Qed.

(* And a pair of them whose value is normal is a double word for both.        *)
Lemma Ddw_FLX xh xl :
  generic_format radix2 Dfexp xh -> generic_format radix2 Dfexp xl ->
  xh = Drnd (xh + xl) -> Dnorm <= Rabs (xh + xl) ->
  double_word prec (fun n => negb (Z.even n)) xh xl.
Proof.
move=> Fxh Fxl xhE xge.
split; first by split; [apply: generic_format_FLX_FLT Fxh |
                        apply: generic_format_FLX_FLT Fxl].
by rewrite -Drnd_FLX0; [exact: xhE | by right].
Qed.

(* Every number twoSum computes is finite: this is its guard, and it is       *)
(* what a program can test.                                                   *)
Definition DtwoSumFin (a b : PrimFloat.float) :=
  Dfin (a + b)%float /\ Dfin ((a + b) - b)%float /\
  Dfin ((a + b) - ((a + b) - b))%float /\ Dfin (a - ((a + b) - b))%float /\
  Dfin (b - ((a + b) - ((a + b) - b)))%float /\
  Dfin ((a - ((a + b) - b)) +
        (b - ((a + b) - ((a + b) - b))))%float.

(* The same for fastTwoSum, three operations instead of six.                  *)
Definition DfastTwoSumFin (a b : PrimFloat.float) :=
  Dfin (a + b)%float /\ Dfin ((a + b) - a)%float /\
  Dfin (b - ((a + b) - a))%float.

(* A guarded call returns two finite numbers, so the next step may run.       *)
Lemma twoSum_fin a b : DtwoSumFin a b ->
  Dfin (dwhi (twoSum a b)) /\ Dfin (dwlo (twoSum a b)).
Proof. by move=> [H1 [_ [_ [_ [_ H6]]]]]; split. Qed.

Lemma fastTwoSum_fin a b : DfastTwoSumFin a b ->
  Dfin (dwhi (fastTwoSum a b)) /\ Dfin (dwlo (fastTwoSum a b)).
Proof. by move=> [H1 [_ H3]]; split. Qed.

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
  Dsame (D2R a + D2R b) ->
  D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b) /\
  D2R (dwlo (twoSum a b)) = TwoSum_err prec Dchoice (D2R a) (D2R b).
Proof.
move=> Fa Fb Hs Ha' Hb' Hda Hdb He Hn.
have Hp : (1 < prec)%Z by [].
have [Eh _] := twoSumE _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Ex := twoSum_exact _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Hsum : D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b).
  by rewrite Eh TwoSum_sumE Drnd_FLX0.
split=> //.
rewrite (TwoSum_correct Hp eq_refl (Dformat_FLX a) (Dformat_FLX b)).
by rewrite -Hsum; lra.
Qed.

(* And in the form the program can check.                                     *)
Lemma twoSum_FLX_fin a b :
  Dfin a -> Dfin b ->
  DtwoSumFin a b ->
  Dsame (D2R a + D2R b) ->
  D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b) /\
  D2R (dwlo (twoSum a b)) = TwoSum_err prec Dchoice (D2R a) (D2R b).
Proof.
move=> Fa Fb [Fs [Fa' [Fb' [Fda [Fdb Fe]]]]] Hn.
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
  Dsame (D2R a + D2R b) ->
  Dsame (D2R (a + b)%float - D2R a) ->
  Dsame (D2R b - D2R ((a + b) - a)%float) ->
  D2R (dwhi (fastTwoSum a b)) =
    fst (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)) /\
  D2R (dwlo (fastTwoSum a b)) =
    snd (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)).
Proof.
move=> Fa Fb Hs Hz Ht H1 H2 H3.
have [Eh [El _]] := fastTwoSumE _ _ Fa Fb Hs Hz Ht.
have [Es Fs] := D2R_add _ _ Fa Fb Hs.
have [Ez _] := D2R_sub _ _ Fs Fa Hz.
have Esx : D2R (a + b)%float = Xrnd (D2R a + D2R b).
  by rewrite Es Drnd_FLX0.
have Ezx : D2R ((a + b) - a)%float = Xrnd (Xrnd (D2R a + D2R b) - D2R a).
  by rewrite Ez Esx Drnd_FLX0 // -Esx.
rewrite Esx in H2; rewrite Ezx in H3.
rewrite /F2Sum.Fast2Sum /F2SumFLX.Fast2Sum /=.
split; first by rewrite Eh Drnd_FLX0.
rewrite El (Drnd_FLX0 _ H1) (Drnd_FLX0 _ H2).
by apply: Drnd_FLX0.
Qed.

(* And in the form the program can check.                                     *)
Lemma fastTwoSum_FLX_fin a b :
  Dfin a -> Dfin b ->
  DfastTwoSumFin a b ->
  Dsame (D2R a + D2R b) ->
  Dsame (D2R (a + b)%float - D2R a) ->
  Dsame (D2R b - D2R ((a + b) - a)%float) ->
  D2R (dwhi (fastTwoSum a b)) =
    fst (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)) /\
  D2R (dwlo (fastTwoSum a b)) =
    snd (F2Sum.Fast2Sum prec Dchoice (D2R a) (D2R b)).
Proof.
move=> Fa Fb [Fs [Fz Ft]] H1 H2 H3.
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

(* And the ten places where the two formats must round alike.  Each names     *)
(* the argument of a rounding the program is about to make, so this too is a  *)
(* test on numbers the program has in hand.                                   *)
Definition DplusDwDwSame (xh xl yh yl : PrimFloat.float) :=
  let sh := dwhi (twoSum xh yh) in
  let sl := dwlo (twoSum xh yh) in
  let th := dwhi (twoSum xl yl) in
  let tl := dwlo (twoSum xl yl) in
  let c := (sl + th)%float in
  let v := fastTwoSum sh c in
  let w := (tl + dwlo v)%float in
  Dsame (D2R xh + D2R yh) /\
  Dsame (D2R xl + D2R yl) /\
  Dsame (D2R sl + D2R th) /\
  Dsame (D2R sh + D2R c) /\
  Dsame (D2R (sh + c)%float - D2R sh) /\
  Dsame (D2R c - D2R ((sh + c) - sh)%float) /\
  Dsame (D2R tl + D2R (dwlo v)) /\
  Dsame (D2R (dwhi v) + D2R w) /\
  Dsame (D2R (dwhi v + w)%float - D2R (dwhi v)) /\
  Dsame (D2R w - D2R ((dwhi v + w) - dwhi v)%float).

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
(* them.                                                                      *)
Lemma plusDwDw_FLX xh xl yh yl :
  DplusDwDwFin xh xl yh yl -> DplusDwDwSame xh xl yh yl ->
  D2R (dwhi (plusDwDw (DWFloat xh xl) (DWFloat yh yl))) =
    fst (XplusDwDw (D2R xh) (D2R xl) (D2R yh) (D2R yl)) /\
  D2R (dwlo (plusDwDw (DWFloat xh xl) (DWFloat yh yl))) =
    snd (XplusDwDw (D2R xh) (D2R xl) (D2R yh) (D2R yl)).
Proof.
move=> [Fxh [Fxl [Fyh [Fyl [T1 [T2 [Fc [G1 [Fw G2]]]]]]]]].
move=> [S1 [S2 [S3 [S4 [S5 [S6 [S7 [S8 [S9 S10]]]]]]]]].
have [Esh Esl] := twoSum_FLX_fin _ _ Fxh Fyh T1 S1.
have [Eth Etl] := twoSum_FLX_fin _ _ Fxl Fyl T2 S2.
have [Fsh Fsl] := twoSum_fin _ _ T1.
have [Fth Ftl] := twoSum_fin _ _ T2.
have [Evh Evl] := fastTwoSum_FLX_fin _ _ Fsh Fc G1 S4 S5 S6.
have [Fvh Fvl] := fastTwoSum_fin _ _ G1.
have [Ezh Ezl] := fastTwoSum_FLX_fin _ _ Fvh Fw G2 S8 S9 S10.
have [Ec _] := Dfin_add _ _ Fsl Fth Fc.
have [Ew _] := Dfin_add _ _ Ftl Fvl Fw.
rewrite Ec (Drnd_FLX0 _ S3) Esh Esl Eth in Evh Evl.
rewrite Ew (Drnd_FLX0 _ S7) Etl Evl Evh in Ezh Ezl.
by rewrite plusDwDwE; split; [exact: Ezh | exact: Ezl].
Qed.
