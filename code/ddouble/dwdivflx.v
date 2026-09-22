From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error Mult_error BinarySingleNaN PrimFloat.
From Flocq Require Import Pff.Pff2Flocq.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn dwtwosum dwprod dwflx.
From dwarith Require Import dwbound F2Sum DWDivDW.

(* The quotient of two double words, read in the format with no bottom.       *)
(*                                                                            *)
(* `dw_updn.v' bounds `divDwDw2' by a shift of sixteen units in the last      *)
(* place, and sixteen is the paper's own constant: `DWDivDW.v' holds          *)
(* Theorem 7.1, admit-free, for `DWDivDW2', which is `divDwDw2' step for      *)
(* step, and it reads `15 u^2 + 56 u^3'.  What stands between that theorem    *)
(* and the program is this file: the theorem is over the reals in the format  *)
(* with no smallest exponent, the program runs primitive floats in the        *)
(* bounded one.  `dwflx.v' is the same road built for the SUM; this is the    *)
(* quotient's.                                                                *)
(*                                                                            *)
(* THE QUOTIENT IS HARDER THAN THE SUM, and for one reason.  A sum of two     *)
(* floats too small for the bounded format to round is exact, so neither      *)
(* format rounds it and they agree with nothing asked - that is               *)
(* `Drnd_FLX_plus' of dwflx.v.  A product and a quotient have no such         *)
(* property: below the smallest normal number the bounded format rounds and   *)
(* the other does not.  Hence every lemma here that touches one carries a     *)
(* range condition, and hence the quotient's BOUND needs a range test where   *)
(* the sum's needs none.                                                      *)

Open Scope R_scope.

(* A product and a quotient, where the two formats agree.                     *)
Lemma Drnd_FLX_mult a b :
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  Drnd (D2R a * D2R b) = Xrnd (D2R a * D2R b).
Proof. by move=> Hn; apply: Drnd_FLX. Qed.

Lemma Drnd_FLX_div a b :
  (Dnorm <= Rabs (D2R a / D2R b))%R ->
  Drnd (D2R a / D2R b) = Xrnd (D2R a / D2R b).
Proof. by move=> Hn; apply: Drnd_FLX. Qed.

(* The high word of the two-product is the rounded product, and the two       *)
(* formats agree on it once it is normal.                                     *)
Lemma twoProd_hi_FLX a b :
  Dfin a -> Dfin b -> Dfin (a * b)%float ->
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) = Xrnd (D2R a * D2R b).
Proof.
move=> Fa Fb Fp Hn.
have [Ep _] := Dfin_mul _ _ Fa Fb Fp.
by rewrite /twoProd /dekker /=; case: (splitC a) => ??; case: (splitC b) => ??;
   rewrite /= Ep; apply: Drnd_FLX.
Qed.

(* And so the two-product computes, in the format with no bottom, exactly     *)
(* the pair the paper's `Fast2Mult' does: the rounded product, and the error  *)
(* of it, which that format holds exactly.  This is the fact the paper        *)
(* assumes of its own two-product, and the note beside that assumption reads  *)
(* "or Dekker's algorithm" - Dekker's algorithm is what this is.              *)
Lemma twoProd_FLX a b :
  Dfin a -> Dfin b -> Dfin (a * b)%float -> Dfin (dwlo (twoProd a b)) ->
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  (Dprodlo <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) = Xrnd (D2R a * D2R b) /\
  D2R (dwlo (twoProd a b)) =
    Xrnd (D2R a * D2R b - Xrnd (D2R a * D2R b)).
Proof.
move=> Fa Fb Fp Fe Hn Hp.
have Ehi := twoProd_hi_FLX _ _ Fa Fb Fp Hn.
have Hex := twoProd_exact _ _ Fe Hp.
split => //.
have Hlo : D2R (dwlo (twoProd a b)) =
           (D2R a * D2R b - Xrnd (D2R a * D2R b))%R by rewrite -Ehi; lra.
rewrite Hlo.
(* The error of a product is itself a number of this format, so the rounding *)
(* of it is itself.  `round_generic' has to be aimed at the OUTER rounding:   *)
(* left to find its own target it takes the inner one and asks for the        *)
(* product to be a number of the format, which it is not.                     *)
have Hp0 : Prec_gt_0 prec by [].
have Hf : Xformat (D2R a * D2R b - Xrnd (D2R a * D2R b)).
  rewrite -Ropp_minus_distr; apply: generic_format_opp.
  by apply: mult_error_FLX; exact: Dformat_FLX.
by rewrite (round_generic _ _ _ _ Hf).
Qed.

(* ---------------------------------------------------------------------------*)
(*  The quotient, composed                                                    *)
(* ---------------------------------------------------------------------------*)

(* What the program computes, written on the reals of the format with no      *)
(* bottom.  Step for step `divDwDw2' of dwarith.v, with each float operation  *)
(* replaced by the rounding of the real one.                                  *)
Definition XtwoProd (a b : R) : R * R :=
  (Xrnd (a * b), Xrnd (a * b - Xrnd (a * b))).

Definition XtimesDwFp1 (yh yl t : R) : R * R :=
  let ch := fst (XtwoProd yh t) in
  let cl1 := snd (XtwoProd yh t) in
  let cl2 := Xrnd (yl * t) in
  let v := F2Sum.Fast2Sum prec Dchoice ch cl2 in
  let tl2 := Xrnd (snd v + cl1) in
  F2Sum.Fast2Sum prec Dchoice (fst v) tl2.

Definition XdivDwDw2 (xh xl yh yl : R) : R * R :=
  let t := Xrnd (xh / yh) in
  let r := XtimesDwFp1 yh yl t in
  let pih := Xrnd (xh - fst r) in
  let dl := Xrnd (xl - snd r) in
  let d := Xrnd (pih + dl) in
  let tl := Xrnd (d / yh) in
  F2Sum.Fast2Sum prec Dchoice t tl.

(* Every number the program makes is a number, and every step that rounds a   *)
(* product or a quotient does so in the range where the two formats agree.    *)
(* The product also has to be above the line where the two-product stops      *)
(* missing it, and that line is the higher of the two, so it carries both.    *)
(*                                                                            *)
(* THE STEPS SHOULD BE NAMED, NOT WRITTEN OUT, and that is worth doing.  Said *)
(* of the expressions themselves, as below, each condition carries the whole  *)
(* of the algorithm up to it: the last is a page, and the proof context is    *)
(* unreadable.  The same thing said of sixteen named floats with an equation  *)
(* apiece - `t = xh / yh', `twoProd yh t = DWFloat ch cl1', and so on - asks  *)
(* exactly as much and every hypothesis stays one line.  The proof below      *)
(* would lose nothing by it; it is a restatement, not a repair.               *)
Definition DdivDwDw2Fin (xh xl yh yl : PrimFloat.float) :=
  let t := (xh / yh)%float in
  let ch := dwhi (twoProd yh t) in
  let cl1 := dwlo (twoProd yh t) in
  let cl2 := (yl * t)%float in
  let v := fastTwoSum ch cl2 in
  let tl2 := (dwlo v + cl1)%float in
  let rh := dwhi (fastTwoSum (dwhi v) tl2) in
  let rl := dwlo (fastTwoSum (dwhi v) tl2) in
  let pih := (xh - rh)%float in
  let dl := (xl - rl)%float in
  let d := (pih + dl)%float in
  let tl := (d / yh)%float in
  Dfin xh /\ Dfin xl /\ Dfin yh /\ Dfin yl /\ Dfin t /\
  Dfin ch /\ Dfin cl1 /\ Dfin cl2 /\ DfastTwoSumFin ch cl2 /\
  Dfin tl2 /\ DfastTwoSumFin (dwhi v) tl2 /\
  Dfin pih /\ Dfin dl /\ Dfin d /\
  Dfin tl /\ DfastTwoSumFin t tl.

(* And the range conditions.  Two of them are stated as what they are FOR -   *)
(* the two formats rounding alike - and not as a magnitude, because a         *)
(* magnitude would refuse the ordinary case.  The low word of a double word   *)
(* is often nought, and then `yl * t' is nought and no magnitude condition    *)
(* can hold of it; a division that comes out exact leaves `d' nought, and     *)
(* the same again.  Both formats round nought to nought, so what is asked is  *)
(* that they agree, which nought meets and a normal number meets too.         *)
Definition DdivDwDw2Rng (xh xl yh yl : PrimFloat.float) :=
  let t := (xh / yh)%float in
  let ch := dwhi (twoProd yh t) in
  let cl1 := dwlo (twoProd yh t) in
  let cl2 := (yl * t)%float in
  let v := fastTwoSum ch cl2 in
  let tl2 := (dwlo v + cl1)%float in
  let rh := dwhi (fastTwoSum (dwhi v) tl2) in
  let rl := dwlo (fastTwoSum (dwhi v) tl2) in
  let pih := (xh - rh)%float in
  let dl := (xl - rl)%float in
  let d := (pih + dl)%float in
  (Dnorm <= Rabs (D2R xh / D2R yh))%R /\
  (Dprodlo <= Rabs (D2R yh * D2R t))%R /\
  Drnd (D2R yl * D2R t) = Xrnd (D2R yl * D2R t) /\
  Drnd (D2R d / D2R yh) = Xrnd (D2R d / D2R yh).

(* The divisor is not nought, and that comes free with the range condition:   *)
(* a quotient by nought is read as nought here, and nought is not above the   *)
(* smallest normal number.                                                    *)
Lemma Dnz_of_norm a b : (Dnorm <= Rabs (D2R a / D2R b))%R -> D2R b <> 0%R.
Proof.
move=> Hn Hb0; move: Hn; rewrite Hb0 /Rdiv Rinv_0 Rmult_0_r Rabs_R0.
by have := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1); lra.
Qed.

(* The composition, written out: the calls the program makes, in order.       *)
Lemma divDwDw2E xh xl yh yl :
  divDwDw2 (DWFloat xh xl) (DWFloat yh yl) =
  (let t := (xh / yh)%float in
   let: DWFloat rh rl := timesDwFp1 (DWFloat yh yl) t in
   fastTwoSum t (((xh - rh) + (xl - rl)) / yh)%float).
Proof. by rewrite /divDwDw2; case: (timesDwFp1 _ _). Qed.

(* THE COMPOSITION.  The program computes, number for number, what the       *)
(* definition above computes on the reals: one quotient, the two-product, a   *)
(* product, two Fast2Sum, two differences, a sum, a second quotient and a     *)
(* third Fast2Sum.  Nothing is asked of the values but that every step be a   *)
(* number, and that the product and the two quotients be in the range where   *)
(* the two formats agree.                                                     *)
Lemma divDwDw2_FLX xh xl yh yl :
  DdivDwDw2Fin xh xl yh yl -> DdivDwDw2Rng xh xl yh yl ->
  D2R (dwhi (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) =
    fst (XdivDwDw2 (D2R xh) (D2R xl) (D2R yh) (D2R yl)) /\
  D2R (dwlo (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) =
    snd (XdivDwDw2 (D2R xh) (D2R xl) (D2R yh) (D2R yl)).
Proof.
move=> [Fxh [Fxl [Fyh [Fyl [Ft [Fch [Fcl1 [Fcl2 [G1 [Ftl2 [G2
       [Fpih [Fdl [Fd [Ftl G3]]]]]]]]]]]]]]] [Hq1 [Hp1 [Hm1 Hq2]]].
have Hyh := Dnz_of_norm _ _ Hq1.
(* the first quotient *)
have [Et _] := Dfin_div _ _ Fxh Hyh Ft.
rewrite (Drnd_FLX_div xh yh Hq1) in Et.
(* the two-product.  The line above which it does not miss is higher than    *)
(* the one where the two formats agree, so it carries both.                  *)
have Hnp : (Dnorm <= Rabs (D2R yh * D2R (xh / yh)%float))%R.
  by apply: Rle_trans Hp1; apply: bpow_le.
have [Ech Ecl1] := twoProd_FLX yh (xh / yh)%float Fyh Ft Fch Fcl1 Hnp Hp1.
(* the lone product, and the first Fast2Sum *)
have [Ecl2 _] := Dfin_mul _ _ Fyl Ft Fcl2.
rewrite Hm1 in Ecl2.
have [Fvh Fvl] := fastTwoSum_fin _ _ G1.
have [Evh Evl] := fastTwoSum_FLX_fin _ _ Fch Fcl2 G1.
(* the sum of the two low words, and the second Fast2Sum *)
have [Etl2e _] := Dfin_add _ _ Fvl Fcl1 Ftl2.
rewrite (Drnd_FLX_plus _ _ (Dformat _) (Dformat _)) in Etl2e.
have [Frh Frl] := fastTwoSum_fin _ _ G2.
have [Erh Erl] := fastTwoSum_FLX_fin _ _ Fvh Ftl2 G2.
(* the two differences and their sum, none of which needs a range           *)
have [Epih _] := Dfin_sub _ _ Fxh Frh Fpih.
rewrite (Drnd_FLX_minus _ _ (Dformat _) (Dformat _)) in Epih.
have [Edle _] := Dfin_sub _ _ Fxl Frl Fdl.
rewrite (Drnd_FLX_minus _ _ (Dformat _) (Dformat _)) in Edle.
have [Ed _] := Dfin_add _ _ Fpih Fdl Fd.
rewrite (Drnd_FLX_plus _ _ (Dformat _) (Dformat _)) in Ed.
(* the second quotient, and the last Fast2Sum *)
have [Etle _] := Dfin_div _ _ Fd Hyh Ftl.
rewrite Hq2 in Etle.
have [Ezh Ezl] := fastTwoSum_FLX_fin _ _ Ft Ftl G3.
(* And the two sides are the same numbers, rewritten from the outside in.    *)
rewrite /XdivDwDw2 /XtimesDwFp1 /XtwoProd /=.
split.
  by rewrite Ezh Etle Ed Epih Edle Erh Erl Etl2e Evh Evl Ech Ecl1 Ecl2 Et.
by rewrite Ezl Etle Ed Epih Edle Erh Erl Etl2e Evh Evl Ech Ecl1 Ecl2 Et.
Qed.


(* ---------------------------------------------------------------------------*)
(*  And the same thing the paper's own definition computes                    *)
(* ---------------------------------------------------------------------------*)

(* The paper's two-product, taken to be `Fast2Mult': the rounded product and  *)
(* the rounding of what it left.  That is what `twoProd_FLX' above says the   *)
(* program's two-product computes, and the note beside the paper's own        *)
(* hypothesis - "or Dekker's algorithm" - is that same remark.                *)
Notation XFast2Mult := (DWTimesFP.Fast2Mult prec Dchoice).

(* The hypothesis the paper leaves open: the two-product is error free.  It   *)
(* holds of numbers of the format, and only of them, which is what the        *)
(* hypothesis now asks - the error of a product is itself a number of the     *)
(* format, so rounding it changes nothing and the pair adds back up.          *)
Lemma XFast2Mult_correct a b :
  Xformat a -> Xformat b ->
  a * b = fst (XFast2Mult a b) + snd (XFast2Mult a b).
Proof.
move=> Fa Fb.
have Hp0 : Prec_gt_0 prec by [].
have Hf : Xformat (a * b - Xrnd (a * b)).
  by rewrite -Ropp_minus_distr; apply/generic_format_opp/mult_error_FLX.
by rewrite /DWTimesFP.Fast2Mult /= (round_generic _ _ _ _ Hf); ring.
Qed.

(* `XtimesDwFp1' IS the paper's `DWTimesFP': the same two-product, the same   *)
(* lone product and the same two Fast2Sum, in the same order.                 *)
Lemma XtimesDwFp1E yh yl t :
  XtimesDwFp1 yh yl t = DWTimesFP.DWTimesFP prec Dchoice XFast2Mult yh yl t.
Proof. by []. Qed.

(* And `XdivDwDw2' is the paper's `DWDivDW2' but for ONE place: the paper     *)
(* writes the head difference `xh - rh' with no rounding, because that        *)
(* subtraction is exact, and the program of course rounds it.  `Algo15_P' is  *)
(* that exactness, so the rounding may be dropped and the two are the same.   *)
Lemma XdivDwDw2E xh xl yh yl :
  DWPlus.double_word prec Dchoice xh xl ->
  DWPlus.double_word prec Dchoice yh yl -> yh <> 0 ->
  XdivDwDw2 xh xl yh yl = DWDivDW2 prec Dchoice XFast2Mult xh xl yh yl.
Proof.
move=> DWx DWy yhn0.
have Hp1 : (1 < prec)%Z by [].
have Hp4 : (4 <= prec)%Z by [].
have Hf := Algo15_P Hp1 eq_refl XFast2Mult_correct eq_refl Hp4 yhn0 DWx DWy.
rewrite /XdivDwDw2 /DWDivDW2 XtimesDwFp1E.
rewrite (surjective_pairing (DWTimesFP.DWTimesFP _ _ _ _ _ _)) /=.
by rewrite (round_generic _ _ _ _ Hf).
Qed.

(* The unit roundoff, as the paper writes it.                                 *)
Notation Du := (bpow radix2 (- prec)).

(* THE QUOTIENT OF TWO DOUBLE WORDS, ON PRIMITIVE FLOATS.  Theorem 7.1 of    *)
(* the paper, said of the program: fifteen units in the last place of the low *)
(* word, and a little.  Two things are asked of the numbers, and nothing      *)
(* else: that the arguments really are double words, and that the guard hold  *)
(* - every step a number, and the product and the two quotients in the range  *)
(* where the two formats agree.                                               *)
Theorem divDwDw2_relerr xh xl yh yl :
  DdivDwDw2Fin xh xl yh yl -> DdivDwDw2Rng xh xl yh yl ->
  D2R xh = Drnd (D2R xh + D2R xl) ->
  D2R yh = Drnd (D2R yh + D2R yl) ->
  Rabs ((D2R (dwhi (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) +
         D2R (dwlo (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) -
         (D2R xh + D2R xl) / (D2R yh + D2R yl)) /
        ((D2R xh + D2R xl) / (D2R yh + D2R yl))) <=
  15 * Du ^ 2 + 56 * Du ^ 3.
Proof.
move=> F G Ex Ey.
have [Eh El] := divDwDw2_FLX xh xl yh yl F G.
have DWx := Ddw_FLX _ _ (Dformat xh) (Dformat xl) Ex.
have DWy := Ddw_FLX _ _ (Dformat yh) (Dformat yl) Ey.
have yhn0 : D2R yh <> 0 by apply: Dnz_of_norm (proj1 G).
have Hp1 : (1 < prec)%Z by [].
have Hp7 : (7 <= prec)%Z by [].
have K := DWDDW_correct Hp1 eq_refl XFast2Mult_correct eq_refl DWx DWy Hp7 yhn0.
rewrite Eh El (XdivDwDw2E _ _ _ _ DWx DWy yhn0).
exact: K.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The guard, from the one test a program makes                              *)
(* ---------------------------------------------------------------------------*)

(* Every number the algorithm makes is a number as soon as the LAST one is.   *)
(* Each is an argument of the operation that made the next, and an operation  *)
(* handed an infinity does not give a number back, so the low word of the     *)
(* answer carries the whole chain.  That is `twoSum_finI' read along the      *)
(* division, and it is why the interface tests one thing and not sixteen.     *)
Lemma divDwDw2_finI xh xl yh yl :
  Dfin yh -> Dfin yl ->
  Dfin (dwlo (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) ->
  DdivDwDw2Fin xh xl yh yl.
Proof.
move=> Fyh Fyl.
rewrite /DdivDwDw2Fin.
set t := (xh / yh)%float.
set ch := dwhi (twoProd yh t).
set cl1 := dwlo (twoProd yh t).
set cl2 := (yl * t)%float.
set v := fastTwoSum ch cl2.
set tl2 := (dwlo v + cl1)%float.
set rh := dwhi (fastTwoSum (dwhi v) tl2).
set rl := dwlo (fastTwoSum (dwhi v) tl2).
set pih := (xh - rh)%float.
set dl := (xl - rl)%float.
set d := (pih + dl)%float.
set tl := (d / yh)%float.
have Ez : divDwDw2 (DWFloat xh xl) (DWFloat yh yl) = fastTwoSum t tl by [].
rewrite Ez => Fz.
have G3 := fastTwoSum_finI _ _ Fz.
have [Ft Ftl] := Dfin_addI _ _ (proj1 G3).
have Fd := Dfin_divI _ _ Ftl.
have [Fpih Fdl] := Dfin_addI _ _ Fd.
have [Fxh Frh] := Dfin_subI _ _ Fpih.
have [Fxl Frl] := Dfin_subI _ _ Fdl.
have G2 := fastTwoSum_finI _ _ Frl.
have [Fvh Ftl2] := Dfin_addI _ _ (proj1 G2).
have [Fvl Fcl1] := Dfin_addI _ _ Ftl2.
have G1 := fastTwoSum_finI _ _ Fvl.
have [Fch Fcl2] := Dfin_addI _ _ (proj1 G1).
by tauto.
Qed.

(* ---------------------------------------------------------------------------*)
(*  From a relative error to a step                                           *)
(* ---------------------------------------------------------------------------*)

(* Neither the number divided nor the divisor is nought, and that comes free  *)
(* with the first range condition: a quotient at or above the smallest normal *)
(* number has both of them away from zero, and a double word whose value is   *)
(* nought has a nought high word.                                             *)
Lemma divDwDw2_nz xh xl yh yl :
  (Dnorm <= Rabs (D2R xh / D2R yh))%R ->
  D2R xh = Drnd (D2R xh + D2R xl) ->
  D2R yh = Drnd (D2R yh + D2R yl) ->
  D2R xh + D2R xl <> 0 /\ D2R yh + D2R yl <> 0.
Proof.
move=> Hq Ex Ey.
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have Hy := Dnz_of_norm _ _ Hq.
have Hx : D2R xh <> 0.
  by move=> Hx0; move: Hq; rewrite Hx0 /Rdiv Rmult_0_l Rabs_R0; lra.
by split => H0; [apply: Hx; rewrite Ex | apply: Hy; rewrite Ey];
   rewrite H0 round_0.
Qed.

(* A ratio bound read as a distance.                                          *)
Lemma Rabs_of_rel a b c :
  b <> 0 -> Rabs ((a - b) / b) <= c -> Rabs (a - b) <= c * Rabs b.
Proof.
move=> Hb H.
have -> : Rabs (a - b) = Rabs ((a - b) / b) * Rabs b.
  by rewrite -Rabs_mult; congr Rabs; field.
by apply: Rmult_le_compat_r => //; exact: Rabs_pos.
Qed.

(* The bound as a distance rather than as a ratio.                            *)
Theorem divDwDw2_err xh xl yh yl :
  DdivDwDw2Fin xh xl yh yl -> DdivDwDw2Rng xh xl yh yl ->
  D2R xh = Drnd (D2R xh + D2R xl) ->
  D2R yh = Drnd (D2R yh + D2R yl) ->
  Rabs (D2R (dwhi (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) +
        D2R (dwlo (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) -
        (D2R xh + D2R xl) / (D2R yh + D2R yl)) <=
  (15 * Du ^ 2 + 56 * Du ^ 3) *
  Rabs ((D2R xh + D2R xl) / (D2R yh + D2R yl)).
Proof.
move=> F G Ex Ey.
have [Hx Hy] := divDwDw2_nz _ _ _ _ (proj1 G) Ex Ey.
have Hxy : (D2R xh + D2R xl) / (D2R yh + D2R yl) <> 0.
  rewrite /Rdiv => /Rmult_integral [H0|H0]; first by case: Hx.
  by case: (Rinv_neq_0_compat _ Hy).
by apply: Rabs_of_rel => //; apply: divDwDw2_relerr.
Qed.


(* ---------------------------------------------------------------------------*)
(*  Sixteen units in the last place cover the paper's fifteen                 *)
(* ---------------------------------------------------------------------------*)

(* The unit roundoff, and the little arithmetic the margin below needs.       *)
Lemma Du_gt0 : 0 < Du.
Proof. by apply: bpow_gt_0. Qed.

Lemma DuE : Du = / 9007199254740992.
Proof. by []. Qed.

Lemma Du_small : Du * 1024 <= 1.
Proof. by rewrite DuE; lra. Qed.

Lemma Dumul a : 0 <= a -> a * Du * 1024 <= a.
Proof.
move=> Ha; have H1 := Du_small.
by rewrite -{2}(Rmult_1_r a) Rmult_assoc; apply: Rmult_le_compat_l.
Qed.

Lemma Dupos k : 0 <= Du ^ k.
Proof. by have H := Du_gt0; apply: pow_le; lra. Qed.

Lemma Du2 : Du ^ 2 * 1024 <= Du.
Proof.
have -> : Du ^ 2 * 1024 = Du * Du * 1024 by ring.
by apply: Dumul; have := Du_gt0; lra.
Qed.

Lemma Du3 : Du ^ 3 * 1024 <= Du ^ 2.
Proof.
have -> : Du ^ 3 * 1024 = Du ^ 2 * Du * 1024 by ring.
by apply/Dumul/Dupos.
Qed.

Lemma Du4 : Du ^ 4 * 1024 <= Du ^ 3.
Proof.
have -> : Du ^ 4 * 1024 = Du ^ 3 * Du * 1024 by ring.
by apply/Dumul/Dupos.
Qed.

Lemma Du5 : Du ^ 5 * 1024 <= Du ^ 4.
Proof.
have -> : Du ^ 5 * 1024 = Du ^ 4 * Du * 1024 by ring.
by apply/Dumul/Dupos.
Qed.

(* SIXTEEN COVERS FIFTEEN, and the margin is the whole of the matter.  The    *)
(* paper's bound is `15 u^2 + 56 u^3' and sixteen is the next power of two    *)
(* above it, so the shift is an exact change of exponent and a sixteenth of   *)
(* the step is left over.  That sixteenth is what pays for reading the bound  *)
(* off the answer rather than off the exact quotient.                         *)
Lemma Du_margin : 15 * Du ^ 2 + 56 * Du ^ 3 <=
                  16 * Du ^ 2 * (1 - (15 * Du ^ 2 + 56 * Du ^ 3)).
Proof.
have H0 := Du_gt0; have H1 := Du_small.
have K2 := Du2; have K3 := Du3; have K4 := Du4; have K5 := Du5.
have P2 := Dupos 2; have P3 := Dupos 3; have P4 := Dupos 4; have P5 := Dupos 5.
by lra.
Qed.

(* And so a step of sixteen units in the last place covers the error.         *)
(*                                                                            *)
(* THE STEP IS TAKEN FROM BOTH WORDS OF THE ANSWER, not from the high word    *)
(* alone.  The paper's bound is relative to the exact quotient, and what      *)
(* stands for the quotient here is the answer: the two words added in         *)
(* absolute value are at or above it whatever the low word does, and nothing  *)
(* has to be known about the low word at all.  From the high word alone the   *)
(* step would need the answer to be a double word - `zl' no larger than `u'   *)
(* times `zh' - and that is a further theorem, which the paper does not       *)
(* leave and which Fast2Sum does not give without its own precondition.       *)
Lemma divDwDw2_step xh xl yh yl (f : R) :
  DdivDwDw2Fin xh xl yh yl -> DdivDwDw2Rng xh xl yh yl ->
  D2R xh = Drnd (D2R xh + D2R xl) ->
  D2R yh = Drnd (D2R yh + D2R yl) ->
  16 * Du ^ 2 *
    (Rabs (D2R (dwhi (divDwDw2 (DWFloat xh xl) (DWFloat yh yl)))) +
     Rabs (D2R (dwlo (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))))) <= f ->
  Rabs (D2R (dwhi (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) +
        D2R (dwlo (divDwDw2 (DWFloat xh xl) (DWFloat yh yl))) -
        (D2R xh + D2R xl) / (D2R yh + D2R yl)) <= f.
Proof.
move=> F G Ex Ey.
have H := divDwDw2_err _ _ _ _ F G Ex Ey.
move: H.
set zh := D2R (dwhi _); set zl := D2R (dwlo _).
set Z := (D2R xh + D2R xl) / (D2R yh + D2R yl).
move=> H Hf.
have Hm := Du_margin.
have P2 := Dupos 2.
have Hs : Rabs (zh + zl) <= Rabs zh + Rabs zl by exact: Rabs_triang.
have Hinv : Rabs Z - Rabs (zh + zl) <= Rabs (zh + zl - Z).
  by rewrite (Rabs_minus_sym (zh + zl)); exact: Rabs_triang_inv.
have HZ : (1 - (15 * Du ^ 2 + 56 * Du ^ 3)) * Rabs Z <= Rabs zh + Rabs zl.
  by rewrite Rmult_minus_distr_r Rmult_1_l; lra.
have T1 : (15 * Du ^ 2 + 56 * Du ^ 3) * Rabs Z <=
          16 * Du ^ 2 * ((1 - (15 * Du ^ 2 + 56 * Du ^ 3)) * Rabs Z).
  rewrite -Rmult_assoc; apply: Rmult_le_compat_r; first exact: Rabs_pos.
  by exact: Hm.
have T2 : 16 * Du ^ 2 * ((1 - (15 * Du ^ 2 + 56 * Du ^ 3)) * Rabs Z) <=
          16 * Du ^ 2 * (Rabs zh + Rabs zl).
  by apply: Rmult_le_compat_l; [lra | exact: HZ].
by lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The guard the operation tests, and the two bounds                         *)
(* ---------------------------------------------------------------------------*)

Lemma D2R_dnorm : D2R dnorm = Dnorm.
Proof. by rewrite /D2R /dnorm; compute; lra. Qed.

Lemma Dfin_dnorm : Dfin dnorm.
Proof. by []. Qed.
Lemma fexp_norm : (Dfexp (SpecFloat.emin prec emax + prec - 1 + 1) <=
                   SpecFloat.emin prec emax + prec - 1)%Z.
Proof. by vm_compute. Qed.

(* A rounded value above a line has its exact value above it: rounding is     *)
(* monotone and the line is a number of the format.                           *)
Lemma Dnorm_of_rnd r : Dnorm < Rabs (Drnd r) -> Dnorm <= Rabs r.
Proof. by apply: Dbpow_of_rnd fexp_norm. Qed.

(* THE TEST IS THE RANGE.  Each of the four things `divOk' looks at is the    *)
(* rounded form of a step the error analysis needs to be normal, and a        *)
(* rounded value above a line has its exact value above it too.               *)
Lemma divOk_Rng xh xl yh yl :
  D2R yh <> 0 ->
  DdivDwDw2Fin xh xl yh yl ->
  divOk (DWFloat xh xl) (DWFloat yh yl) = true ->
  DdivDwDw2Rng xh xl yh yl.
Proof.
move=> Hy0 F.
have [Fxh [Fxl [Fyh [Fyl [Ft [Fch [Fcl1 [Fcl2 [G1 [Ftl2 [G2
     [Fpih [Fdl [Fd [Ftl G3]]]]]]]]]]]]]]] := F.
rewrite /divOk /DdivDwDw2Rng.
move=> /andb_prop [/andb_prop [/andb_prop [H1 H2] H3] H4].
have [Et _] := Dfin_div _ _ Fxh Hy0 Ft.
have [Ech _] := Dfin_mul _ _ Fyh Ft Fch.
have [Ecl2 _] := Dfin_mul _ _ Fyl Ft Fcl2.
have [Etl _] := Dfin_div _ _ Fd Hy0 Ftl.
split.
  apply: Dnorm_of_rnd; rewrite -Et.
  by have := Dltb_abs _ _ Dfin_dnorm Ft H1; rewrite D2R_dnorm.
split.
  apply: Dprodlo_of_rnd; rewrite -Ech.
  by have := Dltb_abs _ _ Dfin_dprodlo Fch H2; rewrite D2R_dprodlo.
split.
  case/Bool.orb_prop: H3 => H3.
    by rewrite (Deqb0 _ Fyl H3) Rmult_0_l !round_0.
  apply: Drnd_FLX; apply: Dnorm_of_rnd; rewrite -Ecl2.
  by have := Dltb_abs _ _ Dfin_dnorm Fcl2 H3; rewrite D2R_dnorm.
case/Bool.orb_prop: H4 => H4.
  by rewrite (Deqb0 _ Fd H4) /Rdiv Rmult_0_l !round_0.
apply: Drnd_FLX; apply: Dnorm_of_rnd; rewrite -Etl.
by have := Dltb_abs _ _ Dfin_dnorm Ftl H4; rewrite D2R_dnorm.
Qed.

Lemma Ddscale : D2R dscale = 16 * Du ^ 2.
Proof. by rewrite /D2R /dscale; compute; lra. Qed.

(* The step the operation takes is at least sixteen units in the last place   *)
(* of the low word, read off both words of the answer.                        *)
Lemma dstep_ge q : Dfin (dstep q) ->
  16 * Du ^ 2 * (Rabs (D2R (dwhi q)) + Rabs (D2R (dwlo q))) <= D2R (dstep q).
Proof.
case: q => zh zl; rewrite /dstep => Fs.
have Fm := Dfin_mulUpI _ _ Fs.
have [Fsc Fa] := Dfin_mulI _ _ Fm.
have Fp := Dfin_upI _ _ Fa.
have [Fah Fal] := Dfin_addI _ _ Fp.
have Ha := addUpFp_ge _ _ Fah Fal Fp Fa.
rewrite !D2R_abs in Ha.
have Hm := mulUpFp_ge _ _ Fsc Fa Fm Fs.
rewrite Ddscale in Hm.
have P2 := Dupos 2.
apply: Rle_trans Hm.
rewrite [dwhi _]/= [dwlo _]/=.
by apply: Rmult_le_compat_l; lra.
Qed.

(* A pair that passes `wellFormed' is a double word: its high word is the     *)
(* rounding of its value.                                                     *)
Lemma Dwf_eq xh xl : Dfin xh -> Dfin xl ->
  wellFormed (DWFloat xh xl) = true -> D2R xh = Drnd (D2R xh + D2R xl).
Proof.
move=> Fh Fl Ew.
have Fs := Dfin_wf _ _ Fh Ew.
have [Es _] := Dfin_add _ _ Fh Fl Fs.
by rewrite -Es (D2R_wf _ _ Fh Fl Ew).
Qed.

(* And its high word is nought only when its value is.                        *)
Lemma Dhi_nz yh yl : Dfin yh -> Dfin yl ->
  wellFormed (DWFloat yh yl) = true ->
  D2R yh + D2R yl <> 0 -> D2R yh <> 0.
Proof.
move=> Fh Fl Ew Hn Hh0; apply: Hn.
have E := Dwf_eq _ _ Fh Fl Ew.
have Ffl : generic_format radix2 Dfexp (D2R yl) by apply: Dformat.
rewrite Hh0 Rplus_0_l (round_generic _ _ _ _ Ffl) in E.
by rewrite Hh0 -E; lra.
Qed.

Theorem divDwUpK_ge xh xl yh yl :
  Dfin xh -> Dfin xl -> Dfin yh -> Dfin yl ->
  wellFormed (DWFloat xh xl) = true -> wellFormed (DWFloat yh yl) = true ->
  Dfin (dwlo (divDwUpK (DWFloat xh xl) (DWFloat yh yl))) ->
  (D2R xh + D2R xl) / (D2R yh + D2R yl) <=
  D2R (dwhi (divDwUpK (DWFloat xh xl) (DWFloat yh yl))) +
  D2R (dwlo (divDwUpK (DWFloat xh xl) (DWFloat yh yl))).
Proof.
move=> Fxh Fxl Fyh Fyl Wx Wy.
rewrite divDwUpKE.
case Hp : (posFp (magDnDw (DWFloat yh yl))); last by [].
have HY : D2R yh + D2R yl <> 0.
  have [Fm Hm] := posFpP _ Hp.
  have Hle := magDnDw_le _ Fm.
  by move=> H0; move: Hle Hm; rewrite [dwhi _]/= [dwlo _]/= H0 Rabs_R0; lra.
have Hy0 := Dhi_nz _ _ Fyh Fyl Wy HY.
case Hx0 : (xh =? 0)%float.
  move=> _.
  have Exh := Deqb0 _ Fxh Hx0.
  have E := Dwf_eq _ _ Fxh Fxl Wx.
  have Ffl : generic_format radix2 Dfexp (D2R xl) by apply: Dformat.
  rewrite Exh Rplus_0_l (round_generic _ _ _ _ Ffl) in E.
  rewrite Exh -E [dwhi _]/= [dwlo _]/= D2R_zero /Rdiv Rplus_0_l Rmult_0_l.
  by lra.
case Hok : (divOk (DWFloat xh xl) (DWFloat yh yl));
  last by apply: divDwUp_geP.
move=> Fz.
have [Fqh [Fql Fs]] := widenUp_finI _ _ Fz.
have Hstep := dstep_ge _ Fs.
have Hw := widenUp_ge _ _ Fz.
have Ffin := divDwDw2_finI _ _ _ _ Fyh Fyl Fql.
have Hrng := divOk_Rng _ _ _ _ Hy0 Ffin Hok.
have Ex := Dwf_eq _ _ Fxh Fxl Wx.
have Ey := Dwf_eq _ _ Fyh Fyl Wy.
have Hd := divDwDw2_step _ _ _ _ _ Ffin Hrng Ex Ey Hstep.
rewrite /shiftUp.
by move: Hd Hw; split_Rabs; lra.
Qed.

Theorem divDwDnK_le xh xl yh yl :
  Dfin xh -> Dfin xl -> Dfin yh -> Dfin yl ->
  wellFormed (DWFloat xh xl) = true -> wellFormed (DWFloat yh yl) = true ->
  Dfin (dwlo (divDwDnK (DWFloat xh xl) (DWFloat yh yl))) ->
  D2R (dwhi (divDwDnK (DWFloat xh xl) (DWFloat yh yl))) +
  D2R (dwlo (divDwDnK (DWFloat xh xl) (DWFloat yh yl))) <=
  (D2R xh + D2R xl) / (D2R yh + D2R yl).
Proof.
move=> Fxh Fxl Fyh Fyl Wx Wy.
rewrite divDwDnKE.
case Hp : (posFp (magDnDw (DWFloat yh yl))); last by [].
have HY : D2R yh + D2R yl <> 0.
  have [Fm Hm] := posFpP _ Hp.
  have Hle := magDnDw_le _ Fm.
  by move=> H0; move: Hle Hm; rewrite [dwhi _]/= [dwlo _]/= H0 Rabs_R0; lra.
have Hy0 := Dhi_nz _ _ Fyh Fyl Wy HY.
case Hx0 : (xh =? 0)%float.
  move=> _.
  have Exh := Deqb0 _ Fxh Hx0.
  have E := Dwf_eq _ _ Fxh Fxl Wx.
  have Ffl : generic_format radix2 Dfexp (D2R xl) by apply: Dformat.
  rewrite Exh Rplus_0_l (round_generic _ _ _ _ Ffl) in E.
  rewrite Exh -E [dwhi _]/= [dwlo _]/= D2R_zero /Rdiv Rplus_0_l Rmult_0_l.
  by lra.
case Hok : (divOk (DWFloat xh xl) (DWFloat yh yl));
  last by apply: divDwDn_leP.
move=> Fz.
have [Fqh [Fql Fs]] := widenDn_finI _ _ Fz.
have Hstep := dstep_ge _ Fs.
have Hw := widenDn_le _ _ Fz.
have Ffin := divDwDw2_finI _ _ _ _ Fyh Fyl Fql.
have Hrng := divOk_Rng _ _ _ _ Hy0 Ffin Hok.
have Ex := Dwf_eq _ _ Fxh Fxl Wx.
have Ey := Dwf_eq _ _ Fyh Fyl Wy.
have Hd := divDwDw2_step _ _ _ _ _ Ffin Hrng Ex Ey Hstep.
rewrite /shiftDn.
by move: Hd Hw; split_Rabs; lra.
Qed.


(* The divisor is away from zero, which is the one thing the operation tests  *)
(* for itself: no amount of an infinity travelling would establish it.        *)
Lemma divDwUpK_nz x y : Dfin (dwlo (divDwUpK x y)) ->
  D2R (dwhi y) + D2R (dwlo y) <> 0.
Proof.
rewrite divDwUpKE; case: x => xh xl.
case Hp : (posFp (magDnDw y)); last by [].
move=> _; have [Fm Hm] := posFpP _ Hp.
have Hle := magDnDw_le _ Fm.
by move=> H0; move: Hle Hm; rewrite H0 Rabs_R0; lra.
Qed.

Lemma divDwDnK_nz x y : Dfin (dwlo (divDwDnK x y)) ->
  D2R (dwhi y) + D2R (dwlo y) <> 0.
Proof.
rewrite divDwDnKE; case: x => xh xl.
case Hp : (posFp (magDnDw y)); last by [].
move=> _; have [Fm Hm] := posFpP _ Hp.
have Hle := magDnDw_le _ Fm.
by move=> H0; move: Hle Hm; rewrite H0 Rabs_R0; lra.
Qed.

(* The two bounds, said of a pair rather than of its two words.               *)
Theorem divDwUpK_geP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  wellFormed x = true -> wellFormed y = true ->
  Dfin (dwlo (divDwUpK x y)) ->
  (D2R (dwhi x) + D2R (dwlo x)) / (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (divDwUpK x y)) + D2R (dwlo (divDwUpK x y)).
Proof. by case: x => xh xl; case: y => yh yl; apply: divDwUpK_ge. Qed.

Theorem divDwDnK_leP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  wellFormed x = true -> wellFormed y = true ->
  Dfin (dwlo (divDwDnK x y)) ->
  D2R (dwhi (divDwDnK x y)) + D2R (dwlo (divDwDnK x y)) <=
  (D2R (dwhi x) + D2R (dwlo x)) / (D2R (dwhi y) + D2R (dwlo y)).
Proof. by case: x => xh xl; case: y => yh yl; apply: divDwDnK_le. Qed.

(* ---------------------------------------------------------------------------*)
(*  The quotient as a double word                                             *)
(* ---------------------------------------------------------------------------*)

(* Fast2Sum gives a double word as soon as its second argument is no larger   *)
(* than its first, and both formats agree on the sum of two numbers with      *)
(* nothing asked at all, so what holds in the one holds in the other.         *)
Lemma fastTwoSum_dw a b :
  Dfin a -> Dfin b -> DfastTwoSumFin a b ->
  Rabs (D2R b) <= Rabs (D2R a) ->
  D2R (dwhi (fastTwoSum a b)) =
  Drnd (D2R (dwhi (fastTwoSum a b)) + D2R (dwlo (fastTwoSum a b))).
Proof.
move=> Fa Fb G Hle.
have Hp1 : (1 < prec)%Z by [].
have Hsym : forall x, Xrnd (- x) = - Xrnd x.
  by move=> x; rewrite round_NE_opp.
have Hb3 : (Zaux.radix_val radix2 <= 3)%Z by [].
have Hc := F2Sum_correct_abs Hp1 Hsym Hb3 (Dformat_FLX a) (Dformat_FLX b) Hle.
have [_ HDW] := F2Sum_correct_DW Hp1 Hc.
have [Eh El] := fastTwoSum_FLX_fin _ _ Fa Fb G.
rewrite (Drnd_FLX_plus _ _ (Dformat _) (Dformat _)) Eh El.
exact: HDW.
Qed.

(* And so the quotient is a double word, once that test has passed.  The      *)
(* division itself has no use for this - its step is read off both words -    *)
(* but the square root adds the quotient to a guess, and a sum of two double  *)
(* words asks that its arguments be double words.                            *)
Lemma divDwDw2_dw x y :
  DdivDwDw2Fin (dwhi x) (dwlo x) (dwhi y) (dwlo y) ->
  divDwOk x y = true ->
  D2R (dwhi (divDwDw2 x y)) =
  Drnd (D2R (dwhi (divDwDw2 x y)) + D2R (dwlo (divDwDw2 x y))).
Proof.
case: x => xh xl; case: y => yh yl.
rewrite /DdivDwDw2Fin /divDwOk.
set t := (xh / yh)%float.
set ch := dwhi (twoProd yh t).
set cl1 := dwlo (twoProd yh t).
set cl2 := (yl * t)%float.
set v := fastTwoSum ch cl2.
set tl2 := (dwlo v + cl1)%float.
set rh := dwhi (fastTwoSum (dwhi v) tl2).
set rl := dwlo (fastTwoSum (dwhi v) tl2).
set d := ((xh - rh) + (xl - rl))%float.
set tl := (d / yh)%float.
have Ez : divDwDw2 (DWFloat xh xl) (DWFloat yh yl) = fastTwoSum t tl by [].
rewrite Ez.
move=> [_ [_ [_ [_ [Ft [_ [_ [_ [_ [_ [_ [_ [_ [_ [Ftl G3]]]]]]]]]]]]]]] Hle.
apply: fastTwoSum_dw => //.
have := Dleb _ _ (Dfin_abs _ Ftl) (Dfin_abs _ Ft) Hle.
by rewrite !D2R_abs.
Qed.
