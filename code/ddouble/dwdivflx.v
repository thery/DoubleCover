From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error Mult_error BinarySingleNaN PrimFloat.
From Flocq Require Import Pff.Pff2Flocq.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn dwtwosum dwprod dwflx.
From dwarith Require Import DWDivDW.

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

(* The smallest product the two-product does not miss: two to the minus nine  *)
(* hundred and sixty-nine.  Flocq's own theorem gives exactness above it and  *)
(* only the three-and-a-half smallest numbers below, and dwprod.v takes the   *)
(* second half of that; this is the first half.                               *)
Notation Dprodlo := (bpow radix2 (SpecFloat.emin prec emax + 2 * prec - 1)).

Theorem twoProd_exact a b : Dfin (dwlo (twoProd a b)) ->
  (Dprodlo <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) + D2R (dwlo (twoProd a b)) = D2R a * D2R b.
Proof.
rewrite dekkerE /= => Fe Hn.
have [Ft3 Ftatb] := Dfin_addI _ _ Fe.
have [Fta Ftb] := Dfin_mulI _ _ Ftatb.
have [Ft2 Ftahb] := Dfin_addI _ _ Ft3.
have [_ Fhb] := Dfin_mulI _ _ Ftahb.
have [Ft1 Fhatb] := Dfin_addI _ _ Ft2.
have [Fha _] := Dfin_mulI _ _ Fhatb.
have [Fnpi Fhahb] := Dfin_addI _ _ Ft1.
have Fpi := Dfin_oppI _ Fnpi.
have [Fa Fb] := Dfin_mulI _ _ Fpi.
have [_ [_ [Eha Eta]]] := splitCE _ Fta.
have [_ [_ [Ehb Etb]]] := splitCE _ Ftb.
rewrite (proj1 (Dfin_add _ _ Ft3 Ftatb Fe)).
rewrite (proj1 (Dfin_add _ _ Ft2 Ftahb Ft3)).
rewrite (proj1 (Dfin_add _ _ Ft1 Fhatb Ft2)).
rewrite (proj1 (Dfin_add _ _ Fnpi Fhahb Ft1)).
rewrite (proj1 (Dfin_mul _ _ Fta Ftb Ftatb)).
rewrite (proj1 (Dfin_mul _ _ Fta Fhb Ftahb)).
rewrite (proj1 (Dfin_mul _ _ Fha Ftb Fhatb)).
rewrite (proj1 (Dfin_mul _ _ Fha Fhb Fhahb)).
rewrite D2R_opp (proj1 (Dfin_mul _ _ Fa Fb Fpi)).
rewrite Eha Eta Ehb Etb.
have Hp0 : Prec_gt_0 prec by [].
have Hp4 : (4 <= prec)%Z by [].
have Hemin : (SpecFloat.emin prec emax < 0)%Z by [].
have Fa2 : generic_format radix2 (FLT_exp (SpecFloat.emin prec emax) prec)
             (D2R a) by rewrite -DfexpE; apply: Dformat.
have Fb2 : generic_format radix2 (FLT_exp (SpecFloat.emin prec emax) prec)
             (D2R b) by rewrite -DfexpE; apply: Dformat.
have Hbeta : (radix_val radix2 = 2%Z) \/ Z.Even prec by left.
have [H _] := Dekker radix2 (SpecFloat.emin prec emax) prec
   (fun n => negb (Z.even n)) Hp4 Hemin (D2R a) (D2R b) Fa2 Fb2 Hbeta.
rewrite -DfexpE -!DrndE in H.
by rewrite -H //; right.
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
