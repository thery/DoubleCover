From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
(* dwtwosum is imported last on purpose: it and dw_updn both name the two     *)
(* words of a pair, and the proofs below need the name the exactness lemmas   *)
(* are stated with.                                                           *)
From dwarith Require Import dwarith dwbridge dw_updn dwprod dwtwosum.

(* Widening, and the one step that makes it safe.                             *)
(* An interval bound must fall on the right side of the exact value, and an   *)
(* operation only promises to be near it.  One step up from a rounded sum is  *)
(* above the exact sum, whichever way the rounding went, and one step down    *)
(* is below it.  That is what the two widening operations rest on.            *)

Open Scope R_scope.

(* One step up, read on the reals.                                            *)
Lemma Dnext_up x : Dfin x -> Dfin (next_up x) ->
  D2R (next_up x) = succ radix2 Dfexp (D2R x).
Proof.
rewrite /Dfin /D2R next_up_equiv => Fx Fs.
have := Bsucc_correct _ _ Hprec Hmax (Prim2B x) Fx.
case: Rlt_bool_spec => [Hlt [-> _]|Hle Hov]; first by [].
by move: Fs Hov; case: Bsucc.
Qed.

Lemma Dnext_down x : Dfin x -> Dfin (next_down x) ->
  D2R (next_down x) = pred radix2 Dfexp (D2R x).
Proof.
rewrite /Dfin /D2R next_down_equiv => Fx Fp.
have := Bpred_correct _ _ Hprec Hmax (Prim2B x) Fx.
case: Rlt_bool_spec => [Hlt [-> _]|Hle Hov]; first by [].
by move: Fp Hov; case: Bpred.
Qed.

(* A number is neither infinity, so a step never meets the one it is told     *)
(* to leave alone, and on numbers it is the plain step.                       *)
Lemma Dnot_ninf x : Dfin x -> (x =? neg_infinity)%float = false.
Proof.
rewrite /Dfin eqb_equiv.
by have -> : Prim2B neg_infinity = B754_infinity true by []; case: (Prim2B x).
Qed.

Lemma Dnot_pinf x : Dfin x -> (x =? infinity)%float = false.
Proof.
rewrite /Dfin eqb_equiv.
by have -> : Prim2B infinity = B754_infinity false by []; case: (Prim2B x).
Qed.

(* And the other way: a step that came back a number was given one.  This     *)
(* is what carries an infinity to the end of a computation - it is the        *)
(* only place where one could have been lost.                                 *)
Lemma Dfin_upFpI x : Dfin (upFp x) -> Dfin x.
Proof.
rewrite /upFp; case E: (_ =? _)%float => //.
rewrite /Dfin next_up_equiv; move: E; rewrite eqb_equiv.
have -> : Prim2B neg_infinity = B754_infinity true by [].
by case: (Prim2B x) => [s1|[]||s1 m1 e1 H1].
Qed.

Lemma Dfin_dnFpI x : Dfin (dnFp x) -> Dfin x.
Proof.
rewrite /dnFp; case E: (_ =? _)%float => //.
rewrite /Dfin next_down_equiv; move: E; rewrite eqb_equiv.
have -> : Prim2B infinity = B754_infinity false by [].
by case: (Prim2B x) => [s1|[]||s1 m1 e1 H1].
Qed.

Lemma Dfin_upI a b : Dfin (addUpFp a b) -> Dfin (a + b)%float.
Proof. exact: Dfin_upFpI. Qed.

Lemma Dfin_dnI a b : Dfin (addDnFp a b) -> Dfin (a + b)%float.
Proof. exact: Dfin_dnFpI. Qed.

Lemma Dfin_mulUpI a b : Dfin (mulUpFp a b) -> Dfin (a * b)%float.
Proof. exact: Dfin_upFpI. Qed.

Lemma Dfin_mulDnI a b : Dfin (mulDnFp a b) -> Dfin (a * b)%float.
Proof. exact: Dfin_dnFpI. Qed.

(* A rounded value stepped up is above the value it was rounded from,         *)
(* whichever way the rounding went, and stepped down is below it.             *)
Lemma upFp_ge r x : Dfin x -> D2R x = Drnd r -> Dfin (upFp x) ->
  r <= D2R (upFp x).
Proof.
move=> Fx Ex Fu.
have Hp0 : Prec_gt_0 prec by [].
move: Fu; rewrite /upFp (Dnot_ninf _ Fx) => Fu.
by rewrite Dnext_up // Ex DfexpE; apply: succ_round_ge_id.
Qed.

Lemma dnFp_le r x : Dfin x -> D2R x = Drnd r -> Dfin (dnFp x) ->
  D2R (dnFp x) <= r.
Proof.
move=> Fx Ex Fd.
have Hp0 : Prec_gt_0 prec by [].
move: Fd; rewrite /dnFp (Dnot_pinf _ Fx) => Fd.
by rewrite Dnext_down // Ex DfexpE; apply: pred_round_le_id.
Qed.

(* The four operations that follow: a sum and a product, each way.            *)
Lemma addUpFp_ge a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  Dfin (addUpFp a b) -> D2R a + D2R b <= D2R (addUpFp a b).
Proof.
move=> Fa Fb Fs Fu; rewrite /addUpFp; apply: (upFp_ge _ _ Fs _ Fu).
by have [-> _] := Dfin_add _ _ Fa Fb Fs.
Qed.

Lemma addDnFp_le a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  Dfin (addDnFp a b) -> D2R (addDnFp a b) <= D2R a + D2R b.
Proof.
move=> Fa Fb Fs Fd; rewrite /addDnFp; apply: (dnFp_le _ _ Fs _ Fd).
by have [-> _] := Dfin_add _ _ Fa Fb Fs.
Qed.

Lemma mulUpFp_ge a b : Dfin a -> Dfin b -> Dfin (a * b)%float ->
  Dfin (mulUpFp a b) -> D2R a * D2R b <= D2R (mulUpFp a b).
Proof.
move=> Fa Fb Fs Fu; rewrite /mulUpFp; apply: (upFp_ge _ _ Fs _ Fu).
by have [-> _] := Dfin_mul _ _ Fa Fb Fs.
Qed.

Lemma mulDnFp_le a b : Dfin a -> Dfin b -> Dfin (a * b)%float ->
  Dfin (mulDnFp a b) -> D2R (mulDnFp a b) <= D2R a * D2R b.
Proof.
move=> Fa Fb Fs Fd; rewrite /mulDnFp; apply: (dnFp_le _ _ Fs _ Fd).
by have [-> _] := Dfin_mul _ _ Fa Fb Fs.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The sum of two double words, bounded                                      *)
(* ---------------------------------------------------------------------------*)

Notation Dsh xh yh := (dwhi (twoSum xh yh)).
Notation Dsl xh yh := (dwlo (twoSum xh yh)).

Lemma addDwUpE xh xl yh yl :
  addDwUp (DWFloat xh xl) (DWFloat yh yl) =
  twoSum (dwhi (twoSum xh yh))
    (addUpFp (addUpFp (dwlo (twoSum xh yh)) (dwhi (twoSum xl yl)))
       (dwlo (twoSum xl yl))).
Proof. by []. Qed.

Lemma addDwDnE xh xl yh yl :
  addDwDn (DWFloat xh xl) (DWFloat yh yl) =
  twoSum (dwhi (twoSum xh yh))
    (addDnFp (addDnFp (dwlo (twoSum xh yh)) (dwhi (twoSum xl yl)))
       (dwlo (twoSum xl yl))).
Proof. by []. Qed.

(* The pair returned is at or above the exact sum.  Both twoSum are exact, so *)
(* the exact sum is the four numbers sh, sl, th and tl added up, and the only *)
(* step that can miss is the adding of the three small ones, which is done    *)
(* upwards.                                                                   *)
Theorem addDwUp_ge xh xl yh yl :
  Dfin xh -> Dfin xl -> Dfin yh -> Dfin yl ->
  DtwoSumFin xh yh -> DtwoSumFin xl yl ->
  Dfin (Dsl xh yh + Dsh xl yl)%float ->
  Dfin (addUpFp (Dsl xh yh) (Dsh xl yl)) ->
  Dfin (addUpFp (Dsl xh yh) (Dsh xl yl) + Dsl xl yl)%float ->
  Dfin (addUpFp (addUpFp (Dsl xh yh) (Dsh xl yl)) (Dsl xl yl)) ->
  DtwoSumFin (Dsh xh yh)
    (addUpFp (addUpFp (Dsl xh yh) (Dsh xl yl)) (Dsl xl yl)) ->
  D2R xh + D2R xl + (D2R yh + D2R yl) <=
  D2R (dwhi (addDwUp (DWFloat xh xl) (DWFloat yh yl))) +
  D2R (dwlo (addDwUp (DWFloat xh xl) (DWFloat yh yl))).
Proof.
move=> Fxh Fxl Fyh Fyl T1 T2 Fa1 Fu1 Fa2 Fu2 T3.
have [Fsh Fsl] := twoSum_fin _ _ T1.
have [Fth Ftl] := twoSum_fin _ _ T2.
have E1 := twoSum_exact_fin _ _ Fxh Fyh T1.
have E2 := twoSum_exact_fin _ _ Fxl Fyl T2.
have G1 := addUpFp_ge _ _ Fsl Fth Fa1 Fu1.
have G2 := addUpFp_ge _ _ Fu1 Ftl Fa2 Fu2.
have E3 := twoSum_exact_fin _ _ Fsh Fu2 T3.
by rewrite addDwUpE; lra.
Qed.

(* And downwards, the same three steps the other way.                         *)
Theorem addDwDn_le xh xl yh yl :
  Dfin xh -> Dfin xl -> Dfin yh -> Dfin yl ->
  DtwoSumFin xh yh -> DtwoSumFin xl yl ->
  Dfin (Dsl xh yh + Dsh xl yl)%float ->
  Dfin (addDnFp (Dsl xh yh) (Dsh xl yl)) ->
  Dfin (addDnFp (Dsl xh yh) (Dsh xl yl) + Dsl xl yl)%float ->
  Dfin (addDnFp (addDnFp (Dsl xh yh) (Dsh xl yl)) (Dsl xl yl)) ->
  DtwoSumFin (Dsh xh yh)
    (addDnFp (addDnFp (Dsl xh yh) (Dsh xl yl)) (Dsl xl yl)) ->
  D2R (dwhi (addDwDn (DWFloat xh xl) (DWFloat yh yl))) +
  D2R (dwlo (addDwDn (DWFloat xh xl) (DWFloat yh yl))) <=
  D2R xh + D2R xl + (D2R yh + D2R yl).
Proof.
move=> Fxh Fxl Fyh Fyl T1 T2 Fa1 Fu1 Fa2 Fu2 T3.
have [Fsh Fsl] := twoSum_fin _ _ T1.
have [Fth Ftl] := twoSum_fin _ _ T2.
have E1 := twoSum_exact_fin _ _ Fxh Fyh T1.
have E2 := twoSum_exact_fin _ _ Fxl Fyl T2.
have G1 := addDnFp_le _ _ Fsl Fth Fa1 Fu1.
have G2 := addDnFp_le _ _ Fu1 Ftl Fa2 Fu2.
have E3 := twoSum_exact_fin _ _ Fsh Fu2 T3.
by rewrite addDwDnE; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The bounds a caller can use                                               *)
(* ---------------------------------------------------------------------------*)

(* The same two bounds, asking for one thing instead of eleven: that the      *)
(* four words given are numbers, and that the answer is one.  Nothing that    *)
(* ran off the range can end in a number, since every step passes an          *)
(* infinity on, so the answer being a number proves the whole chain was.      *)
Theorem addDwUp_geP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  Dfin (dwlo (addDwUp x y)) ->
  D2R (dwhi x) + D2R (dwlo x) + (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (addDwUp x y)) + D2R (dwlo (addDwUp x y)).
Proof.
case: x => xh xl; case: y => yh yl /= Fxh Fxl Fyh Fyl Fz.
have T3 := twoSum_finI _ _ Fz.
have [Fsw _] := T3.
have [_ Fw] := Dfin_addI _ _ Fsw.
have Fa2 := Dfin_upI _ _ Fw.
have [Fv Ftl] := Dfin_addI _ _ Fa2.
have Fa1 := Dfin_upI _ _ Fv.
have [Fsl _] := Dfin_addI _ _ Fa1.
by apply: addDwUp_ge => //; apply: twoSum_finI.
Qed.

Theorem addDwDn_leP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  Dfin (dwlo (addDwDn x y)) ->
  D2R (dwhi (addDwDn x y)) + D2R (dwlo (addDwDn x y)) <=
  D2R (dwhi x) + D2R (dwlo x) + (D2R (dwhi y) + D2R (dwlo y)).
Proof.
case: x => xh xl; case: y => yh yl /= Fxh Fxl Fyh Fyl Fz.
have T3 := twoSum_finI _ _ Fz.
have [Fsw _] := T3.
have [_ Fw] := Dfin_addI _ _ Fsw.
have Fa2 := Dfin_dnI _ _ Fw.
have [Fv Ftl] := Dfin_addI _ _ Fa2.
have Fa1 := Dfin_dnI _ _ Fv.
have [Fsl _] := Dfin_addI _ _ Fa1.
by apply: addDwDn_le => //; apply: twoSum_finI.
Qed.

(* A difference is a sum with the second double word negated, and both        *)
(* its words are negated exactly.  So it is the sum's bound read through      *)
(* the two changes of sign.  Whether the negated pair is still a double       *)
(* word is never asked: only the values of its two words are used.            *)
Theorem subDwUp_geP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  Dfin (dwlo (subDwUp x y)) ->
  D2R (dwhi x) + D2R (dwlo x) - (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (subDwUp x y)) + D2R (dwlo (subDwUp x y)).
Proof.
case: y => yh yl Fxh Fxl Fyh Fyl Fz.
have := addDwUp_geP x (DWFloat (- yh) (- yl))%float
          Fxh Fxl (Dfin_opp _ Fyh) (Dfin_opp _ Fyl) Fz.
by rewrite /subDwUp /negDw /= !D2R_opp; lra.
Qed.

Theorem subDwDn_leP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  Dfin (dwlo (subDwDn x y)) ->
  D2R (dwhi (subDwDn x y)) + D2R (dwlo (subDwDn x y)) <=
  D2R (dwhi x) + D2R (dwlo x) - (D2R (dwhi y) + D2R (dwlo y)).
Proof.
case: y => yh yl Fxh Fxl Fyh Fyl Fz.
have := addDwDn_leP x (DWFloat (- yh) (- yl))%float
          Fxh Fxl (Dfin_opp _ Fyh) (Dfin_opp _ Fyl) Fz.
by rewrite /subDwDn /negDw /= !D2R_opp; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The product of two double words, bounded                                  *)
(* ---------------------------------------------------------------------------*)

(* The step that covers what the two-product may have missed.                 *)
Lemma Ddeps : D2R deps = 4 * bpow radix2 (SpecFloat.emin prec emax).
Proof. by rewrite /D2R /deps; compute; lra. Qed.

(* The product written out, with the words of the two-product named.          *)
Lemma mulDwUpE xh xl yh yl :
  mulDwUp (DWFloat xh xl) (DWFloat yh yl) =
  twoSum (dwhi (twoProd xh yh))
    (addUpFp (addUpFp (addUpFp (dwlo (twoProd xh yh)) (mulUpFp xh yl))
                      (addUpFp (mulUpFp xl yh) (mulUpFp xl yl)))
             deps).
Proof. by rewrite /mulDwUp; case: (twoProd xh yh). Qed.

Lemma mulDwDnE xh xl yh yl :
  mulDwDn (DWFloat xh xl) (DWFloat yh yl) =
  twoSum (dwhi (twoProd xh yh))
    (addDnFp (addDnFp (addDnFp (dwlo (twoProd xh yh)) (mulDnFp xh yl))
                      (addDnFp (mulDnFp xl yh) (mulDnFp xl yl)))
             (- deps)).
Proof. by rewrite /mulDwDn; case: (twoProd xh yh). Qed.

(* The pair returned is at or above the exact product.  The product of the    *)
(* two high words is two numbers that miss it by less than three and a        *)
(* half of the smallest number there is; the other three products are each    *)
(* rounded upwards; the four are added upwards, and so is the step that       *)
(* covers the miss.  The last twoSum changes no value.                        *)
Theorem mulDwUp_geP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  Dfin (dwlo (mulDwUp x y)) ->
  (D2R (dwhi x) + D2R (dwlo x)) * (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (mulDwUp x y)) + D2R (dwlo (mulDwUp x y)).
Proof.
case: x => xh xl; case: y => yh yl; rewrite mulDwUpE.
change (dwhi (DWFloat xh xl)) with xh; change (dwlo (DWFloat xh xl)) with xl.
change (dwhi (DWFloat yh yl)) with yh; change (dwlo (DWFloat yh yl)) with yl.
move=> Fxh Fxl Fyh Fyl Fz.
have T := twoSum_finI _ _ Fz.
have [Fsum _] := T.
have [Fch FW] := Dfin_addI _ _ Fsum.
have FVd := Dfin_upI _ _ FW.
have [FV Fd] := Dfin_addI _ _ FVd.
have FS12 := Dfin_upI _ _ FV.
have [FS1 FS2] := Dfin_addI _ _ FS12.
have FclM1 := Dfin_upI _ _ FS1.
have [Fcl FM1] := Dfin_addI _ _ FclM1.
have FM2M3 := Dfin_upI _ _ FS2.
have [FM2 FM3] := Dfin_addI _ _ FM2M3.
have Fp1 := Dfin_mulUpI _ _ FM1.
have Fp2 := Dfin_mulUpI _ _ FM2.
have Fp3 := Dfin_mulUpI _ _ FM3.
have Hp := twoProd_err _ _ Fcl.
have G1 := mulUpFp_ge _ _ Fxh Fyl Fp1 FM1.
have G2 := mulUpFp_ge _ _ Fxl Fyh Fp2 FM2.
have G3 := mulUpFp_ge _ _ Fxl Fyl Fp3 FM3.
have H1 := addUpFp_ge _ _ Fcl FM1 FclM1 FS1.
have H2 := addUpFp_ge _ _ FM2 FM3 FM2M3 FS2.
have H3 := addUpFp_ge _ _ FS1 FS2 FS12 FV.
have H4 := addUpFp_ge _ _ FV Fd FVd FW.
have E := twoSum_exact_fin _ _ Fch FW T.
have Hb : 0 < bpow radix2 (SpecFloat.emin prec emax) by apply: bpow_gt_0.
have Hx : (D2R xh + D2R xl) * (D2R yh + D2R yl) =
          D2R xh * D2R yh + D2R xh * D2R yl + D2R xl * D2R yh + D2R xl * D2R yl
  by ring.
move: Hp; rewrite Ddeps in H4; split_Rabs; lra.
Qed.

(* And downwards, the same pieces the other way.                              *)
Theorem mulDwDn_leP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  Dfin (dwlo (mulDwDn x y)) ->
  D2R (dwhi (mulDwDn x y)) + D2R (dwlo (mulDwDn x y)) <=
  (D2R (dwhi x) + D2R (dwlo x)) * (D2R (dwhi y) + D2R (dwlo y)).
Proof.
case: x => xh xl; case: y => yh yl; rewrite mulDwDnE.
change (dwhi (DWFloat xh xl)) with xh; change (dwlo (DWFloat xh xl)) with xl.
change (dwhi (DWFloat yh yl)) with yh; change (dwlo (DWFloat yh yl)) with yl.
move=> Fxh Fxl Fyh Fyl Fz.
have T := twoSum_finI _ _ Fz.
have [Fsum _] := T.
have [Fch FW] := Dfin_addI _ _ Fsum.
have FVd := Dfin_dnI _ _ FW.
have [FV Fd] := Dfin_addI _ _ FVd.
have FS12 := Dfin_dnI _ _ FV.
have [FS1 FS2] := Dfin_addI _ _ FS12.
have FclM1 := Dfin_dnI _ _ FS1.
have [Fcl FM1] := Dfin_addI _ _ FclM1.
have FM2M3 := Dfin_dnI _ _ FS2.
have [FM2 FM3] := Dfin_addI _ _ FM2M3.
have Fp1 := Dfin_mulDnI _ _ FM1.
have Fp2 := Dfin_mulDnI _ _ FM2.
have Fp3 := Dfin_mulDnI _ _ FM3.
have Hp := twoProd_err _ _ Fcl.
have G1 := mulDnFp_le _ _ Fxh Fyl Fp1 FM1.
have G2 := mulDnFp_le _ _ Fxl Fyh Fp2 FM2.
have G3 := mulDnFp_le _ _ Fxl Fyl Fp3 FM3.
have H1 := addDnFp_le _ _ Fcl FM1 FclM1 FS1.
have H2 := addDnFp_le _ _ FM2 FM3 FM2M3 FS2.
have H3 := addDnFp_le _ _ FS1 FS2 FS12 FV.
have H4 := addDnFp_le _ _ FV Fd FVd FW.
have E := twoSum_exact_fin _ _ Fch FW T.
have Hb : 0 < bpow radix2 (SpecFloat.emin prec emax) by apply: bpow_gt_0.
have Hx : (D2R xh + D2R xl) * (D2R yh + D2R yl) =
          D2R xh * D2R yh + D2R xh * D2R yl + D2R xl * D2R yh + D2R xl * D2R yl
  by ring.
move: Hp; rewrite D2R_opp Ddeps in H4; split_Rabs; lra.
Qed.
