From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
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

(* Each bound asks for one thing: that the answer is a number.  Nothing       *)
(* that ran off the range can end in a number, since every step passes an     *)
(* infinity on, so the answer being a number proves the whole chain was -     *)
(* the four words given included.  That last part is worth having on its      *)
(* own, because an operation built on these needs it of their arguments.      *)
Lemma addDw_finI x y : Dfin (dwlo (addDwUp x y)) ->
  Dfin (dwhi x) /\ Dfin (dwlo x) /\ Dfin (dwhi y) /\ Dfin (dwlo y).
Proof.
case: x => xh xl; case: y => yh yl; rewrite addDwUpE => Fz.
have [Fsw _] := twoSum_finI _ _ Fz.
have [_ Fw] := Dfin_addI _ _ Fsw.
have [Fv Ftl] := Dfin_addI _ _ (Dfin_upI _ _ Fw).
have [Fsl _] := Dfin_addI _ _ (Dfin_upI _ _ Fv).
have [Fs1 _] := twoSum_finI _ _ Fsl.
have [Fs2 _] := twoSum_finI _ _ Ftl.
have [Fxh Fyh] := Dfin_addI _ _ Fs1.
by have [Fxl Fyl] := Dfin_addI _ _ Fs2.
Qed.

Lemma addDwDn_finI x y : Dfin (dwlo (addDwDn x y)) ->
  Dfin (dwhi x) /\ Dfin (dwlo x) /\ Dfin (dwhi y) /\ Dfin (dwlo y).
Proof.
case: x => xh xl; case: y => yh yl; rewrite addDwDnE => Fz.
have [Fsw _] := twoSum_finI _ _ Fz.
have [_ Fw] := Dfin_addI _ _ Fsw.
have [Fv Ftl] := Dfin_addI _ _ (Dfin_dnI _ _ Fw).
have [Fsl _] := Dfin_addI _ _ (Dfin_dnI _ _ Fv).
have [Fs1 _] := twoSum_finI _ _ Fsl.
have [Fs2 _] := twoSum_finI _ _ Ftl.
have [Fxh Fyh] := Dfin_addI _ _ Fs1.
by have [Fxl Fyl] := Dfin_addI _ _ Fs2.
Qed.

Theorem addDwUp_geP x y : Dfin (dwlo (addDwUp x y)) ->
  D2R (dwhi x) + D2R (dwlo x) + (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (addDwUp x y)) + D2R (dwlo (addDwUp x y)).
Proof.
move=> Fz; have [Fxh [Fxl [Fyh Fyl]]] := addDw_finI _ _ Fz.
move: Fxh Fxl Fyh Fyl Fz; case: x => xh xl; case: y => yh yl.
rewrite addDwUpE.
change (dwhi (DWFloat xh xl)) with xh; change (dwlo (DWFloat xh xl)) with xl.
change (dwhi (DWFloat yh yl)) with yh; change (dwlo (DWFloat yh yl)) with yl.
move=> Fxh Fxl Fyh Fyl Fz.
have T3 := twoSum_finI _ _ Fz.
have [Fsw _] := T3.
have [_ Fw] := Dfin_addI _ _ Fsw.
have Fa2 := Dfin_upI _ _ Fw.
have [Fv Ftl] := Dfin_addI _ _ Fa2.
have Fa1 := Dfin_upI _ _ Fv.
have [Fsl _] := Dfin_addI _ _ Fa1.
by apply: addDwUp_ge => //; apply: twoSum_finI.
Qed.

Theorem addDwDn_leP x y : Dfin (dwlo (addDwDn x y)) ->
  D2R (dwhi (addDwDn x y)) + D2R (dwlo (addDwDn x y)) <=
  D2R (dwhi x) + D2R (dwlo x) + (D2R (dwhi y) + D2R (dwlo y)).
Proof.
move=> Fz; have [Fxh [Fxl [Fyh Fyl]]] := addDwDn_finI _ _ Fz.
move: Fxh Fxl Fyh Fyl Fz; case: x => xh xl; case: y => yh yl.
rewrite addDwDnE.
change (dwhi (DWFloat xh xl)) with xh; change (dwlo (DWFloat xh xl)) with xl.
change (dwhi (DWFloat yh yl)) with yh; change (dwlo (DWFloat yh yl)) with yl.
move=> Fxh Fxl Fyh Fyl Fz.
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
Lemma subDwUp_finI x y : Dfin (dwlo (subDwUp x y)) ->
  Dfin (dwhi x) /\ Dfin (dwlo x) /\ Dfin (dwhi y) /\ Dfin (dwlo y).
Proof.
case: y => yh yl Fz.
have [Fxh [Fxl [Fnh Fnl]]] := addDw_finI _ _ Fz.
by split => //; split => //; split; apply: Dfin_oppI.
Qed.

Lemma subDwDn_finI x y : Dfin (dwlo (subDwDn x y)) ->
  Dfin (dwhi x) /\ Dfin (dwlo x) /\ Dfin (dwhi y) /\ Dfin (dwlo y).
Proof.
case: y => yh yl Fz.
have [Fxh [Fxl [Fnh Fnl]]] := addDwDn_finI _ _ Fz.
by split => //; split => //; split; apply: Dfin_oppI.
Qed.

Theorem subDwUp_geP x y : Dfin (dwlo (subDwUp x y)) ->
  D2R (dwhi x) + D2R (dwlo x) - (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (subDwUp x y)) + D2R (dwlo (subDwUp x y)).
Proof.
case: y => yh yl Fz.
have := addDwUp_geP x (DWFloat (- yh) (- yl))%float Fz.
by rewrite /subDwUp /negDw /= !D2R_opp; lra.
Qed.

Theorem subDwDn_leP x y : Dfin (dwlo (subDwDn x y)) ->
  D2R (dwhi (subDwDn x y)) + D2R (dwlo (subDwDn x y)) <=
  D2R (dwhi x) + D2R (dwlo x) - (D2R (dwhi y) + D2R (dwlo y)).
Proof.
case: y => yh yl Fz.
have := addDwDn_leP x (DWFloat (- yh) (- yl))%float Fz.
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

(* Here too the answer being a number proves the four words given were.       *)
Lemma mulDw_finI x y : Dfin (dwlo (mulDwUp x y)) ->
  Dfin (dwhi x) /\ Dfin (dwlo x) /\ Dfin (dwhi y) /\ Dfin (dwlo y).
Proof.
case: x => xh xl; case: y => yh yl; rewrite mulDwUpE => Fz.
have [Fsw _] := twoSum_finI _ _ Fz.
have [_ FW] := Dfin_addI _ _ Fsw.
have [FV _] := Dfin_addI _ _ (Dfin_upI _ _ FW).
have [FS1 FS2] := Dfin_addI _ _ (Dfin_upI _ _ FV).
have [_ FM1] := Dfin_addI _ _ (Dfin_upI _ _ FS1).
have [FM2 FM3] := Dfin_addI _ _ (Dfin_upI _ _ FS2).
have [Fxh Fyl] := Dfin_mulI _ _ (Dfin_mulUpI _ _ FM1).
have [Fxl Fyh] := Dfin_mulI _ _ (Dfin_mulUpI _ _ FM2).
by [].
Qed.

Lemma mulDwDn_finI x y : Dfin (dwlo (mulDwDn x y)) ->
  Dfin (dwhi x) /\ Dfin (dwlo x) /\ Dfin (dwhi y) /\ Dfin (dwlo y).
Proof.
case: x => xh xl; case: y => yh yl; rewrite mulDwDnE => Fz.
have [Fsw _] := twoSum_finI _ _ Fz.
have [_ FW] := Dfin_addI _ _ Fsw.
have [FV _] := Dfin_addI _ _ (Dfin_dnI _ _ FW).
have [FS1 FS2] := Dfin_addI _ _ (Dfin_dnI _ _ FV).
have [_ FM1] := Dfin_addI _ _ (Dfin_dnI _ _ FS1).
have [FM2 FM3] := Dfin_addI _ _ (Dfin_dnI _ _ FS2).
have [Fxh Fyl] := Dfin_mulI _ _ (Dfin_mulDnI _ _ FM1).
have [Fxl Fyh] := Dfin_mulI _ _ (Dfin_mulDnI _ _ FM2).
by [].
Qed.

(* The pair returned is at or above the exact product.  The product of the    *)
(* two high words is two numbers that miss it by less than three and a        *)
(* half of the smallest number there is; the other three products are each    *)
(* rounded upwards; the four are added upwards, and so is the step that       *)
(* covers the miss.  The last twoSum changes no value.                        *)
Theorem mulDwUp_geP x y : Dfin (dwlo (mulDwUp x y)) ->
  (D2R (dwhi x) + D2R (dwlo x)) * (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (mulDwUp x y)) + D2R (dwlo (mulDwUp x y)).
Proof.
move=> Fz0; have [Fxh [Fxl [Fyh Fyl]]] := mulDw_finI _ _ Fz0.
move: Fxh Fxl Fyh Fyl Fz0; case: x => xh xl; case: y => yh yl.
rewrite mulDwUpE.
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
Theorem mulDwDn_leP x y : Dfin (dwlo (mulDwDn x y)) ->
  D2R (dwhi (mulDwDn x y)) + D2R (dwlo (mulDwDn x y)) <=
  (D2R (dwhi x) + D2R (dwlo x)) * (D2R (dwhi y) + D2R (dwlo y)).
Proof.
move=> Fz0; have [Fxh [Fxl [Fyh Fyl]]] := mulDwDn_finI _ _ Fz0.
move: Fxh Fxl Fyh Fyl Fz0; case: x => xh xl; case: y => yh yl.
rewrite mulDwDnE.
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

(* ---------------------------------------------------------------------------*)
(*  The quotient of two double words, bounded                                 *)
(* ---------------------------------------------------------------------------*)

(* A quotient rounded and stepped up is above the exact quotient.             *)
Lemma divUpFp_ge a b : Dfin a -> D2R b <> 0 -> Dfin (a / b)%float ->
  Dfin (divUpFp a b) -> D2R a / D2R b <= D2R (divUpFp a b).
Proof.
move=> Fa Nb Fs Fu; rewrite /divUpFp; apply: (upFp_ge _ _ Fs _ Fu).
by have [-> _] := Dfin_div _ _ Fa Nb Fs.
Qed.

(* The divisor made smaller is at or below its magnitude: a sum is at         *)
(* least the first term less the second, in absolute value.                   *)
Lemma magDnDw_le y : Dfin (magDnDw y) ->
  D2R (magDnDw y) <= Rabs (D2R (dwhi y) + D2R (dwlo y)).
Proof.
case: y => yh yl /= Fm.
have Fw := Dfin_dnFpI _ Fm.
have [Fah Fal] := Dfin_subI _ _ Fw.
have Ew : D2R (abs yh - abs yl)%float
        = Drnd (Rabs (D2R yh) - Rabs (D2R yl)).
  by have [-> _] := Dfin_sub _ _ Fah Fal Fw; rewrite !D2R_abs.
have := dnFp_le _ _ Fw Ew Fm.
by move=> H; move: H; split_Rabs; lra.
Qed.

(* Widening moves the pair by at least the amount asked for.  The twoSum      *)
(* at the end is exact, so the two words still add up to what they did.       *)
Lemma widenUpE zh zl f : widenUp (DWFloat zh zl) f = twoSum zh (addUpFp zl f).
Proof. by []. Qed.

Lemma widenDnE zh zl f :
  widenDn (DWFloat zh zl) f = twoSum zh (addDnFp zl (- f)).
Proof. by []. Qed.

(* Widening too passes on what it was given.                                  *)
Lemma widenUp_finI d f : Dfin (dwlo (widenUp d f)) ->
  Dfin (dwhi d) /\ Dfin (dwlo d) /\ Dfin f.
Proof.
case: d => zh zl; rewrite widenUpE => Fz.
have [Fsw _] := twoSum_finI _ _ Fz.
have [Fzh FW] := Dfin_addI _ _ Fsw.
by have [Fzl Ff] := Dfin_addI _ _ (Dfin_upI _ _ FW).
Qed.

Lemma widenDn_finI d f : Dfin (dwlo (widenDn d f)) ->
  Dfin (dwhi d) /\ Dfin (dwlo d) /\ Dfin f.
Proof.
case: d => zh zl; rewrite widenDnE => Fz.
have [Fsw _] := twoSum_finI _ _ Fz.
have [Fzh FW] := Dfin_addI _ _ Fsw.
have [Fzl Ff] := Dfin_addI _ _ (Dfin_dnI _ _ FW).
by split => //; split => //; apply: Dfin_oppI.
Qed.

Lemma widenUp_ge d f : Dfin (dwlo (widenUp d f)) ->
  D2R (dwhi d) + D2R (dwlo d) + D2R f <=
  D2R (dwhi (widenUp d f)) + D2R (dwlo (widenUp d f)).
Proof.
case: d => zh zl; rewrite widenUpE.
change (dwhi (DWFloat zh zl)) with zh; change (dwlo (DWFloat zh zl)) with zl.
move=> Fz.
have T := twoSum_finI _ _ Fz.
have [Fsw _] := T.
have [Fzh FW] := Dfin_addI _ _ Fsw.
have Fa := Dfin_upI _ _ FW.
have [Fzl Ff] := Dfin_addI _ _ Fa.
have G := addUpFp_ge _ _ Fzl Ff Fa FW.
have E := twoSum_exact_fin _ _ Fzh FW T.
by lra.
Qed.

Lemma widenDn_le d f : Dfin (dwlo (widenDn d f)) ->
  D2R (dwhi (widenDn d f)) + D2R (dwlo (widenDn d f)) <=
  D2R (dwhi d) + D2R (dwlo d) - D2R f.
Proof.
case: d => zh zl; rewrite widenDnE.
change (dwhi (DWFloat zh zl)) with zh; change (dwlo (DWFloat zh zl)) with zl.
move=> Fz.
have T := twoSum_finI _ _ Fz.
have [Fsw _] := T.
have [Fzh FW] := Dfin_addI _ _ Fsw.
have Fa := Dfin_dnI _ _ FW.
have [Fzl Ff] := Dfin_addI _ _ Fa.
have G := addDnFp_le _ _ Fzl Ff Fa FW.
have E := twoSum_exact_fin _ _ Fzh FW T.
by move: G; rewrite D2R_opp; lra.
Qed.

(* Making a quotient of bounds smaller: a smaller numerator over a larger     *)
(* denominator, both kept positive where it matters.                          *)
(* The residual of x against two bounds of the same quantity, the two         *)
(* words of each added in absolute value.  It is at or above the distance     *)
(* from x to that quantity, whichever side the bounds fall.                   *)
Notation Dresid x z1 z2 :=
  (addUpFp (addUpFp (abs (dwhi (subDwUp x z1))) (abs (dwlo (subDwUp x z1))))
           (addUpFp (abs (dwhi (subDwDn x z2))) (abs (dwlo (subDwDn x z2))))).

(* That residual over a divisor made smaller: how far the quotient can be     *)
(* from q, and how far the root can be from q.                                *)
Notation Dquo x y q :=
  (divUpFp (Dresid x (mulDwDn q y) (mulDwUp q y)) (magDnDw y)).
Notation Droot x q :=
  (divUpFp (Dresid x (mulDwDn q q) (mulDwUp q q)) (valDnDw q)).

Lemma Rdiv_le_bound a b c d :
  a <= c -> 0 <= c -> 0 < d -> d <= b -> a / b <= c / d.
Proof.
move=> ac c0 d0 db.
have b0 : 0 < b by lra.
rewrite /Rdiv; apply: Rle_trans (_ : c * / b <= _).
  by apply: Rmult_le_compat_r => //; apply/Rlt_le/Rinv_0_lt_compat.
by apply: Rmult_le_compat_l => //; apply: Rinv_le_contravar.
Qed.

(* The residual argument itself, on the reals and nothing else.  Whatever     *)
(* q is, if the residual x - q*y is caught between two numbers, both no       *)
(* bigger than r, and the divisor's magnitude is at least m, then the true    *)
(* quotient is within r/m of q.                                               *)
Lemma resid_bound X Y Q MD MU RU RD Rr M E :
  MD <= Q * Y -> Q * Y <= MU ->
  X - MD <= RU -> RD <= X - MU ->
  RU <= Rr -> - RD <= Rr -> 0 <= Rr ->
  0 < M -> M <= Rabs Y -> Rr / M <= E ->
  X / Y <= Q + E.
Proof.
move=> H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
have [HYn|HYp] : Y < 0 \/ 0 < Y.
  by move: H9; rewrite /Rabs; case: Rcase_abs => H; [left|right]; lra.
- have HYne : Y <> 0 by lra.
  have HE : X / Y = Q + (- (X - Q * Y)) / (- Y) by field.
  have Hab : - (X - Q * Y) <= Rr by lra.
  have Hbd : M <= - Y by move: H9; rewrite /Rabs; case: Rcase_abs => H; lra.
  have := Rdiv_le_bound _ _ _ _ Hab H7 H8 Hbd.
  by rewrite HE; lra.
- have HYne : Y <> 0 by lra.
  have HE : X / Y = Q + (X - Q * Y) / Y by field.
  have Hab : X - Q * Y <= Rr by lra.
  have Hbd : M <= Y by move: H9; rewrite /Rabs; case: Rcase_abs => H; lra.
  have := Rdiv_le_bound _ _ _ _ Hab H7 H8 Hbd.
  by rewrite HE; lra.
Qed.

(* The quotient, bounded above.  Nothing is asked of the algorithm that       *)
(* produced q: the true quotient is within |x - q*y| / |y| of it whatever     *)
(* it is, and that distance is what the operation computes - the residual     *)
(* bounded on both sides, its words added in absolute value, over a           *)
(* divisor made smaller.                                                      *)
Theorem divDwUpQ_ge x y q :
  posFp (magDnDw y) = true ->
  Dfin (dwlo (widenUp q (Dquo x y q))) ->
  (D2R (dwhi x) + D2R (dwlo x)) / (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (widenUp q (Dquo x y q))) + D2R (dwlo (widenUp q (Dquo x y q))).
Proof.
move=> E.
have [E1 E2] : (0 <? magDnDw y)%float = true /\
               (magDnDw y <? infinity)%float = true.
  by move: E; rewrite /posFp; case: (0 <? _)%float; case: (_ <? _)%float.
have [Fm Pm] := Dpos _ E1 E2.
have Hm := magDnDw_le _ Fm.
set rup := subDwUp x (mulDwDn q y).
set rdn := subDwDn x (mulDwUp q y).
set r := addUpFp (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
                 (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))).
move=> Fz.
have Hw := widenUp_ge _ _ Fz.
have [_ [_ Fe]] := widenUp_finI _ _ Fz.
have Fd := Dfin_upFpI _ Fe.
have Fr := Dfin_divI _ _ Fd.
have [FA FB] := Dfin_addI _ _ (Dfin_upI _ _ Fr).
have [FA1 FA2] := Dfin_addI _ _ (Dfin_upI _ _ FA).
have [FB1 FB2] := Dfin_addI _ _ (Dfin_upI _ _ FB).
have Fuh := Dfin_absI _ FA1; have Ful := Dfin_absI _ FA2.
have Fdh := Dfin_absI _ FB1; have Fdl := Dfin_absI _ FB2.
have Hup := subDwUp_geP x (mulDwDn q y) Ful.
have Hdn := subDwDn_leP x (mulDwUp q y) Fdl.
have [_ [_ [_ Fmd]]] := subDwUp_finI _ _ Ful.
have [_ [_ [_ Fmu]]] := subDwDn_finI _ _ Fdl.
have Hmd := mulDwDn_leP q y Fmd.
have Hmu := mulDwUp_geP q y Fmu.
have Hnm : D2R (magDnDw y) <> 0 by lra.
have He := divUpFp_ge _ _ Fr Hnm Fd Fe.
have HA := addUpFp_ge _ _ FA1 FA2 (Dfin_upI _ _ FA) FA.
have HB := addUpFp_ge _ _ FB1 FB2 (Dfin_upI _ _ FB) FB.
have HR0 := addUpFp_ge _ _ FA FB (Dfin_upI _ _ Fr) Fr.
have HR : D2R (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
        + D2R (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))) <= D2R r := HR0.
rewrite !D2R_abs in HA HB.
have PA1 := Rabs_pos (D2R (dwhi rup)); have PA2 := Rabs_pos (D2R (dwlo rup)).
have PB1 := Rabs_pos (D2R (dwhi rdn)); have PB2 := Rabs_pos (D2R (dwlo rdn)).
have QA := Rle_abs (D2R (dwhi rup) + D2R (dwlo rup)).
have QC := Rle_abs (- (D2R (dwhi rdn) + D2R (dwlo rdn))).
have TA := Rabs_triang (D2R (dwhi rup)) (D2R (dwlo rup)).
have TB := Rabs_triang (D2R (dwhi rdn)) (D2R (dwlo rdn)).
rewrite Rabs_Ropp in QC.
have Hr0 : 0 <= D2R r by lra.
have HU : D2R (dwhi rup) + D2R (dwlo rup) <= D2R r by lra.
have HD : - (D2R (dwhi rdn) + D2R (dwlo rdn)) <= D2R r by lra.
apply: Rle_trans _ Hw.
by apply: (resid_bound _ _ _ _ _ _ _ _ _ _
             Hmd Hmu Hup Hdn HU HD Hr0 Pm Hm He).
Qed.

(* And the operation itself, which is that with q the seed the algorithm      *)
(* happens to use.                                                            *)
Theorem divDwUp_geP x y : Dfin (dwlo (divDwUp x y)) ->
  (D2R (dwhi x) + D2R (dwlo x)) / (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (divDwUp x y)) + D2R (dwlo (divDwUp x y)).
Proof.
rewrite /divDwUp /divDwErr; case E: (posFp (magDnDw y)); last by [].
exact: divDwUpQ_ge.
Qed.

(* The same, the other way round.                                             *)
Lemma resid_bound_lo X Y Q MD MU RU RD Rr M E :
  MD <= Q * Y -> Q * Y <= MU ->
  X - MD <= RU -> RD <= X - MU ->
  RU <= Rr -> - RD <= Rr -> 0 <= Rr ->
  0 < M -> M <= Rabs Y -> Rr / M <= E ->
  Q - E <= X / Y.
Proof.
move=> H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
have [HYn|HYp] : Y < 0 \/ 0 < Y.
  by move: H9; rewrite /Rabs; case: Rcase_abs => H; [left|right]; lra.
- have HYne : Y <> 0 by lra.
  have HE : X / Y = Q + (- (X - Q * Y)) / (- Y) by field.
  have HN : (X - Q * Y) / (- Y) = - ((- (X - Q * Y)) / (- Y)) by field.
  have Hab : X - Q * Y <= Rr by lra.
  have Hbd : M <= - Y by move: H9; rewrite /Rabs; case: Rcase_abs => H; lra.
  have H := Rdiv_le_bound _ _ _ _ Hab H7 H8 Hbd.
  by rewrite HN in H; rewrite HE; lra.
- have HYne : Y <> 0 by lra.
  have HE : X / Y = Q + (X - Q * Y) / Y by field.
  have HN : (- (X - Q * Y)) / Y = - ((X - Q * Y) / Y) by field.
  have Hab : - (X - Q * Y) <= Rr by lra.
  have Hbd : M <= Y by move: H9; rewrite /Rabs; case: Rcase_abs => H; lra.
  have H := Rdiv_le_bound _ _ _ _ Hab H7 H8 Hbd.
  by rewrite HN in H; rewrite HE; lra.
Qed.

(* The quotient, bounded below, from the same residual and the same           *)
(* divisor made smaller.                                                      *)
Theorem divDwDnQ_le x y q :
  posFp (magDnDw y) = true ->
  Dfin (dwlo (widenDn q (Dquo x y q))) ->
  D2R (dwhi (widenDn q (Dquo x y q))) + D2R (dwlo (widenDn q (Dquo x y q))) <=
  (D2R (dwhi x) + D2R (dwlo x)) / (D2R (dwhi y) + D2R (dwlo y)).
Proof.
move=> E.
have [E1 E2] : (0 <? magDnDw y)%float = true /\
               (magDnDw y <? infinity)%float = true.
  by move: E; rewrite /posFp; case: (0 <? _)%float; case: (_ <? _)%float.
have [Fm Pm] := Dpos _ E1 E2.
have Hm := magDnDw_le _ Fm.
set rup := subDwUp x (mulDwDn q y).
set rdn := subDwDn x (mulDwUp q y).
set r := addUpFp (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
                 (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))).
move=> Fz.
have Hw := widenDn_le _ _ Fz.
have [_ [_ Fe]] := widenDn_finI _ _ Fz.
have Fd := Dfin_upFpI _ Fe.
have Fr := Dfin_divI _ _ Fd.
have [FA FB] := Dfin_addI _ _ (Dfin_upI _ _ Fr).
have [FA1 FA2] := Dfin_addI _ _ (Dfin_upI _ _ FA).
have [FB1 FB2] := Dfin_addI _ _ (Dfin_upI _ _ FB).
have Fuh := Dfin_absI _ FA1; have Ful := Dfin_absI _ FA2.
have Fdh := Dfin_absI _ FB1; have Fdl := Dfin_absI _ FB2.
have Hup := subDwUp_geP x (mulDwDn q y) Ful.
have Hdn := subDwDn_leP x (mulDwUp q y) Fdl.
have [_ [_ [_ Fmd]]] := subDwUp_finI _ _ Ful.
have [_ [_ [_ Fmu]]] := subDwDn_finI _ _ Fdl.
have Hmd := mulDwDn_leP q y Fmd.
have Hmu := mulDwUp_geP q y Fmu.
have Hnm : D2R (magDnDw y) <> 0 by lra.
have He := divUpFp_ge _ _ Fr Hnm Fd Fe.
have HA := addUpFp_ge _ _ FA1 FA2 (Dfin_upI _ _ FA) FA.
have HB := addUpFp_ge _ _ FB1 FB2 (Dfin_upI _ _ FB) FB.
have HR0 := addUpFp_ge _ _ FA FB (Dfin_upI _ _ Fr) Fr.
have HR : D2R (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
        + D2R (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))) <= D2R r := HR0.
rewrite !D2R_abs in HA HB.
have PA1 := Rabs_pos (D2R (dwhi rup)); have PA2 := Rabs_pos (D2R (dwlo rup)).
have PB1 := Rabs_pos (D2R (dwhi rdn)); have PB2 := Rabs_pos (D2R (dwlo rdn)).
have QA := Rle_abs (D2R (dwhi rup) + D2R (dwlo rup)).
have QC := Rle_abs (- (D2R (dwhi rdn) + D2R (dwlo rdn))).
have TA := Rabs_triang (D2R (dwhi rup)) (D2R (dwlo rup)).
have TB := Rabs_triang (D2R (dwhi rdn)) (D2R (dwlo rdn)).
rewrite Rabs_Ropp in QC.
have Hr0 : 0 <= D2R r by lra.
have HU : D2R (dwhi rup) + D2R (dwlo rup) <= D2R r by lra.
have HD : - (D2R (dwhi rdn) + D2R (dwlo rdn)) <= D2R r by lra.
apply: Rle_trans Hw _.
by apply: (resid_bound_lo _ _ _ _ _ _ _ _ _ _
             Hmd Hmu Hup Hdn HU HD Hr0 Pm Hm He).
Qed.

Theorem divDwDn_leP x y : Dfin (dwlo (divDwDn x y)) ->
  D2R (dwhi (divDwDn x y)) + D2R (dwlo (divDwDn x y)) <=
  (D2R (dwhi x) + D2R (dwlo x)) / (D2R (dwhi y) + D2R (dwlo y)).
Proof.
rewrite /divDwDn /divDwErr; case E: (posFp (magDnDw y)); last by [].
exact: divDwDnQ_le.
Qed.

(* An answer that is a number also says the divisor was not zero: the         *)
(* operation only answers when it has bounded the divisor away from it.       *)
Lemma divDwUp_nz x y : Dfin (dwlo (divDwUp x y)) ->
  D2R (dwhi y) + D2R (dwlo y) <> 0.
Proof.
rewrite /divDwUp /divDwErr; case E: (posFp (magDnDw y)); last by [].
move=> _.
have [E1 E2] : (0 <? magDnDw y)%float = true /\
               (magDnDw y <? infinity)%float = true.
  by move: E; rewrite /posFp; case: (0 <? _)%float; case: (_ <? _)%float.
have [Fm Pm] := Dpos _ E1 E2.
by have := magDnDw_le _ Fm; split_Rabs; lra.
Qed.

Lemma divDwDn_nz x y : Dfin (dwlo (divDwDn x y)) ->
  D2R (dwhi y) + D2R (dwlo y) <> 0.
Proof.
rewrite /divDwDn /divDwErr; case E: (posFp (magDnDw y)); last by [].
move=> _.
have [E1 E2] : (0 <? magDnDw y)%float = true /\
               (magDnDw y <? infinity)%float = true.
  by move: E; rewrite /posFp; case: (0 <? _)%float; case: (_ <? _)%float.
have [Fm Pm] := Dpos _ E1 E2.
by have := magDnDw_le _ Fm; split_Rabs; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The square root of a double word, bounded                                 *)
(* ---------------------------------------------------------------------------*)

(* The two tests taken apart.                                                 *)
Lemma posFpP m : posFp m = true -> Dfin m /\ 0 < D2R m.
Proof.
rewrite /posFp => H.
have [E1 E2] : (0 <? m)%float = true /\ (m <? infinity)%float = true.
  by move: H; case: (0 <? m)%float; case: (m <? infinity)%float.
exact: Dpos.
Qed.

(* A rounded value above zero was above zero before it was rounded: the       *)
(* rounding of anything at or below zero is at or below zero.                 *)
Lemma Drnd_pos r : 0 < Drnd r -> 0 < r.
Proof.
move=> H; have Hp0 : Prec_gt_0 prec by [].
case: (Rle_lt_dec r 0) => // Hr.
have H0 : Drnd r <= Drnd 0 by apply: round_le.
by move: H0; rewrite round_0; lra.
Qed.

Lemma DposX xh xl : Dfin (xh + xl)%float -> 0 < D2R (xh + xl)%float ->
  0 < D2R xh + D2R xl.
Proof.
move=> Fs P.
have [Fh Fl] := Dfin_addI _ _ Fs.
have [E _] := Dfin_add _ _ Fh Fl Fs.
by apply: Drnd_pos; rewrite -E.
Qed.

(* The two words of a double word add up to at least the sum of them          *)
(* rounded down.                                                              *)
Lemma valDnDw_le d : Dfin (valDnDw d) ->
  D2R (valDnDw d) <= D2R (dwhi d) + D2R (dwlo d).
Proof.
case: d => h l /= F.
have Fs := Dfin_dnI _ _ F.
have [Fh Fl] := Dfin_addI _ _ Fs.
by apply: addDnFp_le.
Qed.

(* The residual argument for the root, on the reals and nothing else.  The    *)
(* root and q differ by the residual over their sum, and that sum is at       *)
(* least q, because a root is never negative.                                 *)
Lemma sqrt_resid_bound X Q MD MU RU RD Rr M E :
  MD <= Q * Q -> Q * Q <= MU ->
  X - MD <= RU -> RD <= X - MU ->
  RU <= Rr -> - RD <= Rr -> 0 <= Rr ->
  0 < M -> M <= Q -> Rr / M <= E -> 0 <= X ->
  R_sqrt.sqrt X <= Q + E /\ Q - E <= R_sqrt.sqrt X.
Proof.
move=> H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 HX.
have HS := sqrt_pos X.
have HSS : R_sqrt.sqrt X * R_sqrt.sqrt X = X by apply: sqrt_sqrt.
have HP : 0 < R_sqrt.sqrt X + Q by lra.
have HE : R_sqrt.sqrt X - Q = (X - Q * Q) / (R_sqrt.sqrt X + Q).
  apply: (Rmult_eq_reg_r (R_sqrt.sqrt X + Q)); last by lra.
  rewrite /Rdiv Rmult_assoc Rinv_l; last by lra.
  have -> : (R_sqrt.sqrt X - Q) * (R_sqrt.sqrt X + Q) =
            R_sqrt.sqrt X * R_sqrt.sqrt X - Q * Q by ring.
  by rewrite HSS Rmult_1_r.
have HA : X - Q * Q <= Rr by lra.
have HB : - (X - Q * Q) <= Rr by lra.
have HM : M <= R_sqrt.sqrt X + Q by lra.
have U1 := Rdiv_le_bound _ _ _ _ HA H7 H8 HM.
have U2 := Rdiv_le_bound _ _ _ _ HB H7 H8 HM.
have HN : (- (X - Q * Q)) / (R_sqrt.sqrt X + Q) =
          - ((X - Q * Q) / (R_sqrt.sqrt X + Q)) by field; lra.
rewrite HN -HE in U2; rewrite -HE in U1.
by split; lra.
Qed.

(* The root, bounded above and below.  The seed is a Newton step on the       *)
(* machine root, but nothing about it is used: the bound holds for any q      *)
(* above zero, and the number itself has to be above zero because the         *)
(* root of a negative is taken to be nought.                                  *)
Theorem sqrtDwUpQ_ge x q :
  posFp (valDnDw q) = true -> posFp (dwhi x + dwlo x)%float = true ->
  Dfin (dwlo (widenUp q (Droot x q))) ->
  R_sqrt.sqrt (D2R (dwhi x) + D2R (dwlo x)) <=
  D2R (dwhi (widenUp q (Droot x q))) + D2R (dwlo (widenUp q (Droot x q))).
Proof.
move=> Em Et.
set m := valDnDw q.
set rup := subDwUp x (mulDwDn q q).
set rdn := subDwDn x (mulDwUp q q).
set r := addUpFp (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
                 (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))).
move=> Fz.
have Hw := widenUp_ge _ _ Fz.
have [_ [_ Fe]] := widenUp_finI _ _ Fz.
have [Fm Pm] := posFpP _ Em.
have [Ft Pt] := posFpP _ Et.
have HX := DposX _ _ Ft Pt.
have Hq := valDnDw_le _ Fm.
have Fd := Dfin_upFpI _ Fe.
have Fr := Dfin_divI _ _ Fd.
have [FA FB] := Dfin_addI _ _ (Dfin_upI _ _ Fr).
have [FA1 FA2] := Dfin_addI _ _ (Dfin_upI _ _ FA).
have [FB1 FB2] := Dfin_addI _ _ (Dfin_upI _ _ FB).
have Fuh := Dfin_absI _ FA1; have Ful := Dfin_absI _ FA2.
have Fdh := Dfin_absI _ FB1; have Fdl := Dfin_absI _ FB2.
have Hup := subDwUp_geP x (mulDwDn q q) Ful.
have Hdn := subDwDn_leP x (mulDwUp q q) Fdl.
have [_ [_ [_ Fmd]]] := subDwUp_finI _ _ Ful.
have [_ [_ [_ Fmu]]] := subDwDn_finI _ _ Fdl.
have Hmd := mulDwDn_leP _ _ Fmd.
have Hmu := mulDwUp_geP _ _ Fmu.
have Hnm : D2R (valDnDw q) <> 0 by lra.
have He := divUpFp_ge _ _ Fr Hnm Fd Fe.
have HA := addUpFp_ge _ _ FA1 FA2 (Dfin_upI _ _ FA) FA.
have HB := addUpFp_ge _ _ FB1 FB2 (Dfin_upI _ _ FB) FB.
have HR0 := addUpFp_ge _ _ FA FB (Dfin_upI _ _ Fr) Fr.
have HR : D2R (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
        + D2R (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))) <= D2R r := HR0.
rewrite !D2R_abs in HA HB.
have PA1 := Rabs_pos (D2R (dwhi rup)); have PA2 := Rabs_pos (D2R (dwlo rup)).
have PB1 := Rabs_pos (D2R (dwhi rdn)); have PB2 := Rabs_pos (D2R (dwlo rdn)).
have QA := Rle_abs (D2R (dwhi rup) + D2R (dwlo rup)).
have QC := Rle_abs (- (D2R (dwhi rdn) + D2R (dwlo rdn))).
have TA := Rabs_triang (D2R (dwhi rup)) (D2R (dwlo rup)).
have TB := Rabs_triang (D2R (dwhi rdn)) (D2R (dwlo rdn)).
rewrite Rabs_Ropp in QC.
have Hr0 : 0 <= D2R r by lra.
have HU : D2R (dwhi rup) + D2R (dwlo rup) <= D2R r by lra.
have HD : - (D2R (dwhi rdn) + D2R (dwlo rdn)) <= D2R r by lra.
have [U _] := sqrt_resid_bound _ _ _ _ _ _ _ _ _
             Hmd Hmu Hup Hdn HU HD Hr0 Pm Hq He (Rlt_le _ _ HX).
by apply: Rle_trans _ Hw.
Qed.

(* And the operation, which is that with the Newton step for q.               *)
Theorem sqrtDwUp_geP x : Dfin (dwlo (sqrtDwUp x)) ->
  R_sqrt.sqrt (D2R (dwhi x) + D2R (dwlo x)) <=
  D2R (dwhi (sqrtDwUp x)) + D2R (dwlo (sqrtDwUp x)).
Proof.
case: x => xh xl; rewrite /sqrtDwUp /sqrtDwErr.
case Em: (posFp (valDnDw (sqrtDw (DWFloat xh xl)))); last by [].
case Et: (posFp (xh + xl)%float); last by [].
exact: sqrtDwUpQ_ge.
Qed.

Theorem sqrtDwDnQ_le x q :
  posFp (valDnDw q) = true -> posFp (dwhi x + dwlo x)%float = true ->
  Dfin (dwlo (widenDn q (Droot x q))) ->
  D2R (dwhi (widenDn q (Droot x q))) + D2R (dwlo (widenDn q (Droot x q))) <=
  R_sqrt.sqrt (D2R (dwhi x) + D2R (dwlo x)).
Proof.
move=> Em Et.
set m := valDnDw q.
set rup := subDwUp x (mulDwDn q q).
set rdn := subDwDn x (mulDwUp q q).
set r := addUpFp (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
                 (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))).
move=> Fz.
have Hw := widenDn_le _ _ Fz.
have [_ [_ Fe]] := widenDn_finI _ _ Fz.
have [Fm Pm] := posFpP _ Em.
have [Ft Pt] := posFpP _ Et.
have HX := DposX _ _ Ft Pt.
have Hq := valDnDw_le _ Fm.
have Fd := Dfin_upFpI _ Fe.
have Fr := Dfin_divI _ _ Fd.
have [FA FB] := Dfin_addI _ _ (Dfin_upI _ _ Fr).
have [FA1 FA2] := Dfin_addI _ _ (Dfin_upI _ _ FA).
have [FB1 FB2] := Dfin_addI _ _ (Dfin_upI _ _ FB).
have Fuh := Dfin_absI _ FA1; have Ful := Dfin_absI _ FA2.
have Fdh := Dfin_absI _ FB1; have Fdl := Dfin_absI _ FB2.
have Hup := subDwUp_geP x (mulDwDn q q) Ful.
have Hdn := subDwDn_leP x (mulDwUp q q) Fdl.
have [_ [_ [_ Fmd]]] := subDwUp_finI _ _ Ful.
have [_ [_ [_ Fmu]]] := subDwDn_finI _ _ Fdl.
have Hmd := mulDwDn_leP _ _ Fmd.
have Hmu := mulDwUp_geP _ _ Fmu.
have Hnm : D2R (valDnDw q) <> 0 by lra.
have He := divUpFp_ge _ _ Fr Hnm Fd Fe.
have HA := addUpFp_ge _ _ FA1 FA2 (Dfin_upI _ _ FA) FA.
have HB := addUpFp_ge _ _ FB1 FB2 (Dfin_upI _ _ FB) FB.
have HR0 := addUpFp_ge _ _ FA FB (Dfin_upI _ _ Fr) Fr.
have HR : D2R (addUpFp (abs (dwhi rup)) (abs (dwlo rup)))
        + D2R (addUpFp (abs (dwhi rdn)) (abs (dwlo rdn))) <= D2R r := HR0.
rewrite !D2R_abs in HA HB.
have PA1 := Rabs_pos (D2R (dwhi rup)); have PA2 := Rabs_pos (D2R (dwlo rup)).
have PB1 := Rabs_pos (D2R (dwhi rdn)); have PB2 := Rabs_pos (D2R (dwlo rdn)).
have QA := Rle_abs (D2R (dwhi rup) + D2R (dwlo rup)).
have QC := Rle_abs (- (D2R (dwhi rdn) + D2R (dwlo rdn))).
have TA := Rabs_triang (D2R (dwhi rup)) (D2R (dwlo rup)).
have TB := Rabs_triang (D2R (dwhi rdn)) (D2R (dwlo rdn)).
rewrite Rabs_Ropp in QC.
have Hr0 : 0 <= D2R r by lra.
have HU : D2R (dwhi rup) + D2R (dwlo rup) <= D2R r by lra.
have HD : - (D2R (dwhi rdn) + D2R (dwlo rdn)) <= D2R r by lra.
have [_ U] := sqrt_resid_bound _ _ _ _ _ _ _ _ _
             Hmd Hmu Hup Hdn HU HD Hr0 Pm Hq He (Rlt_le _ _ HX).
by apply: Rle_trans Hw _.
Qed.

(* And the operation, which is that with the Newton step for q.               *)
Theorem sqrtDwDn_leP x : Dfin (dwlo (sqrtDwDn x)) ->
  D2R (dwhi (sqrtDwDn x)) + D2R (dwlo (sqrtDwDn x)) <=
  R_sqrt.sqrt (D2R (dwhi x) + D2R (dwlo x)).
Proof.
case: x => xh xl; rewrite /sqrtDwDn /sqrtDwErr.
case Em: (posFp (valDnDw (sqrtDw (DWFloat xh xl)))); last by [].
case Et: (posFp (xh + xl)%float); last by [].
exact: sqrtDwDnQ_le.
Qed.
