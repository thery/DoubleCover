From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error BinarySingleNaN PrimFloat.
From Interval Require Import Primitive_ops.
From mathcomp Require Import ssreflect.
(* dwtwosum is imported last on purpose: it and dw_updn both name the two     *)
(* words of a pair, and the proofs below need the name the exactness lemmas   *)
(* are stated with.                                                           *)
From dwarith Require Import dwarith dwbridge dw_updn dwtwosum.

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

(* A sum rounded and then stepped up is above the exact sum.                  *)
Lemma addUpFp_ge a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  Dfin (addUpFp a b) -> D2R a + D2R b <= D2R (addUpFp a b).
Proof.
move=> Fa Fb Fs Fu.
have Hp0 : Prec_gt_0 prec by [].
rewrite /addUpFp Dnext_up //.
have [-> _] := Dfin_add _ _ Fa Fb Fs.
by rewrite DfexpE; apply: succ_round_ge_id.
Qed.

(* And stepped down is below it.                                              *)
Lemma addDnFp_le a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  Dfin (addDnFp a b) -> D2R (addDnFp a b) <= D2R a + D2R b.
Proof.
move=> Fa Fb Fs Fd.
have Hp0 : Prec_gt_0 prec by [].
rewrite /addDnFp Dnext_down //.
have [-> _] := Dfin_add _ _ Fa Fb Fs.
by rewrite DfexpE; apply: pred_round_le_id.
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
(*  The tests the program runs on itself                                      *)
(* ---------------------------------------------------------------------------*)

(* A float is finite exactly when it reads as a real number, so the test the  *)
(* program runs is the one the proofs below speak about.                      *)
Definition Dfinb f := PrimitiveFloat.real f.

Lemma DfinbW f : Dfinb f = true -> Dfin f.
Proof.
by rewrite /Dfinb -{1}(B2Prim_Prim2B f) PrimitiveFloat.real_is_finite.
Qed.

(* Seven tests are run at once, and taken apart one at a time.                *)
Lemma andb7E (a b c d e f g : bool) :
  (a && b && c && d && e && f && g)%bool = true ->
  a = true /\ b = true /\ c = true /\ d = true /\ e = true /\ f = true /\
  g = true.
Proof. by case: a; case: b; case: c; case: d; case: e; case: f; case: g. Qed.

(* Everything the upward sum needs to know about itself, in seven tests on    *)
(* numbers it has just computed.  Both TwoSum calls are covered by their low  *)
(* word alone, and so is the last one; the three left are the two additions   *)
(* of the small words and their stepping up.  Nothing here looks at the       *)
(* arguments: whether those are numbers is the caller's question.             *)
Definition addUpOk (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let sl := dwlo (twoSum xh yh) in
  let th := dwhi (twoSum xl yl) in
  let tl := dwlo (twoSum xl yl) in
  let v := addUpFp sl th in
  let w := addUpFp v tl in
  (Dfinb sl && Dfinb tl && Dfinb (sl + th)%float && Dfinb v &&
   Dfinb (v + tl)%float && Dfinb w &&
   Dfinb (dwlo (twoSum (dwhi (twoSum xh yh)) w)))%bool.

Definition addDnOk (x y : dwfloat) :=
  let: DWFloat xh xl := x in
  let: DWFloat yh yl := y in
  let sl := dwlo (twoSum xh yh) in
  let th := dwhi (twoSum xl yl) in
  let tl := dwlo (twoSum xl yl) in
  let v := addDnFp sl th in
  let w := addDnFp v tl in
  (Dfinb sl && Dfinb tl && Dfinb (sl + th)%float && Dfinb v &&
   Dfinb (v + tl)%float && Dfinb w &&
   Dfinb (dwlo (twoSum (dwhi (twoSum xh yh)) w)))%bool.

(* The two bounds again, with their seven finiteness hypotheses replaced      *)
(* by the one test.  What is left to ask is that the four words given are     *)
(* numbers, which is the caller's side of the bargain.                        *)
Theorem addDwUp_geP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  addUpOk x y = true ->
  D2R (dwhi x) + D2R (dwlo x) + (D2R (dwhi y) + D2R (dwlo y)) <=
  D2R (dwhi (addDwUp x y)) + D2R (dwlo (addDwUp x y)).
Proof.
case: x => xh xl; case: y => yh yl /= Fxh Fxl Fyh Fyl.
move=> /andb7E[Osl [Otl [Oa1 [Ov [Oa2 [Ow Oz]]]]]].
apply: addDwUp_ge => //.
- by apply: twoSum_finI; apply: DfinbW.
- by apply: twoSum_finI; apply: DfinbW.
- by apply: DfinbW.
- by apply: DfinbW.
- by apply: DfinbW.
- by apply: DfinbW.
by apply: twoSum_finI; apply: DfinbW.
Qed.

Theorem addDwDn_leP x y :
  Dfin (dwhi x) -> Dfin (dwlo x) -> Dfin (dwhi y) -> Dfin (dwlo y) ->
  addDnOk x y = true ->
  D2R (dwhi (addDwDn x y)) + D2R (dwlo (addDwDn x y)) <=
  D2R (dwhi x) + D2R (dwlo x) + (D2R (dwhi y) + D2R (dwlo y)).
Proof.
case: x => xh xl; case: y => yh yl /= Fxh Fxl Fyh Fyl.
move=> /andb7E[Osl [Otl [Oa1 [Ov [Oa2 [Ow Oz]]]]]].
apply: addDwDn_le => //.
- by apply: twoSum_finI; apply: DfinbW.
- by apply: twoSum_finI; apply: DfinbW.
- by apply: DfinbW.
- by apply: DfinbW.
- by apply: DfinbW.
- by apply: DfinbW.
by apply: twoSum_finI; apply: DfinbW.
Qed.
