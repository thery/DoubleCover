From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From twarith Require Import twarith tw_updn.
From dwarith Require Import dwbridge dwtwosum dwprod dwbound.

(* The bounds on the triple-word operations.                                  *)
(*                                                                            *)
(* THE SUM AND THE PRODUCT NEED NO THEOREM FROM THE PAPER, and it is worth    *)
(* saying why, because the paper is where everything else here comes from.    *)
(* The paper is proved for round to nearest throughout; these two operations  *)
(* round in a direction, so none of it applies to them.  It does not have to: *)
(* every step up to the last one changes no value at all - `Merge' and        *)
(* `sortMag' move the terms about, and `vecSum' and `vseb' are sweeps of      *)
(* `twoSum', which is exact - so the whole error is the cut down to three      *)
(* words, and the cut is made in the direction wanted.  That is the same      *)
(* argument `code/ddouble' makes for its own sum and product.                 *)
(*                                                                            *)
(* THE CHAIN IS CARRIED BY ONE TEST, as it is there: a sweep's output being   *)
(* made of numbers proves its input was, since every one of them is an        *)
(* argument of the two-sum that made the next.                                *)

Open Scope R_scope.

(* `simpl' must not take a two-sum apart into its six operations: after that  *)
(* nothing on the screen matches a lemma about `twoSum'.  The two sweeps are  *)
(* written with the two words named, so blocking these three is enough to     *)
(* keep every step of a sweep whole while the sweep itself unfolds.           *)
Arguments twoSum : simpl never.
Arguments dwhi : simpl never.
Arguments dwlo : simpl never.
Arguments twoProd : simpl never.
Arguments sortMag : simpl never.


(* What a list of floats stands for, and when it is made of numbers.          *)
Fixpoint sumL (l : seq PrimFloat.float) : R :=
  match l with [::] => 0 | x :: l' => D2R x + sumL l' end.

Fixpoint finL (l : seq PrimFloat.float) : Prop :=
  match l with [::] => True | x :: l' => Dfin x /\ finL l' end.

Lemma finL_cons x l : finL (x :: l) -> Dfin x /\ finL l.
Proof. by []. Qed.

(* ---------------------------------------------------------------------------*)
(*  Moving the terms about changes nothing                                    *)
(* ---------------------------------------------------------------------------*)

(* Merging two lists adds what they stand for.                                *)
Lemma Merge_sum l1 l2 : sumL (Merge l1 l2) = sumL l1 + sumL l2.
Proof.
elim: l1 l2 => [|a1 l1 IH1] l2 /=; first by rewrite Rplus_0_l; case: l2.
elim: l2 => [|a2 l2 IH2] /=; first by rewrite Rplus_0_r.
by case: (abs a2 <=? abs a1)%float; rewrite /= ?IH1 ?IH2 /=; lra.
Qed.

(* And so does putting one in order of size.                                  *)
Lemma insMag_sum x l : sumL (insMag x l) = D2R x + sumL l.
Proof.
by elim: l => [|a l IH] /=; [lra | case: (abs a <=? abs x)%float; rewrite /= ?IH; lra].
Qed.

Lemma sortMag_sum l : sumL (sortMag l) = sumL l.
Proof. by elim: l => [|x l IH] //=; rewrite /sortMag /= insMag_sum IH. Qed.

(* ---------------------------------------------------------------------------*)
(*  And neither does either sweep                                             *)
(* ---------------------------------------------------------------------------*)

(* The first sweep, from the end of the list to the front.  Each term it      *)
(* returns is the error of the two-sum that made the next, so the output      *)
(* being made of numbers proves the input was, and then every two-sum in it   *)
(* is exact.                                                                  *)
(* HOW THE SWEEPS ARE READ.  `simpl' takes a two-sum apart into its six       *)
(* operations, so after it nothing on the screen matches a lemma about        *)
(* `twoSum'.  Rather than fight that, the two words are handed over by a      *)
(* cast -- `dwlo (twoSum a b)' IS the expression `simpl' leaves, so the one   *)
(* is accepted for the other -- and the equation that comes back is unfolded  *)
(* the same way before it is used.                                            *)

(* ---------------------------------------------------------------------------*)
(*  The first sweep, from the end of the list to the front                    *)
(* ---------------------------------------------------------------------------*)

Lemma vecSumAux_sum l es s :
  vecSumAux l = (es, s) -> finL (s :: es) -> D2R s + sumL es = sumL l.
Proof.
elim: l es s => [|x l IH] es s /=.
  by case=> <- <- _ /=; rewrite D2R_zero; lra.
case: l IH => [|y l'] IH.
  by case=> <- <- _ /=; lra.
case E: (vecSumAux (y :: l')) => [es' s'] /=.
case=> <- <- [Fs [Fe Fes']].
have T := twoSum_finI _ _ Fe.
have [Fx Fs'] := Dfin_addI _ _ (proj1 T).
have Ex := twoSum_exact_fin _ _ Fx Fs' T.
have IHs := IH _ _ E (conj Fs' Fes').
by move: IHs Ex; rewrite /= => H1 H2; lra.
Qed.

Lemma vecSum_sum l : finL (vecSum l) -> sumL (vecSum l) = sumL l.
Proof.
rewrite /vecSum; case E: (vecSumAux l) => [es s] F.
by rewrite /= (vecSumAux_sum _ _ _ E F).
Qed.

(* ---------------------------------------------------------------------------*)
(*  The second sweep, front to back                                           *)
(* ---------------------------------------------------------------------------*)

(* A term that came out nought is dropped rather than kept, so the output can *)
(* be shorter than the input, and the test for nought is read as a statement  *)
(* about the real number it stands for.                                       *)
Lemma vsebAux_finI l eps : finL (vsebAux eps l) -> Dfin eps.
Proof.
elim: l eps => [|e l IH] eps /=; first by case.
case: l IH => [|e' l'] IH /=.
  move=> [_ [Fy1 _]].
  by have [F0 _] := Dfin_addI _ _ (proj1 (twoSum_finI _ _ Fy1)).
case Ez: (_ =? 0)%float => F.
  have [Fet _] := Dfin_eqb0 _ Ez.
  by have [F0 _] := Dfin_addI _ _ (proj1 (twoSum_finI _ _ Fet)).
have [_ Ft] := finL_cons _ _ F.
have Fet := IH _ Ft.
by have [F0 _] := Dfin_addI _ _ (proj1 (twoSum_finI _ _ Fet)).
Qed.

Lemma vsebAux_sum l eps :
  finL (vsebAux eps l) -> sumL (vsebAux eps l) = D2R eps + sumL l.
Proof.
elim: l eps => [|e l IH] eps /=; first by move=> _ /=; lra.
case: l IH => [|e' l'] IH /=.
  move=> [Fy0 [Fy1 _]].
  have T := twoSum_finI _ _ Fy1.
  have [Fe0 Fe] := Dfin_addI _ _ (proj1 T).
  have Ex := twoSum_exact_fin _ _ Fe0 Fe T.
  by move: Ex; rewrite /= => H; lra.
(* the term that came out nought and was dropped, and then the one kept *)
case Ez: (_ =? 0)%float => F.
  have [Fet Eet] := Dfin_eqb0 _ Ez.
  have T := twoSum_finI _ _ Fet.
  have [Fe0 Fe] := Dfin_addI _ _ (proj1 T).
  have Ex := twoSum_exact_fin _ _ Fe0 Fe T.
  by move: (IH (dwhi (twoSum eps e)) F) Ex Eet; rewrite /= => H1 H2 H3; lra.
have [Fr Ft] := finL_cons _ _ F.
have Fet := vsebAux_finI (e' :: l') (dwlo (twoSum eps e)) Ft.
have T := twoSum_finI _ _ Fet.
have [Fe0 Fe] := Dfin_addI _ _ (proj1 T).
have Ex := twoSum_exact_fin _ _ Fe0 Fe T.
by move: (IH (dwlo (twoSum eps e)) Ft) Ex; rewrite /= => H1 H2; lra.
Qed.

Lemma vseb_sum l : finL (vseb l) -> sumL (vseb l) = sumL l.
Proof.
case: l => [|e0 l'] //= F.
by rewrite (vsebAux_sum _ _ F).
Qed.

(* Reading a sorted or swept list back to the one it came from: each is a     *)
(* rearrangement or a sweep, so the answer being made of numbers proves the   *)
(* list was.                                                                  *)
Lemma insMag_finI x l : finL (insMag x l) -> Dfin x /\ finL l.
Proof.
elim: l => [|a l IH] /=; first by case=> Fx _.
case: (abs a <=? abs x)%float => /=; first by case=> Fx [Fa Fl].
by case=> Fa /IH [Fx Fl].
Qed.

Lemma sortMag_finI l : finL (sortMag l) -> finL l.
Proof.
elim: l => [|x l IH] //=.
by rewrite /sortMag /= => /insMag_finI [Fx /IH Fl].
Qed.

Lemma vecSumAux_finI l es s :
  vecSumAux l = (es, s) -> finL (s :: es) -> finL l.
Proof.
elim: l es s => [|x l IH] es s /=; first by case=> <- <- _.
case: l IH => [|y l'] IH.
  by case=> <- <- [Fs _]; split.
case E: (vecSumAux (y :: l')) => [es' s'] /=.
case=> <- <- [Fs [Fe Fes']].
have T := twoSum_finI _ _ Fe.
have [Fx Fs'] := Dfin_addI _ _ (proj1 T).
by split => //; apply: (IH _ _ E (conj Fs' Fes')).
Qed.

Lemma vecSum_finI l : finL (vecSum l) -> finL l.
Proof.
rewrite /vecSum; case E: (vecSumAux l) => [es s] F.
by apply: (vecSumAux_finI _ _ _ E F).
Qed.

(* ---------------------------------------------------------------------------*)
(*  The cut down to three words, which is the only step that loses anything    *)
(* ---------------------------------------------------------------------------*)

(* What a triple word stands for.                                             *)
Definition twval t := D2R (tw0 t) + D2R (tw1 t) + D2R (tw2 t).
Arguments twval : simpl never.

Lemma twvalE a b c : twval (TWFloat a b c) = D2R a + D2R b + D2R c.
Proof. by []. Qed.

(* The tail is folded into the third word, upwards, so what comes out is at   *)
(* or above what went in.                                                     *)
Lemma foldUp_finI tl e : Dfin (foldr addUpFp e tl) -> Dfin e /\ finL tl.
Proof.
elim: tl => [|a tl IH] //= F.
have [Fa Fr] := Dfin_addI _ _ (Dfin_upI _ _ F).
by have [Fe Ftl] := IH Fr.
Qed.

Lemma foldUp_ge tl e :
  Dfin (foldr addUpFp e tl) -> D2R e + sumL tl <= D2R (foldr addUpFp e tl).
Proof.
elim: tl => [|a tl IH] /=; first by rewrite Rplus_0_r; lra.
move=> F.
have Fs := Dfin_upI _ _ F.
have [Fa Fr] := Dfin_addI _ _ Fs.
have G := addUpFp_ge _ _ Fa Fr Fs F.
by have := IH Fr; lra.
Qed.

(* The second sweep's output being made of numbers proves its input was.      *)
Lemma vsebAux_finIl l eps : finL (vsebAux eps l) -> Dfin eps /\ finL l.
Proof.
elim: l eps => [|e l IH] eps /=; first by case=> Fe _; split.
case: l IH => [|e' l'] IH /=.
  move=> [Fy0 [Fy1 _]].
  have T := twoSum_finI _ _ Fy1.
  by have [F0 F1] := Dfin_addI _ _ (proj1 T).
case Ez: (_ =? 0)%float => F.
  have [Fet _] := Dfin_eqb0 _ Ez.
  have T := twoSum_finI _ _ Fet.
  have [F0 F1] := Dfin_addI _ _ (proj1 T).
  by have [_ Ftl] := IH (dwhi (twoSum eps e)) F; split.
have [Fr Ft] := finL_cons _ _ F.
have [Fet Ftl] := IH (dwlo (twoSum eps e)) Ft.
have T := twoSum_finI _ _ Fet.
by have [F0 F1] := Dfin_addI _ _ (proj1 T); split.
Qed.

Lemma vseb_finI l : finL (vseb l) -> finL l.
Proof.
case: l => [|e0 l'] //= F.
by have [Fe0 Fl] := vsebAux_finIl _ _ F; split.
Qed.

(* A list of three or fewer words read back as a triple word keeps its value  *)
(* and its numbers: what is missing is filled out with noughts.               *)
Lemma l2tw_val m : (size m <= 3)%N -> twval (l2tw m) = sumL m.
Proof.
case: m => [|a [|b [|c [|d m]]]] //= _;
  by rewrite /twval /= ?D2R_zero; lra.
Qed.

Lemma l2tw_finI m : (size m <= 3)%N -> finL (tw2l (l2tw m)) -> finL m.
Proof.
by case: m => [|a [|b [|c [|d m]]]] //= _ [Fa [Fb [Fc _]]]; split => //; split.
Qed.

(* And the second sweep never lengthens a list of three.                      *)
Lemma vseb3_size a b c : (size (vseb [:: a; b; c]) <= 3)%N.
Proof.
rewrite /vseb /=; case: (_ =? 0)%float => /=; last by [].
by case: (_ =? 0)%float.
Qed.

(* A triple word read as a list stands for what the triple does.              *)
Lemma finL_tw2l t :
  Dfin (tw0 t) -> Dfin (tw1 t) -> Dfin (tw2 t) -> finL (tw2l t).
Proof. by case: t => a b c /= F0 F1 F2; split; [|split; [|split]]. Qed.

(* And its three words are numbers when it is read as one.                    *)
Lemma tw2l_finLI t :
  finL (tw2l t) -> Dfin (tw0 t) /\ Dfin (tw1 t) /\ Dfin (tw2 t).
Proof. by case: t => a b c [F0 [F1 [F2 _]]]. Qed.

Lemma tw2l_sum t : sumL (tw2l t) = twval t.
Proof. by case: t => x0 x1 x2; rewrite /twval /=; lra. Qed.

(* The cut's answer being made of numbers proves the swept list was, and so   *)
(* the list it swept.                                                         *)
Lemma expUp_finI l :
  finL (tw2l (expUp l)) -> finL (vseb l) /\ finL l.
Proof.
rewrite /expUp.
have K m : (size m <= 3)%N -> finL (tw2l (l2tw m)) -> finL m
  by move=> Hs Hf; apply: l2tw_finI Hf.
case E: (vseb l) => [|e0 [|e1 [|e2 tl]]] F.
- by split=> //; apply: vseb_finI; rewrite E.
- have Fm := K _ (isT : (size [:: e0] <= 3)%N) F.
  by split=> //; apply: vseb_finI; rewrite E.
- have Fm := K _ (isT : (size [:: e0; e1] <= 3)%N) F.
  by split=> //; apply: vseb_finI; rewrite E.
have Fm := K _ (vseb3_size _ _ _) F.
have [Fe0 [Fe1 [Ff _]]] := vseb_finI _ Fm.
have [Fe2 Ftl] := foldUp_finI _ _ Ff.
have Fw : finL [:: e0, e1, e2 & tl] by split => //; split => //; split.
by split=> //; apply: vseb_finI; rewrite E.
Qed.

(* AND THE CUT IS THE WHOLE ERROR.  What the second sweep leaves is either    *)
(* three words or fewer, and then nothing is lost at all, or more, and then   *)
(* the tail is folded into the third word upwards.                            *)
Lemma expUp_ge l : finL (tw2l (expUp l)) -> sumL l <= twval (expUp l).
Proof.
move=> F; have [Fv Fl] := expUp_finI _ F.
have Hl := vseb_sum _ Fv.
move: F Fv Hl; rewrite /expUp.
case E: (vseb l) => [|e0 [|e1 [|e2 tl]]] F Fv Hl.
- by rewrite (l2tw_val [::] isT); move: Hl; rewrite /=; lra.
- by rewrite (l2tw_val [:: e0] isT); move: Hl; rewrite /=; lra.
- by rewrite (l2tw_val [:: e0; e1] isT); move: Hl; rewrite /=; lra.
have Fm := l2tw_finI _ (vseb3_size _ _ _) F.
have [Fe0 [Fe1 [Ff _]]] := vseb_finI _ Fm.
have Hf := foldUp_ge _ _ Ff.
have Hs := vseb_sum _ Fm.
rewrite (l2tw_val _ (vseb3_size _ _ _)) Hs.
by move: Hl Hf; rewrite /= => H1 H2; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  And the same the other way round                                          *)
(* ---------------------------------------------------------------------------*)

Lemma foldDn_finI tl e : Dfin (foldr addDnFp e tl) -> Dfin e /\ finL tl.
Proof.
elim: tl => [|a tl IH] //= F.
have [Fa Fr] := Dfin_addI _ _ (Dfin_dnI _ _ F).
by have [Fe Ftl] := IH Fr.
Qed.

Lemma foldDn_le tl e :
  Dfin (foldr addDnFp e tl) -> D2R (foldr addDnFp e tl) <= D2R e + sumL tl.
Proof.
elim: tl => [|a tl IH] /=; first by rewrite Rplus_0_r; lra.
move=> F.
have Fs := Dfin_dnI _ _ F.
have [Fa Fr] := Dfin_addI _ _ Fs.
have G := addDnFp_le _ _ Fa Fr Fs F.
by have := IH Fr; lra.
Qed.

Lemma expDn_finI l :
  finL (tw2l (expDn l)) -> finL (vseb l) /\ finL l.
Proof.
rewrite /expDn.
have K m : (size m <= 3)%N -> finL (tw2l (l2tw m)) -> finL m
  by move=> Hs Hf; apply: l2tw_finI Hf.
case E: (vseb l) => [|e0 [|e1 [|e2 tl]]] F.
- by split=> //; apply: vseb_finI; rewrite E.
- have Fm := K _ (isT : (size [:: e0] <= 3)%N) F.
  by split=> //; apply: vseb_finI; rewrite E.
- have Fm := K _ (isT : (size [:: e0; e1] <= 3)%N) F.
  by split=> //; apply: vseb_finI; rewrite E.
have Fm := K _ (vseb3_size _ _ _) F.
have [Fe0 [Fe1 [Ff _]]] := vseb_finI _ Fm.
have [Fe2 Ftl] := foldDn_finI _ _ Ff.
have Fw : finL [:: e0, e1, e2 & tl] by split => //; split => //; split.
by split=> //; apply: vseb_finI; rewrite E.
Qed.

Lemma expDn_le l : finL (tw2l (expDn l)) -> twval (expDn l) <= sumL l.
Proof.
move=> F; have [Fv Fl] := expDn_finI _ F.
have Hl := vseb_sum _ Fv.
move: F Fv Hl; rewrite /expDn.
case E: (vseb l) => [|e0 [|e1 [|e2 tl]]] F Fv Hl.
- by rewrite (l2tw_val [::] isT); move: Hl; rewrite /=; lra.
- by rewrite (l2tw_val [:: e0] isT); move: Hl; rewrite /=; lra.
- by rewrite (l2tw_val [:: e0; e1] isT); move: Hl; rewrite /=; lra.
have Fm := l2tw_finI _ (vseb3_size _ _ _) F.
have [Fe0 [Fe1 [Ff _]]] := vseb_finI _ Fm.
have Hf := foldDn_le _ _ Ff.
have Hs := vseb_sum _ Fm.
rewrite (l2tw_val _ (vseb3_size _ _ _)) Hs.
by move: Hl Hf; rewrite /= => H1 H2; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  What the two guards on the quotient and the root are worth                *)
(* ---------------------------------------------------------------------------*)

(* A difference rounded down is at or below the difference.                   *)
Lemma subDnFp_le a b : Dfin a -> Dfin b -> Dfin (a - b)%float ->
  Dfin (subDnFp a b) -> D2R (subDnFp a b) <= D2R a - D2R b.
Proof.
move=> Fa Fb Fs Fd; rewrite /subDnFp; apply: (dnFp_le _ _ Fs _ Fd).
by have [-> _] := Dfin_sub _ _ Fa Fb Fs.
Qed.

(* And a difference rounded up is at or above it.                             *)
Lemma subUpFp_ge a b : Dfin a -> Dfin b -> Dfin (a - b)%float ->
  Dfin (subUpFp a b) -> D2R a - D2R b <= D2R (subUpFp a b).
Proof.
move=> Fa Fb Fs Fu; rewrite /subUpFp; apply: (upFp_ge _ _ Fs _ Fu).
by have [-> _] := Dfin_sub _ _ Fa Fb Fs.
Qed.

(* The divisor made smaller is at or below its magnitude: a sum is at least   *)
(* the first term less the other two, in absolute value, and the two steps    *)
(* down keep that true.                                                       *)
Lemma magDnTw_le y : Dfin (magDnTw y) -> D2R (magDnTw y) <= Rabs (twval y).
Proof.
case: y => y0 y1 y2 /= Fm.
have Fw2 := Dfin_dnFpI _ Fm.
have [Fs1 Fa2] := Dfin_subI _ _ Fw2.
have Fw1 := Dfin_dnFpI _ Fs1.
have [Fa0 Fa1] := Dfin_subI _ _ Fw1.
have H2 := subDnFp_le _ _ Fs1 Fa2 Fw2 Fm.
have H1 := subDnFp_le _ _ Fa0 Fa1 Fw1 Fs1.
rewrite !D2R_abs in H1 H2.
by move: H1 H2; rewrite /twval /=; split_Rabs; lra.
Qed.

(* The three words added downwards are at or below what they add to.          *)
Lemma valDnTw_le q : Dfin (valDnTw q) -> D2R (valDnTw q) <= twval q.
Proof.
case: q => q0 q1 q2 /= F.
have Fs2 := Dfin_dnI _ _ F.
have [Fv Fq2] := Dfin_addI _ _ Fs2.
have Fs1 := Dfin_dnI _ _ Fv.
have [Fq0 Fq1] := Dfin_addI _ _ Fs1.
have H2 := addDnFp_le _ _ Fv Fq2 Fs2 F.
have H1 := addDnFp_le _ _ Fq0 Fq1 Fs1 Fv.
by move: H1 H2; rewrite /twval /=; lra.
Qed.

(* WHAT FOLLOWS THE LEADING WORD IS AT MOST THREE QUARTERS OF IT.  The second *)
(* word is within half a step of the first, and half a step of a number is at *)
(* most half the number; the third is within half a step of the second, so at *)
(* most a quarter of the first.  `wellFormed_lead' in `tw_ops.v' throws the   *)
(* quarter away and keeps one; the guards below need the three quarters,      *)
(* because what they have to rule out is the value being nought.              *)
Lemma wellFormed_lead34 t : finL (tw2l t) -> wellFormed t = true ->
  (Rabs (D2R (tw1 t) + D2R (tw2 t)) <= 3 / 4 * Rabs (D2R (tw0 t)))%R.
Proof.
case: t => x0 x1 x2 [F0 [F1 [F2 _]]] /=.
rewrite /wellFormed => /andb_prop [E1 E2].
have H1 := wellFormed_half x0 x1 F0 F1 E1.
have H2 := wellFormed_half x1 x2 F1 F2 E2.
have T := Rabs_triang (D2R x1) (D2R x2).
by move: H1 H2 T; split_Rabs; lra.
Qed.

(* So a triple word whose leading word is above nought is above nought, and   *)
(* the leading word is what the guard on the root ends up testing: the second *)
(* word is dropped by the first addition, being a triple word, and the third  *)
(* is too small to change the sign of the first.                              *)
Lemma wellFormed_posV t : finL (tw2l t) -> wellFormed t = true ->
  (0 < D2R (tw0 t))%R -> (0 < twval t)%R.
Proof.
move=> Fl Ew H0; have Hq := wellFormed_lead34 _ Fl Ew.
by move: Hq H0; rewrite /twval; split_Rabs; lra.
Qed.

(* And the third word alone is at most a quarter of the leading one.          *)
Lemma wellFormed_quarter t : finL (tw2l t) -> wellFormed t = true ->
  (Rabs (D2R (tw2 t)) <= / 4 * Rabs (D2R (tw0 t)))%R.
Proof.
case: t => x0 x1 x2 [F0 [F1 [F2 _]]] /=.
rewrite /wellFormed => /andb_prop [E1 E2].
have H1 := wellFormed_half x0 x1 F0 F1 E1.
have H2 := wellFormed_half x1 x2 F1 F2 E2.
by move: H1 H2; split_Rabs; lra.
Qed.

Lemma wellFormed_pos02 t : finL (tw2l t) -> wellFormed t = true ->
  (0 < D2R (tw0 t) + D2R (tw2 t))%R -> (0 < D2R (tw0 t))%R.
Proof.
move=> Fl Ew H; have Hq := wellFormed_quarter _ Fl Ew.
by move: Hq H; split_Rabs; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Widening a triple word by a step                                          *)
(* ---------------------------------------------------------------------------*)

(* The step goes into the last word and the sweep puts the three back in      *)
(* order.  Neither the sweep nor the cut loses anything in the wrong          *)
(* direction, and the one addition is made in the direction wanted, so the    *)
(* answer is above what the triple stood for by at least the step.  This is   *)
(* what the quotient and the root are meant to be read through: the step      *)
(* itself is not proved -- `twpaper.v' measures it -- but that widening by a  *)
(* step widens by a step is, and it takes nothing from the paper.             *)
Lemma widenUp_ge t f :
  finL (tw2l (widenUp t f)) -> twval t + D2R f <= twval (widenUp t f).
Proof.
rewrite /widenUp => F.
have H := expUp_ge _ F.
have [_ [F0 [F1 [Fu _]]]] := expUp_finI _ F.
have Fs := Dfin_upI _ _ Fu.
have [F2 Ff] := Dfin_addI _ _ Fs.
have Hg := addUpFp_ge _ _ F2 Ff Fs Fu.
by move: H; rewrite /twval /=; lra.
Qed.

Lemma widenDn_le t f :
  finL (tw2l (widenDn t f)) -> twval (widenDn t f) <= twval t - D2R f.
Proof.
rewrite /widenDn => F.
have H := expDn_le _ F.
have [_ [F0 [F1 [Fu _]]]] := expDn_finI _ F.
have Fs := Dfin_dnI _ _ Fu.
have [F2 Ff] := Dfin_addI _ _ Fs.
have Hg := addDnFp_le _ _ F2 Ff Fs Fu.
rewrite D2R_opp in Hg.
by move: H; rewrite /twval /=; lra.
Qed.

(* And the words of a widened triple word are numbers only if the ones it     *)
(* was made from are.                                                         *)
Lemma widenUp_finI t f :
  finL (tw2l (widenUp t f)) -> finL (tw2l t) /\ Dfin f.
Proof.
rewrite /widenUp => F.
have [_ [F0 [F1 [Fu _]]]] := expUp_finI _ F.
have [F2 Ff] := Dfin_addI _ _ (Dfin_upI _ _ Fu).
by split => //; apply: finL_tw2l.
Qed.

Lemma widenDn_finI t f :
  finL (tw2l (widenDn t f)) -> finL (tw2l t) /\ Dfin f.
Proof.
rewrite /widenDn => F.
have [_ [F0 [F1 [Fu _]]]] := expDn_finI _ F.
have [F2 Ff] := Dfin_addI _ _ (Dfin_dnI _ _ Fu).
split; last exact: Dfin_oppI Ff.
by apply: finL_tw2l.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The sum of two triple words, bounded above                                *)
(* ---------------------------------------------------------------------------*)

(* Merging the six words changes nothing, the sweep changes nothing, and the  *)
(* cut is made upwards.  No error analysis enters, and nothing of the paper's *)
(* is used: the paper is proved for round to nearest, and this is not.        *)
Theorem addTwUp_ge x y :
  finL (tw2l (addTwUp x y)) -> twval x + twval y <= twval (addTwUp x y).
Proof.
rewrite /addTwUp vecSum6_eq => F.
have H := expUp_ge _ F.
have [_ Fv] := expUp_finI _ F.
have Hv := vecSum_sum _ Fv.
by move: H; rewrite Hv Merge_sum !tw2l_sum.
Qed.

Theorem addTwDn_le x y :
  finL (tw2l (addTwDn x y)) -> twval (addTwDn x y) <= twval x + twval y.
Proof.
rewrite /addTwDn vecSum6_eq => F.
have H := expDn_le _ F.
have [_ Fv] := expDn_finI _ F.
have Hv := vecSum_sum _ Fv.
by move: H; rewrite Hv Merge_sum !tw2l_sum.
Qed.

(* Negating a triple word is exact, so subtraction is the sum of the negated  *)
(* words and needs nothing new.                                               *)
Lemma twval_neg t : finL (tw2l (negTw t)) -> twval (negTw t) = - twval t.
Proof.
by case: t => x0 x1 x2 _; rewrite /twval /= !D2R_opp; lra.
Qed.

Lemma finL_negTwI t : finL (tw2l t) -> finL (tw2l (negTw t)).
Proof.
case: t => x0 x1 x2 /= [F0 [F1 [F2 _]]].
split; first exact: Dfin_opp _ F0.
split; first exact: Dfin_opp _ F1.
by split; first exact: Dfin_opp _ F2.
Qed.

Lemma finL_negTw t : finL (tw2l (negTw t)) -> finL (tw2l t).
Proof.
case: t => x0 x1 x2 /= [F0 [F1 [F2 _]]].
split; first exact: Dfin_oppI _ F0.
split; first exact: Dfin_oppI _ F1.
by split; first exact: Dfin_oppI _ F2.
Qed.

Theorem subTwUp_ge x y :
  finL (tw2l (subTwUp x y)) -> finL (tw2l y) ->
  twval x - twval y <= twval (subTwUp x y).
Proof.
move=> F /finL_negTwI Fn; have H := addTwUp_ge x (negTw y) F.
rewrite (twval_neg _ Fn) in H.
by move: H; rewrite /subTwUp; lra.
Qed.

Theorem subTwDn_le x y :
  finL (tw2l (subTwDn x y)) -> finL (tw2l y) ->
  twval (subTwDn x y) <= twval x - twval y.
Proof.
move=> F /finL_negTwI Fn; have H := addTwDn_le x (negTw y) F.
rewrite (twval_neg _ Fn) in H.
by move: H; rewrite /subTwDn; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The product of two triple words, bounded                                  *)
(* ---------------------------------------------------------------------------*)

(* Sixteen of the smallest number there is.  Each of the four two-products    *)
(* can miss what it was given, but by no more than three and a half of        *)
(* those, so four of them miss by at most fourteen and this covers them.      *)
Lemma Dteps :
  D2R teps = 16 * bpow radix2 (SpecFloat.emin FloatOps.prec FloatOps.emax).
Proof. by rewrite /D2R /teps; compute; lra. Qed.

Lemma Descale_pos : (0 <= D2R escale)%R.
Proof. by rewrite /D2R /escale; compute; lra. Qed.

Lemma Dfin_teps : Dfin teps.
Proof. by []. Qed.

(* The step the product is widened by is at least the fixed one: it is the   *)
(* larger of the two, and the test that picks it is a test on the numbers.   *)
Lemma Dpstep w : Dfin (pstep w) ->
  (16 * bpow radix2 (SpecFloat.emin FloatOps.prec FloatOps.emax)
     <= D2R (pstep w))%R.
Proof.
rewrite -Dteps /pstep; case E: (_ <? _)%float => Fst; last by lra.
by have := Dltb _ _ Dfin_teps Fst E; lra.
Qed.

Lemma Dnpstep w : Dfin (pstep w) ->
  (D2R (- pstep w)%float
     <= - (16 * bpow radix2 (SpecFloat.emin FloatOps.prec FloatOps.emax)))%R.
Proof.
move=> Fst; have := Dpstep _ Fst.
by rewrite D2R_opp; lra.
Qed.

(* A product with a nought in it needs no rounding, and the finiteness that  *)
(* carries the whole computation goes through it just the same.              *)
Lemma Dfin_mulUp0I a b : Dfin (mulUp0 a b) -> Dfin (a * b)%float.
Proof. by rewrite /mulUp0; case: ifP => // _; apply: Dfin_mulUpI. Qed.

Lemma Dfin_mulDn0I a b : Dfin (mulDn0 a b) -> Dfin (a * b)%float.
Proof. by rewrite /mulDn0; case: ifP => // _; apply: Dfin_mulDnI. Qed.

Lemma mulUp0_ge a b : Dfin a -> Dfin b -> Dfin (a * b)%float ->
  Dfin (mulUp0 a b) -> (D2R a * D2R b <= D2R (mulUp0 a b))%R.
Proof.
move=> Fa Fb Fs; rewrite /mulUp0; case E: (_ || _)%float; last first.
  by move=> Fu; apply: mulUpFp_ge.
move=> _.
have E0 : Drnd (0 : R) = (0 : R) by rewrite DrndE round_0.
have [-> _] := Dfin_mul _ _ Fa Fb Fs.
have [Ez|Ez] := orP E.
  by have [_ ->] := Dfin_eqb0 _ Ez; rewrite Rmult_0_l E0; lra.
by have [_ ->] := Dfin_eqb0 _ Ez; rewrite Rmult_0_r E0; lra.
Qed.

Lemma mulDn0_le a b : Dfin a -> Dfin b -> Dfin (a * b)%float ->
  Dfin (mulDn0 a b) -> (D2R (mulDn0 a b) <= D2R a * D2R b)%R.
Proof.
move=> Fa Fb Fs; rewrite /mulDn0; case E: (_ || _)%float; last first.
  by move=> Fu; apply: mulDnFp_le.
move=> _.
have E0 : Drnd (0 : R) = (0 : R) by rewrite DrndE round_0.
have [-> _] := Dfin_mul _ _ Fa Fb Fs.
have [Ez|Ez] := orP E.
  by have [_ ->] := Dfin_eqb0 _ Ez; rewrite Rmult_0_l E0; lra.
by have [_ ->] := Dfin_eqb0 _ Ez; rewrite Rmult_0_r E0; lra.
Qed.

Lemma Dnteps :
  D2R (- teps)%float =
  - (16 * bpow radix2 (SpecFloat.emin FloatOps.prec FloatOps.emax)).
Proof. by rewrite /D2R /teps; compute; lra. Qed.

(* WHAT THE PRODUCT IS, and the whole of its error.  Of the nine products in  *)
(* the expansion of the two triples, the four that carry the value are taken  *)
(* by a two-product, which returns two words that all but add up to the       *)
(* product; the five that are smaller than the last word are each rounded in  *)
(* the direction wanted.  The list is then sorted, swept and cut, and none of *)
(* those three changes a value except the cut.  So the error is the four      *)
(* two-products' and the five roundings', and the first is covered by `teps'  *)
(* while the second is on the right side by construction.                     *)
Theorem mulTwUp_ge x y :
  finL (tw2l (mulTwUp x y)) ->
  twval x * twval y <= twval (mulTwUp x y).
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite !twvalE /mulTwUp vecSum14_eq /= => F.
have H := expUp_ge _ F.
have [_ Fv] := expUp_finI _ F.
have Fl := vecSum_finI _ Fv.
rewrite (vecSum_sum _ Fv) in H.
move: Fl; rewrite /= => -[Fp00 [Fp01 [Fp10 [Fe00
        [Fp11 [Fe01 [Fe10 [FM1 [FM2 [Fe11 [FM3 [FM4 [FM5 [Fst _]]]]]]]]]]]]]].
have Hs := Dpstep _ Fst.
(* the four two-products, each within three and a half of the smallest       *)
have K00 := twoProd_err x0 y0 Fe00.
have K01 := twoProd_err x0 y1 Fe01.
have K10 := twoProd_err x1 y0 Fe10.
have K11 := twoProd_err x1 y1 Fe11.
(* the five that are simply rounded upwards                                  *)
have [Fx0 Fy2] := Dfin_mulI _ _ (Dfin_mulUp0I _ _ FM1).
have [Fx2 Fy0] := Dfin_mulI _ _ (Dfin_mulUp0I _ _ FM2).
have [Fx1 Fy2'] := Dfin_mulI _ _ (Dfin_mulUp0I _ _ FM3).
have [Fx2' Fy1] := Dfin_mulI _ _ (Dfin_mulUp0I _ _ FM4).
have G1 := mulUp0_ge _ _ Fx0 Fy2 (Dfin_mulUp0I _ _ FM1) FM1.
have G2 := mulUp0_ge _ _ Fx2 Fy0 (Dfin_mulUp0I _ _ FM2) FM2.
have G3 := mulUp0_ge _ _ Fx1 Fy2' (Dfin_mulUp0I _ _ FM3) FM3.
have G4 := mulUp0_ge _ _ Fx2' Fy1 (Dfin_mulUp0I _ _ FM4) FM4.
have G5 := mulUp0_ge _ _ Fx2 Fy2 (Dfin_mulUp0I _ _ FM5) FM5.
have Hb : 0 < bpow radix2 (SpecFloat.emin FloatOps.prec FloatOps.emax)
  by apply: bpow_gt_0.
move: H; rewrite /= => H.
have Hx : (D2R x0 + D2R x1 + D2R x2) * (D2R y0 + D2R y1 + D2R y2) =
          D2R x0 * D2R y0 + D2R x0 * D2R y1 + D2R x1 * D2R y0 +
          D2R x1 * D2R y1 + D2R x0 * D2R y2 + D2R x2 * D2R y0 +
          D2R x1 * D2R y2 + D2R x2 * D2R y1 + D2R x2 * D2R y2 by ring.
rewrite Hx.
by move: K00 K01 K10 K11; split_Rabs; lra.
Qed.

(* And downwards, the same nine products the other way.                       *)
Theorem mulTwDn_le x y :
  finL (tw2l (mulTwDn x y)) ->
  twval (mulTwDn x y) <= twval x * twval y.
Proof.
case: x => x0 x1 x2; case: y => y0 y1 y2.
rewrite !twvalE /mulTwDn vecSum14_eq /= => F.
have H := expDn_le _ F.
have [_ Fv] := expDn_finI _ F.
have Fl := vecSum_finI _ Fv.
rewrite (vecSum_sum _ Fv) in H.
move: Fl; rewrite /= => -[Fp00 [Fp01 [Fp10 [Fe00
        [Fp11 [Fe01 [Fe10 [FM1 [FM2 [Fe11 [FM3 [FM4 [FM5 [Fst _]]]]]]]]]]]]]].
have Hs := Dnpstep _ (Dfin_oppI _ Fst).
have K00 := twoProd_err x0 y0 Fe00.
have K01 := twoProd_err x0 y1 Fe01.
have K10 := twoProd_err x1 y0 Fe10.
have K11 := twoProd_err x1 y1 Fe11.
have [Fx0 Fy2] := Dfin_mulI _ _ (Dfin_mulDn0I _ _ FM1).
have [Fx2 Fy0] := Dfin_mulI _ _ (Dfin_mulDn0I _ _ FM2).
have [Fx1 Fy2'] := Dfin_mulI _ _ (Dfin_mulDn0I _ _ FM3).
have [Fx2' Fy1] := Dfin_mulI _ _ (Dfin_mulDn0I _ _ FM4).
have G1 := mulDn0_le _ _ Fx0 Fy2 (Dfin_mulDn0I _ _ FM1) FM1.
have G2 := mulDn0_le _ _ Fx2 Fy0 (Dfin_mulDn0I _ _ FM2) FM2.
have G3 := mulDn0_le _ _ Fx1 Fy2' (Dfin_mulDn0I _ _ FM3) FM3.
have G4 := mulDn0_le _ _ Fx2' Fy1 (Dfin_mulDn0I _ _ FM4) FM4.
have G5 := mulDn0_le _ _ Fx2 Fy2 (Dfin_mulDn0I _ _ FM5) FM5.
have Hb : 0 < bpow radix2 (SpecFloat.emin FloatOps.prec FloatOps.emax)
  by apply: bpow_gt_0.
move: H; rewrite /= => H.
have Hx : (D2R x0 + D2R x1 + D2R x2) * (D2R y0 + D2R y1 + D2R y2) =
          D2R x0 * D2R y0 + D2R x0 * D2R y1 + D2R x1 * D2R y0 +
          D2R x1 * D2R y1 + D2R x0 * D2R y2 + D2R x2 * D2R y0 +
          D2R x1 * D2R y2 + D2R x2 * D2R y1 + D2R x2 * D2R y2 by ring.
rewrite Hx.
by move: K00 K01 K10 K11; split_Rabs; lra.
Qed.
