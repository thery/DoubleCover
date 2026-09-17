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
