From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From threewords Require Import TwoSum TWR VecSum VSEB.
From twarith Require Import twarith twbound.
From dwarith Require Import dwbridge dwtwosum dwprod dwflx.

(* THE BRIDGE: PRIMITIVE FLOATS TO THE PAPER'S REALS.                         *)
(*                                                                            *)
(* `twarith.v' computes with Rocq's primitive floats; `threewords/' proves    *)
(* about real numbers in FLX -- the format with no smallest exponent, which   *)
(* is where the paper's bounds live.  This file says the two compute the same *)
(* thing, so that a theorem proved there can be read here.                    *)
(*                                                                            *)
(* THE SUMS NEED NO RANGE CONDITION.  `code/ddouble''s `dwflx.v' settled      *)
(* that: a sum of two binary64 numbers is rounded alike by both formats --    *)
(* above the smallest normal number because the bound on the exponent does    *)
(* not bite, below it because such a sum is itself a binary64 number and      *)
(* neither format has anything to round.  So `TwoSum', `Fast2Sum' and         *)
(* everything built from them -- the two sweeps, the merge, the sort -- cross *)
(* over on finiteness alone.                                                  *)
(*                                                                            *)
(* THE PRODUCTS DO ASK FOR MORE, and the scaling is what pays it.  A product  *)
(* can underflow where a sum cannot, so its two formats part company at the   *)
(* bottom of the range.  Algorithm 15 is spared that: scaling by an EVEN      *)
(* power of two is exact on every word, puts the argument in a fixed binade,  *)
(* and the answer comes back by half the exponent -- so every intermediate is *)
(* normal and the condition is discharged once, for all of them, rather than  *)
(* operation by operation.                                                    *)

Notation Dchoice := (fun n : Z => negb (Z.even n)).
(* `Xrnd' and `Xformat' come from `code/ddouble''s `dwflx.v': stating them     *)
(* again here, even to the same thing, gives `lra' two atoms where there is    *)
(* one.                                                                        *)

(* The paper's own names, instantiated at binary64 and round to nearest.      *)
Notation XTwoSum := (TwoSum prec Dchoice).
Notation XvecSum := (VecSum.vecSum prec Dchoice).

(* A list of primitive floats, read as a list of reals.                       *)
Definition l2R (l : seq PrimFloat.float) : seq R := [seq D2R z | z <- l].

Lemma l2R_cons a l : l2R (a :: l) = D2R a :: l2R l.
Proof. by []. Qed.

(* ---------------------------------------------------------------------------*)
(*  TwoSum                                                                    *)
(* ---------------------------------------------------------------------------*)

(* `code/ddouble' already matches the six roundings against the double-word   *)
(* paper's `TwoSum'; the three-word paper's is the same six, so the two       *)
(* readings are the same number and the transfer is that lemma re-read.       *)
Lemma twoSum_X a b : Dfin a -> Dfin b -> DtwoSumFin a b ->
  D2R (dwhi (twoSum a b)) = dwh (XTwoSum (D2R a) (D2R b)) /\
  D2R (dwlo (twoSum a b)) = dwl (XTwoSum (D2R a) (D2R b)).
Proof.
move=> Fa Fb Hfin.
have [Eh El] := twoSum_FLX_fin _ _ Fa Fb Hfin.
by rewrite Eh El.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The first sweep                                                           *)
(* ---------------------------------------------------------------------------*)

(* Both sweeps, one step, kept folded.  Left to itself `/=' unfolds the whole *)
(* recursion and there is nothing left for the induction hypothesis to meet.  *)
Lemma vecSumAux_cons2 x y (l : seq PrimFloat.float) :
  vecSumAux (x :: y :: l)
  = let: (es, s) := vecSumAux (y :: l) in
    (dwlo (twoSum x s) :: es, dwhi (twoSum x s)).
Proof. by []. Qed.

Lemma XvecSumAux_cons2 x y (l : seq R) :
  VecSum.vecSumAux prec Dchoice (x :: y :: l)
  = let: (es, s) := VecSum.vecSumAux prec Dchoice (y :: l) in
    let: DWR si ei1 := XTwoSum x s in (ei1 :: es, si).
Proof. by []. Qed.

(* The sweep's output being made of numbers is the one hypothesis, as it is   *)
(* everywhere else here: `twoSum_finI' turns it into the six each step needs. *)
Lemma vecSumAux_X l es s :
  vecSumAux l = (es, s) -> finL (s :: es) ->
  VecSum.vecSumAux prec Dchoice (l2R l) = (l2R es, D2R s).
Proof.
elim: l es s => [|x l IH] es s.
  by rewrite /=; case=> <- <- _; congr (_, _); rewrite /D2R B2R_Prim2B_0.
case: l IH => [|y l'] IH.
  by rewrite /=; case=> <- <- _.
rewrite vecSumAux_cons2.
case E: (vecSumAux (y :: l')) => [es' s'].
case=> <- <- [Fs [Fe Fes']].
have T := twoSum_finI _ _ Fe.
have [Fx Fs'] := Dfin_addI _ _ (proj1 T).
have Hrec := IH _ _ E (conj Fs' Fes').
have -> : l2R (x :: y :: l') = D2R x :: D2R y :: l2R l' by [].
rewrite XvecSumAux_cons2.
have -> : D2R y :: l2R l' = l2R (y :: l') by [].
rewrite Hrec.
have [Eh El] := twoSum_X _ _ Fx Fs' T.
have -> : l2R (dwlo (twoSum x s') :: es') = D2R (dwlo (twoSum x s')) :: l2R es'
  by [].
case E2: (XTwoSum (D2R x) (D2R s')) => [si ei1].
rewrite E2 /= in Eh El.
by rewrite Eh El.
Qed.

Lemma vecSum_X l : finL (vecSum l) -> l2R (vecSum l) = XvecSum (l2R l).
Proof.
rewrite /vecSum /VecSum.vecSum; case E: (vecSumAux l) => [es s] F.
by rewrite (vecSumAux_X _ _ _ E F).
Qed.

(* ---------------------------------------------------------------------------*)
(*  The second sweep                                                         *)
(* ---------------------------------------------------------------------------*)

(* The sweep drops a term that came out nought.  Here that is a float test,   *)
(* there a test on the real number; for a float that is a number the two      *)
(* agree, and minus nought is caught as well as nought.                       *)
Lemma Deqb0I a : Dfin a -> D2R a = 0 -> (a =? 0)%float = true.
Proof.
move=> Fa H0; rewrite eqb_equiv.
have F0 : Dfin 0%float by [].
rewrite (Beqb_correct _ _ _ _ Fa F0).
have -> : B2R (Prim2B 0%float) = 0 by [].
by move: H0; rewrite /D2R => ->; case: Req_bool_spec.
Qed.

(* Resolving the sweep's zero test, out of the way of the recursion.  Cased  *)
(* in place it asks to generalise a term the conclusion still uses.           *)
Lemma if_R_eq0 (A : Type) (x : R) (a b : A) :
  x = 0 -> (if Req_EM_T x 0 then a else b) = a.
Proof. by move=> ->; case: (Req_EM_T 0 0). Qed.

Lemma if_R_ne0 (A : Type) (x : R) (a b : A) :
  x <> 0 -> (if Req_EM_T x 0 then a else b) = b.
Proof. by move=> H; case: (Req_EM_T x 0) => // H0; case: (H H0). Qed.

Lemma vsebAux_one eps e :
  vsebAux eps [:: e] = [:: dwhi (twoSum eps e); dwlo (twoSum eps e)].
Proof. by []. Qed.

Lemma XvsebAux_one eps e :
  VSEB.vsebAux prec Dchoice eps [:: e]
  = let: DWR y0 y1 := XTwoSum eps e in [:: y0; y1].
Proof. by []. Qed.

(* With the `let' expanded: left in, the test is not a subterm of the goal    *)
(* and there is nothing for the case analysis to take hold of.                 *)
Lemma vsebAux_cons2 eps e y (l : seq PrimFloat.float) :
  vsebAux eps (e :: y :: l)
  = if (dwlo (twoSum eps e) =? 0)%float
    then vsebAux (dwhi (twoSum eps e)) (y :: l)
    else dwhi (twoSum eps e) :: vsebAux (dwlo (twoSum eps e)) (y :: l).
Proof. by []. Qed.

(* Stated with the projections rather than a `let'-match: a match on a pair   *)
(* cannot be taken apart in the goal without generalising what it came from,  *)
(* and here that is used elsewhere in the conclusion.                         *)
Lemma XvsebAux_cons2 eps e y (l : seq R) :
  VSEB.vsebAux prec Dchoice eps (e :: y :: l)
  = if Req_EM_T (dwl (XTwoSum eps e)) 0
    then VSEB.vsebAux prec Dchoice (dwh (XTwoSum eps e)) (y :: l)
    else dwh (XTwoSum eps e)
         :: VSEB.vsebAux prec Dchoice (dwl (XTwoSum eps e)) (y :: l).
Proof. by rewrite /VSEB.vsebAux; case: (XTwoSum eps e). Qed.

(* And the sweep itself.  Its output being made of numbers is the hypothesis, *)
(* as everywhere else; `vsebAux_finIl' in `twbound.v' unpacks it.             *)
Lemma vsebAux_X eps l : Dfin eps -> finL l -> finL (vsebAux eps l) ->
  VSEB.vsebAux prec Dchoice (D2R eps) (l2R l) = l2R (vsebAux eps l).
Proof.
elim: l eps => [|e l IH] eps Feps Fl F; first by [].
case: l IH Fl F => [|y l'] IH Fl F.
  have [Fe _] := Fl.
  have [Fh [Flo _]] := F.
  have T := twoSum_finI _ _ Flo.
  have [Eh El] := twoSum_X _ _ Feps Fe T.
  have -> : l2R [:: e] = [:: D2R e] by [].
  have -> : l2R [:: dwhi (twoSum eps e); dwlo (twoSum eps e)]
          = [:: D2R (dwhi (twoSum eps e)); D2R (dwlo (twoSum eps e))] by [].
  rewrite El Eh XvsebAux_one.
  by case: (XTwoSum (D2R eps) (D2R e)).
have [Fe Fyl] := Fl.
have Hyl : l2R (y :: l') = D2R y :: l2R l' by [].
(* one step on both sides, and on the hypothesis, before the tests are met   *)
rewrite vsebAux_cons2 in F *.
have -> : l2R [:: e, y & l'] = D2R e :: D2R y :: l2R l' by [].
rewrite XvsebAux_cons2 -Hyl.
move: F; case Ez: ((dwlo (twoSum eps e) =? 0)%float) => F.
  have [Flo Vlo] := Dfin_eqb0 _ Ez.
  have T := twoSum_finI _ _ Flo.
  have [Eh El] := twoSum_X _ _ Feps Fe T.
  have [Fh _] := vsebAux_finIl _ _ F.
  have Het : dwl (XTwoSum (D2R eps) (D2R e)) = 0 by rewrite -El.
  rewrite (if_R_eq0 _ _ _ _ Het) -Eh.
  by apply: IH.
have [Fh Ft] := F.
have [Flo _] := vsebAux_finIl _ _ Ft.
have T := twoSum_finI _ _ Flo.
have [Eh El] := twoSum_X _ _ Feps Fe T.
have Het : dwl (XTwoSum (D2R eps) (D2R e)) <> 0.
  rewrite -El => H0.
  by move: Ez; rewrite (Deqb0I _ Flo H0).
rewrite (if_R_ne0 _ _ _ _ Het) -Eh -El [l2R (_ :: _)]/=; congr (_ :: _).
by apply: IH.
Qed.

Lemma vseb_X l : finL l -> finL (vseb l) ->
  VSEB.vseb prec Dchoice (l2R l) = l2R (vseb l).
Proof.
case: l => [|e l] // Fl F.
have [Fe _] := Fl.
by rewrite /VSEB.vseb /vseb /= (vsebAux_X _ _ Fe (proj2 Fl) F).
Qed.

(* ---------------------------------------------------------------------------*)
(*  The plumbing round the sweeps                                            *)
(* ---------------------------------------------------------------------------*)

(* Reading a list of floats commutes with taking a prefix and with indexing.   *)
Lemma l2R_take k l : l2R (take k l) = take k (l2R l).
Proof. by rewrite /l2R map_take. Qed.

Lemma l2R_nth l i : D2R (nth 0%float l i) = nth 0 (l2R l) i.
Proof.
rewrite /l2R.
have [Hi|Hi] := ltnP i (size l); first by rewrite (nth_map 0%float).
by rewrite !nth_default ?size_map // /D2R B2R_Prim2B_0.
Qed.

(* A triple word read from a list: both developments fill a short list out    *)
(* with noughts, so the two readings agree with nothing asked at all.         *)
Definition tw2R (t : twfloat) : twR :=
  TWR (D2R (tw0 t)) (D2R (tw1 t)) (D2R (tw2 t)).

Lemma TWval_tw2R t : TWval (tw2R t) = twval t.
Proof. by case: t => a b c; rewrite /TWval /twval. Qed.

(* ---------------------------------------------------------------------------*)
(*  TwoProd -- the first one that asks about the range                       *)
(* ---------------------------------------------------------------------------*)

Notation Dprodlo := (bpow radix2 (SpecFloat.emin prec emax + 2 * prec - 1)).
Notation XTwoProd := (MULTmore.TwoProd prec radix2 (Znearest Dchoice)).

(* Here the two formats part company, and the condition is the one            *)
(* `code/ddouble' already isolated: the product must be clear of the bottom of *)
(* the range.  Above `Dprodlo' the error of a product is a float in both       *)
(* formats, so the pair is the same pair.  `Dprodlo' is `prec' above the       *)
(* smallest normal number, so the rounding of the product agrees as well.      *)
Lemma twoProd_X a b : Dfin (dwlo (twoProd a b)) ->
  (Dprodlo <= Rabs (D2R a * D2R b))%R ->
  D2R (dwhi (twoProd a b)) = (XTwoProd (D2R a) (D2R b)).1 /\
  D2R (dwlo (twoProd a b)) = (XTwoProd (D2R a) (D2R b)).2.
Proof.
move=> Fe Hn.
have Hp : (1 < prec)%Z by [].
have [Fa [Fb [Fh Eh]]] := twoProd_hi _ _ Fe.
have Ex := twoProd_exact _ _ Fe Hn.
have HN : (bpow radix2 (SpecFloat.emin prec emax + prec - 1)
           <= Rabs (D2R a * D2R b))%R.
  apply: Rle_trans Hn; apply: bpow_le; lia.
have Ehx : D2R (dwhi (twoProd a b)) = Xrnd (D2R a * D2R b).
  by rewrite Eh (Drnd_FLX _ HN).
have Hp0 : Prec_gt_0 prec by [].
have Hvr : Valid_rnd (Znearest Dchoice) by apply: valid_rnd_N.
have Hc := @MULTmore.TwoProd_correct prec Hp0 radix2 (Znearest Dchoice) Hvr
             _ _ (Dformat_FLX a) (Dformat_FLX b).
move: Hc; rewrite /MULTmore.TwoProd /= => [] [Hpr Hsum _ _].
split; first by rewrite Ehx.
by move: Ex Ehx Hsum; lra.
Qed.

(* The way both developments read a list back as a triple word: a head and    *)
(* what the cut left, filled out with noughts.                                *)
Definition l2twR (a : R) (m : seq R) : twR :=
  match m with
  | [:: r1, r2 & _] => TWR a r1 r2
  | [:: r1]         => TWR a r1 0
  | [::]            => TWR a 0 0
  end.

Lemma tw2R_l2tw a m : tw2R (l2tw (a :: m)) = l2twR (D2R a) (l2R m).
Proof.
case: m => [|r1 [|r2 m]] //=; rewrite /tw2R /=;
  by congr TWR; rewrite /D2R B2R_Prim2B_0.
Qed.
