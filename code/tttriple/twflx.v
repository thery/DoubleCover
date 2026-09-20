From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From twarith.threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From twarith.threewords Require Import TwoSum TWR VecSum VSEB.
From twarith.threewords Require Import ThreeProd ThreeProdDW ThreeProdOne.
From twarith.threewords Require Import ThreeSqRt.
From twarith Require Import twarith twbound twpaper twseed.
From dwarith Require Import dwbridge dwtwosum dwprod dwbound dwflx dwsqrt.

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
Notation XvsebK := (VSEB.vsebK prec Dchoice).

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

(* An element of a list of numbers is a number, the default included.         *)
Lemma finL_nth l i : finL l -> Dfin (nth 0%float l i).
Proof. by elim: l i => [|a l IH] [|i] //= [Fa Fl] //; apply: IH. Qed.

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

(* ---------------------------------------------------------------------------*)
(*  One operation at a time                                                  *)
(* ---------------------------------------------------------------------------*)

(* A sum and a difference cross with nothing asked but that the answer is a    *)
(* number.  This is `Drnd_FLX_plus' read through the bridge.                   *)
Lemma add_X a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  D2R (a + b)%float = Xrnd (D2R a + D2R b).
Proof.
move=> Fa Fb Fs.
have [E _] := Dfin_add _ _ Fa Fb Fs.
by rewrite E (Drnd_FLX_plus _ _ (Dformat a) (Dformat b)).
Qed.

Lemma sub_X a b : Dfin a -> Dfin b -> Dfin (a - b)%float ->
  D2R (a - b)%float = Xrnd (D2R a - D2R b).
Proof.
move=> Fa Fb Fs.
have [E _] := Dfin_sub _ _ Fa Fb Fs.
by rewrite E (Drnd_FLX_minus _ _ (Dformat a) (Dformat b)).
Qed.

(* A product does ask: below the bottom of the range the two formats round it  *)
(* differently, and `Dprodlo' is where they agree again.                       *)
Lemma mul_X a b : Dfin a -> Dfin b -> Dfin (a * b)%float ->
  (Dprodlo <= Rabs (D2R a * D2R b))%R ->
  D2R (a * b)%float = Xrnd (D2R a * D2R b).
Proof.
move=> Fa Fb Fs Hn.
have [E _] := Dfin_mul _ _ Fa Fb Fs.
rewrite E; apply: Drnd_FLX.
apply: Rle_trans Hn.
have -> : (SpecFloat.emin prec emax + prec - 1
           = SpecFloat.emin prec emax + 2 * prec - 1 - prec)%Z by ring.
by apply: bpow_le; have : (0 < prec)%Z by []; lia.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Scaling by a power of two                                                *)
(* ---------------------------------------------------------------------------*)

(* This is what pays for the products' range condition.  Multiplying a float  *)
(* by a power of two moves the exponent and leaves the digits, so it is exact *)
(* as long as it stays in the range -- and nothing has to be said about where *)
(* the number was to begin with.                                              *)
Lemma mul_pow_exact a s e : Dfin s -> D2R s = bpow radix2 e -> (0 <= e)%Z ->
  Dfin a -> Dfin (a * s)%float -> D2R (a * s)%float = D2R a * bpow radix2 e.
Proof.
move=> Fs Hs He Fa Fm.
have [E _] := Dfin_mul _ _ Fa Fs Fm.
rewrite E Hs round_generic //.
by apply: Dformat_scale => //; apply: Dformat.
Qed.

(* A triple word scales word by word, and its value scales with it.           *)
Lemma twval_scale x0 x1 x2 s e :
  Dfin s -> D2R s = bpow radix2 e -> (0 <= e)%Z ->
  Dfin x0 -> Dfin x1 -> Dfin x2 ->
  Dfin (x0 * s)%float -> Dfin (x1 * s)%float -> Dfin (x2 * s)%float ->
  twval (TWFloat (x0 * s) (x1 * s) (x2 * s))%float
  = twval (TWFloat x0 x1 x2) * bpow radix2 e.
Proof.
move=> Fs Hs He F0 F1 F2 M0 M1 M2.
rewrite /twval /= (mul_pow_exact _ _ _ Fs Hs He F0 M0)
        (mul_pow_exact _ _ _ Fs Hs He F1 M1)
        (mul_pow_exact _ _ _ Fs Hs He F2 M2).
by ring.
Qed.

(* And the root of a number taken up by an EVEN power of two is the root      *)
(* taken up by half of it, which is why the root can be scaled and the        *)
(* quotient cannot.                                                           *)
Lemma sqrt_scale_even (v : R) (k : Z) : (0 <= v)%R ->
  R_sqrt.sqrt (v * bpow radix2 (2 * k))
  = R_sqrt.sqrt v * bpow radix2 k.
Proof.
move=> Hv.
have Hp : (0 < bpow radix2 k)%R by apply: bpow_gt_0.
have -> : bpow radix2 (2 * k) = bpow radix2 k * bpow radix2 k.
  by rewrite -bpow_plus; congr bpow; ring.
have -> : v * (bpow radix2 k * bpow radix2 k)
        = (v * bpow radix2 k) * bpow radix2 k by ring.
rewrite sqrt_mult_alt; last by nra.
rewrite sqrt_mult_alt //.
have Hq : R_sqrt.sqrt (bpow radix2 k) * R_sqrt.sqrt (bpow radix2 k)
        = bpow radix2 k by rewrite sqrt_sqrt //; lra.
by rewrite Rmult_assoc Hq.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Algorithm 11 across the bridge                                           *)
(* ---------------------------------------------------------------------------*)

(* What the transfer asks of the two arguments.  Every clause is either a     *)
(* word being a number -- which the guard in `tw_ops.v' tests anyway -- or a  *)
(* product being clear of the bottom of the range, which is what the scaling  *)
(* above is for.                                                              *)
Definition prodDW_ok (x0 x1 y0 y1 y2 : PrimFloat.float) : Prop :=
  let b := vecSum [:: dwlo (twoProd x0 y0); dwhi (twoProd x0 y1);
                      dwhi (twoProd x1 y0)] in
  let e := vecSum [:: dwhi (twoProd x0 y0); nth 0%float b 0; nth 0%float b 1;
                      (nth 0%float b 2 + x1 * y1)%float;
                      ((dwlo (twoProd x1 y0) + x0 * y2)
                        + dwlo (twoProd x0 y1))%float] in
  [/\ Dfin x0, Dfin x1, Dfin y0, Dfin y1 & Dfin y2]
  /\ [/\ Dfin (dwlo (twoProd x0 y0)), Dfin (dwlo (twoProd x0 y1))
        & Dfin (dwlo (twoProd x1 y0))]
  /\ [/\ (Dprodlo <= Rabs (D2R x0 * D2R y0))%R,
         (Dprodlo <= Rabs (D2R x0 * D2R y1))%R &
         (Dprodlo <= Rabs (D2R x1 * D2R y0))%R]
  /\ [/\ (Dprodlo <= Rabs (D2R x1 * D2R y1))%R &
         (Dprodlo <= Rabs (D2R x0 * D2R y2))%R]
  /\ [/\ Dfin (x1 * y1)%float, Dfin (x0 * y2)%float,
         Dfin (nth 0%float b 2 + x1 * y1)%float,
         Dfin (dwlo (twoProd x1 y0) + x0 * y2)%float &
         Dfin ((dwlo (twoProd x1 y0) + x0 * y2)
               + dwlo (twoProd x0 y1))%float]
  /\ finL b
  /\ finL e
  /\ finL (vseb [:: nth 0%float e 1; nth 0%float e 2;
                    nth 0%float e 3; nth 0%float e 4]).

(* The two, with the intermediates handed in rather than bound by a `let':    *)
(* `nth3', the `let' on a triple and the two `let's on the sweeps all block    *)
(* rewriting, and none of them survives being named.                          *)
Lemma threeProdDW_shape x0 x1 x2 y0 y1 y2 b e :
  b = vecSum [:: dwlo (twoProd x0 y0); dwhi (twoProd x0 y1);
                 dwhi (twoProd x1 y0)] ->
  e = vecSum [:: dwhi (twoProd x0 y0); nth 0%float b 0; nth 0%float b 1;
                 (nth 0%float b 2 + x1 * y1)%float;
                 ((dwlo (twoProd x1 y0) + x0 * y2)
                   + dwlo (twoProd x0 y1))%float] ->
  threeProdDW (TWFloat x0 x1 x2) (TWFloat y0 y1 y2)
  = l2tw (nth 0%float e 0
          :: take 2 (vseb [:: nth 0%float e 1; nth 0%float e 2;
                              nth 0%float e 3; nth 0%float e 4])).
Proof.
move=> -> ->; rewrite /threeProdDW.
by case: (twoProd x0 y0) => ??; case: (twoProd x0 y1) => ??;
   case: (twoProd x1 y0) => ??.
Qed.

Lemma ThreeProdDWn_shape (x0 x1 x2 y0 y1 y2 : R) b e :
  b = XvecSum [:: (XTwoProd x0 y0).2; (XTwoProd x0 y1).1;
                  (XTwoProd x1 y0).1] ->
  e = XvecSum [:: (XTwoProd x0 y0).1; nth 0 b 0; nth 0 b 1;
                  Xrnd (nth 0 b 2 + Xrnd (x1 * y1));
                  Xrnd (Xrnd ((XTwoProd x1 y0).2 + Xrnd (x0 * y2))
                        + (XTwoProd x0 y1).2)] ->
  ThreeProdDWn prec Dchoice (TWR x0 x1 x2) (TWR y0 y1 y2)
  = l2twR (nth 0 e 0)
          (XvsebK 2 [:: nth 0 e 1; nth 0 e 2; nth 0 e 3; nth 0 e 4]).
Proof.
move=> -> ->; rewrite /ThreeProdDWn /l2twR.
by case: (XTwoProd x0 y0) => ??; case: (XTwoProd x0 y1) => ??;
   case: (XTwoProd x1 y0) => ??.
Qed.

Lemma threeProdDW_X x0 x1 x2 y0 y1 y2 :
  prodDW_ok x0 x1 y0 y1 y2 ->
  tw2R (threeProdDW (TWFloat x0 x1 x2) (TWFloat y0 y1 y2))
  = ThreeProdDWn prec Dchoice
      (tw2R (TWFloat x0 x1 x2)) (tw2R (TWFloat y0 y1 y2)).
Proof.
rewrite /prodDW_ok
  => [] [[Fx0 Fx1 Fy0 Fy1 Fy2] [[F00m F01m F10m]
        [[H00 H01 H10] [[H11 H02] [[M11 M02 Fc F31 F3] [Fb [Fe Fv]]]]]]].
have [Eh00 El00] := twoProd_X _ _ F00m H00.
have [Eh01 El01] := twoProd_X _ _ F01m H01.
have [Eh10 El10] := twoProd_X _ _ F10m H10.
set B := vecSum [:: dwlo (twoProd x0 y0); dwhi (twoProd x0 y1);
                    dwhi (twoProd x1 y0)] in Fb Fe *.
set E := vecSum [:: dwhi (twoProd x0 y0); nth 0%float B 0; nth 0%float B 1;
                    (nth 0%float B 2 + x1 * y1)%float;
                    ((dwlo (twoProd x1 y0) + x0 * y2)
                      + dwlo (twoProd x0 y1))%float] in Fe Fv *.
rewrite (threeProdDW_shape x0 x1 x2 y0 y1 y2 B E erefl erefl).
have -> : tw2R (TWFloat x0 x1 x2) = TWR (D2R x0) (D2R x1) (D2R x2) by [].
have -> : tw2R (TWFloat y0 y1 y2) = TWR (D2R y0) (D2R y1) (D2R y2) by [].
(* the inner sweep, then the outer one, each on the list the other made      *)
have EB : l2R B = XvecSum [:: (XTwoProd (D2R x0) (D2R y0)).2;
                              (XTwoProd (D2R x0) (D2R y1)).1;
                              (XTwoProd (D2R x1) (D2R y0)).1].
  by rewrite /B (vecSum_X _ Fb) [l2R [:: _; _; _]]/= El00 Eh01 Eh10.
have EE : l2R E
        = XvecSum [:: (XTwoProd (D2R x0) (D2R y0)).1;
                      nth 0 (l2R B) 0; nth 0 (l2R B) 1;
                      Xrnd (nth 0 (l2R B) 2 + Xrnd (D2R x1 * D2R y1));
                      Xrnd (Xrnd ((XTwoProd (D2R x1) (D2R y0)).2
                                  + Xrnd (D2R x0 * D2R y2))
                            + (XTwoProd (D2R x0) (D2R y1)).2)].
  rewrite /E (vecSum_X _ Fe).
  have -> : l2R [:: dwhi (twoProd x0 y0); nth 0%float B 0; nth 0%float B 1;
                    (nth 0%float B 2 + x1 * y1)%float;
                    ((dwlo (twoProd x1 y0) + x0 * y2)
                      + dwlo (twoProd x0 y1))%float]
          = [:: D2R (dwhi (twoProd x0 y0)); D2R (nth 0%float B 0);
                D2R (nth 0%float B 1);
                D2R (nth 0%float B 2 + x1 * y1)%float;
                D2R ((dwlo (twoProd x1 y0) + x0 * y2)
                      + dwlo (twoProd x0 y1))%float] by [].
  rewrite Eh00 !l2R_nth.
  rewrite (add_X _ _ (@finL_nth B 2 Fb) M11 Fc) (mul_X _ _ Fx1 Fy1 M11 H11).
  rewrite (add_X _ _ F31 F01m F3) (add_X _ _ F10m M02 F31).
  by rewrite (mul_X _ _ Fx0 Fy2 M02 H02) El10 El01 l2R_nth.
rewrite (ThreeProdDWn_shape (D2R x0) (D2R x1) (D2R x2)
           (D2R y0) (D2R y1) (D2R y2) (l2R B) (l2R E) EB EE).
rewrite tw2R_l2tw /VSEB.vsebK.
have -> : [:: nth 0 (l2R E) 1; nth 0 (l2R E) 2; nth 0 (l2R E) 3;
              nth 0 (l2R E) 4]
        = l2R [:: nth 0%float E 1; nth 0%float E 2; nth 0%float E 3;
                  nth 0%float E 4].
  have -> : l2R [:: nth 0%float E 1; nth 0%float E 2; nth 0%float E 3;
                    nth 0%float E 4]
          = [:: D2R (nth 0%float E 1); D2R (nth 0%float E 2);
                D2R (nth 0%float E 3); D2R (nth 0%float E 4)] by [].
  by rewrite !l2R_nth.
have Fl4 : finL [:: nth 0%float E 1; nth 0%float E 2; nth 0%float E 3;
                    nth 0%float E 4].
  by do ![split; first by apply: finL_nth].
by rewrite (vseb_X _ Fl4 Fv) l2R_take.
Qed.


(* ---------------------------------------------------------------------------*)
(*  Fast2Sum, and the swap                                                    *)
(* ---------------------------------------------------------------------------*)

Notation XFast2Sum := (TwoSum.Fast2Sum prec Dchoice).
Notation XFast2SumS := (TwoSum.Fast2SumS prec Dchoice).

(* `Dleb' the other way round: the swap has to be read on both branches.      *)
Lemma DlebF a b : Dfin a -> Dfin b -> (a <=? b)%float = false ->
  (D2R b < D2R a)%R.
Proof.
rewrite /Dfin /D2R leb_equiv => Fa Fb.
rewrite (Bleb_correct _ _ _ _ Fa Fb).
by case: Rle_bool_spec => // H _.
Qed.

(* The three-word paper's `Fast2Sum' is the double-word paper's, written on   *)
(* `DWR' instead of a pair, so `dwflx.v' settles this one too.                *)
Lemma fastTwoSum_X a b : Dfin a -> Dfin b -> DfastTwoSumFin a b ->
  D2R (dwhi (fastTwoSum a b)) = dwh (XFast2Sum (D2R a) (D2R b)) /\
  D2R (dwlo (fastTwoSum a b)) = dwl (XFast2Sum (D2R a) (D2R b)).
Proof. by move=> Fa Fb H; apply: fastTwoSum_FLX_fin. Qed.

Lemma XFast2SumS_le a b : (Rabs b <= Rabs a)%R ->
  XFast2SumS a b = XFast2Sum a b.
Proof.
by rewrite /TwoSum.Fast2SumS => H; case: (Rle_dec (Rabs b) (Rabs a)).
Qed.

Lemma XFast2SumS_gt a b : (Rabs a < Rabs b)%R ->
  XFast2SumS a b = XFast2Sum b a.
Proof.
rewrite /TwoSum.Fast2SumS => H.
by case: (Rle_dec (Rabs b) (Rabs a)) => // H1; lra.
Qed.

Definition Dfast2SumSFin (a b : PrimFloat.float) : Prop :=
  if (abs b <=? abs a)%float then DfastTwoSumFin a b else DfastTwoSumFin b a.

Lemma fast2SumS_X a b : Dfin a -> Dfin b -> Dfast2SumSFin a b ->
  D2R (dwhi (fast2SumS a b)) = dwh (XFast2SumS (D2R a) (D2R b)) /\
  D2R (dwlo (fast2SumS a b)) = dwl (XFast2SumS (D2R a) (D2R b)).
Proof.
move=> Fa Fb.
have Faa : Dfin (abs a) by apply: Dfin_abs.
have Fab : Dfin (abs b) by apply: Dfin_abs.
have [E|E] : ((abs b <=? abs a)%float = true) \/ ((abs b <=? abs a)%float = false)
  by case: (abs b <=? abs a)%float; [left|right].
- rewrite /Dfast2SumSFin /fast2SumS E => H.
  have Hle : (Rabs (D2R b) <= Rabs (D2R a))%R
    by rewrite -!D2R_abs; apply: Dleb.
  by rewrite (XFast2SumS_le _ _ Hle); apply: fastTwoSum_X.
rewrite /Dfast2SumSFin /fast2SumS E => H.
have Hgt : (Rabs (D2R a) < Rabs (D2R b))%R
  by rewrite -!D2R_abs; apply: DlebF.
by rewrite (XFast2SumS_gt _ _ Hgt); apply: fastTwoSum_X.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Algorithm 20                                                              *)
(* ---------------------------------------------------------------------------*)

Definition prodOne_ok (x0 x1 x2 y1 y2 : PrimFloat.float) : Prop :=
  let z01p := dwhi (twoProd x0 y1) in
  let z01m := dwlo (twoProd x0 y1) in
  let bh := dwhi (fast2SumS x1 z01p) in
  let bl := dwlo (fast2SumS x1 z01p) in
  let z31 := (z01m + x1 * y1)%float in
  let z3 := (z31 + x0 * y2)%float in
  let s3 := (bl + z3)%float in
  let e := vecSum [:: x0; bh; (s3 + x2)%float] in
  [/\ Dfin x0, Dfin x1, Dfin x2, Dfin y1 & Dfin y2]
  /\ [/\ Dfin z01p, Dfin z01m, Dfin bh & Dfin bl]
  /\ [/\ (Dprodlo <= Rabs (D2R x0 * D2R y1))%R,
         (Dprodlo <= Rabs (D2R x1 * D2R y1))%R
       & (Dprodlo <= Rabs (D2R x0 * D2R y2))%R]
  /\ Dfast2SumSFin x1 z01p
  /\ [/\ Dfin (x1 * y1)%float, Dfin (x0 * y2)%float, Dfin z31, Dfin z3
       & Dfin s3]
  /\ Dfin (s3 + x2)%float
  /\ finL e
  /\ Dfast2SumSFin (nth 0%float e 1) (nth 0%float e 2).

Lemma threeProdOneTW_shape x0 x1 x2 y0 y1 y2 z01p z01m bh bl e :
  twoProd x0 y1 = DWFloat z01p z01m ->
  fast2SumS x1 z01p = DWFloat bh bl ->
  e = vecSum [:: x0; bh;
        ((bl + ((z01m + x1 * y1) + x0 * y2)) + x2)%float] ->
  threeProdOneTW (TWFloat x0 x1 x2) (TWFloat y0 y1 y2)
  = let: DWFloat r1 r2 := fast2SumS (nth 0%float e 1) (nth 0%float e 2) in
    TWFloat (nth 0%float e 0) r1 r2.
Proof. by move=> H1 H2 ->; rewrite /threeProdOneTW /p18head H1 H2 /nth3. Qed.

Lemma ThreeProdOneTWn_shape (x0 x1 x2 y0 y1 y2 : R) z01p z01m bh bl e :
  XTwoProd x0 y1 = (z01p, z01m) ->
  XFast2SumS x1 z01p = DWR bh bl ->
  e = XvecSum [:: x0; bh;
        Xrnd (Xrnd (bl + Xrnd (Xrnd (z01m + Xrnd (x1 * y1))
                               + Xrnd (x0 * y2))) + x2)] ->
  ThreeProdOneTWn prec Dchoice (TWR x0 x1 x2) (TWR y0 y1 y2)
  = let: DWR r1 r2 := XFast2SumS (nth 0 e 1) (nth 0 e 2) in
    TWR (nth 0 e 0) r1 r2.
Proof.
move=> H1 H2 ->.
by rewrite (ThreeProdOneTWn_unfold prec Dchoice) H1 H2.
Qed.

(* Reading back the last `Fast2Sum' of an algorithm: both sides end the same  *)
(* way, a double word spread over the last two limbs.                         *)
Lemma tw2R_f2s e0 d D :
  D2R (dwhi d) = dwh D -> D2R (dwlo d) = dwl D ->
  tw2R (let: DWFloat r1 r2 := d in TWFloat e0 r1 r2)
  = let: DWR r1 r2 := D in TWR (D2R e0) r1 r2.
Proof.
case: d => a b; case: D => c d0 /= Eh El.
by rewrite /tw2R /= Eh El.
Qed.

Lemma dwE (d : dwfloat) : d = DWFloat (dwhi d) (dwlo d).
Proof. by case: d. Qed.

Lemma XdwE (d : dwR) : d = DWR (dwh d) (dwl d).
Proof. by case: d. Qed.

Lemma XTwoProdE (a b : R) :
  XTwoProd a b = ((XTwoProd a b).1, (XTwoProd a b).2).
Proof. by case: XTwoProd. Qed.

Lemma threeProdOneTW_X x0 x1 x2 y0 y1 y2 :
  prodOne_ok x0 x1 x2 y1 y2 ->
  tw2R (threeProdOneTW (TWFloat x0 x1 x2) (TWFloat y0 y1 y2))
  = ThreeProdOneTWn prec Dchoice
      (tw2R (TWFloat x0 x1 x2)) (tw2R (TWFloat y0 y1 y2)).
Proof.
rewrite /prodOne_ok
  => [] [[Fx0 Fx1 Fx2 Fy1 Fy2] [[Fz01p Fz01m Fbh Fbl]
        [[H01 H11 H02] [Hb [[M11 M02 Fz31 Fz3 Fs3]
          [Fs3x [Fe Hlast]]]]]]].
have [Eh01 El01] := twoProd_X _ _ Fz01m H01.
set z01p := dwhi (twoProd x0 y1) in Fz01p Hb Fe Hlast Eh01 *.
set z01m := dwlo (twoProd x0 y1) in Fz01m Fz31 El01 Fz3 Fs3 Fs3x Fe Hlast *.
set bh := dwhi (fast2SumS x1 z01p) in Fbh Fe Hlast *.
set bl := dwlo (fast2SumS x1 z01p) in Fbl Fs3 Fs3x Fe Hlast *.
have [Ebh Ebl] := fast2SumS_X _ _ Fx1 Fz01p Hb.
rewrite -/z01p -/bh -/bl in Ebh Ebl.
set E := vecSum [:: x0; bh; ((bl + ((z01m + x1 * y1) + x0 * y2))
                             + x2)%float] in Fe Hlast *.
rewrite (threeProdOneTW_shape x0 x1 x2 y0 y1 y2 z01p z01m bh bl E
           (dwE _) (dwE _) erefl).
have -> : tw2R (TWFloat x0 x1 x2) = TWR (D2R x0) (D2R x1) (D2R x2) by [].
have -> : tw2R (TWFloat y0 y1 y2) = TWR (D2R y0) (D2R y1) (D2R y2) by [].
have EE : l2R E
        = XvecSum [:: D2R x0; D2R bh;
            Xrnd (Xrnd (D2R bl
                        + Xrnd (Xrnd (D2R z01m + Xrnd (D2R x1 * D2R y1))
                                + Xrnd (D2R x0 * D2R y2))) + D2R x2)].
  rewrite /E (vecSum_X _ Fe).
  have -> : l2R [:: x0; bh; ((bl + ((z01m + x1 * y1) + x0 * y2))
                             + x2)%float]
          = [:: D2R x0; D2R bh;
                D2R ((bl + ((z01m + x1 * y1) + x0 * y2)) + x2)%float] by [].
  rewrite (add_X _ _ Fs3 Fx2 Fs3x) (add_X _ _ Fbl Fz3 Fs3).
  rewrite (add_X _ _ Fz31 M02 Fz3) (add_X _ _ Fz01m M11 Fz31).
  by rewrite (mul_X _ _ Fx1 Fy1 M11 H11) (mul_X _ _ Fx0 Fy2 M02 H02).
rewrite (ThreeProdOneTWn_shape (D2R x0) (D2R x1) (D2R x2)
           (D2R y0) (D2R y1) (D2R y2) (D2R z01p) (D2R z01m)
           (D2R bh) (D2R bl) (l2R E)); last by rewrite EE.
- have [EH EL] := fast2SumS_X _ _ (finL_nth E 1 Fe) (finL_nth E 2 Fe) Hlast.
  rewrite -/E in EH EL.
  rewrite (tw2R_f2s _ _ (XFast2SumS (nth 0 (l2R E) 1) (nth 0 (l2R E) 2)));
    first by rewrite l2R_nth.
  + by rewrite -!l2R_nth; exact: EH.
  by rewrite -!l2R_nth; exact: EL.
- by rewrite Eh01 El01; case: (XTwoProd (D2R x0) (D2R y1)).
by rewrite Ebh Ebl; case: (XFast2SumS (D2R x1) (D2R z01p)).
Qed.

(* ---------------------------------------------------------------------------*)
(*  The seed of Algorithm 15                                                  *)
(* ---------------------------------------------------------------------------*)

(* The paper's own names, at binary64.                                        *)
Notation XsqrtS := (sqrtS prec Dchoice).
Notation XsqrtA := (sqrtA prec Dchoice).
Notation XsqrtA' := (sqrtA' prec Dchoice).
Notation XsqrtH0_1 := (sqrtH0_1 prec Dchoice).
Notation XsqrtH11_1 := (sqrtH11_1 prec Dchoice).
Notation XsqrtH01_2 := (sqrtH01_2 prec Dchoice).
Notation XsqrtH11_2 := (sqrtH11_2 prec Dchoice).
Notation XsqrtH0_2 := (sqrtH0_2 prec Dchoice).
Notation XsqrtB01 := (sqrtB01 prec Dchoice).
Notation XsqrtB11 := (sqrtB11 prec Dchoice).
Notation XsqrtH1_1n := (sqrtH1_1n prec Dchoice).
Notation XsqrtH1_2n := (sqrtH1_2n prec Dchoice).
Notation XsqrtB12n := (sqrtB12n prec Dchoice).
Notation XsqrtBn := (sqrtBn prec Dchoice).
Notation XsqrtBWn := (sqrtBWn prec Dchoice).

(* The two operations `code/ddouble' did not need.                            *)
Lemma sqrt_X a : (Dnorm <= Rabs (R_sqrt.sqrt (D2R a)))%R ->
  D2R (PrimFloat.sqrt a) = Xrnd (R_sqrt.sqrt (D2R a)).
Proof. by move=> H; rewrite Dsqrt (Drnd_FLX _ H). Qed.

Lemma div_X a b : Dfin a -> (D2R b <> 0)%R -> Dfin (a / b)%float ->
  (Dnorm <= Rabs (D2R a / D2R b))%R ->
  D2R (a / b)%float = Xrnd (D2R a / D2R b).
Proof.
move=> Fa Nb Fd Hn.
by have [E _] := Dfin_div _ _ Fa Nb Fd; rewrite E (Drnd_FLX _ Hn).
Qed.

(* Halving is exact as long as it stays normal: the format is closed under a  *)
(* power of two and there is nothing left to round.                           *)
Lemma half_X a : Dfin a -> Dfin (a / 2)%float ->
  (Dnorm <= Rabs (D2R a / 2))%R -> D2R (a / 2)%float = (D2R a / 2)%R.
Proof.
move=> Fa Fd Hn.
have E2 : D2R 2%float = 2%R by rewrite /D2R; compute; lra.
have N2 : (D2R 2%float <> 0)%R by rewrite E2; lra.
rewrite (div_X _ _ Fa N2 Fd); last by rewrite E2.
have Hp2 : (1 < prec)%Z by [].
rewrite E2 round_generic //.
have -> : (D2R a / 2 = D2R a * bpow radix2 (-1))%R
  by rewrite /= /Z.pow_pos /=; lra.
by apply: ((format_scale Hp2 Dchoice (D2R a) (-1)).2); apply: Dformat_FLX.
Qed.

Lemma Dfin_onep4 : Dfin onep4.
Proof. by rewrite /Dfin /onep4; compute. Qed.

Lemma Dfin_three2 : Dfin three2.
Proof. by rewrite /Dfin /three2; compute. Qed.

(* The literals.                                                              *)
Lemma Donep4 : D2R onep4 = (1 + 4 * u prec radix2)%R.
Proof. by rewrite /D2R /onep4 (u_pow prec); compute; lra. Qed.

Lemma Dthree2 : D2R three2 = (3 / 2)%R.
Proof. by rewrite /D2R /three2; compute; lra. Qed.

(* What the transfer asks of the seed.  Every clause is a word being a        *)
(* number, or a product or a quotient being clear of the bottom of the        *)
(* range -- which is what the scaling is for.                                 *)
Definition sqrtBW_ok (x0 x1 : PrimFloat.float) : Prop :=
  let s := PrimFloat.sqrt x0 in
  let a := (onep4 / s)%float in
  let a' := (a / 2)%float in
  let h01_1 := dwhi (twoProd a x0) in
  let h11_1 := dwlo (twoProd a x0) in
  let h1_1 := (h11_1 + a * x1)%float in
  let h01_2 := dwhi (twoProd a' h01_1) in
  let h11_2 := dwlo (twoProd a' h01_1) in
  let h0_2 := (three2 - h01_2)%float in
  let h1_2 := (- (h11_2 + a' * h1_1))%float in
  let b01 := dwhi (twoProd a h0_2) in
  let b11 := dwlo (twoProd a h0_2) in
  let b12 := (b11 + a * h1_2)%float in
  [/\ Dfin x0, Dfin x1, (0 < D2R x0)%R, Dfin a & Dfin a']
  /\ [/\ (Dnorm <= Rabs (R_sqrt.sqrt (D2R x0)))%R,
         (D2R s <> 0)%R,
         (Dnorm <= Rabs (D2R onep4 / D2R s))%R
       & (Dnorm <= Rabs (D2R a / 2))%R]
  /\ [/\ Dfin h11_1, Dfin h11_2, Dfin b11, Dfin h0_2 & Dfin h1_2]
  /\ [/\ (Dprodlo <= Rabs (D2R a * D2R x0))%R,
         (Dprodlo <= Rabs (D2R a' * D2R h01_1))%R,
         (Dprodlo <= Rabs (D2R a * D2R h0_2))%R,
         (Dprodlo <= Rabs (D2R a * D2R x1))%R
       & (Dprodlo <= Rabs (D2R a' * D2R h1_1))%R]
  /\ (Dprodlo <= Rabs (D2R a * D2R h1_2))%R
  /\ [/\ Dfin (a * x1)%float, Dfin h1_1, Dfin (a' * h1_1)%float,
         Dfin (h11_2 + a' * h1_1)%float & Dfin (a * h1_2)%float]
  /\ Dfin b12
  /\ DfastTwoSumFin b01 b12.

Lemma sqrtBW_X x0 x1 :
  sqrtBW_ok x0 x1 ->
  tw2R (sqrtBW x0 x1) = XsqrtBWn (D2R x0) (D2R x1).
Proof.
rewrite /sqrtBW_ok
  => [] [[Fx0 Fx1 Hx0 Fa Fa'] [[Hs Ns Ha Ha']
        [[F11_1 F11_2 Fb11 F0_2 F1_2] [[P1 P2 P3 P4 P5]
          [P6 [[Max1 F1_1 Ma1 F21 Ma2] [Fb12 Hfast]]]]]]].
have Hp2 : (1 < prec)%Z by [].
have Hp11 : (11 <= prec)%Z by [].
(* the reciprocal and its half                                               *)
have Es : D2R (PrimFloat.sqrt x0) = XsqrtS (D2R x0) by apply: sqrt_X.
set s := PrimFloat.sqrt x0 in Ns Ha Fa Es *.
have Ea : D2R (onep4 / s)%float = XsqrtA (D2R x0).
  by rewrite (div_X _ _ Dfin_onep4 Ns Fa Ha) Donep4 Es.
set a := (onep4 / s)%float in Fa Fa' Ha' P1 P3 P4 P6 Max1 Ma2 Ea *.
have Ea' : D2R (a / 2)%float = XsqrtA' (D2R x0).
  by rewrite (half_X _ Fa Fa' Ha') Ea.
set a' := (a / 2)%float in Fa' P2 P5 Ma1 Ea' *.
(* the first two-product and the first split line                            *)
have [Eh01_1 Eh11_1] := twoProd_X _ _ F11_1 P1.
rewrite Ea in Eh01_1 Eh11_1.
set h01_1 := dwhi (twoProd a x0) in P2 Eh01_1 *.
set h11_1 := dwlo (twoProd a x0) in F11_1 Eh11_1 *.
have Eh1_1 : D2R (h11_1 + a * x1)%float = XsqrtH1_1n (D2R x0) (D2R x1).
  rewrite (add_X _ _ F11_1 Max1 F1_1) (mul_X _ _ Fa Fx1 Max1 P4) Ea Eh11_1.
  by rewrite /sqrtH1_1n.
set h1_1 := (h11_1 + a * x1)%float in F1_1 P5 Ma1 Eh1_1 *.
(* the second two-product, the exact subtraction and the second split line   *)
have [Eh01_2 Eh11_2] := twoProd_X _ _ F11_2 P2.
rewrite Ea' Eh01_1 in Eh01_2 Eh11_2.
set h01_2 := dwhi (twoProd a' h01_1) in Eh01_2 *.
set h11_2 := dwlo (twoProd a' h01_1) in F11_2 Eh11_2 *.
have F01_2 : Dfin h01_2 by have [_ [_ []]] := twoProd_hi _ _ F11_2.
have Eh0_2 : D2R (three2 - h01_2)%float = XsqrtH0_2 (D2R x0).
  rewrite (sub_X _ _ Dfin_three2 F01_2 F0_2) Dthree2 Eh01_2.
  by rewrite /sqrtH0_2 round_generic //;
     apply: (sqrtH0_2_exact Hp2 Hp11 Dchoice); [apply: Dformat_FLX | lra].
set h0_2 := (three2 - h01_2)%float in F0_2 P3 Eh0_2 *.
have Eh1_2 : D2R (- (h11_2 + a' * h1_1))%float = XsqrtH1_2n (D2R x0) (D2R x1).
  rewrite D2R_opp (add_X _ _ F11_2 Ma1 F21) (mul_X _ _ Fa' F1_1 Ma1 P5).
  by rewrite Ea' Eh11_2 Eh1_1 /sqrtH1_2n.
set h1_2 := (- (h11_2 + a' * h1_1))%float in F1_2 P6 Ma2 Eh1_2 *.
(* the third two-product and the last split line                             *)
have [Eb01 Eb11] := twoProd_X _ _ Fb11 P3.
rewrite Ea Eh0_2 in Eb01 Eb11.
set b01 := dwhi (twoProd a h0_2) in Eb01 *.
set b11 := dwlo (twoProd a h0_2) in Fb11 Eb11 *.
have Eb12 : D2R (b11 + a * h1_2)%float = XsqrtB12n (D2R x0) (D2R x1).
  rewrite (add_X _ _ Fb11 Ma2 Fb12) (mul_X _ _ Fa F1_2 Ma2 P6) Ea Eb11 Eh1_2.
  by rewrite /sqrtB12n.
set b12 := (b11 + a * h1_2)%float in Fb12 Hfast Eb12 *.
(* and the Fast2Sum that ends it                                             *)
have Fb01 : Dfin b01 by have [_ [_ []]] := twoProd_hi _ _ Fb11.
have [Ebh Ebl] := fastTwoSum_X _ _ Fb01 Fb12 Hfast.
rewrite Eb01 Eb12 in Ebh Ebl.
rewrite /sqrtBW -/s -/a -/a'.
rewrite (dwE (twoProd a x0)) -/h01_1 -/h11_1 -/h1_1.
rewrite (dwE (twoProd a' h01_1)) -/h01_2 -/h11_2 -/h0_2 -/h1_2.
rewrite (dwE (twoProd a h0_2)) -/b01 -/b11 -/b12.
rewrite (dwE (fastTwoSum b01 b12)).
rewrite /XsqrtBWn /sqrtBWn /sqrtBn /tw2R /=.
have E0 : D2R 0%float = 0%R by rewrite /D2R; compute; lra.
by rewrite Ebh Ebl E0.
Qed.

(* ---------------------------------------------------------------------------*)
(*  Algorithm 15                                                              *)
(* ---------------------------------------------------------------------------*)

Notation XThreeProdDWn := (ThreeProdDWn prec Dchoice).
Notation XThreeProdOneTWn := (ThreeProdOneTWn prec Dchoice).

(* Halving a triple word, word by word.                                      *)
Definition halfTw_ok (t : twfloat) : Prop :=
  let: TWFloat x0 x1 x2 := t in
  [/\ Dfin x0, Dfin x1 & Dfin x2]
  /\ [/\ Dfin (x0 / 2)%float, Dfin (x1 / 2)%float & Dfin (x2 / 2)%float]
  /\ [/\ (Dnorm <= Rabs (D2R x0 / 2))%R, (Dnorm <= Rabs (D2R x1 / 2))%R
       & (Dnorm <= Rabs (D2R x2 / 2))%R].

Lemma halfTw_X t : halfTw_ok t ->
  tw2R (halfTw t) = scaleTW (-1) (tw2R t).
Proof.
case: t => x0 x1 x2 [[F0 F1 F2] [[H0 H1 H2] [N0 N1 N2]]].
rewrite /halfTw /scaleTW /tw2R /=.
rewrite (half_X _ F0 H0 N0) (half_X _ F1 H1 N1) (half_X _ F2 H2 N2).
by congr TWR; rewrite /= /Z.pow_pos /=; lra.
Qed.

(* Three halves less a triple word: exact on the leading word by Sterbenz,   *)
(* and a negation on the other two.                                         *)
Definition sub32Tw_ok (t : twfloat) : Prop :=
  let: TWFloat x0 x1 x2 := t in
  [/\ Dfin x0, Dfin x1, Dfin x2, Dfin (three2 - x0)%float
    & (3 / 4 <= D2R x0 <= 3)%R].

Lemma sub32Tw_X t : sub32Tw_ok t -> tw2R (sub32Tw t) = sub32TW (tw2R t).
Proof.
case: t => x0 x1 x2 [F0 F1 F2 Fs Hr].
have Hp0 : Prec_gt_0 prec by [].
have Ve : Valid_exp Dfexp by rewrite DfexpE; apply: FLT_exp_valid.
have Mo : Monotone_exp Dfexp by rewrite DfexpE; apply: FLT_exp_monotone.
have F32 : generic_format radix2 Dfexp (3 / 2)%R
  by rewrite -Dthree2; apply: Dformat.
have Fe : generic_format radix2 Dfexp (3 / 2 - D2R x0)%R.
  by apply: (Sterbenz.sterbenz radix2 Dfexp) => //; [apply: Dformat | lra].
have [E _] := Dfin_sub _ _ Dfin_three2 F0 Fs.
rewrite /sub32Tw /sub32TW /tw2R /=.
by rewrite E Dthree2 round_generic // !D2R_opp.
Qed.

(* The two products, stated on a triple word rather than on three words.     *)
Lemma threeProdDW_XT (X Y : twfloat) :
  prodDW_ok (tw0 X) (tw1 X) (tw0 Y) (tw1 Y) (tw2 Y) ->
  tw2R (threeProdDW X Y) = XThreeProdDWn (tw2R X) (tw2R Y).
Proof.
by case: X => x0 x1 x2; case: Y => y0 y1 y2; apply: threeProdDW_X.
Qed.

Lemma threeProdOneTW_XT (X Y : twfloat) :
  prodOne_ok (tw0 X) (tw1 X) (tw2 X) (tw1 Y) (tw2 Y) ->
  tw2R (threeProdOneTW X Y) = XThreeProdOneTWn (tw2R X) (tw2R Y).
Proof.
by case: X => x0 x1 x2; case: Y => y0 y1 y2; apply: threeProdOneTW_X.
Qed.

(* What the whole of Algorithm 15 asks.  Every clause is one of the three     *)
(* above, at the argument the algorithm gives it.                             *)
Definition sqrt_ok (x : twfloat) : Prop :=
  let bw := sqrtBW (tw0 x) (tw1 x) in
  let i1 := threeProdDW bw x in
  let hb := halfTw bw in
  let p2 := threeProdDW hb i1 in
  let s2 := sub32Tw p2 in
  sqrtBW_ok (tw0 x) (tw1 x)
  /\ prodDW_ok (tw0 bw) (tw1 bw) (tw0 x) (tw1 x) (tw2 x)
  /\ halfTw_ok bw
  /\ prodDW_ok (tw0 hb) (tw1 hb) (tw0 i1) (tw1 i1) (tw2 i1)
  /\ sub32Tw_ok p2
  /\ prodOne_ok (tw0 i1) (tw1 i1) (tw2 i1) (tw1 s2) (tw2 s2).

(* AND THE WHOLE OF ALGORITHM 15 CROSSES.                                     *)
Lemma threeSqRt_X x : sqrt_ok x ->
  tw2R (threeSqRt x) = ThreeSqRtNn prec Dchoice (tw2R x).
Proof.
rewrite /sqrt_ok /threeSqRt /ThreeSqRtNn /ThreeSqRtAuxN
  => [] [Hseed [Hp1 [Hhalf [Hp2 Hrest]]]].
have [Hsub Hp3] := Hrest.
have Ebw : tw2R (sqrtBW (tw0 x) (tw1 x))
         = XsqrtBWn (D2R (tw0 x)) (D2R (tw1 x)) by apply: sqrtBW_X.
rewrite (threeProdOneTW_XT _ _ Hp3) (sub32Tw_X _ Hsub)
        (threeProdDW_XT _ _ Hp2) (halfTw_X _ Hhalf)
        (threeProdDW_XT _ _ Hp1) Ebw.
by case: x {Hseed Hp1 Hhalf Hp2 Hsub Hp3 Hrest Ebw}.
Qed.

(* ---------------------------------------------------------------------------*)
(*  What Algorithm 15 is out by, on primitive floats                          *)
(* ---------------------------------------------------------------------------*)

Notation Xu := (u prec radix2).

Lemma Dchoice_te : ties_to_even Dchoice.
Proof. by []. Qed.

Lemma Dchoice_sym : forall x : Z, Dchoice x = ~~ Dchoice (- (x + 1))%Z.
Proof.
move=> x /=; rewrite Z.even_opp Z.even_add /=.
by case: (Z.even x).
Qed.

(* THE ROOT'S ERROR, READ BACK.  `ThreeSqRtNn_error' says the algorithm is    *)
(* out by `31u^3 + 22500u^4' of the root; `threeSqRt_X' says the primitive    *)
(* floats compute it; so this is the two put together, with `sqrt_ok' the     *)
(* only thing left to pay for.                                                *)
Theorem threeSqRt_error x :
  sqrt_ok x -> isTW prec (tw2R x) -> (0 < D2R (tw0 x))%R ->
  (Rabs (twval (threeSqRt x) - R_sqrt.sqrt (twval x))
     <= (31 * (Xu * Xu * Xu) + 22500 * (Xu * Xu * Xu * Xu))
        * Rabs (R_sqrt.sqrt (twval x)))%R.
Proof.
move=> Hok Hx Hx0.
have Hp2 : (1 < prec)%Z by [].
have Hp11 : (11 <= prec)%Z by [].
have Ht0 : TWR.tw0 (tw2R x) = D2R (tw0 x) by case: x {Hok Hx Hx0}.
have H := ThreeSqRtNn_error Hp2 Hp11 Dchoice_sym Dchoice_te Hx
            (ltac:(by rewrite Ht0) : (0 < TWR.tw0 (tw2R x))%R).
rewrite -!TWval_tw2R (threeSqRt_X _ Hok).
exact: H.
Qed.

(* AND WHAT THE STEP HAS TO BE.  `31u^3' is `31 * 2^-159', which is           *)
(* `3.875 * 2^-156' -- so the measured `kscale = 2^-156' does not cover the   *)
(* proved bound, and `2^-154' does, with three per cent to spare.  The        *)
(* measurement said 2.3 units of the last place and the proof says 3.9, so    *)
(* the two are within a factor of two of each other; the bits are the price   *)
(* of the proof, not of the algorithm.                                        *)
Lemma kscale_needed :
  (31 * (Xu * Xu * Xu) + 22500 * (Xu * Xu * Xu * Xu)
     <= bpow radix2 (-154))%R.
Proof.
have -> : Xu = bpow radix2 (-53) by rewrite (u_pow prec).
rewrite /bpow /= /Z.pow_pos /=; lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  And `kstep_sqrt' itself, where the guard holds                            *)
(* ---------------------------------------------------------------------------*)

Lemma Dkscale : D2R kscale = bpow radix2 (-154).
Proof. by rewrite /D2R /kscale; compute; lra. Qed.

Lemma DnormLo : D2R tw_updn.normLo = bpow radix2 (-900).
Proof. by rewrite /D2R /tw_updn.normLo; compute; lra. Qed.

Lemma Dltb a b : Dfin a -> Dfin b -> (a <? b)%float = true ->
  (D2R a < D2R b)%R.
Proof.
rewrite /Dfin /D2R ltb_equiv => Fa Fb.
rewrite (Bltb_correct _ _ _ _ Fa Fb).
by case: Rlt_bool_spec.
Qed.

(* THE LEADING WORD CARRIES ALL BUT A UNIT ROUNDOFF OF THE VALUE.             *)
(*                                                                            *)
(* `wellFormed' says the second word is at most half an `ulp' of the first    *)
(* and the third at most half the second.  Above the smallest normal number   *)
(* an `ulp' is at most `2u' of what it is an `ulp' of, so the two together    *)
(* come to `1.5u' of the leading word and no more.                            *)
Lemma wellFormed_lead_tight t : finL (tw2l t) -> wellFormed t = true ->
  (Dnorm <= Rabs (D2R (tw0 t)))%R ->
  (Rabs (twval t)
     <= (1 + 3 / 2 * bpow radix2 (-52)) * Rabs (D2R (tw0 t)))%R.
Proof.
case: t => x0 x1 x2 [F0 [F1 [F2 _]]].
rewrite /wellFormed => /andb_prop [E1 E2] Hn.
rewrite /tw0 in Hn.
have Hp0 : Prec_gt_0 prec by [].
have H1 := wellFormedP x0 x1 F0 F1 E1.
have H2 := wellFormed_half x1 x2 F1 F2 E2.
have Hu1 : (ulp radix2 Dfexp (D2R x0) <= Rabs (D2R x0) * bpow radix2 (-52))%R.
  have -> : (-52 = 1 - prec)%Z by [].
  by apply: ulp_FLT_le.
have Hb := bpow_gt_0 radix2 (-52).
have Hx0 := Rabs_pos (D2R x0).
have Hx1 := Rabs_pos (D2R x1).
have HX : (0 <= Rabs (D2R x0) * bpow radix2 (-52))%R by nra.
have Hx1b : (Rabs (D2R x1)
             <= / 2 * (Rabs (D2R x0) * bpow radix2 (-52)))%R by lra.
have Hx2b : (Rabs (D2R x2)
             <= / 4 * (Rabs (D2R x0) * bpow radix2 (-52)))%R by lra.
have T := Rabs_triang (D2R x0 + D2R x1) (D2R x2).
have T2 := Rabs_triang (D2R x0) (D2R x1).
rewrite /twval /tw0 /tw1 /tw2; lra.
Qed.


(* ---------------------------------------------------------------------------*)
(*  A well-formed triple of floats is the paper's triple word                  *)
(* ---------------------------------------------------------------------------*)

(* Above the smallest normal number the bounded format's `ulp' is the          *)
(* unbounded one's: the exponent floor does not bite.                          *)
Lemma ulp_FLT_FLX y : (Dnorm <= Rabs y)%R ->
  ulp radix2 Dfexp y = ulp radix2 (FLX_exp prec) y.
Proof.
move=> Hn.
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have Hy0 : y <> 0%R.
  by move=> Hz; move: Hn; rewrite Hz Rabs_R0; lra.
rewrite !ulp_neq_0 // /cexp DfexpE /FLT_exp /FLX_exp.
have Hm : (SpecFloat.emin prec emax + prec <= mag radix2 y)%Z.
  by apply: mag_ge_bpow.
by congr bpow; lia.
Qed.

(* `wellFormed' is the paper's `isTW', once both the first and the second      *)
(* word are clear of the bottom of the range -- and a zero second word         *)
(* forces a zero third, so that case needs nothing.                            *)
Lemma wellFormed_isTW t : finL (tw2l t) -> wellFormed t = true ->
  (Dnorm <= Rabs (D2R (tw0 t)))%R ->
  (D2R (tw1 t) = 0%R \/ (Dnorm <= Rabs (D2R (tw1 t)))%R) ->
  isTW prec (tw2R t).
Proof.
case: t => x0 x1 x2 [F0 [F1 [F2 _]]].
rewrite /wellFormed => /andb_prop [E1 E2] Hn0 Hn1.
rewrite /tw0 in Hn0; rewrite /tw1 in Hn1.
rewrite /tw2R /tw0 /tw1 /tw2.
have Hp0 : Prec_gt_0 prec by [].
have H1 := wellFormedP x0 x1 F0 F1 E1.
have H2 := wellFormedP x1 x2 F1 F2 E2.
have Hu0 : (0 < ulp radix2 (FLX_exp prec) (D2R x0))%R.
  rewrite -(ulp_FLT_FLX _ Hn0) ulp_neq_0; first by apply: bpow_gt_0.
  have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
  by move: Hn0; split_Rabs; lra.
split; try exact: Dformat_FLX.
- right; rewrite -(ulp_FLT_FLX _ Hn0).
  have Hp := ulp_ge_0 radix2 Dfexp (D2R x0).
  have Hq : (0 < ulp radix2 Dfexp (D2R x0))%R
    by rewrite (ulp_FLT_FLX _ Hn0).
  by lra.
case: Hn1 => [Hz|Hn1]; last first.
  right; rewrite -(ulp_FLT_FLX _ Hn1).
  have Hq : (0 < ulp radix2 Dfexp (D2R x1))%R.
    rewrite ulp_neq_0; first by apply: bpow_gt_0.
    have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
    by move: Hn1; split_Rabs; lra.
  by lra.
left; move: H2; rewrite Hz ulp_FLT_0 // => H2.
have Hs := Dfin_wf _ _ F1 E2.
have [Es _] := Dfin_add _ _ F1 F2 Hs.
have Eq := D2R_wf _ _ F1 F2 E2.
move: Eq; rewrite Es Hz Rplus_0_l => Eq.
by rewrite -Eq round_generic //; apply: Dformat.
Qed.

(* WHAT THE STEP HAS TO COVER, AND DOES.                                      *)
(*                                                                            *)
(* The root is out by `31u^3' of the answer and the step is `2^-154' of the   *)
(* leading word.  `31u^3' is `0.96875 * 2^-154', and the leading word is all  *)
(* but `1.5u' of the answer, so the one clears the other with three per cent  *)
(* to spare.  That three per cent is the whole of the margin: at the measured *)
(* `2^-156' it would have been a factor of four the wrong way.                *)
Theorem kstep_sqrt_ok x :
  finL (tw2l x) -> wellFormed x = true -> (0 < twval x)%R ->
  (Dnorm <= Rabs (D2R (tw0 x)))%R ->
  (D2R (tw1 x) = 0%R \/ (Dnorm <= Rabs (D2R (tw1 x)))%R) ->
  sqrt_ok x ->
  finL (tw2l (threeSqRt x)) -> wellFormed (threeSqRt x) = true ->
  (tw_updn.normLo <? abs (tw0 (threeSqRt x)))%float = true ->
  Dfin (kscale * abs (tw0 (threeSqRt x)))%float ->
  Dfin (dw_updn.mulUpFp kscale (abs (tw0 (threeSqRt x)))) ->
  (Rabs (twval (threeSqRt x) - R_sqrt.sqrt (twval x))
     <= D2R (kstep (threeSqRt x)))%R.
Proof.
move=> Fx Wx Hx0 Hnx0 Hnx1 Hok Fr Wr Hlo Fm Fu.
have Hx := wellFormed_isTW _ Fx Wx Hnx0 Hnx1.
have Hx0' : (0 < D2R (tw0 x))%R.
  have Hq := wellFormed_lead34 _ Fx Wx.
  by move: Hq Hx0; rewrite /twval; split_Rabs; lra.
have Herr := threeSqRt_error _ Hok Hx Hx0'.
set r := threeSqRt x in Fr Wr Hlo Fm Fu Herr *.
have Fr0 : Dfin (tw0 r).
  by move: Fr; rewrite /tw2l; case: (r) => r0 r1 r2 [].
have Far0 : Dfin (abs (tw0 r)) by apply: Dfin_abs.
have Fk : Dfin kscale by rewrite /Dfin /kscale; compute.
(* the step, read as a number *)
have Estep : D2R (kstep r) = D2R (dw_updn.mulUpFp kscale (abs (tw0 r))).
  by move: Hlo; rewrite /kstep; case: (r) => r0 r1 r2 /= ->.
have Hge : (bpow radix2 (-154) * Rabs (D2R (tw0 r)) <= D2R (kstep r))%R.
  rewrite Estep -Dkscale -D2R_abs.
  by apply: dwbound.mulUpFp_ge.
(* the leading word carries the value *)
have Hn : (Dnorm <= Rabs (D2R (tw0 r)))%R.
  have Hn1 : (D2R tw_updn.normLo < Rabs (D2R (tw0 r)))%R
    by rewrite -D2R_abs; apply: Dltb.
  move: Hn1; rewrite DnormLo => Hn1.
  apply: Rle_trans (Rlt_le _ _ Hn1).
  by apply: bpow_le; rewrite /SpecFloat.emin /=; lia.
have Hlead := wellFormed_lead_tight _ Fr Wr Hn.
(* and the arithmetic *)
have Hs : (0 < R_sqrt.sqrt (twval x))%R by apply: sqrt_lt_R0.
have Hsa : Rabs (R_sqrt.sqrt (twval x)) = R_sqrt.sqrt (twval x)
  by apply: Rabs_pos_eq; lra.
rewrite Hsa in Herr.
have Hv : (R_sqrt.sqrt (twval x) * (1 - (31 * (Xu * Xu * Xu)
             + 22500 * (Xu * Xu * Xu * Xu))) <= Rabs (twval r))%R.
  have T := Rabs_triang_inv (twval r) (R_sqrt.sqrt (twval x)).
  have T2 : (Rabs (R_sqrt.sqrt (twval x)) - Rabs (twval r)
             <= Rabs (twval r - R_sqrt.sqrt (twval x)))%R
    by move: T; rewrite Rabs_minus_sym; split_Rabs; lra.
  by move: T2; rewrite Hsa; lra.
have Eu : Xu = bpow radix2 (-53) by rewrite (u_pow prec).
have H52 : bpow radix2 (-52) = (2 * bpow radix2 (-53))%R.
  have -> : (2 = bpow radix2 1)%R by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -bpow_plus.
have H154 : bpow radix2 (-154) = (32 * (bpow radix2 (-53)
             * (bpow radix2 (-53) * bpow radix2 (-53))))%R.
  have -> : (32 = bpow radix2 5)%R by rewrite /= /Z.pow_pos /=; lra.
  by rewrite -!bpow_plus.
have Hb53 : (0 < bpow radix2 (-53))%R by apply: bpow_gt_0.
have Hb53s : (bpow radix2 (-53) <= / 1048576)%R.
  have -> : (/ 1048576 = bpow radix2 (-20))%R
    by rewrite /= /Z.pow_pos /=; lra.
  by apply: bpow_le; lia.
have Hr0 := Rabs_pos (D2R (tw0 r)).
move: Herr Hlead Hv Hge; rewrite Eu H52 H154.
set w := bpow radix2 (-53) in Hb53 Hb53s *.
set S := R_sqrt.sqrt (twval x) in Hs *.
set R0 := Rabs (D2R (tw0 r)) in Hr0 *.
move=> Herr Hlead Hv Hge.
set V := Rabs (twval r) in Hlead Hv *.
set E := (31 * (w * w * w) + 22500 * (w * w * w * w))%R in Herr Hv *.
have Ht : (0 <= w * w * w)%R by nra.
have Ht4 : (0 <= w * w * w * w)%R by nra.
have Hw2 : (w * w <= / 1048576 * w)%R by nra.
have Hw3 : (w * w * w <= / 1048576 * (w * w))%R by nra.
have Hw4 : (w * w * w * w <= / 1048576 * (w * w * w))%R by nra.
have HE0 : (0 <= E)%R by rewrite /E; lra.
have HEu : (E <= 311 / 10 * (w * w * w))%R by rewrite /E; lra.
have HEs : (E <= 1 / 100)%R by lra.
have HE1 : (0 < 1 - E)%R by lra.
(* the scalar margin: 31 against 32, and what the 1.5u of the leading word   *)
(* and the E of the answer take off it.                                      *)
have Hscal : (E * (1 + 3 * w) <= 32 * (w * w * w) * (1 - E))%R.
  have H1 : (E * (1 + 3 * w) <= 311 / 10 * (w * w * w) * (1 + 3 * w))%R
    by nra.
  have H2 : (311 / 10 * (w * w * w) * (1 + 3 * w)
             <= 32 * (w * w * w) * (99 / 100))%R by nra.
  have H3 : (32 * (w * w * w) * (99 / 100) <= 32 * (w * w * w) * (1 - E))%R
    by nra.
  lra.
have Hchain : (S * (1 - E) <= (1 + 3 * w) * R0)%R by lra.
have Hstep1 : (E * (S * (1 - E)) <= E * ((1 + 3 * w) * R0))%R by nra.
have Hstep2 : (E * ((1 + 3 * w) * R0) <= 32 * (w * w * w) * (1 - E) * R0)%R
  by nra.
have Hfin : (E * S <= 32 * (w * w * w) * R0)%R by nra.
lra.
Qed.

(* ---------------------------------------------------------------------------*)
(*  The guard, as a test                                                      *)
(* ---------------------------------------------------------------------------*)

(* `sqrt_ok' is a conjunction of two kinds of clause: a word being a number,  *)
(* and a value being clear of a line.  Both are testable -- the first because *)
(* a number less itself is nought and nothing else is, the second because     *)
(* rounding is monotone and the line is a float, so a ROUNDED value above the *)
(* line has its exact value above it too.  This is what the double-word       *)
(* development's `divOk' and `sqrtOk' do, clause for clause.                  *)

Definition tnorm := Eval compute in 0x1p-1022%float.

Lemma D2R_tnorm : D2R tnorm = Dnorm.
Proof. by rewrite /D2R /tnorm; compute; lra. Qed.

Lemma Dfin_tnorm : Dfin tnorm.
Proof. by []. Qed.

Lemma fexp_normT : (Dfexp (SpecFloat.emin prec emax + prec - 1 + 1)
                    <= SpecFloat.emin prec emax + prec - 1)%Z.
Proof. by vm_compute. Qed.

Lemma DnormT_of_rnd r : (Dnorm < Rabs (Drnd r))%R -> (Dnorm <= Rabs r)%R.
Proof. by apply: Dbpow_of_rnd fexp_normT. Qed.

(* A number at all. *)
Definition finF (a : PrimFloat.float) := (a - a =? 0)%float.

Lemma finFP a : finF a = true -> Dfin a.
Proof.
by move=> /Dfin_eqb0 [Fa _]; have [H _] := Dfin_subI _ _ Fa.
Qed.

(* Above the smallest normal number. *)
Definition normF (a : PrimFloat.float) := (tnorm <? abs a)%float.

Lemma normFP a : Dfin a -> normF a = true -> (Dnorm < Rabs (D2R a))%R.
Proof.
move=> Fa H.
rewrite -D2R_abs -D2R_tnorm.
by apply: Dltb; [exact: Dfin_tnorm | exact: Dfin_abs | exact: H].
Qed.

(* Above the line where the two formats round a product alike. *)
Definition prodF (a : PrimFloat.float) := (dw_updn.dprodlo <? abs a)%float.

Lemma prodFP a : Dfin a -> prodF a = true -> (Dprodlo < Rabs (D2R a))%R.
Proof.
move=> Fa H.
rewrite -D2R_abs -D2R_dprodlo.
by apply: Dltb; [exact: Dfin_dprodlo | exact: Dfin_abs | exact: H].
Qed.

(* The three shapes the range clauses come in.                               *)
Lemma prod_rng a b : Dfin a -> Dfin b -> Dfin (a * b)%float ->
  prodF (a * b)%float = true -> (Dprodlo <= Rabs (D2R a * D2R b))%R.
Proof.
move=> Fa Fb Fs H.
have [E _] := Dfin_mul _ _ Fa Fb Fs.
by apply: Dprodlo_of_rnd; rewrite -E; apply: prodFP.
Qed.

Lemma div_rng a b : Dfin a -> (D2R b <> 0)%R -> Dfin (a / b)%float ->
  normF (a / b)%float = true -> (Dnorm <= Rabs (D2R a / D2R b))%R.
Proof.
move=> Fa Nb Fs H.
have [E _] := Dfin_div _ _ Fa Nb Fs.
by apply: DnormT_of_rnd; rewrite -E; apply: normFP.
Qed.

Lemma sqrt_rng a : Dfin (PrimFloat.sqrt a) ->
  normF (PrimFloat.sqrt a) = true ->
  (Dnorm <= Rabs (R_sqrt.sqrt (D2R a)))%R.
Proof.
move=> Fs H.
by apply: DnormT_of_rnd; rewrite -Dsqrt; apply: normFP.
Qed.

(* Halving, and three halves less a triple word.                              *)
Definition halfTw_okb (t : twfloat) : bool :=
  let: TWFloat x0 x1 x2 := t in
  [&& finF x0, finF x1, finF x2, finF (x0 / 2)%float & finF (x1 / 2)%float]
  && [&& finF (x2 / 2)%float, normF (x0 / 2)%float, normF (x1 / 2)%float
       & normF (x2 / 2)%float].

Definition sub32Tw_okb (t : twfloat) : bool :=
  let: TWFloat x0 x1 x2 := t in
  [&& finF x0, finF x1, finF x2, finF (three2 - x0)%float
    & ((3 / 4 <=? x0) && (x0 <=? 3))%float].

Lemma half_rng a : Dfin a -> Dfin (a / 2)%float ->
  normF (a / 2)%float = true -> (Dnorm <= Rabs (D2R a / 2))%R.
Proof.
move=> Fa Fs H.
have E2 : D2R 2%float = 2%R by rewrite /D2R; compute; lra.
have N2 : (D2R 2%float <> 0)%R by rewrite E2; lra.
have [E _] := Dfin_div _ _ Fa N2 Fs.
by apply: DnormT_of_rnd; rewrite -E2 -E; apply: normFP.
Qed.

Lemma halfTw_okbP t : halfTw_okb t = true -> halfTw_ok t.
Proof.
case: t => x0 x1 x2 /andP[/and5P[H0 H1 H2 H3 H4] /and4P[H5 H6 H7 H8]].
have F0 := finFP _ H0; have F1 := finFP _ H1; have F2 := finFP _ H2.
have G0 := finFP _ H3; have G1 := finFP _ H4; have G2 := finFP _ H5.
split; first by split.
split; first by split.
by split; [apply: half_rng | apply: half_rng | apply: half_rng].
Qed.

Lemma sub32Tw_okbP t : sub32Tw_okb t = true -> sub32Tw_ok t.
Proof.
case: t => x0 x1 x2 /and5P[H0 H1 H2 H3 /andP[Hl Hh]].
have F0 := finFP _ H0; have F1 := finFP _ H1; have F2 := finFP _ H2.
have Fs := finFP _ H3.
have E34 : D2R (3 / 4)%float = (3 / 4)%R by rewrite /D2R; compute; lra.
have E3 : D2R 3%float = 3%R by rewrite /D2R; compute; lra.
have F34 : Dfin (3 / 4)%float by [].
have F3 : Dfin 3%float by [].
split => //; split.
- by rewrite -E34; apply: Dleb.
by rewrite -E3; apply: Dleb.
Qed.


Definition fastTwoSumOkb (a b : PrimFloat.float) : bool :=
  [&& finF (a + b)%float, finF ((a + b) - a)%float
    & finF (b - ((a + b) - a))%float].

Lemma fastTwoSumOkbP a b : fastTwoSumOkb a b = true -> DfastTwoSumFin a b.
Proof.
by move=> /and3P[H1 H2 H3]; split; [|split]; apply: finFP.
Qed.

Definition fast2SumSOkb (a b : PrimFloat.float) : bool :=
  if (abs b <=? abs a)%float then fastTwoSumOkb a b else fastTwoSumOkb b a.

Lemma fast2SumSOkbP a b : fast2SumSOkb a b = true -> Dfast2SumSFin a b.
Proof.
rewrite /fast2SumSOkb /Dfast2SumSFin.
by case: (abs b <=? abs a)%float => H; apply: fastTwoSumOkbP.
Qed.

Definition finLb (l : seq PrimFloat.float) : bool := all finF l.

Lemma finLbP l : finLb l = true -> finL l.
Proof.
by elim: l => [|a l IH] //= /andP[Ha Hl]; split; [apply: finFP | apply: IH].
Qed.

(* Algorithm 11's guard.                                                      *)
Definition prodDW_okb (x0 x1 y0 y1 y2 : PrimFloat.float) : bool :=
  let b := vecSum [:: dwlo (twoProd x0 y0); dwhi (twoProd x0 y1);
                      dwhi (twoProd x1 y0)] in
  let e := vecSum [:: dwhi (twoProd x0 y0); nth 0%float b 0; nth 0%float b 1;
                      (nth 0%float b 2 + x1 * y1)%float;
                      ((dwlo (twoProd x1 y0) + x0 * y2)
                        + dwlo (twoProd x0 y1))%float] in
  [&& finF x0, finF x1, finF y0, finF y1 & finF y2]
  && [&& finF (dwlo (twoProd x0 y0)), finF (dwlo (twoProd x0 y1))
       & finF (dwlo (twoProd x1 y0))]
  && [&& finF (x0 * y0)%float, finF (x0 * y1)%float, finF (x1 * y0)%float,
         finF (x1 * y1)%float & finF (x0 * y2)%float]
  && [&& prodF (x0 * y0)%float, prodF (x0 * y1)%float, prodF (x1 * y0)%float,
         prodF (x1 * y1)%float & prodF (x0 * y2)%float]
  && [&& finF (nth 0%float b 2 + x1 * y1)%float,
         finF (dwlo (twoProd x1 y0) + x0 * y2)%float
       & finF ((dwlo (twoProd x1 y0) + x0 * y2)
               + dwlo (twoProd x0 y1))%float]
  && [&& finLb b, finLb e
       & finLb (vseb [:: nth 0%float e 1; nth 0%float e 2;
                         nth 0%float e 3; nth 0%float e 4])].

Lemma prodDW_okbP x0 x1 y0 y1 y2 :
  prodDW_okb x0 x1 y0 y1 y2 = true -> prodDW_ok x0 x1 y0 y1 y2.
Proof.
move=> /andP[/andP[/andP[/andP[/andP[/and5P[A0 A1 A2 A3 A4]
        /and3P[B0 B1 B2]] /and5P[C0 C1 C2 C3 C4]]
        /and5P[D0 D1 D2 D3 D4]] /and3P[E0 E1 E2]] /and3P[G0 G1 G2]].
have Fx0 := finFP _ A0; have Fx1 := finFP _ A1.
have Fy0 := finFP _ A2; have Fy1 := finFP _ A3; have Fy2 := finFP _ A4.
have M00 := finFP _ C0; have M01 := finFP _ C1; have M10 := finFP _ C2.
have M11 := finFP _ C3; have M02 := finFP _ C4.
split; first by split.
split; first by split; apply: finFP.
split.
  by split; apply: prod_rng => //; apply: finFP.
split.
  by split; apply: prod_rng => //; apply: finFP.
split.
  by split; apply: finFP.
split; first by apply: finLbP.
by split; apply: finLbP.
Qed.

(* Algorithm 20's.                                                            *)
Definition prodOne_okb (x0 x1 x2 y1 y2 : PrimFloat.float) : bool :=
  let z01p := dwhi (twoProd x0 y1) in
  let z01m := dwlo (twoProd x0 y1) in
  let bh := dwhi (fast2SumS x1 z01p) in
  let bl := dwlo (fast2SumS x1 z01p) in
  let z31 := (z01m + x1 * y1)%float in
  let z3 := (z31 + x0 * y2)%float in
  let s3 := (bl + z3)%float in
  let e := vecSum [:: x0; bh; (s3 + x2)%float] in
  [&& finF x0, finF x1, finF x2, finF y1 & finF y2]
  && [&& finF z01p, finF z01m, finF bh & finF bl]
  && [&& finF (x0 * y1)%float, finF (x1 * y1)%float & finF (x0 * y2)%float]
  && [&& prodF (x0 * y1)%float, prodF (x1 * y1)%float & prodF (x0 * y2)%float]
  && fast2SumSOkb x1 z01p
  && [&& finF z31, finF z3, finF s3 & finF (s3 + x2)%float]
  && finLb e
  && fast2SumSOkb (nth 0%float e 1) (nth 0%float e 2).

Lemma prodOne_okbP x0 x1 x2 y1 y2 :
  prodOne_okb x0 x1 x2 y1 y2 = true -> prodOne_ok x0 x1 x2 y1 y2.
Proof.
move=> /andP[/andP[/andP[/andP[/andP[/andP[/andP[/and5P[A0 A1 A2 A3 A4]
        /and4P[B0 B1 B2 B3]] /and3P[C0 C1 C2]] /and3P[D0 D1 D2]] Hb]
        /and4P[E0 E1 E2 E3]] Hfl] Hlast].
have Fx0 := finFP _ A0; have Fx1 := finFP _ A1; have Fx2 := finFP _ A2.
have Fy1 := finFP _ A3; have Fy2 := finFP _ A4.
have M01 := finFP _ C0; have M11 := finFP _ C1; have M02 := finFP _ C2.
split; first by split.
split; first by split; apply: finFP.
split.
  by split; apply: prod_rng.
split; first by apply: fast2SumSOkbP.
split; first by split; apply: finFP.
split; first by apply: finFP.
split; first by apply: finLbP.
by apply: fast2SumSOkbP.
Qed.

(* The seed's.                                                                *)
Definition sqrtBW_okb (x0 x1 : PrimFloat.float) : bool :=
  let s := PrimFloat.sqrt x0 in
  let a := (onep4 / s)%float in
  let a' := (a / 2)%float in
  let h01_1 := dwhi (twoProd a x0) in
  let h11_1 := dwlo (twoProd a x0) in
  let h1_1 := (h11_1 + a * x1)%float in
  let h01_2 := dwhi (twoProd a' h01_1) in
  let h11_2 := dwlo (twoProd a' h01_1) in
  let h0_2 := (three2 - h01_2)%float in
  let h1_2 := (- (h11_2 + a' * h1_1))%float in
  let b01 := dwhi (twoProd a h0_2) in
  let b11 := dwlo (twoProd a h0_2) in
  let b12 := (b11 + a * h1_2)%float in
  [&& finF x0, finF x1, (0 <? x0)%float, finF a & finF a']
  && [&& normF s, normF a & normF a']
  && [&& finF s, finF h11_1, finF h11_2, finF b11 & finF h0_2]
  && [&& finF h1_2, finF (a * x0)%float, finF (a' * h01_1)%float,
         finF (a * h0_2)%float & finF (a * x1)%float]
  && [&& finF (a' * h1_1)%float, finF (a * h1_2)%float, finF h1_1,
         finF (h11_2 + a' * h1_1)%float & finF b12]
  && [&& prodF (a * x0)%float, prodF (a' * h01_1)%float,
         prodF (a * h0_2)%float, prodF (a * x1)%float
       & prodF (a' * h1_1)%float]
  && prodF (a * h1_2)%float
  && fastTwoSumOkb b01 b12.

Lemma sqrtBW_okbP x0 x1 : sqrtBW_okb x0 x1 = true -> sqrtBW_ok x0 x1.
Proof.
move=> /andP[/andP[/andP[/andP[/andP[/andP[/andP[/and5P[A0 A1 A2 A3 A4]
        /and3P[N0 N1 N2]] /and5P[B0 B1 B2 B3 B4]]
        /and5P[C0 C1 C2 C3 C4]] /and5P[D0 D1 D2 D3 D4]]
        /and5P[P0 P1 P2 P3 P4]] P5] Hfast].
have Fx0 := finFP _ A0; have Fx1 := finFP _ A1.
have Fa := finFP _ A3; have Fa' := finFP _ A4.
have Fs := finFP _ B0.
have Hs := normFP _ Fs N0.
have Hp := bpow_gt_0 radix2 (SpecFloat.emin prec emax + prec - 1).
have Ns : (D2R (PrimFloat.sqrt x0) <> 0)%R by move: Hs; split_Rabs; lra.
have Hx0 : (0 < D2R x0)%R.
  have E0 : D2R 0%float = 0%R by rewrite /D2R; compute; lra.
  by rewrite -E0; apply: Dltb.
have Fo4 : Dfin onep4 by apply: Dfin_onep4.
split; first by split.
split.
  split.
  - by apply: sqrt_rng.
  - exact: Ns.
  - by apply: div_rng.
  by apply: half_rng.
split; first by split; apply: finFP.
split.
  by split; apply: prod_rng => //; apply: finFP.
split.
  by apply: prod_rng => //; apply: finFP.
split; first by split; apply: finFP.
split; first by apply: finFP.
by apply: fastTwoSumOkbP.
Qed.

(* And the whole of Algorithm 15's.                                           *)
Definition sqrt_okb (x : twfloat) : bool :=
  let bw := sqrtBW (tw0 x) (tw1 x) in
  let i1 := threeProdDW bw x in
  let hb := halfTw bw in
  let p2 := threeProdDW hb i1 in
  let s2 := sub32Tw p2 in
  [&& sqrtBW_okb (tw0 x) (tw1 x),
      prodDW_okb (tw0 bw) (tw1 bw) (tw0 x) (tw1 x) (tw2 x)
    & halfTw_okb bw]
  && [&& prodDW_okb (tw0 hb) (tw1 hb) (tw0 i1) (tw1 i1) (tw2 i1),
         sub32Tw_okb p2
       & prodOne_okb (tw0 i1) (tw1 i1) (tw2 i1) (tw1 s2) (tw2 s2)].

Lemma sqrt_okbP x : sqrt_okb x = true -> sqrt_ok x.
Proof.
move=> /andP[/and3P[H1 H2 H3] /and3P[H4 H5 H6]].
split; first by apply: sqrtBW_okbP.
split; first by apply: prodDW_okbP.
split; first by apply: halfTw_okbP.
split; first by apply: prodDW_okbP.
split; first by apply: sub32Tw_okbP.
by apply: prodOne_okbP.
Qed.

(* ---------------------------------------------------------------------------*)
(*  `kstep_sqrt', with every hypothesis a test                                *)
(* ---------------------------------------------------------------------------*)

(* THIS IS THE AXIOM, WITH NOTHING ASSUMED.  Every hypothesis is a boolean    *)
(* the program can evaluate: the three words are numbers, the triple is well  *)
(* formed, the value is above nought, the first two words are clear of the    *)
(* bottom of the range, and `sqrt_okb' -- the six guards of Algorithm 15's    *)
(* parts, clause for clause -- comes out true.  What the last one rules out   *)
(* is a product inside the algorithm underflowing, which is what scaling the  *)
(* argument into a fixed binade would rule out by construction; until that    *)
(* is done the test stands in its place, and it is the same test              *)
(* `code/ddouble' makes for the double-word root.                             *)
Theorem kstep_sqrt_testable x :
  finL (tw2l x) -> wellFormed x = true -> (0 < twval x)%R ->
  normF (tw0 x) = true ->
  ((tw1 x =? 0)%float || normF (tw1 x)) = true ->
  sqrt_okb x = true ->
  finL (tw2l (threeSqRt x)) -> wellFormed (threeSqRt x) = true ->
  (tw_updn.normLo <? abs (tw0 (threeSqRt x)))%float = true ->
  finF (kscale * abs (tw0 (threeSqRt x)))%float = true ->
  finF (dw_updn.mulUpFp kscale (abs (tw0 (threeSqRt x)))) = true ->
  (Rabs (twval (threeSqRt x) - R_sqrt.sqrt (twval x))
     <= D2R (kstep (threeSqRt x)))%R.
Proof.
move=> Fx Wx Hx0 Hn0 Hn1 Hok Fr Wr Hlo Hm Hu.
have Fx0 : Dfin (tw0 x).
  by move: Fx; rewrite /tw2l; case: (x) => x0 x1 x2 [].
have Fx1 : Dfin (tw1 x).
  by move: Fx; rewrite /tw2l; case: (x) => x0 x1 x2 [_ []].
apply: kstep_sqrt_ok => //.
- by have := normFP _ Fx0 Hn0; lra.
- case/orP: Hn1 => [Hz|Hn]; first by left; have [] := Dfin_eqb0 _ Hz.
  by right; have := normFP _ Fx1 Hn; lra.
- by apply: sqrt_okbP.
- by apply: finFP.
by apply: finFP.
Qed.
