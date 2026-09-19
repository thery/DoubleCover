From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import all_ssreflect.
From threewords Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From threewords Require Import TwoSum TWR VecSum.
From twarith Require Import twarith twbound.
From dwarith Require Import dwbridge dwtwosum dwflx.

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
Notation Xrnd := (round radix2 (FLX_exp prec) (round_mode mode_NE)).
Notation Xformat := (generic_format radix2 (FLX_exp prec)).

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
