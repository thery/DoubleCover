(* =========================================================================  *)
(*  RowLeaf.v -- a position of H is its three ranks.                          *)
(* =========================================================================  *)

(* WHAT RowInst STILL ASKS FOR, taken apart.  memb2tab builds a cube from     *)
(* three ranks and tomemb reads three ranks off a cube; leaf_memb and         *)
(* tomemb_tab say the two undo each other on a position of H.                 *)
(*                                                                            *)
(* THE PREMISE IN RowInst IS THE WRONG ONE.  It reads `wdist (p1get p1 c) =   *)
(* 0', and p1 is a VARIABLE -- an arbitrary array.  Nothing ties that number  *)
(* to the cube, so neither fact is provable as it stands.  What is meant is   *)
(* that the position is in H, and that is a condition on the POSITION: no     *)
(* corner twisted, no edge flipped, the middle four in the middle layer.  p1  *)
(* is then only the pruning table, which soundness never looks at.            *)
(*                                                                            *)
(* Being in H says the same thing three times, once for each layout: the      *)
(* position carries a place to a place and leaves the SLOT alone.  That is    *)
(* assumed here, as hqc, hqu and hqm, and it is what is left to prove.        *)
(* leaf_memb is proved from it below.                                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the parity of a permutation of the places --------------------------- *)

(* Counted as inversions, which is what the tables have to agree with.        *)
Definition prmn (n : nat) (q : nat -> nat) : bool :=
  odd (count (fun ij => ((ij.1 < ij.2) && (q ij.2 < q ij.1))%N)
             (allpairs (fun i j => (i, j)) (iota 0 n) (iota 0 n))).

(* ---- a fold does not look past its list ---------------------------------- *)

Lemma foldl_eq_in (T : eqType) (R : Type) (F G : R -> T -> R)
  (s : seq T) (r : R) :
  (forall x r', x \in s -> F r' x = G r' x) -> foldl F r s = foldl G r s.
Proof.
elim: s r => [|x s ih] r hFG //=.
rewrite hFG ?mem_head //; apply: ih => y r' hy.
by apply: hFG; rewrite in_cons hy orbT.
Qed.

(* so the rank only looks at the places                                       *)
Lemma lrank_eq n (f g : nat -> nat) :
  (forall p, (p < n)%N -> f p = g p) -> lrank n f = lrank n g.
Proof.
move=> hfg; rewrite /lrank; apply: foldl_eq_in => i r.
rewrite mem_iota add0n => /andP[_ hi]; congr (_ + _)%N.
apply: eq_in_count => j; rewrite mem_iota => /andP[hj1 hj2].
by rewrite !hfg // (leq_trans hj2) // subnKC.
Qed.

(* ---- the first facelet of a place, the same three times ------------------ *)

Lemma cflatp_prim :
  all (fun p => nth 0%N cflatp (p * 3)%N == nth 0%N cprimp p) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma ulay_prim :
  all (fun p => nth 0%N ulay (p * 2)%N == nth 0%N eprim p) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma mlay_prim :
  all (fun p => nth 0%N mlay (p * 2)%N == nth 0%N eprim (8 + p)%N) (iota 0 4).
Proof. by vm_compute. Qed.

(* ---- and reading a place back off its own layout ------------------------- *)

Lemma cposn_lay p : (p < 8)%N -> cposn (nth 0%N cflatp (p * 3)%N) = p.
Proof.
move=> hp; have hi : (p * 3 < 8 * 3)%N by rewrite ltn_mul2r.
have /and4P[_ _ /eqP h _] := layP clayokC hi.
by rewrite h mulnK.
Qed.

Lemma eposn_ulay p : (p < 8)%N -> eposn (nth 0%N ulay (p * 2)%N) = p.
Proof.
move=> hp; have hi : (p * 2 < 8 * 2)%N by rewrite ltn_mul2r.
have /and4P[_ _ /eqP h _] := layP ulayokC hi.
by rewrite h mulnK.
Qed.

Lemma mplc_mlay p : (p < 4)%N -> mplc (nth 0%N mlay (p * 2)%N) = p.
Proof.
move=> hp; have hi : (p * 2 < 4 * 2)%N by rewrite ltn_mul2r.
have /and4P[_ _ /eqP h _] := layP mlayokC hi.
by rewrite h mulnK.
Qed.

Section Leaf.

(* ---- the position, as the table tomemb reads ----------------------------- *)

(* tomemb reads the INVERSE table: at the primary facelet of a place it gives *)
(* the home facelet of whatever sits there.                                   *)
Variable u : seq nat.

(* ---- 1, ASSUMED: being in H is three place permutations ------------------ *)

Variable qc qu qm : nat -> nat.

Hypothesis hqc : forall p j, (p < 8)%N -> (j < 3)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3 + j)%N) = nth 0%N cflatp (qc p * 3 + j)%N.
Hypothesis hqu : forall p j, (p < 8)%N -> (j < 2)%N ->
  nth 0%N u (nth 0%N ulay (p * 2 + j)%N) = nth 0%N ulay (qu p * 2 + j)%N.
Hypothesis hqm : forall p j, (p < 4)%N -> (j < 2)%N ->
  nth 0%N u (nth 0%N mlay (p * 2 + j)%N) = nth 0%N mlay (qm p * 2 + j)%N.

Hypothesis hqcP : perm_eq [seq qc p | p <- iota 0 8] (iota 0 8).
Hypothesis hquP : perm_eq [seq qu p | p <- iota 0 8] (iota 0 8).
Hypothesis hqmP : perm_eq [seq qm p | p <- iota 0 4] (iota 0 4).

(* a permutation of the places stays inside them                              *)
Lemma qc_lt p : (p < 8)%N -> (qc p < 8)%N.
Proof.
move=> hp; have : qc p \in [seq qc q | q <- iota 0 8].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hqcP) mem_iota.
Qed.

Lemma qu_lt p : (p < 8)%N -> (qu p < 8)%N.
Proof.
move=> hp; have : qu p \in [seq qu q | q <- iota 0 8].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hquP) mem_iota.
Qed.

Lemma qm_lt p : (p < 4)%N -> (qm p < 4)%N.
Proof.
move=> hp; have : qm p \in [seq qm q | q <- iota 0 4].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hqmP) mem_iota.
Qed.

(* ---- what the ranking owes, and it is not about the cube ----------------- *)

(* A Lehmer rank of eight places is below eight factorial.  Pure arithmetic   *)
(* on lrank, nothing to do with the cube.                                     *)
Hypothesis rank8_lt : forall q, (rank8 q <? npagei)%uint63.
Hypothesis rank4_lt : forall q, (rank4 q <? nbiti)%uint63.

(* ---- what the parity tables owe, and it is a walk ------------------------ *)

Variable par8t par4t : arr.

Hypothesis hpar8 : forall q, perm_eq [seq q p | p <- iota 0 8] (iota 0 8) ->
  PArray.get par8t (rank8 q) = (if prmn 8 q then 1 else 0)%uint63.
Hypothesis hpar4 : forall q, perm_eq [seq q p | p <- iota 0 4] (iota 0 4) ->
  PArray.get par4t (rank4 q) = (if prmn 4 q then 1 else 0)%uint63.

(* ---- and the one fact about the cube ------------------------------------- *)

(* THE THIRD INVARIANT.  The corner permutation and the edge permutation have *)
(* the same parity, and the edges here are the outer eight and the middle     *)
(* four apart, so the corner parity is the two of them together.  It holds    *)
(* for a position REACHED BY MOVES -- every face turn is a four cycle on the  *)
(* corners and a four cycle on the edges, both odd -- and not for every       *)
(* facelet permutation that pairs up the way a cube does.                     *)
Hypothesis hcube : prmn 8 qc = prmn 8 qu (+) prmn 4 qm.

(* ---- the three ranks tomemb reads are the three permutations ------------- *)

Lemma tomembE a : ti2t flast (inv_tabi flast a) = u ->
  tomemb a = (rank8 qc, rank8 qu, rank4 qm).
Proof.
move=> hu; rewrite /tomemb hu; congr (_, _, _); rewrite /rank8 /rank4.
- have -> : lrank 8 (fun p => cposn (nth 0%N u (nth 0%N cprimp p)))
          = lrank 8 qc; last by [].
  apply: lrank_eq => p hp.
  rewrite -(eqP (all_iota_lt cflatp_prim hp)).
  by rewrite -[(p * 3)%N]addn0 hqc // addn0 cposn_lay // qc_lt.
- have -> : lrank 8 (fun p => eposn (nth 0%N u (nth 0%N eprim p)))
          = lrank 8 qu; last by [].
  apply: lrank_eq => p hp.
  rewrite -(eqP (all_iota_lt ulay_prim hp)).
  by rewrite -[(p * 2)%N]addn0 hqu // addn0 eposn_ulay // qu_lt.
have -> : lrank 4 (fun p => (eposn (nth 0%N u (nth 0%N eprim (8 + p)%N)) - 8)%N)
        = lrank 4 qm; last by [].
apply: lrank_eq => p hp.
rewrite -(eqP (all_iota_lt mlay_prim hp)).
rewrite -[(p * 2)%N]addn0 hqm // addn0.
by have := mplc_mlay (qm_lt hp); rewrite /mplc.
Qed.

(* ---- and they satisfy membok --------------------------------------------  *)

Lemma leaf_membH a : ti2t flast (inv_tabi flast a) = u ->
  membok par8t par4t (tomemb a).
Proof.
move=> hu; rewrite (tomembE hu) /membok /mcp /mud /mmp.
rewrite !rank8_lt rank4_lt /=.
rewrite (hpar8 hqcP) (hpar8 hquP) (hpar4 hqmP) hcube.
by case: (prmn 8 qu); case: (prmn 4 qm).
Qed.

End Leaf.
