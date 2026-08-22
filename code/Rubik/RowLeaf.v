(* =========================================================================  *)
(*  RowLeaf.v -- a position of H is its three ranks.  SKELETON.               *)
(* =========================================================================  *)

(* WHAT RowInst STILL ASKS FOR, taken apart.  leaf_memb and tomemb_tab are    *)
(* the bridge the other way: memb2tab builds a cube from three ranks, tomemb  *)
(* reads three ranks off a cube, and these say the two undo each other on a   *)
(* position of H.                                                             *)
(*                                                                            *)
(* THE PREMISE IN RowInst IS THE WRONG ONE.  It reads `wdist (p1get p1 c) =   *)
(* 0', and p1 is a VARIABLE -- an arbitrary array.  Nothing ties that number  *)
(* to the cube, so the two facts are not provable as stated.  What is meant   *)
(* is that the position is in H, and that is a condition on the position:     *)
(* no corner twisted, no edge flipped, the middle four in the middle layer.   *)
(* p1 is then only the pruning table, which soundness never looks at.         *)
(*                                                                            *)
(* Every proof here is Admitted on purpose: this file is the shape of the     *)
(* argument, written down to see where the work is.                           *)

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

(* ---- being in H, as a condition on the position -------------------------- *)

(* The three coordinates solved.  coordtw is Phase1's corner twist, coordfs   *)
(* is Coordfs's flip and slice together, and the solved cube is the value     *)
(* they have to take.                                                         *)
Definition inH (g : {perm facelet}) : bool :=
  (coordtw g =? coordtw 1)%uint63 && (coordfs g =? coordfs 1)%uint63.

(* ---- what being in H says about the facelets ----------------------------- *)

(* THE THREE STRUCTURAL FACTS, and they are the whole of the difficulty.  A   *)
(* coordinate is a packed number; these turn each one back into a statement   *)
(* about where facelets go.                                                   *)

(* the twist is nought: a corner goes to a corner keeping its slot            *)
Lemma inH_corner g : cubP g -> inH g ->
  {q : nat -> nat |
     forall p j, (p < 8)%N -> (j < 3)%N ->
       g (inord (nth 0%N cflatp (p * 3 + j)%N))
       = inord (nth 0%N cflatp (q p * 3 + j)%N)}.
Proof. Admitted.

(* the flip is nought and the slice is solved: an outer edge goes to an outer *)
(* edge and a middle one to a middle one, each keeping its slot               *)
Lemma inH_outer g : cubP g -> inH g ->
  {q : nat -> nat |
     forall p j, (p < 8)%N -> (j < 2)%N ->
       g (inord (nth 0%N ulay (p * 2 + j)%N))
       = inord (nth 0%N ulay (q p * 2 + j)%N)}.
Proof. Admitted.

Lemma inH_middle g : cubP g -> inH g ->
  {q : nat -> nat |
     forall p j, (p < 4)%N -> (j < 2)%N ->
       g (inord (nth 0%N mlay (p * 2 + j)%N))
       = inord (nth 0%N mlay (q p * 2 + j)%N)}.
Proof. Admitted.

(* ---- and then the three ranks are those three permutations --------------- *)

(* tomemb reads a rank at each of the three layouts; lrank is the prototype's *)
(* own ranking and up8 its unranking, so this is that they undo each other.   *)
Lemma up8_lrank (q : nat -> nat) :
  perm_eq [seq q p | p <- iota 0 8] (iota 0 8) ->
  forall p, (p < 8)%N -> up8 (rank8 q) p = q p.
Proof. Admitted.

Lemma up4_lrank (q : nat -> nat) :
  perm_eq [seq q p | p <- iota 0 4] (iota 0 4) ->
  forall p, (p < 4)%N -> up4 (rank4 q) p = q p.
Proof. Admitted.

(* ---- the two facts RowInst wants ----------------------------------------- *)

(* The three ranks put the position back together.  Given the three           *)
(* structural facts and the two unranking ones, this is part by part: each    *)
(* part is the place permutation its rank names, and their composition is g   *)
(* because the three sets of facelets are disjoint and cover the forty eight. *)
Lemma tomemb_tabH (a : PArray.array int) : tabi_ok flast a -> cubti a ->
  inH (pt flast (ti2t flast a)) ->
  pt flast (memb2tab (tomemb a)) = pt flast (ti2t flast a).
Proof. Admitted.

(* and the parity condition: the three place permutations have parities that  *)
(* agree, which is the cube's own parity invariant read off the three ranks   *)
Lemma leaf_membH (a : PArray.array int) (par8t par4t : PArray.array int) :
  tabi_ok flast a -> cubti a -> inH (pt flast (ti2t flast a)) ->
  membok par8t par4t (tomemb a).
Proof. Admitted.
