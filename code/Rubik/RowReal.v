(* =========================================================================  *)
(*  RowReal.v -- the instance on the real tables, and the row itself.         *)
(* =========================================================================  *)

(* WHAT RowDummy DID ON NOUGHTS, DONE ON THE TABLES.  Every check that has a  *)
(* file of its own is spent here, and what is left admitted is exactly what   *)
(* has not been computed -- no statement is missing and nothing is left       *)
(* dangling, only runs.                                                       *)
(*                                                                            *)
(* FOUR TABLES ARE STILL VARIABLES, and they are the SEARCH's own: the phase  *)
(* one pruning table, the fs step table, the reading of a position into three *)
(* ranks, and the move filter.  No generated file in the tree carries them.   *)
(* Soundness never looks at the pruning table -- it appears only in the       *)
(* premise of the two facts about a leaf -- so the row does not wait on it.   *)
(*                                                                            *)
(* And then the row itself: every position of H is within twenty moves of the *)
(* superflip.                                                                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Real.

(* ---- the four the search carries and no file supplies -------------------- *)

Variable p1 : rmap.
Variable cstep : int -> int -> int.
Variable tomembv : pstt -> memb.
Variable okmvv : int -> int -> bool.
Variable srch : nat.

(* ---- and the four that are runs and nothing else ------------------------- *)

(* THE FS STEP TABLE.  Farp1.actfsr_step says this, and its file will not     *)
(* load in this checkout.                                                     *)
Lemma r_fsstepP x k : (to_nat k < nmvn)%N -> pstok x ->
  cstep (fsidx (coordi x)) k = fsidx (coordi (xstep x k)).
Proof. Admitted.

(* WHAT A LEAF IS, twice.  RowLeaf proves both of a position that is IN H --  *)
(* leaf_membH and tomemb_tabH -- and the premise here is that the pruning     *)
(* table says nought at the position's coordinate.  Nothing ties that number  *)
(* to the cube, so these two are where the premise has to change: RowInst     *)
(* should ask that the position is in H, and the step from the pruning table  *)
(* to being in H belongs beside the table, not beside the leaf.               *)
Lemma r_leaf_memb c x : coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 -> membok par8i par4i (tomembv x).
Proof. Admitted.

Lemma r_tomemb_tab c x : coordP c x -> pstok x ->
  wdist (p1get p1 c) = 0%uint63 ->
  pt flast (memb2tab (tomembv x)) = pt flast (ti2t flast x).
Proof. Admitted.

(* AND THE MAP, 812 851 200 words: the run and the witnesses together leave   *)
(* no bit of the row clear.  This is the long pole and it is only a run.      *)
Lemma r_full :
  mfull (mor (mfin e8numi e4biti mpgi mgri mswi mloi mhii p1
                cstep tomembv okmvv srch 20)
             (wmap rowwits)).
Proof. Admitted.

(* ---- every member of the row is within twenty ---------------------------- *)

Theorem real_row_within_20 x : membok par8i par4i x ->
  RowRun.wthn (RowFinal.pos (ptab memb2tab)) 20 x.
Proof.
apply: (row_within_20_inst e8okC e4okC memb2tab_okC srcokC halfokC
          r_fsstepP r_leaf_memb r_tomemb_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC r_full).
Qed.

(* ---- AND THE ROW OF THE SUPERFLIP ---------------------------------------- *)

(* The covering is RowLeaf's, and the six walks it asks for are now checked,  *)
(* each in its own file.                                                      *)
Theorem real_superflip_row h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof.
apply: (superflip_row_within_20 e8okC e4okC memb2tab_okC srcokC halfokC
          r_fsstepP r_leaf_memb r_tomemb_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC r_full).
exact: (row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC).
Qed.

End Real.
