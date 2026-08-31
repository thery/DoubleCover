(* =========================================================================  *)
(*  RowCubProof.v -- what the plain run's answer buys.                        *)
(* =========================================================================  *)

(* rowfullp = true -> the row of the superflip is within twenty.  Nothing is  *)
(* computed here; RowCubBool settles the boolean and RowCubDone puts the two  *)
(* together.  RowFoldCubProof is this file on the folded map.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal FsmChk.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowSrch RowMark RowCubReal RowCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* ---- the two names for the same map -------------------------------------- *)

(* RowCubDef loads no proof, so it builds the map under its own names.  Left  *)
(* to itself the unifier does not fail when a name will not match: it         *)
(* reduces, and reducing this is the run again, in the kernel.  So the        *)
(* equation is written out and rewritten with.                               *)
Lemma rowwitspE : rowwitsp =
  ycwitsr p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
          ishmi.
Proof. by rewrite /rowwitsp /rowmapp /wmarkof /ycwitsr /ycmfinsp. Qed.

(* ---- what the run buys --------------------------------------------------- *)

Theorem row_of_runp : rowfullp = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite /rowfullp rowwitspE => hf.
exact: (@real_superflip_row_p p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data ishmi fsmoveCP hf).
Qed.

Corollary row_of_runp_superflip : rowfullp = true ->
  forall m, m \in H -> superflip * m \in ball Sset 20.
Proof.
move=> hr m hm.
have hV : superflip^-1 = superflip.
  by apply: (mulgI superflip); rewrite mulgV; move: superflip2;
     rewrite expgS expg1.
rewrite -{1}hV.
apply: row_of_runp.
exact: hr.
exact: hm.
Qed.
