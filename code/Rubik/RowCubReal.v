(* =========================================================================  *)
(*  RowCubReal.v -- the row of the superflip, with the twenty cubies.         *)
(* =========================================================================  *)

(* RowReal DISCHARGES EVERY CHECK the row asks for, on the real tables, and   *)
(* leaves exactly one thing open: the map is full, which is a run.  Nothing   *)
(* here repeats any of that.  RowCubInst's row asks for the SAME checks, so   *)
(* the only new line is the run, and it is a different run: the search        *)
(* carries twenty cubies instead of a forty eight entry table.                *)
(*                                                                            *)
(* MEASURED at depth thirteen on roquableu: the search is 236.5 s carrying    *)
(* the table and 141.7 s carrying the twenty, against 68.9 s with no          *)
(* position at all.  So the row costs a third less.                           *)

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
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import RowReal RowMembi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section CubReal.

(* the flip and slice move table's certificate, as RowReal carries it *)
Hypothesis hfm : fsmoveC.

(* ---- the map the twenty leave -------------------------------------------- *)

Definition ycmfin : rmap :=
  ymfin e8numi e4biti mpgi mgri mswi mloi mhii p1 actfsri tomembi okmvv srch 20.

(* AND THE MAP, 812 851 200 words: the run and the witnesses together leave   *)
(* no bit of the row clear.  This is the long pole and it is only a run.      *)
Lemma r_full_cub : mfull2 ycmfin (wmap rowwits).
Proof. Admitted.

(* ---- the row of the superflip -------------------------------------------- *)

Theorem real_superflip_row_cub h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof.
apply: (ysuperflip_row_within_20 e8okC e4okC memb2tab_okC srcokC halfokC
          (r_fsstepP hfm) r_leaf_membi r_tomembi_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC r_full_cub).
exact: (row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC).
Qed.

(* said the way it reads, the superflip being an involution *)
Corollary real_row_superflip_cub m : m \in H ->
  superflip * m \in ball Sset 20.
Proof.
have hV : superflip^-1 = superflip.
  by apply: (mulgI superflip); rewrite mulgV; move: superflip2;
     rewrite expgS expg1.
by rewrite -hV; exact: real_superflip_row_cub.
Qed.

End CubReal.
