(* =========================================================================  *)
(*  RowCubRun.v -- the row's map, on the plain map, with the twenty cubies.   *)
(* =========================================================================  *)

(* THIS IS THE RUN THE PROOF ASKS FOR.  RowCubReal leaves exactly one thing   *)
(* open -- that the map the search fills, together with the witnesses, leaves *)
(* no bit of the row clear -- and this is that question, asked.  It must      *)
(* print true, and then r_full_cub is no longer admitted.                     *)
(*                                                                            *)
(* IT IS THE PLAIN MAP, 812 851 200 words and 6.5 GB.  RowFoldCubRun asks     *)
(* the same row on the folded map, which is eleven times faster and 0.45 GB   *)
(* -- and which no proof in the tree covers.                                  *)
(*                                                                            *)
(* MEASURED at depth thirteen on roquableu: the search is 236.5 s carrying    *)
(* the table and 141.7 s carrying the twenty.                                 *)

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
Require Import RowReal FsmChk.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* the map the twenty leave, exactly as RowCubReal names it *)
Definition ycmfin : rmap :=
  ymfin e8numi e4biti mpgi mgri mswi mloi mhii p1 actfsri tomemb okmvv srch 20.

(* THE RUN.  This is RowCubReal's r_full_cub, discharged rather than          *)
(* admitted, so the corollary below stands on nothing but the primitives.     *)
Lemma r_full_cub_run : mfull2 ycmfin (wmap rowwits).
Proof. Time native_cast_no_check (erefl true). Qed.

(* ---- and the row of the superflip, with nothing left open ---------------- *)

Theorem real_superflip_row_run h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof.
apply: (ysuperflip_row_within_20 e8okC e4okC memb2tab_okC srcokC halfokC
          (r_fsstepP fsmoveCP) r_leaf_memb r_tomemb_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC r_full_cub_run).
exact: (row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC).
Qed.

Corollary real_row_superflip_run m : m \in H ->
  superflip * m \in ball Sset 20.
Proof.
have hV : superflip^-1 = superflip.
  by apply: (mulgI superflip); rewrite mulgV; move: superflip2;
     rewrite expgS expg1.
by rewrite -hV; exact: real_superflip_row_run.
Qed.

(* IT MUST NAME NOTHING BUT THE int63 AND PArray PRIMITIVES *)
Print Assumptions real_row_superflip_run.
