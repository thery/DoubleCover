(* =========================================================================  *)
(*  RowCubReal.v -- the row on the PLAIN map, with nothing left open but the *)
(*  run.                                                                     *)
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
Require Import RowReal RowMembi RowMark RowSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section CubReal.

(* THE FOLDED PHASE ONE TABLE IS A VARIABLE HERE, and that is not a gap: no   *)
(* proof in the tree says what it holds.  The distance and the moves it names *)
(* are numbers the search tests, and a table that prunes too little only      *)
(* makes the search bigger.  So the theorem holds for any of them, and the    *)
(* run names the real one.  RowFoldCubReal does the same.                     *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.
Variable ishm : int.

(* the flip and slice move table's certificate, as RowReal carries it *)
Hypothesis hfm : fsmoveC.

(* ---- what the run buys --------------------------------------------------- *)

(* THIS FILE RUNS NOTHING.  RowCubDef names the map the twenty leave and the  *)
(* one boolean about it; RowCubBool settles that boolean in a process that    *)
(* loads no proof.  Here is what its being true buys, and RowCubDone puts     *)
(* the two together.                                                         *)

(* ---- the map, named ------------------------------------------------------ *)

(* The map the run leaves, and the same with the witnesses marked in.  They   *)
(* are named here so that RowCubProof can match RowCubDef's names against     *)
(* them by unfolding: left to itself the unifier does not fail when a name    *)
(* will not match -- it reduces, and reducing this is the run again, in the   *)
(* kernel.                                                                    *)
Definition ycmfinsp : rmap :=
  ymfinsk e8numi e4biti mpgi mgri mswi mloi mhii
          F frep fsym twsym dnlo dnhi fllo flhi
          ishm actfsri tomembi okmvv srch 20.

Definition ycwitsr : rmap := wmarkof rowwits ycmfinsp.

(* ---- the certificate, with the optimizations on -------------------------- *)

Theorem real_superflip_row_p : mfull ycwitsr ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hr h hh; move: h hh.
apply: (ysuperflipsk_marked_within_20 e8okC e4okC memb2tab_okC srcokC halfokC
          (r_fsstepP hfm) r_leaf_membi r_tomembi_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC hr).
exact: (row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC).
Qed.

End CubReal.
