(* =========================================================================  *)
(*  RowCubDef.v -- the plain run's definitions, and not one proof.            *)
(* =========================================================================  *)

(* The map the twenty leave on the plain map, and the boolean the certificate *)
(* asks about it.  See doc/rowfold-bridge.md.                                 *)

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
Require Import P1Table RowReal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* the map the twenty leave, exactly as RowCubReal names it                   *)
Definition ycmfinp : rmap :=
  ymfin e8numi e4biti mpgi mgri mswi mloi mhii p1 actfsri tomembi okmvv
        srch 20.

(* ---- and the boolean the run has to settle ------------------------------- *)

Definition rowfullp : bool := mfull2 ycmfinp (wmap rowwits).
