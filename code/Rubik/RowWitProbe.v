(* =========================================================================  *)
(*  RowWitProbe.v -- is it the witness map, or the final sweep?               *)
(* =========================================================================  *)

(* The row's run sits flat for about an hour and then its memory climbs.      *)
(* Three things could do it: the last levels, which write nearly everywhere;  *)
(* the witness map, which is only built once the levels are done; the final   *)
(* sweep, which is only read once they are done.  This file runs the second   *)
(* and the third on their own, with no levels at all.                         *)
(*                                                                            *)
(* THE WORK.  The first line allocates one empty map -- 388 arrays of two     *)
(* million words, 6.5 GB -- and sets one bit for each witness.  It reads one  *)
(* word and stops, so nothing is swept.  The second allocates two empty maps, *)
(* 13 GB, and reads all 812 851 200 pairs of words without writing any.       *)
(* RowFoldProbe measures one such sweep at 72.7 s.                            *)
(*                                                                            *)
(* WHAT IT SETTLES.  If neither line goes above 13 GB, neither the witness    *)
(* map nor the sweep can be what climbs, and it is the levels.                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowWits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* the witness map, exactly as RowFinal builds it *)
Definition wm : rmap := wmapof rowwits.

(* ---- 2: the witness map on its own --------------------------------------- *)

Time Eval native_compute in gget wm 0%uint63.

(* ---- 3: the final sweep on its own --------------------------------------- *)

Time Eval native_compute in mfull2 (mkempty tt) (mkempty tt).
