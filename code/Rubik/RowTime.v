(* =========================================================================  *)
(*  RowTime.v -- how long the row itself takes.                              *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  This file runs the row and prints the time, so     *)
(* that the one number worth comparing with a C program is measured and not   *)
(* guessed.  It evaluates exactly the term r_full states, and nothing else.   *)
(*                                                                           *)
(*   the search fills the map, the witnesses fill in what it missed, and      *)
(*   mfull asks whether every bit of the row is set                           *)
(*                                                                           *)
(* It should print true.  If it prints false the row is not settled at this   *)
(* depth, and the number to raise is srch in RowReal.v.                       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Time Eval native_compute in
  mfull2 (mfin e8numi e4biti mpgi mgri mswi mloi mhii p1
                actfsri tomemb okmvv srch 20)
          (wmap rowwits).
