(* =========================================================================  *)
(*  RowGrow.v -- how the search grows with depth.                            *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  Before spending hours on the full twenty levels,   *)
(* run the same search at eight, ten, twelve and fourteen and look at what    *)
(* each one costs.  The ratio between two of them says what twenty will cost, *)
(* and it says it in minutes rather than in hours.                            *)
(*                                                                            *)
(* Each line prints false -- the row is not full at these depths -- and the   *)
(* number that matters is the time beside it.                                 *)

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

Notation mrun d :=
  (mfull (mfin e8numi e4biti mpgi mgri mswi mloi mhii p1
            actfsri tomemb okmvv srch d)).

Time Eval native_compute in mrun 8.
Time Eval native_compute in mrun 10.
Time Eval native_compute in mrun 12.
Time Eval native_compute in mrun 14.
Time Eval native_compute in mrun 16.
