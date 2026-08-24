(* =========================================================================  *)
(*  RowFoldProbe.v -- what the fullness scan costs, folded and not.           *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  Both scans are in one file so that the machine and *)
(* the loading are the same for both.  Measured on gukesh, native:            *)
(*                                                                            *)
(*   mfull mempty     72.7 s, and 69.4 s again at the foot of the file        *)
(*   mfullf memptyf    5.0 s                                                  *)
(*                                                                            *)
(* 13.9x, against a fold of 14.57x: the scan costs what the map is big, word  *)
(* for word.                                                                  *)
(*                                                                            *)
(* AND IT DOES NOT STOP EARLY.  mfull is a chain of &&, so on an empty map it *)
(* looks as though it should answer false at the first word.  native_compute  *)
(* is call by value: the recursive call is evaluated before andb ever sees    *)
(* its first argument, so the whole map is walked whether it is empty or      *)
(* full.  That is why the scan on mempty costs what a scan on a full map      *)
(* costs, and why every mfull in the row is a full sweep.                     *)
From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowTabL RowTabP RowTab RowTabF RowFoldTab.
Set Implicit Arguments.
Local Open Scope uint63_scope.

Time Eval native_compute in mfull mempty.
Time Eval native_compute in mfullf memptyf.
Time Eval native_compute in mfull mempty.
