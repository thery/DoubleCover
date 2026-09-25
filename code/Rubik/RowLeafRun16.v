(* =========================================================================  *)
(*  RowLeafRun16.v -- the run to sixteen, with the fast leaf and the old one. *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.                                            *)
(*                                                                            *)
(* RowLeafRun14 measured fourteen: 1 198 s with bitleaf against 2 573 s with  *)
(* the run's leaf.  Fifteen and sixteen are where the run spends its time,    *)
(* so this is the same comparison there.  The run is the real one: the fast   *)
(* leaf is RowFoldCubDefB's rowmapiB, the proved one, and the old leaf is     *)
(* RowFoldCubDefI's rowmapi.                                                  *)
(*                                                                            *)
(*   cd code/Rubik && ulimit -s unlimited                                     *)
(*   /usr/bin/time -v make RowLeafRun16.vo                                    *)
(*                                                                            *)
(* THE FAST LEAF COMES FIRST, so its time arrives first; the old one can be   *)
(* stopped if it is not wanted.  THE TWO COUNTS MUST BE THE SAME.  The first  *)
(* Eval pays for the tables arriving and is thrown away.  Run it alone on     *)
(* the machine: two runs side by side share the memory bus.                   *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldTab RowFoldCubDef RowFoldCubDefI RowFoldCubDefB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition dlev : nat := 16.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiB dlev).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapi dlev).
