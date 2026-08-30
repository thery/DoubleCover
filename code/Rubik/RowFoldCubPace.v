(* =========================================================================  *)
(*  RowFoldCubPace.v -- what the certificate's own run costs at thirteen.     *)
(* =========================================================================  *)

(* MEMORY IS THE CONSTRAINT ON THIS MACHINE, and it is measured before a run  *)
(* is paid for, not after it is killed.  This is RowFoldCubDef's map, the     *)
(* certificate's own step and leaf, stopped at thirteen: minutes, and the     *)
(* count must be 14 731 320.                                                  *)
(*                                                                            *)
(* WATCH RES.  The map is allocated whole at mkempty, so what this settles    *)
(* at is what twenty settles at, plus whatever the deeper levels leave        *)
(* behind.  If it climbs here it climbs there, and twenty is not worth        *)
(* starting.                                                                  *)
(*                                                                            *)
(* The measuring run's own thirteen, for comparison: 751.3 s.                 *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldTab RowFoldCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving                                           *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

Time Eval native_compute in fcount forbi fpopi (rowmap 13).
