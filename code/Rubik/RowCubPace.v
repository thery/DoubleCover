(* =========================================================================  *)
(*  RowCubPace.v -- what the plain run costs at thirteen.                     *)
(* =========================================================================  *)

(* RowFoldCubPace, for the unfolded map.  MEMORY IS THE CONSTRAINT, and it is *)
(* measured before a run is paid for, not after it is killed.  This is        *)
(* RowCubDef's map, the certificate's own step and leaf, stopped at thirteen. *)
(*                                                                            *)
(* WATCH RES.  The map is allocated whole at mkempty, so what this settles at *)
(* is what twenty settles at, plus whatever the deeper levels leave behind.   *)
(* If it climbs here it climbs there, and twenty is not worth starting.       *)
(*                                                                            *)
(* THE COUNT MUST BE 14 731 320, which is what the folded run counts at       *)
(* thirteen.  The two maps hold the same members: the fold weighs a bit by    *)
(* the size of its orbit, and here a page stands for itself, so the totals    *)
(* agree.  A different number means the two are not running the same search.  *)
(*                                                                            *)
(* The folded run's own thirteen, for comparison: 751.3 s.                    *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap RowSrch RowCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving                                           *)
Time Eval native_compute in mcount (mkempty tt).

Time Eval native_compute in mcount (rowmapp 13).
