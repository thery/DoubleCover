(* =========================================================================  *)
(*  RowCubPaceI.v -- the plain run at thirteen, with the depth as an int.     *)
(* =========================================================================  *)

(* RowCubPace, over rowmappi.  The same map, the same cuts, the same stop;    *)
(* the only difference is that no node makes a unary nat of the table's       *)
(* distance.  Run the two side by side and the difference is that and         *)
(* nothing else.                                                              *)
(*                                                                            *)
(* THE COUNT MUST BE 14 731 320, which is what both the folded run and the    *)
(* plain one count at thirteen.  A different number means the search is not   *)
(* the same search.                                                           *)
(*                                                                            *)
(* For comparison, both measured on roquableu: the folded run's thirteen is   *)
(* 751.3 s, and the plain run's, over the nat search, 3014.8 s.               *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap RowSrch RowCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving                                           *)
Time Eval native_compute in mcount (mkempty tt).

Time Eval native_compute in mcount (rowmappi 13).
