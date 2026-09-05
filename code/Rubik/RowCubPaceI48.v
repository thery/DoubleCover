(* =========================================================================  *)
(*  RowCubPaceI48.v -- the forty eight bit run at thirteen.                   *)
(* =========================================================================  *)

(* RowCubPaceI, over rowmappi48.  The same search, the same cuts, the same    *)
(* stop; the map is 3.25 GB instead of 6.5 and a cell is two corner           *)
(* permutations instead of one.                                               *)
(*                                                                            *)
(* THE COUNT MUST BE 14 731 320.  It is what the folded run, the plain run    *)
(* and this one all hold at thirteen -- the members are the same members, and *)
(* only where their bits sit has changed.  A different number means the       *)
(* layout or the count is wrong, and it says so in an hour instead of ten.    *)
(*                                                                            *)
(* For comparison, both measured on roquableu: the folded run's thirteen is   *)
(* 751.3 s, the plain run's over the int search 2963.8 s.                     *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMap48 RowSrch48 RowCubDef48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving, and the map allocated                    *)
Time Eval native_compute in mcount (mkempty48 tt).

Time Eval native_compute in mcount (rowmappi48 13).
