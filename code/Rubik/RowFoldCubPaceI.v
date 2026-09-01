(* =========================================================================  *)
(*  RowFoldCubPaceI.v -- the folded run at thirteen, depth as an int.         *)
(* =========================================================================  *)

(* The count must be 14 731 320, which is what the folded run counts at       *)
(* thirteen.  For comparison, measured on roquableu: 751.3 s over the nat     *)
(* search.                                                                    *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldSrch RowFoldCubDef RowFoldCubDefI.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving                                           *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

Time Eval native_compute in fcount forbi fpopi (rowmapi 13).
