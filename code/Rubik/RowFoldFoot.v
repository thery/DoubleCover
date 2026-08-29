(* =========================================================================  *)
(*  RowFoldFoot.v -- what the tables alone cost, before any run.              *)
(* =========================================================================  *)

(* THE FLOOR.  It loads exactly what RowFoldOpt10 loads and then makes ONE    *)
(* folded map and counts it.  No level, no search.  So the resident size at   *)
(* the end is the tables as Coq holds them, plus one map of 0.45 GB, and      *)
(* nothing else.                                                              *)
(*                                                                            *)
(* That is the number that says whether the fold can help the memory at all:  *)
(* if this alone is ten gigabytes, the map was never the bulk and folding it  *)
(* buys speed only.                                                           *)
(*                                                                            *)
(* Run it alone and watch RES.  It costs a table load, not a run.             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldTab RowFoldOptT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Time Eval native_compute in fcount forbi fpopi (mkempty tt).
