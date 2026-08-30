(* =========================================================================  *)
(*  RowFoldCubBool.v -- the boolean, and nothing else at all.                 *)
(* =========================================================================  *)

(* ONE Require, ONE Lemma.  RowFoldCubDef names the map and requires only     *)
(* tables, so the process that runs for hours holds no proof it does not      *)
(* read -- and there is no proof it reads.                                    *)
(*                                                                            *)
(* NOTHING ABOUT THE CUBE IS PROVED HERE.  The cube side is                   *)
(* RowFoldCubReal.real_superflip_row_foldo, which asks exactly this bit, and  *)
(* RowFoldCubProof puts the two together without computing.                   *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma rowfullE : rowfull = true.
Proof. Time native_cast_no_check (erefl true). Qed.
