(* =========================================================================  *)
(*  Fsmain.v                                                                  *)
(*                                                                            *)
(*  The sixteen slices, glued: checkStep for the real table and the real      *)
(*  moves.  This is the local certificate the whole lower bound rests on --   *)
(*  Coordfs.v never asks the table to be correct, only that it holds 0 at     *)
(*  the identity and drops by at most one per move.                          *)
(*                                                                            *)
(*  IT IS STATED AT mtabs, NOT FOR ALL mtabs.  FsTable.v used to admit                                    *)
(*  "Lemma fstab_checkStep mtabs : checkStep fstab mtabs", quantified over    *)
(*  every table list, and that is false: for mtabs = [:: U then R ] the       *)
(*  check fails inside the first 2 ^ 20 coordinates, because a two move       *)
(*  composition cuts the flip x slice distance by two.  It was also not       *)
(*  something the computation could ever discharge, mtabs being a variable.   *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
From Rubik Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root.
From Rubik Require Import Coord Coordfs Coordfsi Fstab FsTable Diameter Moves.
From Rubik Require Import Fspar.
From Rubik Require Import Fs_00 Fs_01 Fs_02 Fs_03 Fs_04 Fs_05 Fs_06 Fs_07
                          Fs_08 Fs_09 Fs_10 Fs_11 Fs_12 Fs_13 Fs_14 Fs_15.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* chunkFE is a delta step and all_pow_glue16 keeps the predicate abstract,
   so nothing here unfolds the loop.  See Fspar.v.                        *)
Lemma fstab_checkStep : checkStep fstab mtabs.
Proof.
rewrite chunkFE.
apply: all_pow_glue16.
- exact: fschk_00. - exact: fschk_01. - exact: fschk_02. - exact: fschk_03.
- exact: fschk_04. - exact: fschk_05. - exact: fschk_06. - exact: fschk_07.
- exact: fschk_08. - exact: fschk_09. - exact: fschk_10. - exact: fschk_11.
- exact: fschk_12. - exact: fschk_13. - exact: fschk_14. - exact: fschk_15.
Qed.
