(* =========================================================================  *)
(*  RowFoldOpt10.v -- the folded row, every optimization on, to depth 10.       *)
(* =========================================================================  *)

(* One depth, one process, so that ten, thirteen, fifteen and twenty go side  *)
(* by side and twenty is measured rather than guessed.                        *)
(*                                                                            *)
(* IT PRINTS THE COUNT AFTER EVERY LEVEL, so a run in progress can be         *)
(* watched.  To thirteen the cuts are still off, so the list must be the      *)
(* known 2560, 72832, 1192960, 14731320; at fourteen they come on and the     *)
(* prototype's count is 148 423 860.                                          *)
(*                                                                            *)
(* THE FIRST Eval IS THROWN AWAY: the first of a file pays for the tables     *)
(* arriving, and that cost does not grow with the depth.                      *)
(*                                                                            *)
(* NOTHING HERE IS PROVED.  It is the measuring run; the certificate is       *)
(* RowFoldCubProof.v.                                                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowFold RowFoldTab RowFoldOptT.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

Time Eval native_compute in fruno 10 0 0%uint63 (mkempty tt) (mkempty tt) [::].
