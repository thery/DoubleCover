(* A PROBE, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* WHAT IT SETTLES.  The edge jobs came back at once, and a sweep that says   *)
(* true because it looked at nothing says true at once too.  The four lines   *)
(* below are, in order: the guard admits a datum; the sweep agrees with the   *)
(* table at that datum; it DISAGREES when handed the wrong table; and one of  *)
(* the twenty four first slots, timed, which is a twenty fourth of the whole  *)
(* edge sweep.                                                                *)
(*                                                                            *)
(*   rocq compile -R . Rubik HSweepCP.v                                       *)
(*                                                                            *)
(* IT MUST PRINT true, true, false, true.  A `false' on the third line is the *)
(* one that matters: it is what says the second line was read off the table   *)
(* and not off nothing.                                                       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HEdge HCorner HSweepC HTables.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* a datum: four slice cubies in four different places                        *)
Definition edat0 : seq nat := [:: 0; 2; 4; 6]%N.

Eval vm_compute in evalid edat0.
Eval vm_compute in eone h_mt_e edat0.
Eval vm_compute in eone h_mt_cl edat0.

Time Eval native_compute in echk_from h_mt_e 0 1.
