(* =========================================================================  *)
(*  RowFoldRun.v -- the folded level, run.                                    *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  This runs the folded level on the ball of H itself *)
(* -- the row of the solved position -- and counts the members each level     *)
(* holds.  The numbers are the prototype's own, so a wrong one shows at once: *)
(*                                                                            *)
(*   flv  2      78                                                           *)
(*   flv  4    3613                                                           *)
(*   flv  6  146635                                                           *)
(*   flv  8  5068603                                                          *)
(*   flv 10  144467208                                                        *)
(*                                                                            *)
(* measured by `ocaml/rubik_row.ml fball', which agrees in its turn with the  *)
(* same ball worked out one position at a time up to five.                    *)
(*                                                                            *)
(* Each line starts from the seed again, as RowGrow.v's ladder does, so the   *)
(* ten lines are 2 + 4 + ... levels and not ten.  ONE LEVEL WAS 40 s HERE     *)
(* with the map nearly empty (gukesh, native); what a level costs once the    *)
(* map is FULL is not measured on this side.  In the prototype it grew about  *)
(* eightfold from empty to full, so do not read the last line off the first.  *)
(*                                                                            *)
(* The row's real question is the line at the bottom: eighteen levels fill    *)
(* the whole of H, 19 508 428 800 members, and mfullf then says true.  It is  *)
(* left commented out because it is the long one.                             *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowTabL RowTabP RowTab RowTabF RowFoldTab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* the solved position, where it stands: the first page, the group of the     *)
(* first outer permutation, and the bit of the first middle one               *)
Definition fseed : PArray.array (PArray.array int) :=
  fmark fpgi fsgri fsbti memptyf 0
    (Uint63.lsr (PArray.get e8numi 0) 1) (PArray.get e4biti 0).

Notation flv n :=
  (flevn fsrci fsgri fsloi fshii mgri mswi mloi mhii n fseed).

Notation fcnt m := (fcount forbi fpopi m).

(* the seed alone first: no level in it at all, so its time is what loading   *)
(* and the count cost, and every line after it is that plus the levels        *)
Time Eval native_compute in fcnt fseed.

Time Eval native_compute in fcnt (flv 1).
Time Eval native_compute in fcnt (flv 2).
Time Eval native_compute in fcnt (flv 3).

(* the whole of H, and the row's own question -- the long one *)
(* Time Eval native_compute in fcnt (flv 18).   19508428800 *)
(* Time Eval native_compute in mfullf (flv 18). true        *)
