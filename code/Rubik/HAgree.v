(* =========================================================================  *)
(*  HAgree.v -- obligation C: the coordinates agree with the tables, for ALL  *)
(*     positions.                                                             *)
(* =========================================================================  *)

(* HChk.v runs mtabsok, which compares the coordinates of HCoord.v with the   *)
(* generated move tables on Reid's six positions and everything two quarter   *)
(* turns from them -- about 950 positions.  IT PASSES, and it is a check, not *)
(* a theorem.  What the search needs is                                       *)
(*                                                                            *)
(*   htriple (a * m) = stepa (htriple a) m   for EVERY position a             *)
(*                                                                            *)
(* and that is the statement below.  It cannot be checked position by         *)
(* position -- there are 4.3e19 of them -- but it does not have to be: the    *)
(* three coordinates take only 190080, 70 and 2187 values, and a table is     *)
(* right exactly when it is right at every VALUE.  Turning the one into the   *)
(* other needs, for each coordinate, a position that realises each value --   *)
(* an unranking, cube_of_e and its two companions in ocaml/rubik_h.ml -- and  *)
(* the round trip that the rank of the unranked value is the value again.     *)
(*                                                                            *)
(* So obligation C is: unranking in Rocq, the round trips, and then a sweep   *)
(* of 190080 x 12 (and 70 x 12, and 2187 x 12).  The sweep is small -- it is  *)
(* the unranking that is the work, and rubik_h.ml's cube_of_e is the spec.    *)
(*                                                                            *)
(* Nothing here is proved yet.  The file exists to hold the statement.        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Coordfs Phase1 HRoot HCoord HSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* The statement, over the tables a run supplies.  mtabsok in HSearch.v is    *)
(* this, restricted to a list of positions; agree is the same for all.        *)
Definition agree (mt_e mt_cl mt_ct : arr) : Prop :=
  forall (a : arr) (m : nat), (m < 12)%N ->
    htriple (comp_tabi flast a (mvi (qt18 m)))
      = stepa mt_e mt_cl mt_ct (htriple a) (of_nat m).
