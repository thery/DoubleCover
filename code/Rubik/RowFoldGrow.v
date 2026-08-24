(* =========================================================================  *)
(*  RowFoldGrow.v -- RowGrow.v, on the folded map and the folded table.       *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  This is RowGrow.v's ladder, run on two folds       *)
(* rather than none:                                                          *)
(*                                                                            *)
(*   the map     2768 pages of 40320 kept        0.45 GB against 6.5          *)
(*   the table   64 430 orbits of 1 013 760      70 MB against 1.1 GB         *)
(*                                                                            *)
(* Each line runs the row for that many levels and then asks whether the map  *)
(* is full.  A level is a prepass and a search: the folds make the prepass    *)
(* and the fullness scan smaller, and leave the search's own tree exactly as  *)
(* it was.  The ratio between two lines says what twenty would cost.          *)
(*                                                                            *)
(* Every line prints false -- the row is not full at these depths -- and the  *)
(* number that matters is the time beside it.                                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1FTable.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* SPELT OUT HERE, NOT TAKEN BY NAME.  These two are RowInst's own -- the step
   with Farp1's flip and slice table in it, and the leaf test -- written out
   so that this file does not depend on how a section discharged them.  A
   checkout whose RowInst differs then fails on the DEFINITION, which says
   what differs, instead of on a unification message. *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedi, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) (coordfs 1)].

Notation fmrun d :=
  (mfullf (frun e8numi e4biti
             fpgi fsrci fsgri fsloi fshii fsbti
             mgri mswi mloi mhii
             p1ftab frepi fsymi twsymi
             fstep xstep tomemb okmvv fsolved croot sroot srch
             d 0 (mkempty tt) (mkempty tt))).

(* the empty map first: no level in it at all, so its time is what loading    *)
(* and the fullness walk cost, and every line after it is that plus the       *)
(* levels                                                                     *)
Time Eval native_compute in mfullf memptyf.

Time Eval native_compute in fmrun 2.
Time Eval native_compute in fmrun 4.
Time Eval native_compute in fmrun 6.
Time Eval native_compute in fmrun 8.
Time Eval native_compute in fmrun 10.
Time Eval native_compute in fmrun 12.
Time Eval native_compute in fmrun 14.
Time Eval native_compute in fmrun 16.
