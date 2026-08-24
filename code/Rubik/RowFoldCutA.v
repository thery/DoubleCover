(* =========================================================================  *)
(*  RowFoldCutA.v -- the row's LEVELS, with the search cut out.               *)
(* =========================================================================  *)

(* CUTTING DOWN FROM THE PROGRAM THAT LEAKS.  RowFoldChk runs ten levels and
   searches at the tenth.  This runs the same ten levels and never searches:
   the map, the fold, the two maps swapping, and nothing else.

   If the memory still climbs, the search is not the cause and the next cut is
   inside the level.  If it is flat, the cause is the search, and RowFoldCutB
   is the search with no map at all. *)

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

Notation fmcnt d :=
  (fcount forbi fpopi
     (frun e8numi e4biti
        fpgi fsrci fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi
        fstep xstep tomemb okmvv fsolved croot sroot srch
        d 0 (mkempty tt) (mkempty tt))).


Notation flv n :=
  (flevn fsrci fsgri fsloi fshii mgri mswi mloi mhii n (mkempty tt) (mkempty tt)).

Time Eval native_compute in fcount forbi fpopi (flv 10).
