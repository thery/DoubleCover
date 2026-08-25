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
Require Import RowWits.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
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

(* SPELT OUT SO THAT RowReal IS NOT REQUIRED.  RowReal is the only file that
   pulls in P1Table -- the UNFOLDED phase one table, 2 217 093 120 entries --
   and the folded row never reads it: it reads p1ftab, the folded one, which
   is 140 908 410.  Requiring it costs whatever native_compute must do to
   bring 2.2 billion entries in, and buys these two definitions. *)
Definition okmvv (pv k : int) : bool :=
  if (18 <=? pv)%uint63 then true
  else let fp := (pv / 3)%uint63 in
       let fk := (k / 3)%uint63 in
       ~~ ((fp =? fk)%uint63 || (fp =? fk + 3)%uint63).

Definition dsrchn : nat := 16.

Notation fmcnt d :=
  (fcount forbi fpopi
     (fruns e8numi e4biti
        fpgi fsrci fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
        fstep xstep tomemb okmvv fsolved croot sroot dsrchn
        d 0 (mkempty tt) (mkempty tt))).


Notation flv n :=
  (flevn fsrci fsgri fsloi fshii mgri mswi mloi mhii n (mkempty tt) (mkempty tt)).

Time Eval native_compute in fcount forbi fpopi (flv 10).
