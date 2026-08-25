(* =========================================================================  *)
(*  RowFoldCutB.v -- the row's SEARCH, with the map cut out.                  *)
(* =========================================================================  *)

(* The other half of RowFoldChk: the search at depth ten, counting the leaves
   it reaches instead of marking them, so NO MAP IS TOUCHED AT ALL -- it
   carries an int and nothing else.  The tables are all still read.

   If the memory climbs here, the leak is in the search or in the tables it
   reads, and no map is involved.  It must print 3072. *)

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
     (frun e8numi e4biti
        fpgi fsrci fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi
        fstep xstep tomemb okmvv fsolved croot sroot dsrchn
        d 0 (mkempty tt) (mkempty tt))).


Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi
    fstep xstep okmvv fsolved 10 croot sroot allmv 18 0.
