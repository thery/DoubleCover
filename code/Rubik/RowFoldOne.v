(* =========================================================================  *)
(*  RowFoldOne.v -- one step of the search, each piece on its own.           *)
(* =========================================================================  *)

(* THE PROBES THAT WERE INSTANT NEVER TOOK A STEP.  A search at depth two or *)
(* six cuts at the root, because the row's own position is ten from H, so    *)
(* neither xstep nor fstep was ever called.  They are called here, one at a  *)
(* time: if one of them does not reduce, that is the whole story.            *)

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

(* the move filter *)
Time Eval native_compute in okmvv 18%uint63 0%uint63.

(* the leaf test at the root *)
Time Eval native_compute in fsolved croot sroot.

(* the coordinate step *)
Time Eval native_compute in fstep croot 0%uint63.

(* the position step, read back as a number so that nothing large is shown *)
Time Eval native_compute in ctwisti (xstep sroot 0%uint63).
Time Eval native_compute in coordi (xstep sroot 0%uint63).

(* two steps, then three: does the cost stay flat *)
Time Eval native_compute in
  coordi (xstep (xstep sroot 0%uint63) 1%uint63).
Time Eval native_compute in
  coordi (xstep (xstep (xstep sroot 0%uint63) 1%uint63) 2%uint63).
