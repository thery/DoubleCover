(* =========================================================================  *)
(*  RowCubDef48.v -- the plain run's definitions, and not one proof.            *)
(* =========================================================================  *)

(* The map the twenty leave on the plain map, and the boolean the certificate *)
(* asks about it.  See doc/rowfold-bridge.md.                                 *)

(* Only the MAP is unfolded.  The table is Rokicki's folded one, read through *)
(* RowMask, and the cuts and the stop are the folded run's own.               *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal.
Require Import Fold FoldTables P1Fdec P1FTable RowMask RowSrch RowMark.
Require Import RowLvl.
Require Import Row48 RowMap48 RowRun48 RowFinal48 RowPrep48 RowSrch48.
Require Import RowMark48 RowCubInst48 RowTab48 RowTabP48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* which of the eighteen are moves of H: those that leave the solved          *)
(* coordinate alone.  RowFoldCubDef works out the same number.                *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition ishmi : int :=
  Eval vm_compute in
  ifold nmvn 0%uint63
    (fun k a =>
       if Uint63.eqb (fstep csolvedci k) csolvedci
       then Uint63.lor a (Uint63.lsl 1%uint63 k) else a)
    0%uint63.

(* The map the twenty leave.  IT IS A FUNCTION AND NOT A VALUE: a nullary     *)
(* Definition is a top level value native_compute keeps for good, which would *)
(* hold the unmarked map alive beside the marked one.                         *)
(* THE LEVEL IS RowLvl's: each page's chunk read once and put back once,      *)
(* where RowMap's finds it again for every word.  It is proved equal to       *)
(* RowMap's, so nothing about the cube changes.                               *)
Definition rowmapp48 (n : nat) : rmap :=
  ymfinsk e8numi e4biti par8i
          p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
          ishmi (prepass48 cpgi cfli mgri mswi mloi mhii)
          actfsri tomembi okmvv RowReal.srch n.

(* The same map, over the search that carries the depth as an int.  Nothing   *)
(* about the cube or the map changes.                                         *)
Definition rowmappi48 (n : nat) : rmap :=
  ymfinski e8numi e4biti par8i
           p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           ishmi (prepass48 cpgi cfli mgri mswi mloi mhii)
           actfsri tomembi okmvv RowReal.srch n.

(* The witnesses go into that map, so there is no second one to hold.  IT IS  *)
(* RowMark's OWN wmarkof AND NOT THE SAME BODY WRITTEN OUT: RowCubReal has to *)
(* match this against the name the theorem is stated with, and unification    *)
(* does not fail when a name will not match -- it reduces, and reducing this  *)
(* is the run again, in the kernel.                                           *)
Definition rowwitsp48 : rmap := wmarkof rowwits48 (rowmapp48 20).

(* The same two over the int run.  RowCubProofI shows the two maps equal, so  *)
(* nothing is proved twice.                                                   *)
Definition rowwitspi48 : rmap := wmarkof rowwits48 (rowmappi48 20).

Definition rowfullpi48 : bool := mfull48 rowwitspi48.

(* ---- and the boolean the run has to settle ------------------------------- *)

Definition rowfullp48 : bool := mfull48 rowwitsp48.
