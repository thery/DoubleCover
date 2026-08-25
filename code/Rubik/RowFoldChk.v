(* =========================================================================  *)
(*  RowFoldChk.v -- the folded row against the prototype's own numbers.       *)
(* =========================================================================  *)

(* THIS IS THE PROGRAM THAT REACHED 41 GB.  It is left exactly as it was, so  *)
(* that it can be run again and compared.  RowFoldChkNoReal.v is the same     *)
(* thing with one dependency dropped -- see its head.                         *)

(* NOT PART OF THE PROOF.  RowFoldGrow.v says whether the map is full, which  *)
(* is false at every depth it can reach.  This counts the members instead, so *)
(* that the folded run can be checked against the prototype, which printed    *)
(* for the superflip's row:                                                   *)
(*                                                                            *)
(*   after depth 10        2 560 members                                      *)
(*   after depth 11       72 832                                              *)
(*                                                                            *)
(* The row's first depth is 10 -- its representative is that far from H --    *)
(* so the levels below it neither search nor spread, and ten levels here are  *)
(* the prototype's depth ten.                                                 *)

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

Notation fmcnt d :=
  (fcount forbi fpopi
     (frun e8numi e4biti
        fpgi fsrci fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
        fstep xstep tomemb okmvv fsolved croot sroot srch
        d 0 (mkempty tt) (mkempty tt))).

(* how many leaves the search reaches at depth ten: the prototype says 3072  *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 10 croot sroot allmv 18 0.

Time Eval native_compute in fmcnt 10.
