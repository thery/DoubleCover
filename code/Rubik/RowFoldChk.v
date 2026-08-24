(* =========================================================================  *)
(*  RowFoldChk.v -- the folded row against the prototype's own numbers.       *)
(* =========================================================================  *)

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
Require Import Fold FoldTables P1FTable.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation fmcnt d :=
  (fcount forbi fpopi
     (frun e8numi e4biti
        fpgi fsrci fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi
        (cstep actfsri) xstep tomemb okmvv csolvedb croot sroot srch
        d 0 memptyf)).

(* how many leaves the search reaches at depth ten: the prototype says 3072  *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi
    (cstep actfsri) xstep okmvv csolvedb 10 croot sroot allmv 18 0.

Time Eval native_compute in fmcnt 10.
