(* =========================================================================  *)
(*  RowFoldStep.v -- where the cost is, one Eval at a time.                  *)
(* =========================================================================  *)

(* The prototype does the depth ten search in no time at all and the same    *)
(* search in Rocq sat at twenty gigabytes, so the cost is not the search.    *)
(* This file walks up to it in small steps, each timed on its own:           *)
(*                                                                           *)
(*   1  a sum of two numbers      -- loading, and nothing else               *)
(*   2  one entry of the table    -- the first touch of a chunk              *)
(*   3  the last entry            -- another chunk, so the cost per chunk    *)
(*   4  a decoding table read     -- the small arrays                        *)
(*   5  one folded read           -- the fold, through all four tables       *)
(*   6  the search at depth 2     -- a handful of positions                  *)
(*   7  the search at depth 6     -- a few thousand                          *)
(*   8  the search at depth 10    -- 8 497, which is the one that matters    *)
(*                                                                           *)
(* Whatever jumps between two lines is the answer.                           *)

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

(* 1 -- loading and nothing else *)
Time Eval native_compute in Uint63.add 1 1.

(* 2 -- one entry, which makes the first chunk a value *)
Time Eval native_compute in p1getm p1ftab 0%uint63.

(* 3 -- an entry in the last chunk *)
Time Eval native_compute in p1getm p1ftab 140908409%uint63.

(* 4 -- the decoding tables *)
Time Eval native_compute in Fold.get20 dnlo_data 0%uint63.

(* 5 -- one folded read, through all four tables *)
Time Eval native_compute in
  Dfoldm p1ftab frepi fsymi twsymi 0%uint63 0%uint63.

(* 6, 7, 8 -- the search, three sizes.  The last says 3072 *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 2 croot sroot allmv 18 0.

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 6 croot sroot allmv 18 0.

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 10 croot sroot allmv 18 0.
