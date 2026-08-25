(* =========================================================================  *)
(*  RowFoldSlice.v -- the depth ten tree, a slice at a time.                 *)
(* =========================================================================  *)

(* Everything below the depth ten search is instant -- loading 1.6 s, a      *)
(* table read, a folded read, the searches that cut at the root -- and the   *)
(* tree itself does not come back.  So the tree is cut here into slices: the *)
(* root is offered one move, then three, then six, then all eighteen.        *)
(*                                                                           *)
(* If the time follows the slice, the search is merely slow a position.  If  *)
(* one move already does not come back, the size of the tree is not what     *)
(* costs.                                                                    *)

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

(* THE LEAF TEST MEETS NO PERMUTATION.  coordfs takes a mathcomp permutation *)
(* and those do not compute; RowInst spends it once, and what the search      *)
(* meets here is a number.                                                    *)
Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedci, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) coordfs1i].

(* one move at the root *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 10 croot sroot 1%uint63 18 0.

(* three *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 10 croot sroot 7%uint63 18 0.

(* six *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 10 croot sroot 63%uint63 18 0.

(* all eighteen: the whole tree, 8 497 positions, 3 072 solutions *)
Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved 10 croot sroot allmv 18 0.
