(* =========================================================================  *)
(*  RowFoldCub13.v -- the twenty cubies in the search, at depth 13.          *)
(* =========================================================================  *)

(* RowFoldPos.v PRICED A TWENTY ENTRY POSITION with tables that were the      *)
(* right size and the wrong meaning: 18.5 s with the forty eight entry table, *)
(* 8.4 with twenty entries, 5.5 with no position at all.  This file is the    *)
(* same three runs with RowCubi's REAL twenty -- the eight corners with their *)
(* turn and the twelve edges with their flip, stepped by the move undone.     *)
(*                                                                           *)
(* THE COUNT IS THE CHECK.  The leaf test is one comparison on the            *)
(* coordinate and never looks at the position, so all three must print        *)
(* 1 438 464.  A different number means the real step is not the step.        *)
(*                                                                           *)
(* The first Eval is thrown away: the first of a file pays for the tables     *)
(* arriving.                                                                  *)

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
Require Import RowCub RowCubi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

Definition dlow  : nat := 10.
Definition dhigh : nat := 13.

Definition xkeep (x : arr) (_ : int) : arr := x.

(* the test as RowInst now has it: one comparison, and it does not look at    *)
(* the position -- which is what makes the three runs comparable at all      *)
Definition fsolved (c : int) (_ : arr) : bool := Uint63.eqb c csolvedci.

(* ---- the same search, with the step handed in ---------------------------- *)

Fixpoint psrch (stp : arr -> int -> arr) (togo : nat) (c : int) (x : arr)
               (msk pv n : int) : int :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmvv pv k then a
         else
           let c' := fstep c k in
           let w := wp1g c' in
           let nd := Uint63.to_nat (mdist w) in
           if (nd <= togo')%N
           then psrch stp togo' c' (stp x k) (wmsk w (togo' - nd)) k a
           else a)
      n
  else if fsolved c x then Uint63.add n 1%uint63 else n.

(* ---- what is asked ------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in psrch xstep dlow croot sroot allmv 18 0.

(* THE THREE MUST PRINT THE SAME NUMBER *)

(* the forty eight entry table, as the row carries it now *)
Time Eval native_compute in psrch xstep dhigh croot sroot allmv 18 0.

(* the twenty cubies *)
Time Eval native_compute in psrch zstepi dhigh croot yrooti allmv 18 0.

(* and no position at all: the floor *)
Time Eval native_compute in psrch xkeep dhigh croot sroot allmv 18 0.
