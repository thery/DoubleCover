(* =========================================================================  *)
(*  RowFoldWide.v -- how many moves a node is actually offered.               *)
(* =========================================================================  *)

(* THE SUSPICION.  The depth twelve tree has 3 148 501 nodes and the depth    *)
(* eleven one 205 378, so the bottom level has 2 943 123 nodes over 196 881   *)
(* parents: FOURTEEN CHILDREN A NODE.  The mask stored beside the distance is *)
(* meant to leave three or four down there -- it offers all eighteen only     *)
(* when there are two moves to spare -- so either the mask is not biting or   *)
(* the distances are not tight.                                              *)
(*                                                                            *)
(* WHAT IT WOULD BE WORTH.  A node pays a coordinate step and a table lookup  *)
(* for every move it tries, and that is seven of the twelve microseconds a    *)
(* node costs.  Fifteen tries down to four is the whole of the search's time  *)
(* over again, and it costs nothing to have -- the mask is already read.      *)
(*                                                                            *)
(* FOUR COUNTS, ONE TREE.  The tree is the same in all of them, so they can   *)
(* be read side by side:                                                      *)
(*                                                                            *)
(*   nodes   how many nodes there are                                        *)
(*   tries   how many moves were tried -- a step and a lookup each           *)
(*   wide    how many nodes were offered all eighteen                        *)
(*   width   the widths added up, so the average follows                     *)
(*                                                                            *)
(* The first Eval is a throwaway: the first of a file pays for the tables     *)
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

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* RowInst's own step, spelt out as the other files spell it                  *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

(* the pruning table read through the fold, and the moves worth trying        *)
Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

(* the twelve low bits of a word counted, which is what the map's own count   *)
(* uses; a mask is eighteen bits, so it is two of those                       *)
Definition mwidth (m : int) : int :=
  Uint63.add (PArray.get fpopi (Uint63.land m 4095%uint63))
             (PArray.get fpopi (Uint63.land (Uint63.lsr m 12%uint63)
                                            4095%uint63)).

Definition dlow  : nat := 11.
Definition dhigh : nat := 12.

(* ---- the same search four times, counting a different thing -------------- *)

(* THE POSITION IS STILL STEPPED.  Taking it out would change nothing in the  *)
(* tree, but leaving it in keeps these runs comparable with the others.       *)

(* the nodes *)
Fixpoint nsrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
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
           then nsrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k
                  (Uint63.add a 1%uint63)
           else a)
      n
  else n.

(* the moves tried: one is counted wherever a step and a lookup are paid *)
Fixpoint tsrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmvv pv k then a
         else
           let a' := Uint63.add a 1%uint63 in
           let c' := fstep c k in
           let w := wp1g c' in
           let nd := Uint63.to_nat (mdist w) in
           if (nd <= togo')%N
           then tsrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k a'
           else a')
      n
  else n.

(* the nodes that were offered all eighteen *)
Fixpoint wsrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
  let n0 := if Uint63.eqb msk allmv then Uint63.add n 1%uint63 else n in
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
           then wsrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k a
           else a)
      n0
  else n0.

(* the widths added up *)
Fixpoint psrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
  let n0 := Uint63.add n (mwidth msk) in
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
           then psrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k a
           else a)
      n0
  else n0.

(* ---- what is asked ------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in nsrch dlow croot sroot allmv 18 0.

(* the nodes below the root: the prototype says 3 148 501 with its own *)
Time Eval native_compute in nsrch dhigh croot sroot allmv 18 0.

(* the moves tried, which is what the seven microseconds a node are spent on *)
Time Eval native_compute in tsrch dhigh croot sroot allmv 18 0.

(* how many of those nodes were offered all eighteen *)
Time Eval native_compute in wsrch dhigh croot sroot allmv 18 0.

(* and the widths added up, so the average width follows *)
Time Eval native_compute in psrch dhigh croot sroot allmv 18 0.
