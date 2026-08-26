(* =========================================================================  *)
(*  RowFoldOkm.v -- what the move table is worth.                             *)
(* =========================================================================  *)

(* THE WASTE, read off the source.  RowReal's okmvv divides the PREVIOUS move *)
(* by three, and the loop calls it once for each of the eighteen moves --     *)
(* though the previous move does not change while a node is being looked at.  *)
(* Seventeen divisions a node, and eighteen comparisons, buying nothing.  The *)
(* prototype works its own out once a node and then only compares.            *)
(*                                                                            *)
(* THREE SEARCHES, ONE TREE.  Which moves a node opens is decided by the      *)
(* coordinate, the pruning table's mask and this test, and RowOkm.okmviE says *)
(* the table agrees with okmvv everywhere -- so all three walk the SAME tree  *)
(* and all three must print 3 148 501.  A faster different number is worth    *)
(* nothing.                                                                   *)
(*                                                                            *)
(*   as it stands   okmvv called at every one of the eighteen moves          *)
(*   read once      the node's row of the table read once, then two bit      *)
(*                  tests in the loop                                        *)
(*   merged         the row folded into the pruning mask once, then ONE bit  *)
(*                  test -- what the loop would look like if the two were    *)
(*                  one                                                      *)
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
Require Import RowWits RowReal RowOkm.
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

Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

Definition dlow  : nat := 11.
Definition dhigh : nat := 12.

(* ---- the same search three times, counting the nodes ---------------------- *)

(* as it stands: okmvv at every move *)
Fixpoint asrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
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
           then asrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k
                  (Uint63.add a 1%uint63)
           else a)
      n
  else n.

(* the node's row read once, and two bit tests in the loop *)
Fixpoint bsrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
  if togo is togo'.+1 then
    let okr := PArray.get okmvi pv in
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if Uint63.eqb (Uint63.land okr (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else
           let c' := fstep c k in
           let w := wp1g c' in
           let nd := Uint63.to_nat (mdist w) in
           if (nd <= togo')%N
           then bsrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k
                  (Uint63.add a 1%uint63)
           else a)
      n
  else n.

(* the row folded into the pruning mask once, and ONE bit test in the loop.   *)
(* THE PROOF THIS ONE WOULD NEED IS NOT DONE: that a bit survives two masks   *)
(* if and only if it survives each.  It is here to say what that proof would  *)
(* be worth before anyone writes it.                                          *)
Fixpoint csrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
  if togo is togo'.+1 then
    let msk2 := Uint63.land msk (PArray.get okmvi pv) in
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk2 (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else
           let c' := fstep c k in
           let w := wp1g c' in
           let nd := Uint63.to_nat (mdist w) in
           if (nd <= togo')%N
           then csrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k
                  (Uint63.add a 1%uint63)
           else a)
      n
  else n.

(* ---- what is asked ------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in asrch dlow croot sroot allmv 18 0.

(* all three must print 3 148 501 *)
Time Eval native_compute in asrch dhigh croot sroot allmv 18 0.
Time Eval native_compute in bsrch dhigh croot sroot allmv 18 0.
Time Eval native_compute in csrch dhigh croot sroot allmv 18 0.
