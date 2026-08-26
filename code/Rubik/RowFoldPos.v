(* =========================================================================  *)
(*  RowFoldPos.v -- what a smaller position would be worth.                   *)
(* =========================================================================  *)

(* THE TWO SIDES CARRY DIFFERENT THINGS.  The prototype's search carries the  *)
(* eight corners and the twelve edges -- twenty numbers, written in place     *)
(* into arrays indexed by depth -- and the coordinate beside them.  Rocq      *)
(* carries a FORTY EIGHT ENTRY FACELET TABLE, freshly composed at every try,  *)
(* because that is what the proofs are stated about.                          *)
(*                                                                            *)
(* MEASURED at depth twelve: with the table 18.5 s, with no position at all   *)
(* 5.5.  So the position is 13.0 s of the 18.5, and this file asks what is    *)
(* left of that if it were twenty entries instead of forty eight.            *)
(*                                                                            *)
(* NO PROOF, AND NONE IS NEEDED FOR THE TIME.  The leaf test is now one       *)
(* comparison on the coordinate and does not look at the position, so the     *)
(* SOLUTIONS ARE COUNTED THE SAME whatever the position is.  All three runs   *)
(* must print 1 438 464; that is the check that the tree has not moved.       *)
(*                                                                            *)
(* WHAT IT DOES NOT MEASURE.  The twenty entry tables here are permutations   *)
(* of twenty places and nothing more -- they are the right SIZE and the wrong *)
(* meaning, which is all a time needs.  And the model change would also make  *)
(* the place cheaper, since the three ranks would come straight off the       *)
(* cubies instead of through the inverse table; that saving is NOT here.      *)

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

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

Definition dlow  : nat := 11.
Definition dhigh : nat := 12.

(* ---- a twenty entry position, and eighteen moves of it ------------------- *)

Definition nsml  : nat := 20.       (* eight corners and twelve edges         *)
Definition nsmli : int := 20%uint63.
Definition nmvi  : int := 18%uint63.

(* eighteen permutations of the twenty places, flat: move k at k * 20         *)
Definition smla : arr :=
  Eval vm_compute in
  mkarrn (Uint63.mul nmvi nsmli)
    [seq of_nat ((((i %/ 20).+1 * ((i %% 20).+1)) %% 20)%N) | i <- iota 0 360].

Definition smlroot : arr :=
  Eval vm_compute in mkarrn nsmli [seq of_nat j | j <- iota 0 20].

(* a move: twenty reads, twenty writes and a new array, where the forty eight *)
(* entry one is forty eight of each                                           *)
Definition sstep (x : arr) (k : int) : arr :=
  ifold nsml 0%uint63
    (fun j a =>
       PArray.set a j
         (PArray.get x (PArray.get smla (Uint63.add (Uint63.mul k nsmli) j))))
    (PArray.make nsmli 0%uint63).

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

(* thrown away: the tables arriving.  86 144, the answers at eleven *)
Time Eval native_compute in psrch xstep dlow croot sroot allmv 18 0.

(* ALL THREE MUST PRINT 1 438 464 *)

(* the forty eight entry table, as it is *)
Time Eval native_compute in psrch xstep dhigh croot sroot allmv 18 0.

(* twenty entries *)
Time Eval native_compute in psrch sstep dhigh croot smlroot allmv 18 0.

(* and none at all: the floor *)
Time Eval native_compute in psrch xkeep dhigh croot sroot allmv 18 0.
