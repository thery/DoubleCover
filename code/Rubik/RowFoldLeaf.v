(* =========================================================================  *)
(*  RowFoldLeaf.v -- the test at the end of a branch.                         *)
(* =========================================================================  *)

(* WHAT WAS FOUND.  Depth twelve, the same tree: a search with the test costs *)
(* 36.7 s and one without it 17.8.  So THE TEST IS HALF THE SEARCH, and it    *)
(* had been counted against the moves all day.                                *)
(*                                                                            *)
(* WHAT IT DOES.  It reads the forty eight entry cube and works the twist and *)
(* the flip and slice rank out of it -- which is the number the search is     *)
(* already carrying, and has updated at every move.  So it computes what it   *)
(* already has, once at the end of every branch, three million times.         *)
(*                                                                            *)
(* WHY THE SHORT TEST SHOULD DO.  csolvedci is a flip and slice rank, so it   *)
(* is below nfsi; and the coordinate is the twist times nfsi plus that rank.  *)
(* A coordinate that equals something below nfsi therefore has twist nought   *)
(* already, and the rank right already.  The other two questions are answered *)
(* by the first.                                                              *)
(*                                                                            *)
(* THAT IS AN ARGUMENT AND NOT A PROOF, and this file does not prove it -- it *)
(* asks the data.  THE SHORT TEST MUST FIND THE SAME 1 438 464 SOLUTIONS.  If *)
(* it finds more, it is letting something through and the argument is wrong.  *)
(*                                                                            *)
(* AND THE POSITION IS PRICED IN THE SAME RUN.  With the short test nothing   *)
(* below the end of a branch looks at the cube at all, so the last run steps  *)
(* no position and is the floor: what the search would cost if the cube were  *)
(* not carried.  All three must print the same number.                        *)

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

Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

Definition dlow  : nat := 11.
Definition dhigh : nat := 12.

(* ---- the two tests, and the two steps ------------------------------------ *)

(* RowInst's own: three questions, two of them of the cube *)
Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedci, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) coordfs1i].

(* and the first of them alone *)
Definition csolvi (c : int) (_ : pstt) : bool := Uint63.eqb c csolvedci.

(* the cube left where it is: with the short test nothing reads it *)
Definition xkeep (x : pstt) (_ : int) : pstt := x.

(* ---- the same search, with the test and the step handed in --------------- *)

(* The tree is the same in all three: which moves a node opens is decided by  *)
(* the coordinate, the mask and the move test, and never by the cube or by    *)
(* what happens at the end of a branch.                                       *)
Fixpoint lsrch (lf : int -> pstt -> bool) (stp : pstt -> int -> pstt)
               (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
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
           then lsrch lf stp togo' c' (stp x k) (wmsk w (togo' - nd)) k a
           else a)
      n
  else if lf c x then Uint63.add n 1%uint63 else n.

(* ---- what is asked ------------------------------------------------------- *)

(* thrown away: the tables arriving.  It prints 86 144, the answers at eleven *)
Time Eval native_compute in lsrch fsolved xstep dlow croot sroot allmv 18 0.

(* the test as it stands, and the cube stepped: 1 438 464 *)
Time Eval native_compute in lsrch fsolved xstep dhigh croot sroot allmv 18 0.

(* the short test, and the cube still stepped.  SAME NUMBER OR THE ARGUMENT   *)
(* IS WRONG.                                                                  *)
Time Eval native_compute in lsrch csolvi xstep dhigh croot sroot allmv 18 0.

(* the short test, and no cube at all: the floor *)
Time Eval native_compute in lsrch csolvi xkeep dhigh croot sroot allmv 18 0.
