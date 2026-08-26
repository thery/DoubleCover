(* =========================================================================  *)
(*  RowFoldPlace.v -- of the hundred microseconds an answer costs, which      *)
(*  part.                                                                     *)
(* =========================================================================  *)

(* MEASURED IN RowFoldMark.v: the search finds 86 144 answers at depth        *)
(* eleven in 2.7 s and puts them in the map in 13.1, so recording one costs   *)
(* 103 microseconds.  Over depths eleven, twelve and thirteen that is 20.7    *)
(* million answers and about 2 130 s -- which is the part of the 2 904.8 s    *)
(* run that nothing else accounted for.                                       *)
(*                                                                            *)
(* THREE THINGS HAPPEN AT AN ANSWER and they are not alike:                   *)
(*                                                                            *)
(*   tomemb   the position, which is a forty eight entry table, is turned     *)
(*            into three ranks.  It inverts the table, writes it out as a    *)
(*            LIST OF UNARY NUMBERS, and walks that list twenty times.        *)
(*   place    the three ranks become a page, a group and a bit: two table    *)
(*            reads and a division.                                          *)
(*   ffor     the bit goes into the map: two reads and two writes.           *)
(*                                                                            *)
(* Each run below adds one of them to the one before, so a difference is one  *)
(* of the three.  The first Eval is a copy of the second and is thrown away:  *)
(* the first of a file pays for the tables arriving.                          *)

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

(* RowInst's own step and leaf test, spelt out as the other files spell them  *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedci, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) coordfs1i].

(* the pruning table read through the fold, and the moves worth trying        *)
Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

(* eleven is enough: 86 144 answers, and the marking already measured at      *)
(* 13.1 s there, so the three parts have a total to add up to                 *)
Definition dlow : nat := 11.

(* ---- the search, with what happens at an answer handed in ---------------- *)

(* The tree is the same in every run below -- nothing above an answer looks   *)
(* at the position -- so the runs differ only in the work at the answers.     *)
Fixpoint lsrch (lf : pstt -> int -> int) (togo : nat) (c : int) (x : pstt)
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
           then lsrch lf togo' c' (xstep x k) (wmsk w (togo' - nd)) k a
           else a)
      n
  else if fsolved c x then lf x n else n.

(* nothing: the answers are counted and dropped                              *)
Definition lnone (_ : pstt) (n : int) : int := Uint63.add n 1%uint63.

(* the position turned into three ranks, and one of them kept so that the     *)
(* work cannot be thrown away                                                 *)
Definition lmemb (x : pstt) (n : int) : int := Uint63.add n (mcp (tomemb x)).

(* and those ranks turned into a page, a group and a bit                      *)
Definition lplace (x : pstt) (n : int) : int :=
  let: (pg, gr, bt) := place e8numi e4biti (tomemb x) in
  Uint63.add n (Uint63.add pg (Uint63.add gr bt)).

(* ---- what is asked ------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in lsrch lnone dlow croot sroot allmv 18 0.

(* the answers counted: 86 144 *)
Time Eval native_compute in lsrch lnone dlow croot sroot allmv 18 0.

(* and turned into three ranks *)
Time Eval native_compute in lsrch lmemb dlow croot sroot allmv 18 0.

(* and those into a page, a group and a bit *)
Time Eval native_compute in lsrch lplace dlow croot sroot allmv 18 0.

(* the sweep that counts the map, on its own, to be taken off the last run    *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

(* and the whole thing: the bit written into the map as the run writes it     *)
Time Eval native_compute in
  fcount forbi fpopi
    (fsrch e8numi e4biti fpgi fsgri fsbti
       p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
       fstep xstep tomemb okmvv fsolved dlow croot sroot allmv 18
       (mkempty tt)).
