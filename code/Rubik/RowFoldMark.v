(* =========================================================================  *)
(*  RowFoldMark.v -- what it costs to PUT the answers in the map.            *)
(* =========================================================================  *)

(* THE ONE THING NEVER TIMED.  Everything measured so far used `fsrchn',      *)
(* which COUNTS the positions the search finds.  The run itself uses          *)
(* `fsrch', which puts each of them in the map -- 86 144 of them at depth     *)
(* eleven and 1 438 464 at twelve.  The two walk the same tree and differ     *)
(* only in what happens at the end of a branch.                              *)
(*                                                                            *)
(* AND THE ARITHMETIC POINTS HERE.  Thirteen levels cost 2 904.8 s.  The      *)
(* levels come to about sixteen seconds each and the searches, counted, to    *)
(* forty at twelve -- a few hundred all told, against nearly three thousand.  *)
(* What is missing is the marking.                                           *)
(*                                                                            *)
(* THE FIRST EVAL OF A FILE IS NOT A MEASUREMENT.  It pays for the tables     *)
(* being brought in, which was worth between one and three seconds in the     *)
(* two files before this one and made a piece look free that is not.  So the  *)
(* first Eval below is the same as the second and is meant to be thrown       *)
(* away.                                                                     *)

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

(* the two depths: eleven finds 86 144 and twelve 1 438 464, sixteen times    *)
(* more, so the pair says whether the marking grows with what it marks        *)
Definition dlow  : nat := 11.
Definition dhigh : nat := 12.

(* ---- what is asked ------------------------------------------------------- *)

(* THE MAP CANNOT BE PRINTED, so what comes back is its count.  That sweep    *)
(* costs something itself and is measured on its own first, to be taken off   *)
(* the two runs below it.                                                     *)

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

(* the sweep alone, over a map with nothing in it *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

(* --- eleven: counted, then marked --- *)

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved dlow croot sroot allmv 18 0.

Time Eval native_compute in
  fcount forbi fpopi
    (fsrch e8numi e4biti fpgi fsgri fsbti
       p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
       fstep xstep tomemb okmvv fsolved dlow croot sroot allmv 18
       (mkempty tt)).

(* --- twelve: counted, then marked --- *)

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved dhigh croot sroot allmv 18 0.

Time Eval native_compute in
  fcount forbi fpopi
    (fsrch e8numi e4biti fpgi fsgri fsbti
       p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
       fstep xstep tomemb okmvv fsolved dhigh croot sroot allmv 18
       (mkempty tt)).
