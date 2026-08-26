(* =========================================================================  *)
(*  RowFoldClimb.v -- the row one depth at a time, each printed as it lands.  *)
(* =========================================================================  *)

(* THE LADDER PRINTS NOTHING UNTIL IT IS DONE, because one Eval gives one    *)
(* answer.  This one asks for each depth separately, so a line and a time    *)
(* land at every step and the next step can be guessed from the last.        *)
(*                                                                           *)
(* IT PAYS FOR THAT.  Each Eval starts from the seed again, so a level is     *)
(* redone once for every depth at or above it -- and the heaviest level is    *)
(* not the last, so asking for all eleven depths costs several times the run. *)
(* TWO ARE ASKED: ten and thirteen.  What they cost before today is 170.9 s   *)
(* and 2 904.8, and the prototype does the whole thing to thirteen in 36.9 -- *)
(* MEASURED, against the 27.7 this file used to quote, which was wrong.       *)
(*                                                                            *)
(* AND BOTH OF TODAY'S CHANGES ARE IN THIS RUN: the test at the end of a      *)
(* branch is one comparison, and a member's place is worked out on int63.     *)
(* Recording an answer went from 105 microseconds to 10.9, and the search at  *)
(* depth twelve from 37.9 s to 18.5, so the whole of this ought to land near  *)
(* 690 s.  THE COUNTS ARE THE CHECK: 2560, 72832, 1192960, 14731320.          *)
(*                                                                           *)
(* The prototype's numbers, for the superflip's row:                         *)
(*                                                                           *)
(*   depth 10          2 560          depth 16  4 973 524 638                *)
(*   depth 11         72 832          depth 17 12 370 176 759                *)
(*   depth 12      1 192 960          depth 18 18 676 620 636                *)
(*   depth 13     14 731 320          depth 19 19 507 349 478                *)
(*   depth 14    148 423 860          depth 20 19 508 428 768                *)
(*   depth 15  1 173 663 208          of 19 508 428 800: thirty two left     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal RowMembi.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* RowInst's own step and leaf test, spelt out as RowFoldChk.v spells them    *)
(* out, so that this file does not depend on how a section discharged them.   *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

(* THE TEST AT THE END OF A BRANCH IS ONE COMPARISON.  It used to ask two    *)
(* more of the forty eight entry cube -- 19.3 s of 37.9 at depth twelve --    *)
(* and Fsinj proves those two are answered by this one.  csolvedbP is the     *)
(* statement; here the number is the int side of it.                          *)
Definition fsolved (c : int) (_ : pstt) : bool := Uint63.eqb c csolvedci.

(* one level of the folded row, with hcoset's stop on the last one searched   *)
Notation flvl1 :=
  (flvls e8numi e4biti
     fpgi fsrci fsgri fsloi fshii fsbti
     mgri mswi mloi mhii
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     fstep xstep tomembi okmvv fsolved croot sroot srch forbi fpopi).

(* the run, keeping the count after each level.  The two maps swap: what the  *)
(* level wrote is the next level's source, and its source is the next one's   *)
(* destination.                                                               *)
Fixpoint frunl (n : nat) (d : nat) (m dst : rmap) (acc : seq int) : seq int :=
  if n is n1.+1 then
    let m' := flvl1 d.+1 m dst in
    frunl n1 d.+1 m' m (rcons acc (fcount forbi fpopi m'))
  else acc.

(* TWO DEPTHS, and what they cost before today: 170.9 s at ten and 2 904.8 at
   thirteen.  The counts must not move -- 2560, 72832, 1192960, 14731320. *)

Time Eval native_compute in frunl 10 0 (mkempty tt) (mkempty tt) [::].

Time Eval native_compute in frunl 13 0 (mkempty tt) (mkempty tt) [::].
