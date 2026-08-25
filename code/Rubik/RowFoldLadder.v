(* =========================================================================  *)
(*  RowFoldLadder.v -- the folded row, level by level, counted at each one.   *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  One run, and the number of members after every     *)
(* level: what the prototype prints in its `done' column, so the two can be   *)
(* set side by side.                                                          *)
(*                                                                            *)
(* ONE RUN, NOT ELEVEN.  A ladder that starts from the seed again at every    *)
(* depth pays for the levels below it every time; this threads the two maps   *)
(* through as the run does and counts the map as it passes.  A count is one   *)
(* sweep of 0.89 GB, so twenty of them are the price of seeing the numbers.   *)
(*                                                                            *)
(* THE ROW'S FIRST DEPTH IS TEN -- its representative is that far from H --   *)
(* so the first nine counts are nought and the tenth is the prototype's       *)
(* depth ten.  For the superflip's row the prototype printed:                 *)
(*                                                                            *)
(*   depth 10          2 560 members                                          *)
(*   depth 11         72 832                                                  *)
(*   depth 12      1 192 960                                                  *)
(*   depth 13     14 731 320                                                  *)
(*   depth 14    148 423 860                                                  *)
(*   depth 15  1 173 663 208                                                  *)
(*   depth 16  4 973 524 638   (the search stopped early, as hcoset's does)   *)
(*   depth 20 19 508 428 768   of 19 508 428 800, so thirty two left over     *)

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
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* RowInst's own step and leaf test, spelt out as RowFoldChk.v spells them    *)
(* out, so that this file does not depend on how a section discharged them.   *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

(* THE LEAF TEST MEETS NO PERMUTATION.  coordfs takes a mathcomp permutation *)
(* and those do not compute; RowInst spends it once, and what the search      *)
(* meets here is a number.                                                    *)
Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedci, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) coordfs1i].

(* one level of the folded row, with hcoset's stop on the last one searched   *)
Notation flvl1 :=
  (flvls e8numi e4biti
     fpgi fsrci fsgri fsloi fshii fsbti
     mgri mswi mloi mhii
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     fstep xstep tomemb okmvv fsolved croot sroot srch forbi fpopi).

(* the run, keeping the count after each level.  The two maps swap: what the  *)
(* level wrote is the next level's source, and its source is the next one's   *)
(* destination.                                                               *)
Fixpoint frunl (n : nat) (d : nat) (m dst : rmap) (acc : seq int) : seq int :=
  if n is n1.+1 then
    let m' := flvl1 d.+1 m dst in
    frunl n1 d.+1 m' m (rcons acc (fcount forbi fpopi m'))
  else acc.

(* the whole row: twenty levels, and the count after each *)
Time Eval native_compute in
  frunl 20 0 (mkempty tt) (mkempty tt) [::].
