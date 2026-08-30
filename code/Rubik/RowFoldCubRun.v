(* =========================================================================  *)
(*  RowFoldCubRun.v -- the folded row, with the twenty cubies carried.        *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  This is RowFoldClimb with the search carrying      *)
(* twenty int63 instead of the forty eight entry table, on the FOLDED map --  *)
(* which is eleven times faster and 0.45 GB where the plain one is 6.5, and   *)
(* which no proof in the tree covers.                                         *)
(*                                                                            *)
(* THE COUNTS ARE THE CHECK.  They must not move: 2560, 72832, 1192960,       *)
(* 14731320.                                                                  *)
(*                                                                            *)
(* MEASURED at depth thirteen on roquableu, on the plain map: the search is   *)
(* 236.5 s with the table and 141.7 s with the twenty.                        *)

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
Require Import Lehmer RowCub RowCubi.

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
Definition fsolved (c : int) : bool := Uint63.eqb c csolvedci.

(* the member, read off the cube the twenty name.  It is asked at an answer  *)
(* and nowhere else, so the forty eight entry array is built there only.     *)
Definition ytomembi (y : arr) : memb := tomembi (y2ti y).

(* one level of the folded row, with hcoset's stop on the last one searched   *)
Notation flvl1 :=
  (flvls e8numi e4biti
     fpgi fsrci fsgri fsloi fshii fsbti
     mgri mswi mloi mhii
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     fstep zstepi ytomembi okmvv fsolved croot yrooti srch forbi fpopi).

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
