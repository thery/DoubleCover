(* =========================================================================  *)
(*  RowFoldOptT.v -- the folded row with EVERY optimization on.               *)
(* =========================================================================  *)

(* WHAT IS NEW.  RowFoldSrch.flvlsk is the early stop AND the two cuts in one *)
(* level; flvls had the first and flvlk the second and neither had both.      *)
(* RowFoldOpt10, 13, 15 and 20 run it, one depth each, so the four go side by *)
(* side and twenty is measured rather than guessed.                           *)
(*                                                                            *)
(* NOTHING HERE IS PROVED -- it is the measuring run.  What says it is right  *)
(* is the count.                                                              *)
(*                                                                            *)
(* This file is RowFoldCut.v with flvlk replaced by flvlsk; the note below is *)
(* that file's and still holds.                                               *)
(*                                                                            *)
(* WHAT THE CUTS ARE.  RowFoldSrch.fsrchk adds the two the prototype has and  *)
(* the Rocq search did not: at the bottom, refuse a move that is in H; and    *)
(* near the bottom, refuse a move that does not go straight at H.  Both are   *)
(* switched on only once the row is past six million members, which is depth  *)
(* fourteen, so nothing below that changes.                                   *)
(*                                                                            *)
(* THE MOVES OF H ARE NOT HARDWIRED.  A move is in H exactly when it leaves   *)
(* the solved phase one coordinate alone -- no twist, no flip, the middle     *)
(* edges where they were -- and that is a computation on the tables the       *)
(* search already reads.  ishmC checks there are ten of them.                 *)
(*                                                                            *)
(* NOTHING HERE IS PROVED.  The cuts are in the measuring search only, and    *)
(* what says they are right is the count: the prototype's row has             *)
(* 148 423 860 members at depth fourteen.                                     *)

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

Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

(* the test at the end of a branch is one comparison, as RowInst has it *)
Definition fsolved (c : int) (_ : pstt) : bool := Uint63.eqb c csolvedci.

(* ---- which of the eighteen are moves of H -------------------------------- *)

(* The solved coordinate is twist nought and the solved flip and slice rank,  *)
(* which is csolvedci itself.  A move of H is one that leaves it alone.       *)
Definition ishmi : int :=
  Eval vm_compute in
  ifold nmvn 0%uint63
    (fun k a =>
       if Uint63.eqb (fstep csolvedci k) csolvedci
       then Uint63.lor a (Uint63.lsl 1%uint63 k) else a)
    0%uint63.

(* there are ten of them, and this says so *)
Definition ishmC : bool :=
  Uint63.eqb (Uint63.add (PArray.get fpopi (Uint63.land ishmi 4095%uint63))
                         (PArray.get fpopi
                            (Uint63.land (Uint63.lsr ishmi 12%uint63)
                                         4095%uint63)))
             10%uint63.

Lemma ishmCP : ishmC. Proof. by vm_compute. Qed.

(* ---- the level, and the run that decides when to cut --------------------- *)

Notation flvlo :=
  (flvlsk e8numi e4biti
     fpgi fsrci fsgri fsloi fshii fsbti
     mgri mswi mloi mhii
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     fstep xstep tomembi okmvv fsolved croot sroot srch forbi fpopi ishmi).

(* ---- the run, with everything on ----------------------------------------- *)

(* THE CUTS COME ON WHEN THE ROW IS BIG, which is the prototype's own rule:   *)
(* past six million members.  The count is taken after every level anyway, so *)
(* it costs nothing to ask -- and it is what lets a run be watched.           *)
Fixpoint fruno (n : nat) (d : nat) (n0 : int) (m dst : rmap)
               (acc : seq int) : seq int :=
  if n is n1.+1 then
    let m' := flvlo (Uint63.ltb ncutb n0) d.+1 m dst in
    let n1' := fcount forbi fpopi m' in
    fruno n1 d.+1 n1' m' m (rcons acc n1')
  else acc.
