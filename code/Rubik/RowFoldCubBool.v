(* =========================================================================  *)
(*  RowFoldCubBool.v -- the boolean the certificate asks, and nothing else.   *)
(* =========================================================================  *)

(* THE RUN AND THE PROOF DO NOT HAVE TO BE IN THE SAME PROCESS.  What the     *)
(* certificate needs from the run is one bit: the map twenty levels leave,    *)
(* with the thirty two witnesses marked in, has no bit of the row clear.      *)
(* Nothing about the cube is read to decide that.                             *)
(*                                                                            *)
(* SO THIS FILE LOADS ONLY WHAT THE RUN READS.  Its Require list is the       *)
(* measuring run's, word for word, plus the four files that name the twenty   *)
(* cubies -- Lehmer, RowCub, RowCubi, RowCubInst.  The thirty eight proof     *)
(* files RowFoldCubProof also loads are not here, because a boolean does not  *)
(* need them.  The measuring run on this list plateaued at 15.5 GB.           *)
(*                                                                            *)
(* THE MAP IS fmfino's BODY, spelled out.  RowFoldFinal defines fmfino as     *)
(* this application of frunsk, and RowFoldCubReal applies it to the tables    *)
(* RowFoldCubProof names; both steps are delta, so the two terms are the      *)
(* same and RowFoldCubProof takes this lemma without computing.               *)
(*                                                                            *)
(* NOTHING ABOUT THE CUBE IS PROVED HERE.  The cube side is                   *)
(* RowFoldCubReal.real_superflip_row_foldo, which asks exactly this bit.      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal RowMembi.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- which of the eighteen are moves of H -------------------------------- *)

(* Word for word RowFoldCubProof's own, so that the two constants are the     *)
(* same literal: both are settled by vm_compute at definition time.           *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition ishmi : int :=
  Eval vm_compute in
  ifold nmvn 0%uint63
    (fun k a =>
       if Uint63.eqb (fstep csolvedci k) csolvedci
       then Uint63.lor a (Uint63.lsl 1%uint63 k) else a)
    0%uint63.

(* ---- the map the run leaves, with the witnesses marked in ---------------- *)

(* fmfino's body, with RowFoldCubReal's arguments and RowFoldCubProof's       *)
(* tables put in.  Every optimization is on: Rokicki's early stop and         *)
(* hcoset's two cuts, which is what frunsk is.                                *)
(*                                                                            *)
(* THE UNMARKED MAP IS NOT NAMED, and that is not a style choice.  A nullary  *)
(* Definition compiles to a top level value that native_compute keeps for     *)
(* good, so naming it would hold the map the marking writes on alive beside   *)
(* the marked one, and every write on a version something still points at is  *)
(* kept as history.  Measured elsewhere in this tree: 7.5 GB -> 13 and 86 s   *)
(* -> 400.  Written inline it is an application, evaluated once and dropped.  *)
Definition ycwitso : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        (frunsk e8numi e4biti fpgi fsrci fsgri fsloi fshii fsbti
                mgri mswi mloi mhii
                p1ftab frepi fsymi twsymi
                dnlo_data dnhi_data fllo_data flhi_data
                (RowInst.cstep actfsri) zstepi (ytomemb tomemb) okmvv ycsolved
                RowInst.croot yrooti srch forbi fpopi ishmi
                20 0 0%uint63 (mkempty tt) (mkempty tt))
        rowwits.

(* ---- and the bit --------------------------------------------------------- *)

(* THE LONG POLE.  Measured on the same search without the marking and        *)
(* without the proof loaded: 33 305 s and 15.5 GB.                            *)
Lemma r_full_bool : mfullf ycwitso.
Proof. Time native_cast_no_check (erefl true). Qed.
