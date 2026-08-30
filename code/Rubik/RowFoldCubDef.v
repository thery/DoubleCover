(* =========================================================================  *)
(*  RowFoldCubDef.v -- everything the run needs, and not one proof.           *)
(* =========================================================================  *)

(* THE RUN AND THE PROOF ARE TWO FILES BECAUSE THEY LOAD TWO DIFFERENT        *)
(* THINGS.  What the search reads is tables; what the certificate reads is    *)
(* proofs about the cube.  This file holds the first and names the map, and   *)
(* RowFoldCubBool asks the one boolean about it, so the process that runs     *)
(* for hours carries nothing it does not read.                                *)
(*                                                                            *)
(* NO Lemma, NO Proof, NO Qed HERE, and that is the point: what a file        *)
(* requires is what it loads, and a definition needs no proof file.           *)
(*                                                                            *)
(* The four definitions RowCubInst and RowReal would have given are written   *)
(* out with the same bodies, so the terms are the same to the kernel and      *)
(* RowFoldCubProof still takes RowFoldCubBool's answer by unfolding alone.    *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi.
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

(* The solved coordinate is twist nought and the solved flip and slice rank,  *)
(* which is csolvedci itself.  A move of H is one that leaves it alone.       *)
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

(* ---- the cube the search carries ----------------------------------------- *)

(* RowCubInst's ycsolved and ytomemb, and RowReal's okmvv and srch, written   *)
(* out.  Same bodies, so the kernel sees the same terms.                      *)
(* THE TEST AT EVERY NODE TAKES THE COORDINATE AND NOTHING ELSE.  The search  *)
(* used to hand it the state as well, and this instance built a forty eight   *)
(* cell array to fill an argument RowInst's csolvedb never read -- at every   *)
(* node, since native_compute is call by value.  The argument is gone from    *)
(* the search itself now, so it cannot come back.                             *)
Definition ycsolvedd (c : int) : bool := Uint63.eqb c csolvedi.

Definition ytomembd (y : arr) : memb := tomembi (y2ti y).

Definition okmvvd (pv k : int) : bool :=
  if (18 <=? pv)%uint63 then true
  else let fp := (pv / 3)%uint63 in
       let fk := (k / 3)%uint63 in
       ~~ ((fp =? fk)%uint63 || (fp =? fk + 3)%uint63).

Definition srchd : nat := 16.

(* ---- the map the run leaves, with the witnesses marked in ---------------- *)

(* fmfino's body, with RowFoldCubReal's arguments and RowFoldCubProof's       *)
(* tables put in.  Every optimization is on: Rokicki's early stop and         *)
(* hcoset's two cuts, which is what frunsk is.                                *)
(*                                                                            *)
(* THE UNMARKED MAP IS NOT NAMED.  A nullary Definition compiles to a top     *)
(* level value native_compute keeps for good, so naming it would hold the map *)
(* the marking writes on alive beside the marked one, and every write on a    *)
(* version something still points at is kept as history.                      *)
(* THE DEPTH IS AN ARGUMENT, so the footprint can be watched at thirteen in   *)
(* minutes before twenty is paid for.  It is a function and not a value, so   *)
(* nothing holds a map after it is read.                                      *)
Definition rowmap (n : nat) : rmap :=
  frunsk e8numi e4biti fpgi fsrci fsgri fsloi fshii fsbti
         mgri mswi mloi mhii
         p1ftab frepi fsymi twsymi
         dnlo_data dnhi_data fllo_data flhi_data
         (RowInst.cstep actfsri) zstepi ytomembd okmvvd ycsolvedd
         RowInst.croot yrooti srchd forbi fpopi ishmi
         n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition ycwitso : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        (rowmap 20) rowwits.

(* ---- and the boolean the run has to settle ------------------------------- *)

(* THE RUN ANSWERS ONE BOOLEAN AND NOTHING ELSE.  Naming it here is what      *)
(* keeps the two files apart: RowFoldCubBool says this is true and needs no   *)
(* proof to say it, and the correctness theorem reads `rowfull = true ->' and *)
(* never has to look inside the map.                                          *)
Definition rowfull : bool := mfullf ycwitso.
