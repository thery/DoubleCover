(* =========================================================================  *)
(*  RowCubDef.v -- the plain run's definitions, and not one proof.            *)
(* =========================================================================  *)

(* THE FOLD'S RUN AND ITS PROOF ARE TWO FILES; SO ARE THE PLAIN ONE'S.  This  *)
(* names the map the twenty leave on the plain map, and the one boolean the   *)
(* certificate asks about it.  RowCubBool settles that boolean and loads no   *)
(* proof to do it; RowCubReal says what being true buys and runs nothing.     *)
(*                                                                            *)
(* NO Lemma, NO Proof, NO Qed HERE, and that is the point.                    *)
(*                                                                            *)
(* IT IS THE PLAIN MAP, 812 851 200 words -- the map is NOT folded, and that  *)
(* is the whole difference from RowFoldCubDef.  Everything else the folded    *)
(* run has is here: Rokicki's folded phase one table with the moves it names, *)
(* his early stop, hcoset's two cuts, and the witnesses marked into the map   *)
(* the run leaves rather than held in a second one.                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal.
Require Import Fold FoldTables P1Fdec P1FTable RowMask RowSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* ---- which of the eighteen are moves of H -------------------------------- *)

(* The solved coordinate is twist nought and the solved flip and slice rank,  *)
(* which is csolvedci itself.  A move of H is one that leaves it alone.       *)
(* RowFoldCubDef works the same number out for the folded run.                *)
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

(* THE MAP THE TWENTY LEAVE, AND IT IS NOT NAMED AS A VALUE.  A nullary      *)
(* Definition compiles to a top level value native_compute keeps for good,   *)
(* so naming the unmarked map would hold it alive beside the marked one, and *)
(* every write on a version something still points at is kept as history.    *)
(* THE DEPTH IS AN ARGUMENT, so the footprint can be watched at thirteen in  *)
(* minutes before twenty is paid for.                                        *)
Definition rowmapp (n : nat) : rmap :=
  ymfinsk e8numi e4biti mpgi mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
          ishmi actfsri tomembi okmvv srch n.

(* THE WITNESSES GO INTO THE MAP THE RUN LEAVES.  RowFinal keeps them in a   *)
(* second whole map -- 812 851 200 words for thirty two bits -- and asks     *)
(* mfull2 of the two.  RowMark says a mark keeps a map sound, so one map     *)
(* does, and mfull alone is the test.                                        *)
Definition ycwitsp : rmap :=
  foldr (fun t m => let: (pg, gr, bt, _) := t in mmark m pg gr bt)
        (rowmapp 20) rowwits.

(* ---- and the boolean the run has to settle ------------------------------- *)

(* THE RUN ANSWERS ONE BOOLEAN AND NOTHING ELSE.  Naming it here is what      *)
(* keeps the two files apart: RowCubBool says this is true and needs no proof *)
(* to say it, and the correctness theorem reads `rowfullp = true ->' and      *)
(* never has to look inside the map.                                          *)
Definition rowfullp : bool := mfull ycwitsp.
