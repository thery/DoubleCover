(* =========================================================================  *)
(*  RowLeafRun14.v -- the run to fourteen, with the run's leaf and straight.  *)
(* =========================================================================  *)

(* A BENCH, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* RowLeafBench measured one leaf: 12.0 us for the run's (the twenty turned   *)
(* back into forty eight and inverted, then ranked) against 1.16 us ranked    *)
(* straight from the twenty with a bit mask.  Fourteen has 148 423 860       *)
(* leaves, so the two runs below should differ by about 1 600 s.             *)
(*                                                                            *)
(*   cd code/Rubik && ulimit -s unlimited                                     *)
(*   /usr/bin/time -v coqc -R . Rubik RowLeafRun14.v                          *)
(*                                                                            *)
(* THE TWO COUNTS MUST BE THE SAME.  The first Eval pays for the tables       *)
(* arriving and is thrown away.                                               *)

(* RowFoldCubDef's own list, so every name rowmapi uses is in scope          *)
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
Require Import RowFoldCubDef RowFoldSrchI RowFoldCubDefI.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* RowLeafBench's bitleaf: the ranks straight from the twenty, with a bit     *)
(* mask.  A piece's count is its value less the values already seen below    *)
(* it, one read of a popcount table; the tables make the values 0 .. n-1.    *)
(* Measured there: 1.16 us a leaf against 12.0 for the run's.                *)
Definition lbmkt (f : int -> int) : arr :=
  ifold 24 0 (fun v a => PArray.set a v (f v)) (PArray.make 24 0).
Definition lbcq : arr := Eval vm_compute in lbmkt (fun v => v / 3).
Definition lbeq : arr := Eval vm_compute in lbmkt (fun v => v / 2).
Definition lbmq : arr :=
  Eval vm_compute in lbmkt (fun v => if 16 <=? v then v / 2 - 8 else 0).
Definition lbpop : arr := Eval vm_compute in
  ifold 256 0 (fun s a => PArray.set a s
     (ifold 8 0 (fun b c => c + ((s >> b) land 1)) 0)) (PArray.make 256 0).

Definition lbrank (tbl a : arr) (off : int) (nn : nat) (ni : int) : int :=
  Uint63.lsr
    (ifold nn 0
      (fun i st =>
         let v := PArray.get tbl (PArray.get a (Uint63.add off i)) in
         let bv := Uint63.lsl 1 v in
         let seen := Uint63.land st 255 in
         let c := Uint63.sub v
                    (PArray.get lbpop (Uint63.land seen (Uint63.sub bv 1))) in
         Uint63.lor
           (Uint63.lsl (Uint63.add (Uint63.mul (Uint63.lsr st 8)
                                               (Uint63.sub ni i)) c) 8)
           (Uint63.lor seen bv))
      0) 8.

Definition bitleaf (y : arr) : memb :=
  (lbrank lbcq y 0 8 8, lbrank lbeq y 8 8 8, lbrank lbmq y 16 4 4).

(* rowmapi with bitleaf in the place of ytomembd, and nothing else changed    *)
Definition rowmapd (n : nat) : rmap :=
  frunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepi bitleaf okmvvd ycsolvedd
          RowInst.croot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition dlev : nat := 14.

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapi dlev).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapd dlev).
