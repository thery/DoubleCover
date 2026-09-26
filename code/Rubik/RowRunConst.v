(* =========================================================================  *)
(*  RowRunConst.v -- the constants both row runs are handed, and not one      *)
(*  proof.                                                                    *)
(* =========================================================================  *)

(* The moves of H, and RowCubInst's ycsolved and ytomemb and RowReal's okmvv  *)
(* and srch written out, for the folded run (RowFoldCubDef) and the plain     *)
(* one (RowCubDef).  RowOpt reads them too.                                   *)

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
Definition ycsolvedd (c : int) : bool := Uint63.eqb c csolvedci.

Definition ytomembd (y : arr) : memb := tomembi (y2ti y).

Definition okmvvd (pv k : int) : bool :=
  if (18 <=? pv)%uint63 then true
  else let fp := (pv / 3)%uint63 in
       let fk := (k / 3)%uint63 in
       ~~ ((fp =? fk)%uint63 || (fp =? fk + 3)%uint63).

Definition srchd : nat := 16.
