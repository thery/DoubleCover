(* =========================================================================  *)
(*  RowCubi.v -- the twenty cubies as twenty int63, the way the search runs.  *)
(* =========================================================================  *)

(* RowCub.v CARRIES A LIST OF nat, which is where the proofs are stated, and  *)
(* a nat operation costs a microsecond where an int63 one costs a twentieth.  *)
(* So the search cannot run on it, exactly as it cannot run on Table.v's      *)
(* lists: Tabi.v is the int63 twin there, and this file is the twin here.     *)
(*                                                                           *)
(* A MOVE IS TWO TABLE READS AND ONE ARRAY READ PER PLACE.  The move's own    *)
(* twenty say, for each place, which place the cubie comes from and how far   *)
(* it is turned on the way; those two are split apart here into ymvpi and     *)
(* ymvti so that the step does no division at all.  ymvpi already carries     *)
(* the offset of eight for an edge, so the read is direct.                    *)
(*                                                                           *)
(* THE MOVE UNDONE IS WHAT IS TABULATED, since that is what composes the      *)
(* move on the right -- see RowCub's zstep.                                   *)
(*                                                                           *)
(* WHAT IS CHECKED: the int63 step and the list step agree, on every position *)
(* two moves from the root.  The bridge lemma itself is not proved yet.       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Lehmer RowTabP RowMemb RowCub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

Definition nsmli : int := 20.               (* eight corners and twelve edges *)
Definition nmvni : int := 18.               (* the moves                      *)

(* ---- the move's twenty, split into a place and a turn -------------------- *)

(* where place p reads from: a corner place under eight, an edge place with   *)
(* the offset of eight already in it                                          *)
Definition ymvpn (k : nat) : seq nat :=
  [seq (let v := nth 0%N (ymvv k) p in
        if (p < 8)%N then (v %/ 3)%N else (8 + v %/ 2)%N) | p <- iota 0 20].

(* and how far it is turned on the way *)
Definition ymvtn (k : nat) : seq nat :=
  [seq (let v := nth 0%N (ymvv k) p in
        if (p < 8)%N then (v %% 3)%N else (v %% 2)%N) | p <- iota 0 20].

(* the eighteen of each, flat: move k at k * 20 *)
Definition ymvpi : arr := Eval vm_compute in
  mkarrn (nmvni * nsmli)
    [seq of_nat v | v <- flatten [seq ymvpn k | k <- iota 0 18]].

Definition ymvti : arr := Eval vm_compute in
  mkarrn (nmvni * nsmli)
    [seq of_nat v | v <- flatten [seq ymvtn k | k <- iota 0 18]].

Definition yrooti : arr := Eval vm_compute in
  mkarrn nsmli [seq of_nat v | v <- yroot].

(* ---- a move ------------------------------------------------------------- *)

(* twenty reads and twenty writes, and the turn added round the place: the    *)
(* corners three at a time, the edges two.  The forty eight entry table is    *)
(* forty eight of each.                                                       *)
Definition zstepi (x : arr) (k : int) : arr :=
  let b := k * nsmli in
  RowMap.ifold 12 8
    (fun j a =>
       let i := b + j in
       let g := PArray.get x (PArray.get ymvpi i) in
       let r := Uint63.mod g 2 in
       PArray.set a j (g - r + Uint63.mod (r + PArray.get ymvti i) 2))
    (RowMap.ifold 8 0
       (fun j a =>
          let i := b + j in
          let g := PArray.get x (PArray.get ymvpi i) in
          let r := Uint63.mod g 3 in
          PArray.set a j (g - r + Uint63.mod (r + PArray.get ymvti i) 3))
       (PArray.make nsmli 0)).

(* ---- and that it is RowCub's step --------------------------------------- *)

Definition a2y (x : arr) : seq nat :=
  [seq to_nat (PArray.get x (of_nat j)) | j <- iota 0 20].

(* the root, every move of it, and every move of those: the int63 twenty and  *)
(* the list twenty are the same twenty.                                       *)
Definition zstepiC : bool :=
  (a2y yrooti == yroot) &&
  all (fun k =>
        (a2y (zstepi yrooti (of_nat k)) == zstep yroot k)
        && all (fun l => a2y (zstepi (zstepi yrooti (of_nat k)) (of_nat l))
                         == zstep (zstep yroot k) l)
              (iota 0 18))
      (iota 0 18).

Lemma zstepiCP : zstepiC. Proof. by vm_compute. Qed.
