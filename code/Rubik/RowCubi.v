(* =========================================================================  *)
(*  RowCubi.v -- the twenty cubies as twenty int63, the way the search runs.  *)
(* =========================================================================  *)

(* RowCub.v CARRIES A LIST OF nat, which is where the proofs are stated, and  *)
(* a nat operation costs a microsecond where an int63 one costs a twentieth.  *)
(* So the search cannot run on it, exactly as it cannot run on Table.v's      *)
(* lists: Tabi.v is the int63 twin there, and this file is the twin here.     *)
(*                                                                           *)
(* A MOVE IS THREE TABLE READS AND ONE ARRAY READ PER PLACE, AND NO           *)
(* ARITHMETIC.  The move's own twenty say, for each place, which place the    *)
(* cubie comes from and how far it is turned on the way.  ymvpi holds the     *)
(* first, with the offset of eight for an edge already in it.  The second is  *)
(* not added but looked up: tturni holds, for every cubie and every turn,     *)
(* the cubie turned, and offi holds where in it this move's place looks.      *)
(*                                                                           *)
(* MEASURED at depth twelve on gukesh: the forty eight entry table 17.9 s,    *)
(* the twenty 11.5 s when the turn was three arithmetic operations, and no    *)
(* position at all 5.4 s.                                                     *)
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

(* the places, flat: move k at k * 20 *)
Definition ymvpi : arr := Eval vm_compute in
  mkarrn (nmvni * nsmli)
    [seq of_nat v | v <- flatten [seq ymvpn k | k <- iota 0 18]].

(* ---- the turn, looked up rather than added ------------------------------ *)

(* a cubie is three times its place plus its turn, so turning it by u is an   *)
(* operation on a number under twenty four.  There are two of them, three     *)
(* turns for a corner and two for an edge, and 2 * 3 * 24 is a small table.   *)
Definition tturnn : seq nat :=
  [seq (let g := (i %% 24)%N in let u := (i %/ 24 %% 3)%N in
        let m := (if (i < 72)%N then 3 else 2)%N in
        (g - g %% m + (g %% m + u) %% m)%N) | i <- iota 0 144].

Definition tturni : arr := Eval vm_compute in
  mkarrn 144 [seq of_nat v | v <- tturnn].

(* and where in it place j of move k looks: the corner half or the edge half, *)
(* at this move's turn                                                        *)
Definition offn (k : nat) : seq nat :=
  [seq (let u := nth 0%N (ymvtn k) j in
        ((if (j < 8)%N then 0 else 72) + u * 24)%N) | j <- iota 0 20].

Definition offi : arr := Eval vm_compute in
  mkarrn (nmvni * nsmli)
    [seq of_nat v | v <- flatten [seq offn k | k <- iota 0 18]].

Definition yrooti : arr := Eval vm_compute in
  mkarrn nsmli [seq of_nat v | v <- yroot].

(* ---- a move ------------------------------------------------------------- *)

(* twenty places, and for each of them three table reads, one array read and  *)
(* one write into a fresh twenty.  The forty eight entry table is forty       *)
(* eight of each.                                                             *)
Definition zstepi (x : arr) (k : int) : arr :=
  let b := k * nsmli in
  foldi 20 0
    (setf (fun j => PArray.get tturni
                      (PArray.get offi (b + j)
                       + PArray.get x (PArray.get ymvpi (b + j)))))
    (PArray.make nsmli 0).

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
