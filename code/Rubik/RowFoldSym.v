(* =========================================================================  *)
(*  RowFoldSym.v -- the fold tables are the renamings, on ranks.              *)
(* =========================================================================  *)

(* fsgr and fsbt say what a renaming does to a group and to a bit.  What that *)
(* has to mean is the renaming acting on the cubies, read through the ranks:  *)
(* unrank the permutation the number names, conjugate it by the renaming,     *)
(* rank it again.  Both sides are computable, so this is a sweep and not a    *)
(* proof -- 16 * 2 * 20160 for the groups and 16 * 24 for the bits.           *)
(*                                                                            *)
(* THE PARITY IS WHY THERE ARE TWO GROUP TABLES.  A group is a pair of outer  *)
(* edge permutations differing by one exchange, and a renaming exchanges two  *)
(* other cubies, so the two members of a pair land in two different pairs.    *)
(* They are told apart by their parity, which is the low bit of the number,   *)
(* and that is the pty the table is indexed by.                               *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord.
Require Import Coordfs Coordfsi Phase1 Diameter Moves Far Sym16.
Require Import Row RowMap RowTabL RowTabP RowTab RowMemb.
Require Import RowFold RowTabF RowFoldTab.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* ---- a renaming, on the twelve edge places ------------------------------- *)

(* Where the renaming sends an edge place: apply it to that place's primary   *)
(* facelet and read which place the answer belongs to.                        *)
Definition se (s p : nat) : nat :=
  eposn (nth 0%N (nth [::] sym16ts s) (nth 0%N eprim p)).

(* and back again, which the conjugation needs *)
Definition seinv (s j : nat) : nat := index j [seq se s p | p <- iota 0 12].


(* ---- the two numberings of the sixteen ----------------------------------- *)

(* Sym16.v orders the renamings one way, and the fold tables, which come from *)
(* the prototype's own list, order them another.  This is the map between the *)
(* two, and it is not taken on trust: renaming u of the tables is asked below *)
(* to be sym16ts (fren2sym u) acting on the ranks, so a wrong entry here makes *)
(* the sweep fail rather than pass.                                           *)
Definition fren2sym : seq nat :=
  [:: 15; 6; 2; 10; 12; 11; 1; 5; 7; 8; 0; 3; 13; 4; 9; 14]%N.

(* THE TWELVE PLACES, WORKED OUT ONCE.  se walks two lists to answer about    *)
(* one place, and a rank asks about eight, so a sweep that calls it inside a  *)
(* rank pays that walk five million times.  A renaming and its inverse are    *)
(* twelve numbers each; they are worked out once for each of the sixteen and  *)
(* then only read.                                                            *)
Definition sev (s : nat) : seq nat := [seq se s p | p <- iota 0 12].
Definition siv (s : nat) : seq nat := [seq seinv s j | j <- iota 0 12].

(* ---- the bounds, and why they are int63 ---------------------------------- *)

(* EVERY INDEX BELOW IS AN int63.  of_nat walks its argument, so naming a     *)
(* slot of the 645 120 entry group table costs 645 120 steps to build the     *)
(* number -- once for every group of every renaming.  Counted in int63 the    *)
(* same index is two multiplications and an addition.                         *)
Definition nptyn : nat := to_nat 2.
Definition nsymn : nat := to_nat nsymi.
Definition nhalfi : int := 4096.               (* the words of half a group  *)
Definition nhalfn : nat := to_nat nhalfi.
Definition nloi : int := 12.                   (* bits in half a word        *)
Definition nlon : nat := to_nat nloi.

(* ---- what the tables have to be ------------------------------------------ *)

(* a group: unrank the outer edges of that number, conjugate, rank, and the   *)
(* number of the answer without its parity bit                                *)
Definition sgrexp (ev iv : seq nat) (pty g : int) : int :=
  let r := PArray.get e8invi (Uint63.add (Uint63.mul 2 g) pty) in
  Uint63.lsr (PArray.get e8numi
                (rank8 (fun j => nth 0%N ev (up8 r (nth 0%N iv j))))) 1.

(* a bit: the same on the middle four, which are the places eight to eleven   *)
Definition sbtexp (ev iv : seq nat) (bt : int) : int :=
  let r := PArray.get e4ofi bt in
  PArray.get e4biti
    (rank4 (fun j =>
       (nth 0%N ev (8 + up4 r (nth 0%N iv (8 + j) - 8))%N - 8)%N)).

(* half a word: twelve bits moved one at a time, which is what the bit table  *)
(* already says.  The low half of a word is the twelve middle permutations of *)
(* one parity and the high half the other twelve, and a renaming keeps a      *)
(* parity, so a bit of a half stays in its own half.                          *)
Definition shalf (u off v : int) : int :=
  ifold nlon 0%uint63
    (fun i a =>
       if Uint63.eqb (Uint63.land (Uint63.lsr v i) 1) 0 then a
       else
         Uint63.lor a
           (Uint63.lsl 1
              (Uint63.sub
                 (PArray.get fsbti
                    (Uint63.add (Uint63.mul u nbiti) (Uint63.add off i)))
                 off)))
    0%uint63.

(* ---- the four sweeps ----------------------------------------------------- *)

Definition fsgrC1 (u : int) : bool :=
  let s := nth 0%N fren2sym (to_nat u) in
  let ev := sev s in
  let iv := siv s in
  let b := Uint63.mul (Uint63.mul u 2) ngroupi in
  iter nptyn 0%uint63 (fun pty =>
    iter ngroupn 0%uint63 (fun g =>
      Uint63.eqb
        (PArray.get fsgri
           (Uint63.add (Uint63.add b (Uint63.mul pty ngroupi)) g))
        (sgrexp ev iv pty g))).

Definition fsgrC : bool := iter nsymn 0%uint63 fsgrC1.

Definition fsbtC1 (u : int) : bool :=
  let s := nth 0%N fren2sym (to_nat u) in
  let ev := sev s in
  let iv := siv s in
  let b := Uint63.mul u nbiti in
  iter nbitn 0%uint63 (fun bt =>
    Uint63.eqb (PArray.get fsbti (Uint63.add b bt)) (sbtexp ev iv bt)).

Definition fsbtC : bool := iter nsymn 0%uint63 fsbtC1.

Definition fsloC1 (u : int) : bool :=
  iter nhalfn 0%uint63 (fun v =>
    Uint63.eqb (PArray.get fsloi (Uint63.add (Uint63.lsl u 12) v))
               (shalf u 0 v)).

Definition fsloC : bool := iter nsymn 0%uint63 fsloC1.

Definition fshiC1 (u : int) : bool :=
  iter nhalfn 0%uint63 (fun v =>
    Uint63.eqb (PArray.get fshii (Uint63.add (Uint63.lsl u 12) v))
               (shalf u nloi v)).

Definition fshiC : bool := iter nsymn 0%uint63 fshiC1.

Lemma fsbtCP : fsbtC. Proof. by vm_compute. Qed.
Lemma fsloCP : fsloC. Proof. by vm_compute. Qed.
Lemma fshiCP : fshiC. Proof. by vm_compute. Qed.
Lemma fsgrCP : fsgrC. Proof. by vm_compute. Qed.
