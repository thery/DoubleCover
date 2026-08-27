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

(* ---- what the two tables have to be -------------------------------------- *)

(* a group: unrank the outer edges of that number, conjugate, rank, and the   *)
(* number of the answer without its parity bit                                *)
Definition sgrexp (s pty g : nat) : int :=
  let r := PArray.get e8invi (of_nat (2 * g + pty)) in
  Uint63.lsr (PArray.get e8numi
                (rank8 (fun j => se s (up8 r (seinv s j))))) 1.

(* a bit: the same on the middle four, which are the places eight to eleven   *)
Definition sbtexp (s bt : nat) : int :=
  let r := PArray.get e4ofi (of_nat bt) in
  PArray.get e4biti
    (rank4 (fun j => (se s (8 + up4 r (seinv s (8 + j) - 8))%N - 8)%N)).

Definition fsgrC : bool :=
  all (fun s => all (fun pty => all (fun g =>
         PArray.get fsgri (of_nat (((s * 2 + pty) * 20160) + g))
         == sgrexp s pty g)
       (iota 0 20160)) (iota 0 2)) (iota 0 16).

Definition fsbtC : bool :=
  all (fun s => all (fun bt =>
         PArray.get fsbti (of_nat (s * 24 + bt)) == sbtexp s bt)
       (iota 0 24)) (iota 0 16).

Lemma fsbtCP : fsbtC. Proof. by vm_compute. Qed.
Lemma fsgrCP : fsgrC. Proof. by vm_compute. Qed.
