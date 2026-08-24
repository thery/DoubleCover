(* =========================================================================  *)
(*  LeakTab.v -- native_compute's memory, on nothing but reading a big table. *)
(* =========================================================================  *)

(* Rounds one and two -- a map written pass after pass, and a tree eighteen   *)
(* wide allocating an array a node -- do not grow.  What a real run has that  *)
(* they do not is a BIG TABLE: the folded phase one table is 140 908 410      *)
(* entries in five chunks, and the search reads it once a node.               *)
(*                                                                            *)
(* This reads it and does nothing else.                                       *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import P1Fold P1FTable.

Local Open Scope uint63_scope.

Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  match n with O => a | S n1 => ifold A n1 (Uint63.add x 1) f (f x a) end.

Arguments ifold {A} n x f a.

Definition nreads : nat := 200000000.

(* a read that wanders over the whole table, as a search does *)
Definition rd (n : nat) : int :=
  ifold n 0
    (fun i a =>
       let c := Uint63.land (Uint63.lsr i 21) 3 in
       let o := Uint63.land (Uint63.add i (Uint63.mul a 7)) 2097151 in
       Uint63.add a (PArray.get (PArray.get p1ftab c) o))
    0.

Time Eval native_compute in rd nreads.
