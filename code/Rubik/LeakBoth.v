(* =========================================================================  *)
(*  LeakBoth.v -- a big table AND writes, which is the one pair not tried.    *)
(* =========================================================================  *)

(* Round one: a map written pass after pass, no table -- flat.                *)
(* Round two: a tree allocating an array a node, no table -- flat.            *)
(* Round three: two hundred million reads of the folded table, no writes --   *)
(*              flat.                                                         *)
(* Round four, here: every word written is a word read from the table.        *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import P1Fold P1FTable.

Local Open Scope uint63_scope.

Definition csizef : int := 1290240.
Definition nchunk : int := 44.
Definition arr := PArray.array int.
Definition rmap := PArray.array arr.

Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  match n with O => a | S n1 => ifold A n1 (Uint63.add x 1) f (f x a) end.

Arguments ifold {A} n x f a.

Definition nchunkn : nat := 44.
Definition ncw : nat := 1290240.

Definition mk (u : unit) : rmap :=
  ifold nchunkn 0
    (fun c a => PArray.set a c (PArray.make csizef 0))
    (PArray.make nchunk (PArray.make 1 0)).

(* one pass: every word written carries a word of the table into it *)
Definition pass (src dst : rmap) : rmap :=
  ifold nchunkn 0
    (fun c d =>
       let sa := PArray.get src c in
       let tc := PArray.get p1ftab (Uint63.land c 3) in
       let a := ifold ncw 0
                  (fun i b =>
                     PArray.set b i
                       (Uint63.lor (PArray.get sa i)
                          (PArray.get tc (Uint63.land i 2097151))))
                  (PArray.get d c) in
       PArray.set d c a)
    dst.

Fixpoint passn (n : nat) (m d : rmap) : rmap :=
  match n with O => m | S n1 => passn n1 (pass m d) m end.

Definition chk (m : rmap) : int :=
  ifold nchunkn 0
    (fun c a => Uint63.add a (PArray.get (PArray.get m c) 0)) 0.

Time Eval native_compute in chk (passn 12 (mk tt) (mk tt)).
