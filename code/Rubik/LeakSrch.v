(* =========================================================================  *)
(*  LeakSrch.v -- the search as it really runs: tree, table, and marks.       *)
(* =========================================================================  *)

(* Round one    a map written pass after pass                    flat         *)
(* Round two    a tree, an array a node, marks into the map      flat         *)
(* Round three  two hundred million reads of the table           flat         *)
(* Round four   writes carrying table reads                      flat         *)
(* Round five, here: ALL THREE AT ONCE, which is what the row's search does:  *)
(*   a tree eighteen wide, a new position at every node, the table read at    *)
(*   every node to decide whether to go on, and a mark at every leaf.         *)

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

Definition mk (u : unit) : rmap :=
  ifold nchunkn 0
    (fun c a => PArray.set a c (PArray.make csizef 0))
    (PArray.make nchunk (PArray.make 1 0)).

Definition npos : nat := 48.

Definition step (x : arr) (k : int) : arr :=
  ifold npos 0
    (fun i a => PArray.set a i (Uint63.add (PArray.get x i) k))
    (PArray.make 48 0).

(* the table read at a node, as p1get is *)
Definition dist (v : int) : int :=
  PArray.get (PArray.get p1ftab (Uint63.land (Uint63.lsr v 21) 3))
             (Uint63.land v 2097151).

Definition mark (m : rmap) (v : int) : rmap :=
  let c := Uint63.land v 31 in
  let a := PArray.get m c in
  let i := Uint63.land v 1048575 in
  PArray.set m c (PArray.set a i (Uint63.lor (PArray.get a i) 1)).

Fixpoint srch (togo : nat) (x : arr) (m : rmap) : rmap :=
  match togo with
  | O => mark m (PArray.get x 0)
  | S t =>
    ifold 18 0
      (fun k mm =>
         let x' := step x k in
         let d := dist (PArray.get x' 0) in
         (* the table decides, as the row's search does *)
         if Uint63.eqb (Uint63.land d 15) 15 then mm else srch t x' mm)
      m
  end.

Definition chk (m : rmap) : int :=
  ifold nchunkn 0
    (fun c a => Uint63.add a (PArray.get (PArray.get m c) 0)) 0.

Time Eval native_compute in chk (srch 6 (PArray.make 48 1) (mk tt)).
