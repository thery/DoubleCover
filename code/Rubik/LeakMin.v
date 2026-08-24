(* =========================================================================  *)
(*  LeakMin.v -- native_compute's memory, on nothing but a persistent map.    *)
(* =========================================================================  *)

(* NOT PART OF ANYTHING.  No cube, no tables, no search: a map of forty four  *)
(* chunks of 1 290 240 words, and a pass that copies every word of one map    *)
(* into another.  Two maps, swapped, so the program holds two at a time and   *)
(* nothing else -- 0.9 GB of data whatever the number of passes.              *)
(*                                                                            *)
(* Run it at four passes and at twelve and compare the peak memory.  The same *)
(* program in OCaml holds 3 GB flat however many passes it does.              *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.

Local Open Scope uint63_scope.

Definition csizef : int := 1290240.
Definition nchunk : int := 44.

Definition arr := PArray.array int.
Definition rmap := PArray.array arr.

(* a count carried down, exactly as RowMap.v's ifold walks one                *)
Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  match n with O => a | S n1 => ifold A n1 (Uint63.add x 1) f (f x a) end.

Arguments ifold {A} n x f a.

Definition nchunkn : nat := 44.
Definition ncw : nat := 1290240.

(* every chunk its own array *)
Definition mk (u : unit) : rmap :=
  ifold nchunkn 0
    (fun c a => PArray.set a c (PArray.make csizef 0))
    (PArray.make nchunk (PArray.make 1 0)).

(* one pass: every word of src into dst, chunk by chunk, the chunk read once  *)
Definition pass (src dst : rmap) : rmap :=
  ifold nchunkn 0
    (fun c d =>
       let sa := PArray.get src c in
       let a := ifold ncw 0
                  (fun i b => PArray.set b i
                                (Uint63.lor (PArray.get b i) (PArray.get sa i)))
                  (PArray.get d c) in
       PArray.set d c a)
    dst.

(* n passes, the two maps swapping                                            *)
Fixpoint passn (n : nat) (m d : rmap) : rmap :=
  match n with O => m | S n1 => passn n1 (pass m d) m end.

(* a checksum, so that the passes are really made                             *)
Definition chk (m : rmap) : int :=
  ifold nchunkn 0
    (fun c a => Uint63.add a (PArray.get (PArray.get m c) 0))
    0.

Definition run (n : nat) : int := chk (passn n (mk tt) (mk tt)).

(* ---- ROUND TWO: a tree that allocates at every node ---------------------- *)

(* The passes above do not leak.  What the row does and they do not is SEARCH:
   a tree eighteen wide, and at every node xstep builds a NEW position -- an
   array -- and threads the map through.  This is that shape and nothing else:
   no cube, no tables, no pruning. *)

Definition npos : nat := 48.

(* a position, stepped: a new array a node, as comp_tabi makes one *)
Definition step (x : arr) (k : int) : arr :=
  ifold npos 0
    (fun i a => PArray.set a i (Uint63.add (PArray.get x i) k))
    (PArray.make 48 0).

Definition mark (m : rmap) (v : int) : rmap :=
  let c := Uint63.land v 31 in
  let a := PArray.get m c in
  PArray.set m c (PArray.set a (Uint63.land v 1023)
                    (Uint63.lor (PArray.get a (Uint63.land v 1023)) 1)).

Fixpoint srch (togo : nat) (x : arr) (m : rmap) : rmap :=
  match togo with
  | O => mark m (PArray.get x 0)
  | S t => ifold 18 0 (fun k mm => srch t (step x k) mm) m
  end.

Definition runs (d : nat) : int := chk (srch d (PArray.make 48 1) (mk tt)).

Time Eval native_compute in runs 6.
