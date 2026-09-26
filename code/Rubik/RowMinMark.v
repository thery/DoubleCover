(* =========================================================================  *)
(*  RowMinMark.v -- RowFold.fmarkn at 20 000 000 pseudo-random members,      *)
(*  with Stdlib only loaded.                                                  *)
(* =========================================================================  *)

(* A BENCH.  The same loop as ocaml/rubik_row_rocq.ml's mark bench and as    *)
(* the one with the development loaded: the count must be 19 843 282.        *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import RowMin RowMinTab.

Local Open Scope uint63_scope.

Definition lcga : int := 2862933555777941757.
Definition lcgc : int := 3037000493.
Definition nxt (x : int) : int := Uint63.add (Uint63.mul x lcga) lcgc.

Definition n100 : nat := 100%nat.
Definition n1k : nat := 1000%nat.
Definition n20k : nat := 20000%nat.

(* r rounds of 20 000 marks                                                   *)
Definition marks (r : nat) : int :=
  let '(mn, _) :=
    ifold r 0
      (fun _ (st : (PArray.array (PArray.array int) * int) * int) =>
         ifold n20k 0
           (fun _ (st : (PArray.array (PArray.array int) * int) * int) =>
              let '(mn, x) := st in
              let x' := nxt x in
              let pg := Uint63.mod (Uint63.lsr x' 30) 40320 in
              let gr := Uint63.mod (Uint63.lsr x' 10) 20160 in
              let bt := Uint63.mod (Uint63.lsr x' 40) 24 in
              (fmarkn fpg_m fsgr_m fsbt_m mn pg gr bt, x'))
           st)
      ((mkempty tt, 0), 1) in
  snd mn.

(* the libraries arriving *)
Time Eval native_compute in PArray.get fsgr_m 5.

Time Eval native_compute in marks n100.
Time Eval native_compute in marks n1k.
Time Eval native_compute in marks n1k.
