(* =========================================================================  *)
(*  RowStepBench.v -- what the packed coordinate costs at every candidate.    *)
(* =========================================================================  *)

(* A BENCH, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* THE RUN CARRIES ONE NUMBER, twist * nfsi + flip-slice, because that is     *)
(* RowInst's coordof.  At every candidate move cstep takes it apart (a        *)
(* division and a modulo), steps the halves and puts it back together, and    *)
(* fp1g takes the new one apart again (a division) to read the table.  The    *)
(* OCaml carries the halves apart.  Here the same walk is made both ways:     *)
(* the same moves, the same states, the same table reads.                     *)
(*                                                                            *)
(*   cd code/Rubik && ulimit -s unlimited                                     *)
(*   /usr/bin/time -v coqc -R . Rubik RowStepBench.v                          *)
(*                                                                            *)
(* THE TWO SUMS AT EACH SIZE MUST BE THE SAME.  Each walk at 1 and 3 million  *)
(* steps; the DIFFERENCE over 2 million is the cost of one step.  The first   *)
(* Eval pays for the tables arriving and is thrown away.                      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* RowMap's, written again                                                    *)
Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  if n is n1.+1 then ifold n1 (x + 1) f (f x a) else a.

(* the moves: a small generator, the same on both sides, so the walk does not *)
(* fall into a short cycle                                                    *)
Definition rnd (s : int) : int :=
  Uint63.land (Uint63.add (Uint63.mul s 1103515245) 12345) 1073741823.
Definition mvof (s : int) : int := Uint63.mod (Uint63.lsr s 16) 18.

(* ---- the run's way: one packed number ------------------------------------ *)

Definition stepP (c k : int) : int * int :=
  (* RowInst.cstep actfsri, written out: ctw is the division, cfs the modulo  *)
  let c' := Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
                       (actfsri (Uint63.mod c nfsi) k) in
  let tw := c' / nfsi in
  (c', Dfoldm p1ftab frepi fsymi twsymi tw (c' - tw * nfsi)).

(* state: the generator, the coordinate, the sum of the table entries read.  *)
(* Both walks start at coordinate 0: any rank is a state the tables know.    *)
Definition walkP (n : nat) : int :=
  let: (_, _, a) :=
    ifold n 0
      (fun _ (st : int * int * int) =>
         let: (s, c, a) := st in
         let s' := rnd s in
         let: (c', w) := stepP c (mvof s') in
         (s', c', a + mdist w))
      (1, 0, 0) in a.

(* ---- the OCaml's way: the two halves apart ------------------------------- *)

Definition stepH (tw fs k : int) : int * int * int :=
  let tw' := acttwii tw k in
  let fs' := actfsri fs k in
  (tw', fs', Dfoldm p1ftab frepi fsymi twsymi tw' fs').

Definition walkH (n : nat) : int :=
  let: (_, _, _, a) :=
    ifold n 0
      (fun _ (st : int * int * int * int) =>
         let: (s, tw, fs, a) := st in
         let s' := rnd s in
         let: (tw', fs', w) := stepH tw fs (mvof s') in
         (s', tw', fs', a + mdist w))
      (1, 0, 0, 0) in a.

(* ---- the floor: the walk with no step at all ----------------------------- *)

Definition walk0 (n : nat) : int :=
  let: (_, a) :=
    ifold n 0
      (fun _ (st : int * int) =>
         let: (s, a) := st in let s' := rnd s in (s', a + mvof s'))
      (1, 0) in a.

Definition n1 : nat := 1000000.
Definition n3 : nat := 3000000.

(* thrown away: the tables arriving *)
Time Eval native_compute in walkP n1.

Time Eval native_compute in walk0 n1.
Time Eval native_compute in walk0 n3.

Time Eval native_compute in walkP n1.
Time Eval native_compute in walkP n3.

Time Eval native_compute in walkH n1.
Time Eval native_compute in walkH n3.
