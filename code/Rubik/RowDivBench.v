(* =========================================================================  *)
(*  RowDivBench.v -- halving an int63: a shift by one or a division by two.   *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.                                            *)
(*                                                                            *)
(*   cd code/Rubik && make RowDivBench.vo                                     *)
(*                                                                            *)
(* Each loop at 10 and 30 million steps; the DIFFERENCE over 20 million is    *)
(* the cost of one step.  All three loops must print the same pair of sums   *)
(* for shift and division.  The first Eval is thrown away.                    *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  if n is n1.+1 then ifold n1 (x + 1) f (f x a) else a.

(* r rounds of 10 000 steps: x runs over 0 .. 9999, so the values vary        *)
Fixpoint loop (h : int -> int) (r : nat) (acc : int) : int :=
  if r is r1.+1
  then loop h r1 (ifold 10000 0 (fun x s => Uint63.add s (h x)) acc)
  else acc.

Definition hnone  (x : int) : int := x.
Definition hshift (x : int) : int := Uint63.lsr x 1.
Definition hdiv   (x : int) : int := Uint63.div x 2.

(* thrown away *)
Time Eval native_compute in loop hshift 1000 0.

Time Eval native_compute in loop hnone 1000 0.
Time Eval native_compute in loop hnone 3000 0.

Time Eval native_compute in loop hshift 1000 0.
Time Eval native_compute in loop hshift 3000 0.

Time Eval native_compute in loop hdiv 1000 0.
Time Eval native_compute in loop hdiv 3000 0.
