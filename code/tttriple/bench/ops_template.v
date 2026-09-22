(* GENERATED per module by bench/run.sh -- do not edit the copies. *)
From Stdlib Require Import ZArith Reals.
From Interval Require Import Xreal Basic Sig Float Float_full.
MODULE_IMPORT
Module F := MODULE_NAME.
Notation p := (F.PtoP PREC).

(* TWO FIXED OPERANDS OF THE SAME MAGNITUDE, every bit of mantissa used.      *)
(* They are constants of the loop, not an accumulator: a loop that lets its   *)
(* value drift times exponent alignment as well as the operation, and for     *)
(* bignums that alone is a factor of two and a half.                          *)
Definition a := F.div_UP p (F.fromZ 1) (F.fromZ 3).
Definition b := F.div_UP p (F.fromZ 1) (F.fromZ 7).

(* Each loop keeps a count so the calls cannot be thrown away, and the empty  *)
(* loop below is subtracted from every row.                                   *)
Fixpoint nul (n : nat) (k : Z) : Z :=
  match n with O => k | S m => nul m (k + 1)%Z end.
Fixpoint addl (n : nat) (k : Z) : Z :=
  match n with O => k | S m => addl m (k + if F.real (F.add_UP p a b) then 1 else 0)%Z end.
Fixpoint subl (n : nat) (k : Z) : Z :=
  match n with O => k | S m => subl m (k + if F.real (F.sub_UP p a b) then 1 else 0)%Z end.
Fixpoint mull (n : nat) (k : Z) : Z :=
  match n with O => k | S m => mull m (k + if F.real (F.mul_UP p a b) then 1 else 0)%Z end.
Fixpoint divl (n : nat) (k : Z) : Z :=
  match n with O => k | S m => divl m (k + if F.real (F.div_UP p a b) then 1 else 0)%Z end.
Fixpoint sqrtl (n : nat) (k : Z) : Z :=
  match n with O => k | S m => sqrtl m (k + if F.real (F.sqrt_UP p a) then 1 else 0)%Z end.
Fixpoint cmpl (n : nat) (k : Z) : Z :=
  match n with O => k | S m => cmpl m (k + match F.cmp a b with Xgt => 1 | _ => 0 end)%Z end.

Definition N := 20000%nat.
Definition R5 (f : nat -> Z -> Z) := f N 0%Z.
Eval vm_compute in (F.real a, F.real b, F.real (F.div_UP p a b)).
Time Eval vm_compute in R5 nul.
Time Eval vm_compute in R5 nul.
Time Eval vm_compute in R5 addl.
Time Eval vm_compute in R5 addl.
Time Eval vm_compute in R5 addl.
Time Eval vm_compute in R5 addl.
Time Eval vm_compute in R5 addl.
Time Eval vm_compute in R5 subl.
Time Eval vm_compute in R5 subl.
Time Eval vm_compute in R5 subl.
Time Eval vm_compute in R5 subl.
Time Eval vm_compute in R5 subl.
Time Eval vm_compute in R5 mull.
Time Eval vm_compute in R5 mull.
Time Eval vm_compute in R5 mull.
Time Eval vm_compute in R5 mull.
Time Eval vm_compute in R5 mull.
Time Eval vm_compute in R5 divl.
Time Eval vm_compute in R5 divl.
Time Eval vm_compute in R5 divl.
Time Eval vm_compute in R5 divl.
Time Eval vm_compute in R5 divl.
Time Eval vm_compute in R5 sqrtl.
Time Eval vm_compute in R5 sqrtl.
Time Eval vm_compute in R5 sqrtl.
Time Eval vm_compute in R5 sqrtl.
Time Eval vm_compute in R5 sqrtl.
Time Eval vm_compute in R5 cmpl.
Time Eval vm_compute in R5 cmpl.
Time Eval vm_compute in R5 cmpl.
Time Eval vm_compute in R5 cmpl.
Time Eval vm_compute in R5 cmpl.
