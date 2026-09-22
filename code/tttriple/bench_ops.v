From Stdlib Require Import ZArith Reals.
From Interval Require Import Xreal Basic Sig Specific_bigint Specific_ops.
From dwarith Require dw_unsafe.
From twarith Require tw_unsafe.

(* The arithmetic on its own, with no tactic above it.                        *)
(*                                                                            *)
(* bench_bands.v measures Interval's tactic over each float module, which is  *)
(* the thing one actually wants to be quick - but it answers two questions at *)
(* once, because the tactic's own cost depends on how tight the arithmetic    *)
(* is: a wider bound means a deeper bisection and more series terms.  This    *)
(* file asks the other question by itself: what does one operation cost.      *)
(*                                                                            *)
(* Each loop below runs the same operation the same number of times on        *)
(* full-mantissa values, so the three columns are comparable.  Run by hand:   *)
(*                                                                            *)
(*   coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith bench_ops.v  *)

Module SFBI2 := SpecificFloat BigIntRadix2.

(* One loop of each operation, over any module meeting the signature.          *)
Module Loops (F : FloatOps).

(* A value with every bit of its mantissa used, and a multiplier that has     *)
(* one too and is close enough to one that ten thousand of them in a row      *)
(* neither overflow nor underflow.                                            *)
Definition seed (p : F.precision) := F.div_UP p (F.fromZ 1) (F.fromZ 3).
Definition mult (p : F.precision) :=
  F.div_UP p (F.fromZ 1073741825) (F.fromZ 1073741824).

(* The multiplier is a PARAMETER of each loop, not a call inside it.  Written *)
(* as `mult p' in the body it is recomputed every iteration, and the loop     *)
(* then times a division and two conversions as well as the operation it is   *)
(* supposed to be timing.  That read as a tenfold difference on addition.     *)
Fixpoint addl (p : F.precision) (n : nat) (c a : F.type) : F.type :=
  match n with O => a | S k => addl p k c (F.add_UP p a c) end.

Fixpoint mull (p : F.precision) (n : nat) (c a : F.type) : F.type :=
  match n with O => a | S k => mull p k c (F.mul_UP p a c) end.

Fixpoint divl (p : F.precision) (n : nat) (c a : F.type) : F.type :=
  match n with O => a | S k => divl p k c (F.div_UP p a c) end.

Fixpoint sqrtl (p : F.precision) (n : nat) (a : F.type) : F.type :=
  match n with O => a | S k => sqrtl p k (F.sqrt_UP p a) end.

(* The comparison.  For three words it reads the VALUE and not the words --   *)
(* see `tw_cmpbad.v' for why -- so it is worth a column of its own.  The two  *)
(* values are the loop's own constants and nothing is computed inside, so     *)
(* this times the comparison and nothing else; the answer is kept so the      *)
(* calls cannot be thrown away.                                               *)
Fixpoint cmpl (p : F.precision) (n : nat) (c a : F.type) (k : Z) : Z :=
  match n with
  | O => k
  | S m => cmpl p m c a (k + match F.cmp a c with Xlt => 1 | _ => 0 end)%Z
  end.

(* The two constants, each computed once.                                     *)
Definition run (p : F.precision) (n : nat)
    (l : F.precision -> nat -> F.type -> F.type -> F.type) : F.type :=
  let c := mult p in let a := seed p in l p n c a.

(* The comparison loop answers a count, not a float, so it gets its own.      *)
Definition runc (p : F.precision) (n : nat) : Z :=
  let c := mult p in let a := seed p in cmpl p n c a 0%Z.

End Loops.

Module LB := Loops SFBI2.
Module LD := Loops dw_unsafe.DwFloatU.
Module LT := Loops tw_unsafe.TwFloatU.

(* Bignums are asked for the precision each word module actually holds, so    *)
(* the comparison is at equal precision and not at equal effort.              *)
Notation pB53  := (SFBI2.PtoP 53).
Notation pB107 := (SFBI2.PtoP 107).
Notation pB159 := (SFBI2.PtoP 159).
Notation pD := (dw_unsafe.DwFloatU.PtoP 107).
Notation pT := (tw_unsafe.TwFloatU.PtoP 159).

Definition N := 10000%nat.
Definition Ns := 1000%nat.
(* A comparison is far cheaper than an operation, so it gets more of them.    *)
Definition Nc := 100000%nat.

(* ------------------------------------------------------------------ addition *)
Time Eval vm_compute in LB.run pB53 N LB.addl.
Time Eval vm_compute in LB.run pB107 N LB.addl.
Time Eval vm_compute in LB.run pB159 N LB.addl.
Time Eval vm_compute in LD.run pD N LD.addl.
Time Eval vm_compute in LT.run pT N LT.addl.

(* ------------------------------------------------------------- multiplication *)
Time Eval vm_compute in LB.run pB53 N LB.mull.
Time Eval vm_compute in LB.run pB107 N LB.mull.
Time Eval vm_compute in LB.run pB159 N LB.mull.
Time Eval vm_compute in LD.run pD N LD.mull.
Time Eval vm_compute in LT.run pT N LT.mull.

(* ------------------------------------------------------------------ division *)
Time Eval vm_compute in LB.run pB53 N LB.divl.
Time Eval vm_compute in LB.run pB107 N LB.divl.
Time Eval vm_compute in LB.run pB159 N LB.divl.
Time Eval vm_compute in LD.run pD N LD.divl.
Time Eval vm_compute in LT.run pT N LT.divl.

(* ---------------------------------------------------------------------- root *)
Time Eval vm_compute in LB.sqrtl pB53 Ns (LB.seed pB53).
Time Eval vm_compute in LB.sqrtl pB107 Ns (LB.seed pB107).
Time Eval vm_compute in LB.sqrtl pB159 Ns (LB.seed pB159).
Time Eval vm_compute in LD.sqrtl pD Ns (LD.seed pD).
Time Eval vm_compute in LT.sqrtl pT Ns (LT.seed pT).

(* ----------------------------------------------------------------- comparison *)
Time Eval vm_compute in LB.runc pB53 Nc.
Time Eval vm_compute in LB.runc pB107 Nc.
Time Eval vm_compute in LB.runc pB159 Nc.
Time Eval vm_compute in LD.runc pD Nc.
Time Eval vm_compute in LT.runc pT Nc.

(* And that no column gave up: each of these must be a real number.           *)
Eval vm_compute in (LB.run pB159 10%nat LB.divl, LD.run pD 10%nat LD.divl,
                    LT.run pT 10%nat LT.divl).
