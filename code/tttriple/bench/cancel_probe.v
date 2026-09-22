(* WHY `cancellation' IS NOT A PRECISION BENCHMARK.                           *)
(*                                                                            *)
(* The goal has two dials -- the bound and `i_depth' -- and neither is the     *)
(* precision.  `exp x - exp x' over a range comes back as wide as the          *)
(* DEPENDENCY, which every arithmetic returns identically, and only bisection  *)
(* narrows it, at two to the depth.  This file is the evidence for that, and   *)
(* for the numbers in the README.  Edit the module below and run it by hand:   *)
(*                                                                            *)
(*   coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith \             *)
(*        bench/cancel_probe.v                                                *)
(*                                                                            *)
(* Measured, primitive floats: 1e-4 at depth 20 proves in 0.19 s, 1e-5 at 20   *)
(* in 1.95, 1e-6 at 20 is REFUSED, 1e-6 at 24 proves in 15.9, 1e-7 at 24 is    *)
(* REFUSED, 1e-7 at 27 proves in 145.3 -- nine times depth 24 for three more   *)
(* levels, which is the doubling, and depth 27 is 134 million splits.          *)
(*                                                                            *)
(* And at 1e-6 with depth 20, where floats give up, SO DOES EVERYTHING ELSE:   *)
(* double words refuse in 44.8 s, triple words in 372.0, and bignums at TWO    *)
(* HUNDRED BITS in 495.2.  Precision buys nothing at all here.                 *)
From Stdlib Require Import Reals.
From Interval Require Import Tactic.
From Interval Require Import Xreal Basic Sig Float Float_full.
From Interval Require Import Primitive_ops.
(* swap these two lines for dw_unsafe.DwFloatU, tw_unsafe.TwFloatU or SFBI2 *)
Module IT := IntervalTactic PrimitiveFloat.
Import IT.
Open Scope R_scope.

Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-4)%R.
Proof. intros x H. idtac "1e-4 depth 20".
Time first [interval with (i_bisect x, i_depth 20); idtac "  ok"
           |idtac "  REFUSED"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-6)%R.
Proof. intros x H. idtac "1e-6 depth 20".
Time first [interval with (i_bisect x, i_depth 20); idtac "  ok"
           |idtac "  REFUSED"]. Abort.
Goal forall x, (0 <= x <= 1)%R -> (Rabs (exp x - exp x) <= 1e-6)%R.
Proof. intros x H. idtac "1e-6 depth 24".
Time first [interval with (i_bisect x, i_depth 24); idtac "  ok"
           |idtac "  REFUSED"]. Abort.
