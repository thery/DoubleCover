(* WHAT A WORD FORMAT IS WORTH, IN BITS, AND WHERE PRECISION ACTUALLY BINDS.  *)
(*                                                                            *)
(* Two probes.  Swap the module below and run by hand:                        *)
(*                                                                            *)
(*   coqc -native-compiler no -Q . twarith -Q ../ddouble dwarith \             *)
(*        bench/precision_probe.v                                             *)
(*                                                                            *)
(* TAKE MINIMA OF SEVERAL RUNS.  At twenty milliseconds a single run is        *)
(* worthless: one reading of the `1e-42' row below came out 0.024 against      *)
(* 0.060 and looked like a threefold win that repetition showed was not there. *)
(*                                                                            *)
(* PROBE ONE, the calibration.  `exp x - exp x' AT A POINT has no dependency   *)
(* in it, so the tightest bound provable is the arithmetic's own rounding and  *)
(* reads the format's precision straight off.  Measured: floats `1e-15' (the   *)
(* same as bignums at 53, which is the control), double words `1e-28', triple  *)
(* words `1e-44'; and bignums give `1e-25' at 85 bits, `1e-29' at 100, `1e-44' *)
(* at 148 and `1e-47' at 159.  So through `exp' a double word is worth about   *)
(* 97 bits and a triple word about 148.  On plain arithmetic -- a degree-sixty *)
(* Horner at a point -- they are worth 103 and 155, so the ten bits lost here  *)
(* are `I.exp''s series and not the format's.                                  *)
(*                                                                            *)
(* PROBE TWO, the sweet spot.  Over `[0,1]' this expression can never test     *)
(* precision: the achievable bound is exactly the dependency, `e*2^-depth',    *)
(* so floats prove `2.6e-6' at depth 20 and refuse `2.5e-6' just as every      *)
(* other format does, and precision would bind only at depth about 150.  On a  *)
(* starting interval narrow enough -- `2^-141' wide -- the dependency at depth *)
(* ten is the size of a triple word's own rounding, the bisection does real    *)
(* work, and precision is what stops it.  Measured, minima of five: at `1e-43' *)
(* triple words 0.166 s, bignums at 150 bits 0.171, at 155 bits 0.181, and at  *)
(* `1e-44' triple words REFUSE while both bignum settings prove it.  A triple  *)
(* word is level with them and reaches one decade less far.                    *)
From Stdlib Require Import Reals.
From Interval Require Import Tactic.
From Interval Require Import Xreal Basic Sig Float Float_full.
From Interval Require Import Primitive_ops.
(* swap for dw_unsafe.DwFloatU, tw_unsafe.TwFloatU, or SFBI2 with an i_prec *)
Module IT := IntervalTactic PrimitiveFloat.
Import IT.
Open Scope R_scope.
Notation pow2 := (Raux.bpow Zaux.radix2).

(* one: the point, which reads the precision off *)
Goal Rabs (exp 1 - exp 1) <= 1e-15.
Proof. idtac "point 1e-15".
Time first [interval; idtac "  ok" | idtac "  REFUSED"]. Abort.
Goal Rabs (exp 1 - exp 1) <= 1e-16.
Proof. idtac "point 1e-16".
Time first [interval; idtac "  ok" | idtac "  REFUSED"]. Abort.

(* two: the narrow interval, where bisection works and precision stops it *)
Goal forall x, 1 <= x <= 1 + pow2 (-141) -> Rabs (exp x - exp x) <= 1e-43.
Proof. intros x H. idtac "narrow 1e-43".
Time first [interval with (i_bisect x, i_depth 10); idtac "  ok"
           |idtac "  REFUSED"]. Abort.
Goal forall x, 1 <= x <= 1 + pow2 (-141) -> Rabs (exp x - exp x) <= 1e-44.
Proof. intros x H. idtac "narrow 1e-44".
Time first [interval with (i_bisect x, i_depth 10); idtac "  ok"
           |idtac "  REFUSED"]. Abort.
