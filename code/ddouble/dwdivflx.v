From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn dwtwosum dwflx.
From dwarith Require Import DWDivDW.

(* The port of the paper's division bound, STARTED AND NOT FINISHED.          *)
(*                                                                            *)
(* `divDwDw2' of dwarith.v is bounded in dw_updn.v by a shift of sixteen      *)
(* units in the last place, and sixteen is the paper's own constant:          *)
(* `DWDivDW.v' holds Theorem 7.1, admit-free, for `DWDivDW2', which is        *)
(* `divDwDw2' step for step -                                                 *)
(*                                                                            *)
(*   Rabs ((zh + zl - xy) / xy) <= 15 * u^2 + 56 * u^3                        *)
(*                                                                            *)
(* - and fifteen units is what that is.  What is missing is the connection:   *)
(* the theorem is over the reals, generic in the precision, in the format     *)
(* with no smallest exponent, while the code runs primitive floats in the     *)
(* bounded format at fifty-three bits.  `dwflx.v' is the same connection made *)
(* for the SUM, and this file is the beginning of it for the quotient.        *)
(*                                                                            *)
(* WHAT IS DONE HERE.  The two lemmas below, and the three files of the       *)
(* paper's development are on the build path, so Theorem 7.1 is reachable.    *)
(*                                                                            *)
(* WHAT BLOCKS IT, and it is not a formality.  `DWTimesFP.v' declares         *)
(*                                                                            *)
(*   Parameter TwoProd : R -> R -> R * R.                                     *)
(*                                                                            *)
(* and every theorem about it carries `TwoProd = Fast2Mult' as a hypothesis.  *)
(* Of an opaque Parameter that can never be discharged, so no unconditional   *)
(* theorem comes out.  Making it a Definition breaks proofs inside that same  *)
(* file which rewrite WITH that equation.  Finishing the port means turning   *)
(* `TwoProd' into a section variable of the paper's file and repairing those   *)
(* proofs, and only then writing the bridge in the shape of                   *)
(* `plusDwDw_FLX' / `plusDwDw_relerr'.                                         *)

Open Scope R_scope.

(* A product and a quotient are NOT rounded alike by the two formats.  What   *)
(* saves the sum is that a sum of two floats too small for the bounded        *)
(* format to round is exact, so neither format rounds it; a product or a      *)
(* quotient has no such property, and below the smallest normal number the    *)
(* bounded format rounds where the other does not.  Hence the normal range     *)
(* below - and hence the quotient's bound needs a range test where the sum's  *)
(* needs none.                                                                *)
Lemma Drnd_FLX_mult a b :
  (Dnorm <= Rabs (D2R a * D2R b))%R ->
  Drnd (D2R a * D2R b) = Xrnd (D2R a * D2R b).
Proof. by move=> Hn; apply: Drnd_FLX. Qed.

Lemma Drnd_FLX_div a b :
  (Dnorm <= Rabs (D2R a / D2R b))%R ->
  Drnd (D2R a / D2R b) = Xrnd (D2R a / D2R b).
Proof. by move=> Hn; apply: Drnd_FLX. Qed.

(* And the paper's theorem, reachable and instantiated at binary64's          *)
(* precision as far as the precision goes.  The two hypotheses left are the   *)
(* two-product being error free, which holds in this format because a         *)
(* product's error is itself a float there, and the one above about           *)
(* `TwoProd'.                                                                  *)
Check DWDDW_correct.
