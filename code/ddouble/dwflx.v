From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwbridge DWPlus.

(* The unbounded format, where the double-word theorems live.                 *)
(* Those theorems are all stated for a format with no bottom, and binary64    *)
(* has one.  Above the smallest normal number the two round alike, so a       *)
(* value that stays there is read the same way by either, and a double word   *)
(* that stays there is a double word for both.  That is what carries the      *)
(* theorems over.                                                             *)

Open Scope R_scope.

(* The smallest normal number.                                                *)
Notation Dnorm := (bpow radix2 (SpecFloat.emin prec emax + prec - 1)).

(* Round to nearest, ties to even, in the format with no bottom.              *)
Notation Xrnd :=
  (round radix2 (FLX_exp prec) (Znearest (fun n => negb (Z.even n)))).
Notation Xformat := (generic_format radix2 (FLX_exp prec)).

(* Zero is the one value below the smallest normal number that the two        *)
(* formats still agree on, and the algorithms do produce it.                  *)
Lemma Drnd_FLX0 r : r = 0 \/ Dnorm <= Rabs r -> Drnd r = Xrnd r.
Proof.
by case=> [->|rge]; [rewrite !round_0 | apply: Drnd_FLX].
Qed.

(* Every binary64 number is a number of the format with no bottom: the        *)
(* bound below is on the exponent only, and removing it takes nothing away.   *)
Lemma Dformat_FLX x : Xformat (D2R x).
Proof. by apply/generic_format_FLX_FLT/Dformat. Qed.

(* And a pair of them whose value is normal is a double word for both.        *)
Lemma Ddw_FLX xh xl :
  generic_format radix2 Dfexp xh -> generic_format radix2 Dfexp xl ->
  xh = Drnd (xh + xl) -> Dnorm <= Rabs (xh + xl) ->
  double_word prec (fun n => negb (Z.even n)) xh xl.
Proof.
move=> Fxh Fxl xhE xge.
split; first by split; [apply: generic_format_FLX_FLT Fxh |
                        apply: generic_format_FLX_FLT Fxl].
by rewrite -Drnd_FLX0; [exact: xhE | by right].
Qed.
