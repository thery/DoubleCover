From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dwtwosum DWPlus.

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

(* Round to nearest, ties to even, as the ported development names it.        *)
Notation Dchoice := (fun n : Z => negb (Z.even n)).

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

(* TwoSum computes the same two numbers in both formats.  Each development    *)
(* proves its own TwoSum error free, so the pair is pinned by the one         *)
(* rounding that makes the high word, and the two formats agree on that as    *)
(* soon as the sum is normal, or zero.                                        *)
Lemma twoSum_FLX a b :
  Dfin a -> Dfin b ->
  Dfits (D2R a + D2R b) ->
  Dfits (D2R (a + b)%float - D2R b) ->
  Dfits (D2R (a + b)%float - D2R ((a + b) - b)%float) ->
  Dfits (D2R a - D2R ((a + b) - b)%float) ->
  Dfits (D2R b - D2R ((a + b) - ((a + b) - b))%float) ->
  Dfits (D2R (a - ((a + b) - b))%float +
         D2R (b - ((a + b) - ((a + b) - b)))%float) ->
  D2R a + D2R b = 0 \/ Dnorm <= Rabs (D2R a + D2R b) ->
  D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b) /\
  D2R (dwlo (twoSum a b)) = TwoSum_err prec Dchoice (D2R a) (D2R b).
Proof.
move=> Fa Fb Hs Ha' Hb' Hda Hdb He Hn.
have Hp : (1 < prec)%Z by [].
have [Eh _] := twoSumE _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Ex := twoSum_exact _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Hsum : D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b).
  by rewrite Eh TwoSum_sumE Drnd_FLX0.
split=> //.
rewrite (TwoSum_correct Hp eq_refl (Dformat_FLX a) (Dformat_FLX b)).
by rewrite -Hsum; lra.
Qed.

(* And in the form the program can check.                                     *)
Lemma twoSum_FLX_fin a b :
  Dfin a -> Dfin b ->
  Dfin (a + b)%float ->
  Dfin ((a + b) - b)%float ->
  Dfin ((a + b) - ((a + b) - b))%float ->
  Dfin (a - ((a + b) - b))%float ->
  Dfin (b - ((a + b) - ((a + b) - b)))%float ->
  Dfin ((a - ((a + b) - b)) +
        (b - ((a + b) - ((a + b) - b))))%float ->
  D2R a + D2R b = 0 \/ Dnorm <= Rabs (D2R a + D2R b) ->
  D2R (dwhi (twoSum a b)) = TwoSum_sum prec Dchoice (D2R a) (D2R b) /\
  D2R (dwlo (twoSum a b)) = TwoSum_err prec Dchoice (D2R a) (D2R b).
Proof.
move=> Fa Fb Fs Fa' Fb' Fda Fdb Fe Hn.
have [_ Hs] := Dfin_add _ _ Fa Fb Fs.
have [_ Ha'] := Dfin_sub _ _ Fs Fb Fa'.
have [_ Hb'] := Dfin_sub _ _ Fs Fa' Fb'.
have [_ Hda] := Dfin_sub _ _ Fa Fa' Fda.
have [_ Hdb] := Dfin_sub _ _ Fb Fb' Fdb.
have [_ He] := Dfin_add _ _ Fda Fdb Fe.
by apply: twoSum_FLX.
Qed.
