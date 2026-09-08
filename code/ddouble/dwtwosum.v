From Stdlib Require Import Reals ZArith.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge.

(* The two error-free transformations of dwarith.v, read on the reals.        *)
(* They are, step for step, the TwoSum and Fast2Sum the double-word proofs    *)
(* are about, so each intermediate is a rounded real operation as soon as no  *)
(* step overflows.  Nothing here needs the arguments to be normal: that only  *)
(* comes in when the unbounded format is brought in.                          *)

(* The two words of a double word.                                            *)
Definition dwhi d := let: DWFloat xh _ := d in xh.
Definition dwlo d := let: DWFloat _ xl := d in xl.

(* Fast2Sum: three operations, and the low word is the exact error of the     *)
(* high one when b is no larger than a.  That last part is the development's  *)
(* theorem; here we only say what the program computes.                       *)
Lemma fastTwoSumE a b :
  Dfin a -> Dfin b ->
  Dfits (D2R a + D2R b) ->
  Dfits (D2R (a + b)%float - D2R a) ->
  Dfits (D2R b - D2R ((a + b) - a)%float) ->
  let s := Drnd (D2R a + D2R b) in
  let z := Drnd (s - D2R a) in
  D2R (dwhi (fastTwoSum a b)) = s /\
  D2R (dwlo (fastTwoSum a b)) = Drnd (D2R b - z) /\
  Dfin (dwhi (fastTwoSum a b)) /\ Dfin (dwlo (fastTwoSum a b)).
Proof.
move=> Fa Fb Hs Hz Ht.
have [Es Fs] := D2R_add _ _ Fa Fb Hs.
have [Ez Fz] := D2R_sub _ _ Fs Fa Hz.
have [Et Ft] := D2R_sub _ _ Fb Fz Ht.
by rewrite /= -Es -Ez.
Qed.

(* TwoSum: six operations, and the low word is the exact error of the high    *)
(* one whatever the two arguments are.                                        *)
Lemma twoSumE a b :
  Dfin a -> Dfin b ->
  Dfits (D2R a + D2R b) ->
  Dfits (D2R (a + b)%float - D2R b) ->
  Dfits (D2R (a + b)%float - D2R ((a + b) - b)%float) ->
  Dfits (D2R a - D2R ((a + b) - b)%float) ->
  Dfits (D2R b - D2R ((a + b) - ((a + b) - b))%float) ->
  Dfits (D2R (a - ((a + b) - b))%float +
         D2R (b - ((a + b) - ((a + b) - b)))%float) ->
  let s := Drnd (D2R a + D2R b) in
  let a' := Drnd (s - D2R b) in
  let b' := Drnd (s - a') in
  let da := Drnd (D2R a - a') in
  let db := Drnd (D2R b - b') in
  D2R (dwhi (twoSum a b)) = s /\
  D2R (dwlo (twoSum a b)) = Drnd (da + db) /\
  Dfin (dwhi (twoSum a b)) /\ Dfin (dwlo (twoSum a b)).
Proof.
move=> Fa Fb Hs Ha' Hb' Hda Hdb He.
have [Es Fs] := D2R_add _ _ Fa Fb Hs.
have [Ea' Fa'] := D2R_sub _ _ Fs Fb Ha'.
have [Eb' Fb'] := D2R_sub _ _ Fs Fa' Hb'.
have [Eda Fda] := D2R_sub _ _ Fa Fa' Hda.
have [Edb Fdb] := D2R_sub _ _ Fb Fb' Hdb.
have [Ee Fe] := D2R_add _ _ Fda Fdb He.
by rewrite /= -Es -Ea' -Eb' -Eda -Edb.
Qed.
