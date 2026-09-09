From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge TwoSumFLT.

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

(* Rounding to nearest with ties to even reads a sign the same way on either  *)
(* side of zero, which is what Knuth's 2Sum asks of a tie rule.               *)
Lemma Dchoice_sym x :
  negb (Z.even x) = negb (negb (Z.even (- (x + 1)))).
Proof.
by rewrite Z.even_opp Z.add_1_r Z.even_succ -Z.negb_even Bool.negb_involutive.
Qed.

(* TwoSum is error-free: the two words of the result sum to the exact sum of  *)
(* the two arguments.  Knuth's theorem, read on the program.                  *)
Lemma twoSum_exact a b :
  Dfin a -> Dfin b ->
  Dfits (D2R a + D2R b) ->
  Dfits (D2R (a + b)%float - D2R b) ->
  Dfits (D2R (a + b)%float - D2R ((a + b) - b)%float) ->
  Dfits (D2R a - D2R ((a + b) - b)%float) ->
  Dfits (D2R b - D2R ((a + b) - ((a + b) - b))%float) ->
  Dfits (D2R (a - ((a + b) - b))%float +
         D2R (b - ((a + b) - ((a + b) - b)))%float) ->
  D2R (dwhi (twoSum a b)) + D2R (dwlo (twoSum a b)) = D2R a + D2R b.
Proof.
move=> Fa Fb Hs Ha' Hb' Hda Hdb He.
have [Eh [El _]] := twoSumE _ _ Fa Fb Hs Ha' Hb' Hda Hdb He.
have Fa' : generic_format radix2 (FLT_exp (SpecFloat.emin prec emax) prec)
             (D2R a) by rewrite -DfexpE; apply: Dformat.
have Fb' : generic_format radix2 (FLT_exp (SpecFloat.emin prec emax) prec)
             (D2R b) by rewrite -DfexpE; apply: Dformat.
have Hp : (1 < prec)%Z by [].
have Hp0 : Prec_gt_0 prec by [].
have K := @Knuth (SpecFloat.emin prec emax) prec Hp Hp0 _ Dchoice_sym
            (D2R a) (D2R b) Fa' Fb'.
rewrite -DfexpE in K.
by rewrite Eh El !DrndE; lra.
Qed.

(* The same, in the form a program can check.  An operation that overflowed   *)
(* returns an infinity, so a finite result is the proof that it did not, and  *)
(* the six tests below are on numbers the algorithm has just computed.  This  *)
(* is the guarded reading of the lemma above; the unguarded one is there for  *)
(* a caller who already knows nothing overflows.                              *)
Lemma twoSum_exact_fin a b :
  Dfin a -> Dfin b ->
  Dfin (a + b)%float ->
  Dfin ((a + b) - b)%float ->
  Dfin ((a + b) - ((a + b) - b))%float ->
  Dfin (a - ((a + b) - b))%float ->
  Dfin (b - ((a + b) - ((a + b) - b)))%float ->
  Dfin ((a - ((a + b) - b)) +
        (b - ((a + b) - ((a + b) - b))))%float ->
  D2R (dwhi (twoSum a b)) + D2R (dwlo (twoSum a b)) = D2R a + D2R b.
Proof.
move=> Fa Fb Fs Fa' Fb' Fda Fdb Fe.
have [_ Hs] := Dfin_add _ _ Fa Fb Fs.
have [_ Ha'] := Dfin_sub _ _ Fs Fb Fa'.
have [_ Hb'] := Dfin_sub _ _ Fs Fa' Fb'.
have [_ Hda] := Dfin_sub _ _ Fa Fa' Fda.
have [_ Hdb] := Dfin_sub _ _ Fb Fb' Fdb.
have [_ He] := Dfin_add _ _ Fda Fdb Fe.
by apply: twoSum_exact.
Qed.
