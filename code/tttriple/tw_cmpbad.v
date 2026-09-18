From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Zaux Raux Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Generic_proof Primitive_ops.
From mathcomp Require Import ssreflect ssrbool.
From twarith Require Import twarith tw_ops.

(* COMPARING THREE WORDS ON THEIR WORDS IS WRONG, AND HERE IS THE PAIR THAT   *)
(* SHOWS IT.                                                                  *)
(*                                                                            *)
(* `TwFloat.cmp' compares on the leading word, and on the next when the ones  *)
(* before agree.  For two words that is sound, and `code/ddouble' proves it:  *)
(* a double word rounds to its own leading word, rounding is monotone, so the *)
(* leading words are in the order the values are.                             *)
(*                                                                            *)
(* A TRIPLE WORD DOES NOT ROUND TO ITS LEADING WORD.  Being a triple word is  *)
(* two tests, each on a pair - the second word is within half a step of the   *)
(* first, and the third within half a step of the second - and the two        *)
(* together do not say that the first plus the other two rounds back to the   *)
(* first.  The triple below is the smallest case of it: one, plus half a step *)
(* of one, plus half a step of that.  The first two are a tie and round to    *)
(* one because one has an even last bit; add the third and the sum is past    *)
(* the halfway point, so it rounds up and away.                               *)
(*                                                                            *)
(* With that, the leading word says nothing about the order.  `X' below has   *)
(* the smaller leading word and the larger value.                             *)
(*                                                                            *)
(* So `cmp_correct' in `tw_ops.v' is not merely unproved: as `cmp' stands it  *)
(* is false, and `min_correct' and `max_correct' with it, since `min' and     *)
(* `max' are `cmp'.  A comparison of three words has to read the value, not   *)
(* the words - the six words of the difference swept exactly, and the sign of *)
(* what leads.  Nothing else in the development depends on `cmp'.             *)

Definition X := TWFloat 0x1p+0%float 0x1p-53%float 0x1p-106%float.
Definition Y := TWFloat 0x1.0000000000001p+0%float
                        (-0x1.fffffffffffffp-54)%float
                        (-0x1.fffffffffffffp-108)%float.

(* Both are triple words, and both denote a real number.                      *)
Lemma XY_wellFormed : wellFormed X = true /\ wellFormed Y = true.
Proof. by vm_compute. Qed.

Lemma XY_real : TwFloat.real X = true /\ TwFloat.real Y = true.
Proof. by vm_compute. Qed.

(* The values, read exactly.  Both are whole multiples of two to the minus    *)
(* one hundred and sixtieth, and the first is the larger of the two.          *)
Notation mX := 365375409332725770115740415482416106408113078272%positive.
Notation mY := 1461501637330903080462961661929655418433197572097%positive.

Lemma toXX : TwFloat.toX X = Xreal (IZR (Zpos mX) * bpow radix2 (-158)).
Proof.
rewrite /TwFloat.toX.
have -> : TwFloat.toF X = Basic.Float false mX (-158)%Z by vm_compute.
by rewrite /FtoX FtoR_split /F2R.
Qed.

Lemma toXY : TwFloat.toX Y = Xreal (IZR (Zpos mY) * bpow radix2 (-160)).
Proof.
rewrite /TwFloat.toX.
have -> : TwFloat.toF Y = Basic.Float false mY (-160)%Z by vm_compute.
by rewrite /FtoX FtoR_split /F2R.
Qed.

Lemma YltX : (IZR (Zpos mY) * bpow radix2 (-160)
              < IZR (Zpos mX) * bpow radix2 (-158))%R.
Proof.
have -> : bpow radix2 (-158) = (bpow radix2 (-160) * 4)%R.
  by rewrite -(bpow_plus radix2 (-160) 2).
have Hb := bpow_gt_0 radix2 (-160).
suff : (IZR (Zpos mY) < IZR (Zpos mX) * 4)%R by nra.
by rewrite -(mult_IZR _ 4); apply: IZR_lt; vm_compute.
Qed.

(* And the leading word of `X' is below the leading word of `Y', so `cmp'     *)
(* answers less than where the values say more.                               *)
Lemma cmp_bad : TwFloat.cmp X Y <> Xcmp (TwFloat.toX X) (TwFloat.toX Y).
Proof.
have -> : TwFloat.cmp X Y = Xlt by vm_compute.
rewrite toXX toXY /Xcmp.
by case: Rcompare_spec => //; have := YltX; lra.
Qed.

(* `min' and `max' go the same way: each returns the wrong one of the two.    *)
Lemma min_bad : TwFloat.toX (TwFloat.min X Y) <>
                Xmin (TwFloat.toX X) (TwFloat.toX Y).
Proof.
have -> : TwFloat.min X Y = X by vm_compute.
rewrite toXX toXY /Xmin Rbasic_fun.Rmin_right; last by have := YltX; lra.
by case=> H; have := YltX; lra.
Qed.

Lemma max_bad : TwFloat.toX (TwFloat.max X Y) <>
                Xmax (TwFloat.toX X) (TwFloat.toX Y).
Proof.
have -> : TwFloat.max X Y = Y by vm_compute.
rewrite toXX toXY /Xmax Rbasic_fun.Rmax_left; last by have := YltX; lra.
by case=> H; have := YltX; lra.
Qed.
