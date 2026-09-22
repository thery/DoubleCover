From Stdlib Require Import ZArith Reals Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Zaux Raux Core BinarySingleNaN PrimFloat.
From Interval Require Import Xreal Basic Sig Generic_proof Primitive_ops.
From mathcomp Require Import ssreflect ssrbool.
From twarith Require Import twarith tw_ops.

(* WHY `cmp' READS THE VALUE AND NOT THE WORDS.                               *)
(*                                                                            *)
(* The obvious way to compare three words is the way two words are compared:  *)
(* on the leading word, and on the next when the ones before agree.  For two  *)
(* words that is sound, and `code/ddouble' proves it -- a double word rounds  *)
(* to its own leading word, rounding is monotone, so the leading words are in *)
(* the order the values are.                                                  *)
(*                                                                            *)
(* A TRIPLE WORD DOES NOT ROUND TO ITS LEADING WORD.  Being a triple word is  *)
(* two tests, each on a pair - the second word is within half a step of the   *)
(* first, and the third within half a step of the second - and the two        *)
(* together do not say that the first plus the other two rounds back to the   *)
(* first.  `X' below is the smallest case of it: one, plus half a step of     *)
(* one, plus half a step of that.  The first two are a tie and round to one   *)
(* because one has an even last bit; add the third and the sum is past the    *)
(* halfway point, so the three of them round to `1 + 2^-52' and not to one.   *)
(*                                                                            *)
(* With that, the leading word says nothing about the order.  `X' has the     *)
(* SMALLER leading word and the LARGER value, and `cmpLex' below - the rule   *)
(* `cmp' used to use - answers less than where the values say more.           *)
(*                                                                            *)
(* This file is what the definition in `tw_ops.v' is answering.  It is kept   *)
(* on the build path so that the rule cannot come back.                       *)

(* The old rule, written out here and nowhere else.                           *)
Definition cmpLex (x y : twfloat) :=
  match PrimitiveFloat.cmp (tw0 x) (tw0 y) with
  | Xeq =>
    match PrimitiveFloat.cmp (tw1 x) (tw1 y) with
    | Xeq => PrimitiveFloat.cmp (tw2 x) (tw2 y)
    | c => c
    end
  | c => c
  end.

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

(* THE OLD RULE IS WRONG ON THIS PAIR.                                        *)
Lemma cmpLex_bad : cmpLex X Y <> Xcmp (TwFloat.toX X) (TwFloat.toX Y).
Proof.
have -> : cmpLex X Y = Xlt by vm_compute.
rewrite toXX toXY /Xcmp.
by case: Rcompare_spec => //; have := YltX; lra.
Qed.

(* And it is not a near miss: the rule says less than, the values say more.   *)
Lemma cmpLex_is_lt : cmpLex X Y = Xlt.
Proof. by vm_compute. Qed.

(* THE RULE IN USE GETS IT RIGHT.  `cmp_correct' in `tw_ops.v' says so for    *)
(* every pair; this is the one pair said out loud, and it is computed, not    *)
(* derived, so it checks the definition and not the proof.                    *)
Lemma cmp_is_gt : TwFloat.cmp X Y = Xgt.
Proof. by vm_compute. Qed.

Lemma cmp_good : TwFloat.cmp X Y = Xcmp (TwFloat.toX X) (TwFloat.toX Y).
Proof.
rewrite cmp_is_gt toXX toXY /Xcmp.
by case: Rcompare_spec => //; have := YltX; lra.
Qed.

(* `min' and `max' follow `cmp', so they get it right too.                    *)
Lemma min_is_Y : TwFloat.min X Y = Y.
Proof. by vm_compute. Qed.

Lemma max_is_X : TwFloat.max X Y = X.
Proof. by vm_compute. Qed.
