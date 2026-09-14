From Stdlib Require Import Reals Psatz ZArith.
From Flocq Require Import Core.
From Interval Require Import Tactic.

Open Scope R_scope.

(* The one goal in Interval's own sources that asks for more than a double    *)
(* word.  It is a side condition of Interval's primitive-float exponential,   *)
(* `src/Interval/Float_full_primfloat.v:657`, where it is discharged by       *)
(* `interval with (i_taylor xR, i_prec 120)`.  A hundred and twenty bits is   *)
(* past the hundred and seven a double word holds, so this is the goal that   *)
(* separates two words from three.                                           *)
(*                                                                           *)
(* It was read off the source by inserting `Show.` before that call and       *)
(* compiling.  Of the forty-odd things in the context there, all that the     *)
(* conclusion needs is `xR` and its range - everything else is a local        *)
(* definition, written out below.  That is what makes this one liftable;      *)
(* the ten other high-precision calls in that file are not.                   *)

Notation pow2 e := (Raux.bpow Zaux.radix2 e).

(* Binary64 rounding to nearest, ties to even, and rounding to a whole        *)
(* number.                                                                    *)
Notation RND x :=
  (Generic_fmt.round Zaux.radix2 (FLT_exp (-1074) 53) Round_NE.ZnearestE x).
Notation RNDI x :=
  (Generic_fmt.round Zaux.radix2 (FIX_exp 0) Round_NE.ZnearestE x).

(* The two halves of ln 2 / 64 as Interval's exponential splits it, and the   *)
(* reciprocal it multiplies by.                                              *)
Definition RLog2div64h := 6243314768150528 * pow2 (-59).
Definition RLog2div64l := 8153543309409082 * pow2 (-98).
Definition RInvLog2div64 := 6497320848556798 * pow2 (-46).

(* The statement: the argument reduction of the exponential loses no more     *)
(* than sixty-five thousand five hundred and thirty-seven of two to the       *)
(* minus seventy-seven.                                                       *)
Definition red_bound (xR : R) : Prop :=
  let k := RNDI (RND (xR * RInvLog2div64)) in
  let u := xR - k * RLog2div64h - RND (k * RLog2div64l) in
  let delt1 := RND u - u in
  let delt2 := RND (k * RLog2div64l) - k * RLog2div64l in
  Rabs (delt1 - delt2 - k * (RLog2div64h + RLog2div64l - ln 2 / 64))
  <= 65537 * pow2 (-77).

Lemma reduction xR : -746 <= xR <= 710 -> red_bound xR.
Proof.
unfold red_bound, RLog2div64h, RLog2div64l, RInvLog2div64.
intros Hx.
Time interval with (i_taylor xR, i_prec 120).
Qed.
