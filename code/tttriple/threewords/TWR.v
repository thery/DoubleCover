(* ---------------------------------------------------------------------------*)
(* Triple-word numbers [twR] (paper Def. 5): a triplet of floats that is      *)
(* P-nonoverlapping.  The record, its projectors [tw0]/[tw1]/[tw2] and value  *)
(* [TWval], the predicate [isTW], the list view [TW2l], and that an [isTW] is *)
(* magnitude-sorted / P-nonoverlapping / made of floats.  Generic over the    *)
(* precision [p]; built on [Nonoverlap].                                     *)
(* ---------------------------------------------------------------------------*)

From Stdlib Require Import ZArith Reals Psatz.
From mathcomp Require Import all_ssreflect all_algebra.
From Flocq Require Import Core Relative Sterbenz Operations Mult_error.
Require Import Nmore Rmore Fmore Rstruct MULTmore prelim.
From Flocq Require Import Pff.Pff2Flocq.
Require Import Nonoverlap.

Delimit Scope R_scope with R.
Delimit Scope Z_scope with Z.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section TWR.

Variable p : Z.
Hypothesis Hp2 : (1 < p)%Z.

Let beta := radix2.

Open Scope R_scope.

Local Instance p_gt_0 : Prec_gt_0 p.
Proof. now apply Z.lt_trans with (2 := Hp2). Qed.

Local Notation fexp := (FLX_exp p).
Local Notation format := (generic_format beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation pow e := (bpow beta e).
Local Notation u := (u p beta).
Local Notation Pnonoverlap := (Pnonoverlap p).
Local Notation pairwise_ulp := (pairwise_ulp p).
Local Notation format_lt_ulp_le := (@format_lt_ulp_le p Hp2).

Inductive twR := TWR (x0 x1 x2 : R).

(* Named projectors for the triple-word record [twR], mirroring [dwh]/[dwl].  *)
Definition tw0 (t : twR) : R := let: TWR x0 _ _ := t in x0.
Definition tw1 (t : twR) : R := let: TWR _ x1 _ := t in x1.
Definition tw2 (t : twR) : R := let: TWR _ _ x2 := t in x2.

Lemma tw0E x0 x1 x2 : tw0 (TWR x0 x1 x2) = x0. Proof. by []. Qed.
Lemma tw1E x0 x1 x2 : tw1 (TWR x0 x1 x2) = x1. Proof. by []. Qed.
Lemma tw2E x0 x1 x2 : tw2 (TWR x0 x1 x2) = x2. Proof. by []. Qed.

Definition TWval (x : twR) : R := let: TWR x0 x1 x2 := x in x0 + x1 + x2.


(* Definition 5: a triple-word number is a P-nonoverlapping triplet           *)
(* of floating-point numbers.                                                 *)
(* Under FLX [ulp 0 = 0], so the strict Priest bound has to carry the same    *)
(* "successor is zero" guard as [Pnonoverlap] -- otherwise NO triple word     *)
(* with a zero limb qualifies, [TWSum]'s own zero-padded output included.     *)
(* This does not weaken the FLT reading, where [ulp 0 = pow emin] makes the   *)
(* guard unreachable for a format successor.                                  *)
Definition isTW (x : twR) : Prop :=
  let: TWR x0 x1 x2 := x in
  [/\ format x0, format x1, format x2,
      x1 = 0 \/ Rabs x1 < ulp x0 & x2 = 0 \/ Rabs x2 < ulp x1].

(* ===========================================================================*)
(*  Triple-word numbers as 3-element sequences                                *)
(* ===========================================================================*)
Definition TW2l x := let: TWR x0 x1 x2 := x in [:: x0; x1; x2].

(* The merge precondition for a single TW: its three limbs are magnitude-     *)
(* sorted.  Two applications of [format_lt_ulp_le] to the [isTW] conjuncts.   *)
Lemma isTW_sorted_mag x : isTW x -> sorted_mag (TW2l x).
Proof.
by case: x => x0 x1 x2 [x0F x1F x2F x1Lux0 x2Lux1] [|[|//]] _;
   [case: x1Lux0 => [->|H] | case: x2Lux1 => [->|H]];
   rewrite ?Rabs_R0 //; try apply: Rabs_pos; apply: format_lt_ulp_le.
Qed.

(* A triple-word, viewed as a 3-element list, is P-nonoverlapping (Def. 5).   *)
Lemma isTW_Pnonoverlap x : isTW x -> Pnonoverlap (TW2l x).
Proof.
by case : x => x0 x1 x2 [x0F x1F x2F x1Lux0 x2Lux1] [|[|[]]] // _; right.
Qed.

(* The three limbs of a triple-word are floats (part of Def. 5).              *)
Lemma isTW_format x : isTW x -> {in (TW2l x), forall z, format z}.
Proof.
by case : x => x0 x1 x2 [x0F x1F x2F _ _] z; rewrite !inE => /or3P[] /eqP->.
Qed.

(* [u = pow (- p)] at radix 2 -- the bridge between the development's unit    *)
(* and the exponent arithmetic of [ulp_lt_ulp_mul].                           *)
Lemma u_pow : u = pow (- p).
Proof.
rewrite /Fmore.u; have -> : (1 - p = 1 + - p)%Z by lia.
by rewrite bpow_plus bpow_1 /=; lra.
Qed.

(* A triple word's THIRD limb is bounded by [2u^2|x0|], NOT the naive         *)
(* [4u^2|x0|].  Reason: [|x1| < ulp x0] puts [x1] a full [p] bits below [x0], *)
(* so [ulp x1 <= u ulp x0] ([ulp_lt_ulp_mul]), and [|x2| < ulp x1].  Going    *)
(* through [ulp x1 <= 2u|x1| <= 2u ulp x0] instead loses that binade.  This   *)
(* is step 1 of doc/thm10.md's plan to bring Algorithm 20's [delta3] down     *)
(* from [8u^3] towards the paper's [3u^3].                                    *)
Lemma isTW_tw2_le t : isTW t -> Rabs (tw2 t) <= 2 * (u * u) * Rabs (tw0 t).
Proof.
case: t => t0 t1 t2 [F0 F1 F2 H1 H2] /=.
have Hu0 : 0 < u by apply: u_gt_0.
have Habs0 : 0 <= Rabs t0 by apply: Rabs_pos.
have Hpos : 0 <= 2 * (u * u) * Rabs t0 by nra.
case: H2 => [->|H2]; first by rewrite Rabs_R0.
case: H1 => [Ht1|H1].
  by move: H2; rewrite Ht1 ulp_FLX_0 => H2; have := Rabs_pos t2; lra.
have Hchain := @ulp_lt_ulp_mul p beta Hp2 _ _ H1.
have Hulp0 := @ulp_2u p beta Hp2 t0.
rewrite -u_pow in Hchain.
by nra.
Qed.

End TWR.
