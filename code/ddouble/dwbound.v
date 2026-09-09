From Stdlib Require Import Reals ZArith Psatz.
From Stdlib Require Import Floats.
From Flocq Require Import Core Plus_error BinarySingleNaN PrimFloat.
From mathcomp Require Import ssreflect.
From dwarith Require Import dwarith dwbridge dw_updn.

(* Widening, and the one step that makes it safe.                             *)
(* An interval bound must fall on the right side of the exact value, and an   *)
(* operation only promises to be near it.  One step up from a rounded sum is  *)
(* above the exact sum, whichever way the rounding went, and one step down    *)
(* is below it.  That is what the two widening operations rest on.            *)

Open Scope R_scope.

(* One step up, read on the reals.                                            *)
Lemma Dnext_up x : Dfin x -> Dfin (next_up x) ->
  D2R (next_up x) = succ radix2 Dfexp (D2R x).
Proof.
rewrite /Dfin /D2R next_up_equiv => Fx Fs.
have := Bsucc_correct _ _ Hprec Hmax (Prim2B x) Fx.
case: Rlt_bool_spec => [Hlt [-> _]|Hle Hov]; first by [].
by move: Fs Hov; case: Bsucc.
Qed.

Lemma Dnext_down x : Dfin x -> Dfin (next_down x) ->
  D2R (next_down x) = pred radix2 Dfexp (D2R x).
Proof.
rewrite /Dfin /D2R next_down_equiv => Fx Fp.
have := Bpred_correct _ _ Hprec Hmax (Prim2B x) Fx.
case: Rlt_bool_spec => [Hlt [-> _]|Hle Hov]; first by [].
by move: Fp Hov; case: Bpred.
Qed.

(* A sum rounded and then stepped up is above the exact sum.                  *)
Lemma addUpFp_ge a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  Dfin (addUpFp a b) -> D2R a + D2R b <= D2R (addUpFp a b).
Proof.
move=> Fa Fb Fs Fu.
have Hp0 : Prec_gt_0 prec by [].
rewrite /addUpFp Dnext_up //.
have [-> _] := Dfin_add _ _ Fa Fb Fs.
by rewrite DfexpE; apply: succ_round_ge_id.
Qed.

(* And stepped down is below it.                                              *)
Lemma addDnFp_le a b : Dfin a -> Dfin b -> Dfin (a + b)%float ->
  Dfin (addDnFp a b) -> D2R (addDnFp a b) <= D2R a + D2R b.
Proof.
move=> Fa Fb Fs Fd.
have Hp0 : Prec_gt_0 prec by [].
rewrite /addDnFp Dnext_down //.
have [-> _] := Dfin_add _ _ Fa Fb Fs.
by rewrite DfexpE; apply: pred_round_le_id.
Qed.
