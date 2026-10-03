(** * Task T5: exp_core *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec E.Rows.

Lemma body_exp_core : semax_body Vprog Gprog f_exp_core exp_core_spec.
Proof.
Admitted.
