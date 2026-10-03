(** * Task T6: exp_encl_bits, maybe_hard_bits *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

Lemma body_exp_encl_bits :
  semax_body Vprog Gprog f_exp_encl_bits exp_encl_bits_spec.
Proof.
Admitted.

Lemma body_maybe_hard_bits :
  semax_body Vprog Gprog f_maybe_hard_bits maybe_hard_bits_spec.
Proof.
Admitted.
