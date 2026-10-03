(** * Task T4: mul_ln2, guess_n *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

Lemma body_mul_ln2 : semax_body Vprog Gprog f_mul_ln2 mul_ln2_spec.
Proof.
Admitted.

Lemma body_guess_n : semax_body Vprog Gprog f_guess_n guess_n_spec.
Proof.
Admitted.
