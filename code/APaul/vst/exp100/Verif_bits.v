(** * Task T2: num_lt, num_bitlen, num_pow2, num_low, num_scale *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

Lemma body_num_lt : semax_body Vprog Gprog f_num_lt num_lt_spec.
Proof.
Admitted.

Lemma body_num_bitlen : semax_body Vprog Gprog f_num_bitlen num_bitlen_spec.
Proof.
Admitted.

Lemma body_num_pow2 : semax_body Vprog Gprog f_num_pow2 num_pow2_spec.
Proof.
Admitted.

Lemma body_num_low : semax_body Vprog Gprog f_num_low num_low_spec.
Proof.
Admitted.

Lemma body_num_scale : semax_body Vprog Gprog f_num_scale num_scale_spec.
Proof.
Admitted.
