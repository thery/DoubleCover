(** * Task T3: num_mulshr *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.

Lemma body_num_mulshr : semax_body Vprog Gprog f_num_mulshr num_mulshr_spec.
Proof.
Admitted.
