Require Import VST.floyd.proofauto.
Require Import E.Limbs E.exp100_clight E.Common E.Spec.
Definition Gprog : funspecs := [num_zero_spec].
Lemma body_num_zero : semax_body Vprog Gprog f_num_zero num_zero_spec.
Proof.
  start_function.
  forward_for_simple_bound 6
    (EX i : Z,
     PROP () LOCAL (temp _a p)
     SEP (data_at sh (tarray tulong NL)
            (vwords (Zrepeat 0 i) ++ Zrepeat Vundef (NL - i)) p)).
  - entailer!.
  - forward.
    entailer!.
    apply derives_refl'; f_equal; unfold vwords, NL; list_solve.
  - unfold num; entailer!.
Qed.
