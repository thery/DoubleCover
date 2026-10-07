(** * The 22 functions of htr_filter.c together

    As [Verif_htr3.v] for htr3.c: [semax_func] over the five functions of
    htr3.c, the 16 functions of exp100.c (without its wrappers on doubles,
    exp_encl and maybe_hard, that search_filter does not call) and
    search_filter, every call being read through the statements of the
    same list [Gprog].  No statement is assumed without its body.

    The bodies of htr3.c and exp100.c are those proved in ../ and
    ../exp100, reused: clightgen names identifiers by string, so the
    function bodies of htr_filter_clight.v are the same terms as those of
    htr3_clight.v and exp100_clight.v; each proof is lifted to the
    context of htr_filter.c by [semax_body_subsumption'] (the compspecs of
    htr3, with no composite, are included in those of exp100, which are
    those of htr_filter.c). *)

Require Import VST.floyd.proofauto.
Require Import HF.htr_filter_clight HF.FCommon HF.Spec_filter HF.Verif_filter.
Require HtrVst.htr3_clight HtrVst.Common.
Require HtrVst.Verif_sub HtrVst.Spec_add HtrVst.Verif_add.
Require HtrVst.Verif_difftab HtrVst.Verif_tstep.
Require HtrVst.Spec_search HtrVst.Verif_search.
Require E.exp100_clight E.Common E.Spec.
Require E.Verif_simple E.Verif_bits E.Verif_mulshr E.Verif_reduce.
Require E.Verif_core E.TopLemmas E.Verif_top.

(** No input or output: the oracle of the C program is empty. *)
#[export] Existing Instance NullExtension.Espec.

(** One function of the program from its body proof [L], made in the
    environment of htr3.c or exp100.c: [fold] is the same body there as
    [fnew] in htr_filter_clight.v, and [CSUB] says that the compspecs of
    [L] are included in those of htr_filter.c.  As the Ltac [cons_body] of
    ../exp100/Verif_prog.v, with [CSUB] in place of [cspecs_sub_refl]. *)
Ltac cons_body fold fnew spec L CSUB :=
  try_prove_tycontext_subVG L;
  eapply semax_func_cons;
  [ reflexivity
  | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
  | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
  | reflexivity | LookupID | LookupB
  | change fnew with fold;
    refine (semax_body_subsumption' _ _ _ _ _ _ fold spec L _ _ _);
    [ exact CSUB
    | repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil
    | apply tycontext_sub_i99; assumption ]
  | ].

Module H := HtrVst.htr3_clight.
Module X := E.exp100_clight.

Theorem htr_filter_funcs_correct :
  semax_func Vprog Gprog (Genv.globalenv prog)
    [(_sub, Internal f_sub); (_add, Internal f_add);
     (_difftab, Internal f_difftab); (_tstep, Internal f_tstep);
     (_search, Internal f_search);
     (_num_zero, Internal f_num_zero); (_num_copy, Internal f_num_copy);
     (_num_add, Internal f_num_add); (_num_sub, Internal f_num_sub);
     (_num_lt, Internal f_num_lt);
     (_num_mul_small, Internal f_num_mul_small);
     (_num_mulshr, Internal f_num_mulshr);
     (_num_bitlen, Internal f_num_bitlen);
     (_num_pow2, Internal f_num_pow2); (_num_low, Internal f_num_low);
     (_num_scale, Internal f_num_scale); (_mul_ln2, Internal f_mul_ln2);
     (_guess_n, Internal f_guess_n); (_exp_core, Internal f_exp_core);
     (_exp_encl_bits, Internal f_exp_encl_bits);
     (_maybe_hard_bits, Internal f_maybe_hard_bits);
     (_search_filter, Internal f_search_filter)] Gprog.
Proof.
  unfold Gprog, HtrVst.Verif_search.Gprog, E.Spec.Gprog; simpl app.
  prove_semax_prog_setup_globalenv.
  cons_body H.f_sub f_sub HtrVst.Verif_sub.sub_spec
    HtrVst.Verif_sub.body_sub cspecs_sub_htr_exp.
  cons_body H.f_add f_add HtrVst.Spec_add.add_spec
    HtrVst.Verif_add.body_add cspecs_sub_htr_exp.
  cons_body H.f_difftab f_difftab HtrVst.Verif_difftab.difftab_spec
    HtrVst.Verif_difftab.body_difftab cspecs_sub_htr_exp.
  cons_body H.f_tstep f_tstep HtrVst.Verif_tstep.tstep_spec
    HtrVst.Verif_tstep.body_tstep cspecs_sub_htr_exp.
  cons_body H.f_search f_search HtrVst.Spec_search.search_spec
    HtrVst.Verif_search.body_search cspecs_sub_htr_exp.
  cons_body X.f_num_zero f_num_zero E.Spec.num_zero_spec
    E.Verif_simple.body_num_zero (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_copy f_num_copy E.Spec.num_copy_spec
    E.Verif_simple.body_num_copy (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_add f_num_add E.Spec.num_add_spec
    E.Verif_simple.body_num_add (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_sub f_num_sub E.Spec.num_sub_spec
    E.Verif_simple.body_num_sub (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_lt f_num_lt E.Spec.num_lt_spec
    E.Verif_bits.body_num_lt (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_mul_small f_num_mul_small E.Spec.num_mul_small_spec
    E.Verif_simple.body_num_mul_small (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_mulshr f_num_mulshr E.Spec.num_mulshr_spec
    E.Verif_mulshr.body_num_mulshr (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_bitlen f_num_bitlen E.Spec.num_bitlen_spec
    E.Verif_bits.body_num_bitlen (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_pow2 f_num_pow2 E.Spec.num_pow2_spec
    E.Verif_bits.body_num_pow2 (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_low f_num_low E.Spec.num_low_spec
    E.Verif_bits.body_num_low (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_num_scale f_num_scale E.Spec.num_scale_spec
    E.Verif_bits.body_num_scale (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_mul_ln2 f_mul_ln2 E.Spec.mul_ln2_spec
    E.Verif_reduce.body_mul_ln2 (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_guess_n f_guess_n E.Spec.guess_n_spec
    E.Verif_reduce.body_guess_n (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_exp_core f_exp_core E.Spec.exp_core_spec
    E.Verif_core.body_exp_core (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_exp_encl_bits f_exp_encl_bits E.Spec.exp_encl_bits_spec
    E.TopLemmas.body_exp_encl_bits (@cspecs_sub_refl E.Common.CompSpecs).
  cons_body X.f_maybe_hard_bits f_maybe_hard_bits E.Spec.maybe_hard_bits_spec
    E.Verif_top.body_maybe_hard_bits (@cspecs_sub_refl E.Common.CompSpecs).
  semax_func_cons body_search_filter.
Qed.

Print Assumptions htr_filter_funcs_correct.
