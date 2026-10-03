(** * The whole program exp100_main.c *)

Require Import VST.floyd.proofauto.
Require Import E.exp100_clight E.Common E.Spec.
Require Import E.Verif_simple E.Verif_bits E.Verif_mulshr E.Verif_reduce.
Require Import E.Verif_core E.TopLemmas E.Verif_top E.Verif_main.
Require E.exp100_main_clight.

#[export] Existing Instance NullExtension.Espec.

(** The statements of exp100_main.c: those of Spec.v for the 16 functions
    of exp100.c, the two wrappers on the reals, and main. *)
Definition Gmain : funspecs :=
  Gprog ++ [exp_encl_spec; maybe_hard_spec; main_spec].

(** One function of the program from its body proof [L], made in the
    environment of exp100.c: [fold] is the same body in exp100_clight.v as
    [fnew] in exp100_main_clight.v.  Floyd's [semax_func_cons] does the
    same, but leaves the unifier to find [fold], which does not end. *)
Ltac cons_body fold fnew spec L :=
  eapply semax_func_cons;
  [ reflexivity
  | repeat apply Forall_cons; try apply Forall_nil; try computable; reflexivity
  | unfold var_sizes_ok; repeat constructor; try (simpl; rep_lia)
  | reflexivity | LookupID | LookupB
  | change fnew with fold;
    refine (semax_body_subsumption' _ _ _ _ _ _ fold spec L _ _ _);
    [ apply cspecs_sub_refl
    | repeat (apply Forall_cons; [reflexivity|]); apply Forall_nil
    | apply tycontext_sub_i99; assumption ]
  | ].

Module M := E.exp100_main_clight.

Theorem exp100_main_correct :
  semax_prog E.exp100_main_clight.prog tt Vprog Gmain.
Proof.
  prove_semax_prog.
  try_prove_tycontext_subVG body_num_zero.
  cons_body f_num_zero M.f_num_zero num_zero_spec body_num_zero.
  cons_body f_num_copy M.f_num_copy num_copy_spec body_num_copy.
  cons_body f_num_add M.f_num_add num_add_spec body_num_add.
  cons_body f_num_sub M.f_num_sub num_sub_spec body_num_sub.
  cons_body f_num_lt M.f_num_lt num_lt_spec body_num_lt.
  cons_body f_num_mul_small M.f_num_mul_small num_mul_small_spec
    body_num_mul_small.
  cons_body f_num_mulshr M.f_num_mulshr num_mulshr_spec body_num_mulshr.
  cons_body f_num_bitlen M.f_num_bitlen num_bitlen_spec body_num_bitlen.
  cons_body f_num_pow2 M.f_num_pow2 num_pow2_spec body_num_pow2.
  cons_body f_num_low M.f_num_low num_low_spec body_num_low.
  cons_body f_num_scale M.f_num_scale num_scale_spec body_num_scale.
  cons_body f_mul_ln2 M.f_mul_ln2 mul_ln2_spec body_mul_ln2.
  cons_body f_guess_n M.f_guess_n guess_n_spec body_guess_n.
  cons_body f_exp_core M.f_exp_core exp_core_spec body_exp_core.
  cons_body f_exp_encl_bits M.f_exp_encl_bits exp_encl_bits_spec
    body_exp_encl_bits.
  cons_body f_maybe_hard_bits M.f_maybe_hard_bits maybe_hard_bits_spec
    body_maybe_hard_bits.
  cons_body f_exp_encl M.f_exp_encl exp_encl_spec body_exp_encl.
  cons_body f_maybe_hard M.f_maybe_hard maybe_hard_spec body_maybe_hard.
  try_prove_tycontext_subVG body_main.
  cons_body M.f_main M.f_main main_spec body_main.
  apply semax_func_nil.
Qed.

Print Assumptions exp100_main_correct.
