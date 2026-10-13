(** * The six functions of htr3.c together

    [htr3.c] has no [main], so there is no whole program to prove; what
    VST checks instead is [semax_func]: each of the six bodies meets its
    statement in the global environment of [htr3.c], every call inside
    them being read through the statements of [Gassumed]: those of the same
    list [Gprog], and [addcarry_spec], the statement of [_addcarry_u64]
    (Spec_add.v), the intrinsic of gcc that [add] calls.  That statement is
    the only one assumed without a body. *)

Require Import VST.floyd.proofauto.
Require Import HtrVst.Words HtrVst.htr3_clight HtrVst.Common.
Require Import HtrVst.Verif_sub HtrVst.Spec_add HtrVst.Verif_add.
Require Import HtrVst.Verif_difftab HtrVst.Verif_tstep.
Require Import HtrVst.Spec_search HtrVst.Verif_search.

(** No input or output: the oracle of the C program is empty. *)
#[export] Existing Instance NullExtension.Espec.

(** The statements of the six functions, and those their calls may use:
    the same, and the statement of [_addcarry_u64], assumed. *)
Definition Gprog : funspecs := Verif_search.Gprog.
Definition Gassumed : funspecs := addcarry_spec :: Gprog.

Lemma htr3_funcs_correct :
  semax_func Vprog Gassumed (Genv.globalenv prog)
    [(_sub, Internal f_sub); (_add, Internal f_add);
     (_difftab, Internal f_difftab); (_tstep_l, Internal f_tstep_l);
     (_tstep, Internal f_tstep);
     (_search, Internal f_search)] Gprog.
Proof.
  unfold Gassumed, Gprog, Verif_search.Gprog.
  prove_semax_prog_setup_globalenv.
  semax_func_cons body_sub.
  semax_func_cons body_add.
  semax_func_cons body_difftab.
  semax_func_cons body_tstep_l.
  semax_func_cons body_tstep.
  semax_func_cons body_search.
Qed.

Print Assumptions htr3_funcs_correct.
