(** * What the proofs of htr_filter.c share

    htr_filter.c includes ../htr3.c and ../../exp100/exp100.c.  The
    composites of htr_filter.c are those of exp100.c (htr3.c has none), so
    the compspecs of exp100's proofs ([E.Common.CompSpecs]) serve here; the
    statements of htr3's functions are made with htr3's own compspecs, and
    an array of [tulong] means the same under both. *)

Require Import VST.floyd.proofauto.
Require Import HF.htr_filter_clight.
Require HtrVst.Common E.Common.

#[export] Existing Instance E.Common.CompSpecs.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** From htr3's compspecs to exp100's, and back. *)
#[export] Instance CCE_htr_exp :
  change_composite_env HtrVst.Common.CompSpecs E.Common.CompSpecs.
Proof. make_cs_preserve HtrVst.Common.CompSpecs E.Common.CompSpecs. Defined.

#[export] Instance CCE_exp_htr :
  change_composite_env E.Common.CompSpecs HtrVst.Common.CompSpecs.
Proof. make_cs_preserve E.Common.CompSpecs HtrVst.Common.CompSpecs. Defined.

(** An array of words is the same under both compspecs. *)
Lemma data_at_htr_exp sh n (v : list val) p :
  @data_at HtrVst.Common.CompSpecs sh (tarray tulong n) v p =
  @data_at E.Common.CompSpecs sh (tarray tulong n) v p.
Proof.
  rewrite (@data_at_change_composite HtrVst.Common.CompSpecs
             E.Common.CompSpecs _ sh (tarray tulong n) v v);
    [reflexivity|apply JMeq_refl|reflexivity].
Qed.

(** htr3's compspecs are included in exp100's: htr3 has no composite. *)
Lemma cspecs_sub_htr_exp :
  cspecs_sub HtrVst.Common.CompSpecs E.Common.CompSpecs.
Proof.
  split3; intros i; unfold sub_option; cbv; auto.
Qed.
