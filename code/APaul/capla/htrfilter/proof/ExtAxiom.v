(** * The external function maybe_hard_bits

    In ../htr_filter.b, [maybe_hard_bits] is external
    ([extern fun maybe_hard_bits(xb: u64) -> u64]): it is the C function
    of ../../../exp100/exp100.c, linked with the program.  Capla runs an
    external function through [eval_ext_func], a [Parameter] of Capla;
    [f_maybe_hard_bits] of htr_filter.v is [External ef] for one external
    function [ef].

    The axiom below says what that call returns: on the word [xb], the
    word [maybe_hard_Z xb] of the model ExpModel.v, and no array (the
    function has no mutable array parameter).  It stands for the VST
    proof of the C maybe_hard_bits (code/APaul/vst/exp100,
    exp100_correct), whose statement gives the same result from the same
    model; the axiom is the link between the two proofs, not proved
    here. *)

From compcert Require Import CaplaProof.
From Exp100 Require ExpModel.
Require Import HtrFilterCapla.htr_filter.

Axiom maybe_hard_bits_ext : forall ef xb,
  f_maybe_hard_bits = External ef ->
  eval_ext_func ef [:: Vint64 xb] =
    Some (Vint64 (Int64.repr (ExpModel.maybe_hard_Z (Int64.unsigned xb))), [::]).
