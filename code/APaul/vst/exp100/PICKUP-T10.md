Pick-up: T10, the 16 functions together and the reals
=====================================================

State: DONE.  Verif_all.v ends in Qed everywhere; no admit, no Admitted
in any .v of this directory.  Spec.v, Common.v and the bodies are
unchanged.

Files
-----
  Verif_all.v   the final theorems (below).
  Makefile      REAL_V: ExpModelBounds, ExpBits, ExpHard, ExpTaylor,
                ExpBudget, ExpBound, ExpFilter, ExpSpec of
                ../../exp100/rocq are copied into exp100-model/ and built
                there as Exp100 (as ExpModel.v already was); Verif_all.vo
                in PROOFS.  Nothing is written into ../../exp100/rocq.
  _CoqProject   -Q . E, -Q exp100-model Exp100 (for rocq-mcp-vst).
ExpLimbs.v is not copied: ExpSpec.v does not need it.

Every file of the real-number side builds unchanged in Rocq 9.0 (switch
vst, with its Flocq, Interval, Coquelicot).

What is proved (Verif_all.v)
----------------------------
- exp100_funcs_correct: semax_func Vprog Gprog (Genv.globalenv prog)
  [the 16 functions] Gprog.  As htr3's Verif_htr3.v: semax_func_cons with
  each body_* lemma.
- encl xb M s: |exp (xreal xb) - M 2^s| <= D 2^s.
- exp_encl_bits_real_spec: the PRE of exp_encl_bits_spec; POST EX rc ms s,
  0 <= rc <= 3, rc = 0 -> encl xb (valW ms) s /\ Zlength ms = NM /\
  Forall word ms; same RETURN and SEP.
- maybe_hard_bits_real_spec: the PRE of maybe_hard_bits_spec; POST EX r,
  0 <= r <= 1, r = 0 -> ~ hard (xreal xb).
- exp_encl_bits_sub, maybe_hard_bits_sub: funspec_sub from the specs of
  Spec.v to these, with ExpSpec.exp_encl_ok and ExpSpec.maybe_hard_ok.
- body_exp_encl_bits_real, body_maybe_hard_bits_real: semax_body of the
  two C bodies against the real specs (semax_body_funspec_sub).
- exp100_correct: semax_func Vprog Gprog (Genv.globalenv prog)
  [the 16 functions] Gprog_real, Gprog_real being Gprog with the two
  entry points replaced by the real specs.

Print Assumptions
-----------------
- exp100_funcs_correct: the VST/Stdlib axioms only (prop_ext,
  functional_extensionality_dep, eq_rect_eq, classic,
  Extensionality_Ensembles, sig_forall_dec, sig_not_dec).
- exp100_correct: the same, plus the kernel primitives of Rocq and their
  specification axioms (PrimInt63, Uint63Axioms, Sint63Axioms, PrimFloat,
  FloatAxioms, PrimArray), which come from Interval's tactic in the
  real-number files.  Nothing of exp100.

What is NOT proved
------------------
- exp100.c has no main: there is no semax_prog, so nothing proves that
  the initial memory of the globals T, C, LN2, RMAX, INV satisfies
  consts gv.  What ties them to ExpTable.v is v_T_init .. v_INV_init in
  Common.v (gvar_init = the lists, by reflexivity).
- The C wrappers exp_encl and maybe_hard (taking a double) are not
  among the 16 functions and have no spec.

Rebuild
-------
From clean (a copy of the sources in the scratchpad, clightgen
included, nice 19, one process): 583 s wall, 1.9 GB peak, exit 0.

  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
  cd code/APaul/vst/exp100 && nice -n 19 make Verif_all.vo
Measured on the desktop (nice 19, one process, other agents running):
  the 8 real-number files 1.6-4.1 s each (23 s in all);
  Verif_all.v 126 s, 1.9 GB (with two Print Assumptions; 182 s with
  four, so each costs tens of seconds; a run stopping at an error in
  the norepet line, before any Print, took 60 s).

Traps met
---------
- R_scope needs `From Stdlib Require Import Rdefinitions`; the real
  names are written qualified (Rbasic_fun.Rabs, Rtrigo_def.exp,
  Flocq.Core.Raux.bpow), never imported next to VST.
- entailer! times out on a funspec_sub goal with consts gv: Local Opaque
  consts.
- After do_funspec_sub and entailer!, the post goal is
  `ve_of rho' = ... -> Vint (Int.repr r) = eval_id ret_temp rho' -> ...`:
  keep the second hypothesis (intros rho' _ Hr), entailer! needs it.
- The norepet side condition of semax_body_funspec_sub:
  apply compute_list_norepet_e; reflexivity.
