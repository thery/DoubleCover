Pick-up: the VST proof of exp100.c
==================================

Goal
----
exp_encl_bits returns rc and (M, s) as exp_encl_Z of rocq/ExpModel.v
gives them, and maybe_hard_bits returns maybe_hard_Z xb.  The real-number
side (the bits of x, the enclosure, the filter) is in rocq/ (ExpBits.v,
ExpBound.v, ExpFilter.v, ExpSpec.v, Rocq 9.1) and is not part of this
work.  The plan is doc/exp100-vst-plan.typ (section "The tasks"); its
Exp100Spec.v and T7-T9 are replaced by rocq/ExpModel.v and rocq/.

Files, in code/APaul/vst/exp100/
--------------------------------
  Makefile        copies rocq/ExpTable.v, ExpConsts.v, ExpModel.v into
                  exp100-model/ (git-ignored) and builds them there as
                  Exp100; runs clightgen -normalize on ../../exp100/exp100.c;
                  builds the rest as E.  No .vo is written into rocq/.
  Common.v        CompSpecs, Vprog; sizes NL NP NT NC NM (notations);
                  valZ, limb, limb_bits (abbreviations of ExpConsts);
                  word, valW (words of 64 bits, for M); vwords, num;
                  valZ_app, valZ_sublist_succ, valZ_bounds; and_mask32,
                  shru32; consts gv (T, C, LN2, RMAX, INV at gv);
                  v_T_init .. v_INV_init (gvar_init = the lists of
                  ExpTable.v, by reflexivity); LN2_num, RMAX_num,
                  INV_limb, T_num, C_num.
  Spec.v          the 16 funspecs and Gprog (all 16).  Helpers speak of
                  valZ and of ExpModel's mulshr, bitlen, pow2, low, scale,
                  q, guess; exp_core_spec of core_Z, exp_encl_bits_spec of
                  exp_encl_Z (M as valW of 3 words), maybe_hard_bits_spec
                  of maybe_hard_Z.
  Rows.v          row_split, row_addr: row i of a 2D global as a
                  data_at at offset_val (48 i).  Proved.
  Verif_simple.v  T1: num_zero, num_add proved; num_copy, num_sub,
                  num_mul_small Admitted.
  Verif_bits.v    T2: num_lt, num_bitlen, num_pow2, num_low, num_scale.
  Verif_mulshr.v  T3: num_mulshr.
  Verif_reduce.v  T4: mul_ln2, guess_n.
  Verif_core.v    T5: exp_core.
  Verif_top.v     T6: exp_encl_bits, maybe_hard_bits.
  T2-T6: every body is Admitted, with its statement fixed.

Build
-----
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
  cd code/APaul/vst/exp100 && nice -n 19 make     (make clean to tidy)
Measured: 52 s from clean on the desktop, one process.

Next
----
1. T1..T6 in parallel: replace each Admitted; use the statements of
   Spec.v only (Gprog), never another body.  Largest: T5 (exp_core).
2. T10: semax_func over the 16 functions, Print Assumptions.

Statement choices to know
-------------------------
- num_scale: e < 128 (scale_emax), since the C writes a[e/32 + 2]; any
  e >= Int.min_signed (the C tests e > -64 before computing -e).
- guess_n: no bound on X; the result is exactly guess (valZ X), since the
  product X INV has 7 limbs.
- mul_ln2 and guess_n take only their own constant (LN2, INV) in SEP;
  exp_core, exp_encl_bits and maybe_hard_bits take consts gv.
- exp_core, exp_encl_bits: EX rc ys hN with rc = 0 -> core_Z xb =
  inr (valZ ys, hN) (and the shape of ys), rc <> 0 -> core_Z xb = inl rc;
  the outputs are written only when rc = 0 (if rc =? 0 in SEP).
- exp_core writes y and s with one share sh; exp_encl_bits has shM, shs.

Traps
-----
- Two switches: VST is only in switch vst (Rocq 9.0); rocq/ is built in
  native (Rocq 9.1) by others.  Run coqc after the eval above, in the same
  shell, else VST is not found.  The rocq-mcp tools run 9.1: no VST.
- Name clash: ExpConsts.v has valZ, limb, num, NL : nat (limbs of 32
  bits); code/APaul/vst/Words.v has another valZ (64 bits); ExpModel.v has
  K, D, q, low, shr, scale.  None is imported: Common.v gives valZ, limb,
  limb_bits as abbreviations, the rest is written qualified
  (Exp100.ExpModel.core_Z).  num is the VST predicate of Common.v.
- The model directory is exp100-model, not a Rocq identifier, so that
  -Q . E does not bind it a second time.
- NL is a notation: tactics taking an identifier refuse it
  (forward_for_simple_bound NL fails; write 6).
- Inside PROP (...), arithmetic needs %Z.
- Vundef default: Znth on list val uses the inhabitant Vundef; state
  helper equalities with @Znth val Vundef, else rewrite finds no subterm.
- Intros substitutes Zlength r = i: do subst i and speak of Zlength r.
- entailer! drops hypotheses: rewrite with them before entailer!.
- Int64 additions: rewrite add64_repr (floyd/coqlib3.v); add_repr is the
  32-bit one.  lia fails on bounds with 2^32; rep_lia works.
- split3_data_at_Tarray leaves naturally_aligned (simpl; tauto) and
  m <= Zlength rows (give the equation, lia fails).
- Forall_Znth of VST is an iff: apply (proj1 (Forall_Znth _ _) H).
