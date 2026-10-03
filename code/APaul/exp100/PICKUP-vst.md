Pick-up: the VST proof of exp100.c (2026-10-03)
================================================

Done
----
- The plan: doc/exp100-vst-plan.typ, compiled to doc/exp100-vst-plan.pdf
  (from the repo root: typst compile --root . doc/exp100-vst-plan.typ).
  It gives the statements of the 16 functions, the integer post of
  exp_core (core_rel), the real and decision theorems, the final theorem,
  the risks, and the tasks T0..T10.
- Probes, in code/APaul/vst/exp100/ (all build, `make` 24 s):
    Makefile      clightgen -normalize on ../../exp100/exp100.c, then coqc -Q . E
    Limbs.v       valL on limbs of 32 bits (to be replaced by valZ of
                  code/APaul/exp100/rocq/ExpConsts.v)
    Common.v      CompSpecs, Vprog, NL, vwords, num, Znth_vwords, upd_vwords
    Spec.v        num_zero_spec, num_add_spec, the shape of exp_core_spec
                  (GLOBALS, 2D T at gv _T): type-checks
    Verif_zero.v  body_num_zero: proved, 13 lines, 4.3 s
    Verif_add.v   body_num_add: proved, 95 lines with two word lemmas, 14 s
    Rows.v        row_split / row_addr: a row C[i] of a 2D global as a
                  data_at at offset_val (48 i); proved, 32 lines, 1.8 s
- Measured: clightgen -normalize 0.07 s, 110 KB; coqc 2.4 s on it.
  code/APaul/exp100/rocq/ExpTable.v and ExpConsts.v (constants agent,
  switch native) also compile in switch vst: 0.9 s, 4.9 s.

Build the probes
----------------
  eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)
  cd code/APaul/vst/exp100 && make        (make clean to tidy)

Not done
--------
Everything else: the other 14 statements, Exp100Spec.v (core_rel), the
gvar_init lemmas, all real-number files, the final semax_func.

Next, in order (details in the plan, section "The tasks")
---------------------------------------------------------
1. T0 alone: Makefile (also building ../../exp100/rocq/ExpTable.v,
   ExpConsts.v in switch vst, as code/APaul/vst/link does), Common.v,
   Spec.v with all 16 funspecs, Exp100Spec.v (core_rel, H, bitlen,
   scale), the gvar_init lemmas (v_T etc. = lists of ExpTable.v, by
   reflexivity), stubs with Admitted, a vm_compute check of core_rel
   against test_exp100 output.
2. In parallel after T0: T1 Verif_simple (zero, copy, add, sub,
   mul_small; start from the probes), T2 Verif_bits (lt, bitlen, pow2,
   low, scale), T3 Verif_mulshr, T4 Verif_reduce (mul_ln2, guess_n),
   T5 Verif_core (exp_core + integer bounds), T6 Verif_top
   (exp_encl_bits, maybe_hard_bits; needs only the statements of T8, T9),
   T7 Exp100Bits (x from its bits, Flocq), T8 Exp100Encl (step 4),
   T9 Exp100Hard (step 5, needs only ExpHard.v). Largest: T5, T8.
3. T10 last: semax_func over the 16 functions, Print Assumptions.

Traps met
---------
- Two switches: VST is only in switch vst (Rocq 9.0); the constants agent
  works in native (Rocq 9.1). Run coqc after
  `eval $(opam env --root=/home/thery/opam-rocq.9.1.0 --switch=vst)` in
  the same shell, else VST is not found. Keep ../rocq building in vst.
- Name clash: ExpConsts.v defines valZ, limb, num, NL : nat (limbs of 32
  bits); code/APaul/vst/Words.v has another valZ (words of 64 bits). Use
  qualified names, never import both.
- Vundef default: Znth on list val in VST goals uses the inhabitant
  Vundef; state helper equalities with `@Znth val Vundef`, else rewrite
  finds no subterm.
- Intros substitutes `Zlength r = i`: do `subst i` and speak of Zlength r.
- entailer! drops hypotheses: rewrite with them before entailer!.
- NL as a Definition blocks list_solve: `unfold NL in *` first (or make
  it a Notation in T0).
- Inside PROP (...), arithmetic needs %Z.
- Int64 additions: rewrite add64_repr (floyd/coqlib3.v); add_repr is the
  32-bit one. lia fails on bounds with 2^32; rep_lia works.
- split3_data_at_Tarray leaves `naturally_aligned` (simpl; tauto) and
  `m <= Zlength rows` (give the equation, lia fails).
- num_scale's comment says e <= 138; e >= 128 writes a[6]. The one call
  has e <= 117.
- No slow step yet; exp_core (6 local arrays, 11 calls) is the guessed one.
