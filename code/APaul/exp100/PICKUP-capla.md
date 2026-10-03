exp100 in Capla: where the work stands
======================================

The plan: doc/exp100-capla-plan.typ (and .pdf). Read it first.

Files
-----
code/APaul/capla/exp100/:
- exp100.b: exp100.c in Capla. Tables T, C, LN2, RMAX are parameters (no
  globals in Capla); rows passed as T[j]; scratch by alloc/free;
  exp_core + decide + maybe_hard_bits, and exp_encl_bits.
- test_capla.c + Makefile: runs exp100.b next to exp100.c. Measured:
  10^6 inputs, 0 differences (14 s).

code/APaul/capla/exp100/proof/ (logical name Exp100Capla; the shared
model files of code/APaul/exp100/rocq are copied into exp100-model/ and
built there as Exp100):
- exp100.v: generated from ../exp100.b (ccomp -dcaplarocq + a sed fix).
- ExpBase.v: ge, val32, limbs, base32, list lemmas, and_mask, shru32.
- Bridge.v: val32 l = valZ (map Int64.unsigned l), limbs <-> Forall limb,
  replace_unsigned (to use valZ_upd of ExpLimbs.v).
- Specs.v: words, vtab (a table as Capla passes it), Tw Cw LN2w RMAXw,
  tables_ok, mant53, scale_emax, arr6 (a scratch array of 6 words);
  proved: val32_words, limbs_words, LN2w_num, RMAXw_num, length_Tw,
  length_Cw, Tw_row (row j of T: 6 limbs, val32 = ExpModel.Tv j),
  Cw_row (row i of C: val32 = ExpModel.Cv i).
- One file per task, statements fixed, bodies Admitted (table below).
- rowcall.b + RowCall.v: the probe of a call with a row: row_copy calls
  num_copy(a, T[j]) (a Sletref on the path T[Scell j]); row_copy_spec is
  PROVED, the callee used through its spec (a Section hypothesis).
  Assumptions: WP_sound, external_functions_sem, the standard axioms.

The specs
---------
Every spec has the shape of num_add_spec: from
`eval_funcall ge (Internal f) args e1 (Some result)`, the out arrays read
by `e1!(param k f)`, their length, `limbs`, and the number against the
model ExpModel.v (qualified: ExpModel.mulshr, .bitlen, .pow2, .low, .scale,
.q, .guess, .core_Z, .decide_Z, .maybe_hard_Z, .exp_encl_Z). The
preconditions are those of vst/exp100/Spec.v, whose bodies are proved.

| file              | spec                 | status   | VST proof to mirror        |
|-------------------|----------------------|----------|----------------------------|
| NumAddProof.v     | num_add_spec         | PROVED   | Verif_simple body_num_add  |
| NumBasicProof.v   | num_zero_spec        | Admitted | Verif_simple body_num_zero |
|                   | num_copy_spec        | Admitted | Verif_simple body_num_copy |
|                   | num_pow2_spec        | Admitted | Verif_bits body_num_pow2   |
|                   | num_low_spec         | Admitted | Verif_bits body_num_low    |
|                   | zeros6 (helper)      | PROVED   | --                         |
| NumSubProof.v     | num_sub_spec         | Admitted | Verif_simple body_num_sub  |
| NumLtProof.v      | num_lt_spec          | Admitted | Verif_bits body_num_lt     |
| NumMulProof.v     | num_mul_small_spec   | Admitted | Verif_simple body_num_mul_small |
|                   | num_mulshr_spec      | Admitted | Verif_mulshr body_num_mulshr |
| NumBitsProof.v    | num_bitlen_spec      | Admitted | Verif_bits body_num_bitlen |
|                   | num_scale_spec       | Admitted | Verif_bits body_num_scale  |
| ReduceProof.v     | mul_ln2_spec         | Admitted | Verif_reduce body_mul_ln2  |
|                   | guess_n_spec         | Admitted | Verif_reduce body_guess_n  |
| ExpCoreProof.v    | exp_core_spec        | Admitted | Verif_core body_exp_core   |
| DecideProof.v     | decide_spec          | Admitted | Verif_top (the decision part of body_maybe_hard_bits) |
| ExpTopProof.v     | maybe_hard_bits_spec | Admitted | Verif_top body_maybe_hard_bits |
|                   | exp_encl_bits_spec   | Admitted | TopLemmas body_exp_encl_bits |

Statement choices (to know before proving):
- num_zero gives the exact list `repeat Int64.zero 6`; zeros6 gives its
  length, limbs and val32 = 0. num_copy gives the exact list ys.
- num_scale: `Int64.unsigned v < 2 ^ mant53`, `Int64.signed e < scale_emax`
  (128: limb e / 32 + 2 must exist), as VST.
- num_mulshr: `val32 xs * val32 ys < 2 ^ (P + num_bits)`, as VST.
- mul_ln2 takes the LN2 argument `Varr (map Vint64 LN2w)`, the form
  tables_ok gives; LN2w_num gives its length, limbs and value.
- exp_core: on rc = 0, y, hs = [Vint64 hN] with
  core_Z xb = inr (val32 y, Int64.signed hN), and the scratch X q q1 r
  (params 3..6) are arr6, so that maybe_hard_bits can pass them to decide.
- decide: its preconditions on y and hN are exactly the conclusion of
  ExpModelBounds.core_bounds (2^P <= y < 2^y_bits, |hN| <= 2^hN_bits).
- exp_encl_bits: M is read by valW (map Int64.unsigned ms) (ExpLimbs.v).
- The function names carry the numbers ccomp gives (num_sub27,
  exp_core138, ...): they change if exp100.b changes.
- tables_ok is a hypothesis of exp_core, maybe_hard_bits and
  exp_encl_bits; the final theorem keeps it (the C driver fills the tables).
- The plan's ExpSpec.v (the program on Z) is ExpModel.v: core_Z, decide_Z,
  maybe_hard_Z.

The VST loop invariants to copy (vst/exp100, read only)
--------------------------------------------------------
- num_zero, num_copy (Verif_simple): first i limbs written, rest unchanged.
- num_sub (Verif_simple): valZ r - c 2^(32 i) = valZ a_<i - valZ b_<i,
  0 <= c <= 1 (num_add's invariant with a minus; NumAddProof.v is the
  Capla canvas).
- num_mul_small (Verif_simple): valZ r + c 2^(32 i) = valZ a_<i * w,
  c < 2^32.
- num_lt (Verif_bits): forward_loop with i from 5 down, sublist (i+1) NL a
  = sublist (i+1) NL b; in Capla k = 5 - i goes up and the loop has a
  return: the invariant must cover Out_return.
- num_bitlen (Verif_bits): b = bitlen (valZ a_<i); inner loop on k:
  b = bitlen (valZ a_<i + 2^(32 i) (a_i mod 2^k)).
- num_low (Verif_bits): the first i limbs of low_list b (f/32) (f mod 32).
- num_pow2, num_scale: no loop (num_pow2 calls num_zero).
- num_mulshr (Verif_mulshr): Capla's alloc gives p = 0, so the first VST
  loop (p = 0) has no counterpart; outer loop on i: valZ p = valZ a_<i *
  valZ b, limbs i+6..11 of p are 0; inner loop on j: valZ p + c 2^(32
  (i+j)) = valZ p0 + a_i valZ b_<j 2^(32 i), c < 2^32; last loop copies
  p[5..10].
- mul_ln2 (Verif_reduce): q = p[1..i] after i steps.
- exp_core (Verif_core, being finished by another agent): the Horner loop
  invariant planned in vst/exp100/PICKUP-T5.md: horner_from r (valZ h)
  (i + 1) = horner r, valZ h < 2^h_bits.

Pure Z lemmas
-------------
All the core_Z facts the Capla proofs need are already in the shared
rocq/ExpModelBounds.v (core_Z_big, core_Z_reduce, core_Z_rmax, core_Z_ok,
core_Z_rc, core_bounds, decide_bits, decide_f, bitlen_range, horner_*,
Tv_bound, Cv_bound, ...): CoreBounds.v and TopLemmas.v of vst/exp100 hold
copies under the same names. Their only other pure lemmas, Cv_all, Tv_all,
qE', valZ_range and Dl_num, restate Cv_bound, Tv_bound, qvE, valZ_num and
the number 16 on 6 limbs; nothing new to move to ExpModelBounds.v.

Build
-----
  eval $(opam env --switch=capla)
  cd code/APaul/capla/exp100 && make && ./test_capla 1000000
  cd proof && nice -n 19 make all
Measured: make all from no .vo (the model already built) 2 min 44 s on the
desktop; each spec file takes about 10 to 20 s, almost all of it loading
Capla and the model. RowCall.v 11 s.

rocq-mcp (server rocq-mcp-capla) works on these files with the absolute
load paths of proof/_CoqProject (written by `make mcp`); give the file as
an absolute path.

Next: two groups for two parallel agents
----------------------------------------
Each agent replaces Admitted by proofs in its files only; the statements
stay as they are (a callee is used through its statement, proved or not).

Group A (word functions without products, then the decision and the top):
  NumBasicProof.v (num_zero, num_copy, num_pow2, num_low), NumSubProof.v,
  NumLtProof.v, NumBitsProof.v (num_bitlen, num_scale), then DecideProof.v
  and ExpTopProof.v (maybe_hard_bits, exp_encl_bits).
  Mirror: Verif_simple.v, Verif_bits.v, Verif_top.v, TopLemmas.v.

Group B (products, reduction, the core):
  NumMulProof.v (num_mul_small, num_mulshr), ReduceProof.v (mul_ln2,
  guess_n), then ExpCoreProof.v (exp_core).
  Mirror: Verif_simple.v (mul_small), Verif_mulshr.v, Verif_reduce.v,
  Verif_core.v + CoreBounds.v.
  For the rows C[16], C[i], T[j] in exp_core: RowCall.v shows the steps
  (rewrite /vtab, the nth of the map of rows, then the callee's spec,
  `change (param 0 f) with A`, `repeat prog`); Tw_row and Cw_row of
  Specs.v give the row as a number.

Traps
-----
- Capla's PrintCoq.ml prints `Salloc (i, e)` as a pair: the proof
  Makefile fixes exp100.v with sed. Report upstream.
- Shift amounts must be u32 or smaller: `x >> (u32) k`. No hex literals.
- In the WP context, `nia` hangs (a nia in the num_add loop body ran for
  minutes) and `set` breaks: put every arithmetic step in a lemma outside
  (num_add_step, carry_end), call it with `exact:`.
- `/=` on val32 unfolds 2^32 into binary digits: use `cbn [val32]`.
- ProofTactics makes Int64.unsigned/repr/modu opaque: lemmas that unfold
  them go in a section with `Transparent` (see ExpBase.v, Section Words).
  lia knows Int64 through Capla's zify (ZifyIntegers): `clia k` works.
- State bounds in Z, never in nat (2^64 in unary hangs).
- Bullets: `repeat split` after the loop end can close goals by itself;
  use `all: first [...]` rather than fixed bullets.
- `apply_WP_stmt` loses the return value: copy
  `Some result = outcome_result_value out` with `have :=` first (needed
  for num_lt, num_bitlen, guess_n, exp_core, decide, maybe_hard_bits).
- A table argument written `vtab tl` stops `prog` (not a constructor):
  `rewrite /vtab` first (RowCall.v).
- `rocq_compile_file` of rocq-mcp deletes the .vo unless keep_vo=true.
- Do not coqc any file of code/APaul/exp100/rocq from the capla switch: it
  overwrites the .vo of the native switch; the Makefile builds copies.
- Do not run `pkill -f coqc...` from the Bash tool: the pattern matches
  the tool's own shell and kills it.
