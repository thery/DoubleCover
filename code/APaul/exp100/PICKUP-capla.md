exp100 in Capla: where the work stands (3 October 2026)
=======================================================

The plan: doc/exp100-capla-plan.typ (and .pdf). Read it first.

Done
----
- code/APaul/capla/exp100/exp100.b: exp100.c in Capla (300 lines). Tables
  T, C, LN2, RMAX are parameters (no globals in Capla); rows passed as T[j];
  scratch by alloc/free; exp_core + decide + maybe_hard_bits.
- code/APaul/capla/exp100/test_capla.c + Makefile: runs exp100.b next to
  exp100.c. Measured: 10^6 inputs, 0 differences (14 s).
- code/APaul/capla/exp100/proof/: Makefile, ExpBase.v (val32, limbs,
  base32, and_mask, shru32), NumAddProof.v (num_add_spec, proved, no
  Admitted). Logical name Exp100Capla (not Exp100: the constants agent
  uses Exp100 in code/APaul/exp100/rocq).
  Measured: exp100.v checks in 5.5 s, NumAddProof 19 s, make all 34 s;
  num_add took about 1 h of agent time with the set-up.

Build
-----
  eval $(opam env --switch=capla)
  cd code/APaul/capla/exp100 && make && ./test_capla 1000000
  cd proof && make all          (makes exp100.v from ../exp100.b, then .vo)

Not done
--------
Everything else of the plan: T0 (the statements of every spec, ExpSpec.v
on Z, tables_ok, one call with a row T[j] through Sletref), then T2..T13 as
in the plan. No _CoqProject / rocq-mcp set-up yet for capla/exp100 (htr3
has `make -C proof mcp`; copy it, with -R proof Exp100Capla).

Next tasks, in order
--------------------
1. T0: write the statements with Admitted (num_zero, num_copy, num_sub,
   num_lt, num_mul_small, num_mulshr, num_bitlen, num_pow2, num_low,
   num_scale, mul_ln2, guess_n, exp_core, decide, maybe_hard_bits) and
   ExpSpec.v; prove one small call with a row (T[j]) to test Sletref.
2. In parallel: T2-T6 (word functions), T8 (bounds on Z), T9 (bits of a
   double), T10 (error bound, shared with VST).
3. T7, T11; then T12 (exp_core, decide); then T13 (final theorem).

Traps
-----
- Capla's PrintCoq.ml prints `Salloc (i, e)` as a pair: the proof
  Makefile fixes exp100.v with sed. Report upstream.
- Shift amounts must be u32 or smaller: `x >> (u32) k`. No hex literals.
- In the WP context, `nia` hangs (a nia in the num_add loop body ran for
  minutes): put every arithmetic step in a lemma outside (num_add_step,
  carry_end), call it with `exact:`.
- `/=` on val32 unfolds 2^32 into binary digits: use `cbn [val32]`.
- ProofTactics makes Int64.unsigned/repr/modu opaque: lemmas that unfold
  them go in a section with `Transparent` (see ExpBase.v, Section Words).
  lia knows Int64 through Capla's zify (ZifyIntegers): `clia k` works.
- Bullets: `repeat split` after the loop end can close goals by itself;
  use `all: first [...]` rather than fixed bullets.
- `apply_WP_stmt` loses the return value: copy
  `Some result = outcome_result_value out` with `have :=` first.
- Do not run `pkill -f coqc...` from the Bash tool: the pattern matches
  the tool's own shell and kills it.
- rocq-mcp was not available to the planning agent; all checks were done
  with coqc in the switch capla.
