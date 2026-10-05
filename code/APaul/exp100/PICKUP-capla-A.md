exp100 in Capla, group A: where the work stands
===============================================

Directory: code/APaul/capla/exp100/proof/ (switch capla). Nothing committed.

Proved (Qed), each file built by make once at the end
-----------------------------------------------------

| file             | specs / lemmas                                | make time |
|------------------|-----------------------------------------------|-----------|
| NumBasicProof.v  | num_zero, num_copy, num_pow2, num_low (specs) | 21 s      |
| NumSubProof.v    | num_sub_spec                                  | not timed |
| NumLtProof.v     | num_lt_spec                                   | not timed |
| NumBitsProof.v   | num_bitlen_spec, num_scale_spec               | 176 s     |
| ReduceLemmas.v   | pure lemmas for mul_ln2 / guess_n             | few s     |
| TopLemmasCapla.v | pure lemmas for the top functions             | few s     |
| ReduceProof.v    | mul_ln2_spec, guess_n_spec (via mul_ln2_gen, guess_n_gen, num_mul_small as a Section hypothesis) | 27 s |
| ExpTopGen.v      | maybe_hard_bits_gen (exp_core, decide as Section hypotheses) | 87 s |

Print Assumptions (num_scale_spec, num_bitlen_spec): WP_sound,
external_functions_sem, classic, functional_extensionality_dep,
sig_not_dec, sig_forall_dec.

Open
----
- ExpTopProof.v: maybe_hard_bits_spec is now
  `exact: (maybe_hard_bits_gen exp_core_spec decide_spec)` (Requires
  ExpCoreProof, DecideProof, ExpTopGen); NOT BUILT: ExpCoreProof.v does not
  compile at the moment (another agent edits it). exp_encl_bits_spec still
  Admitted: waits for exp_encl_bits_gen of ExpEnclGen.v (another agent).
- Then `nice -n 19 make CaplaFinal.vo` and its Print Assumptions.

Traps found
-----------
- Goal order: side conditions of `rewrite` come FIRST (`first lia`, not
  `last lia`).
- `rewrite H !lemma` or `rewrite /x ?lemma` (a hypothesis or an unfolding
  followed by a `!`/`?` item) fails with "expected to have type positive":
  split into two rewrites.
- After `case T: (Int64.ltu ..); simplWP; repeat prog`, an if-body that is
  a block needs a second `simplWP; repeat prog`.
- Never `change` a boolean scrutinee of the WP match: it breaks the lock;
  use `case X: (...)` on the term.
- `/=` on val32 unfolds 2^32: `cbn [val32 ...]`.
- In Ltac defined in another file, hypothesis names (exec, FUNC) are not
  resolved: match on types / bodies (`H := context [no_repet_check_correct]`).
- Probe goals with coqc: `all: peek. Show 1.` then read the make log
  (rocq-mcp's import cache keeps a stale GroupALemmas.vo).
- `clia` takes identifiers only (`set d := ...; clia d`).
- NumBitsProof.v takes about 3 min (num_scale's nia steps).

The five alloc functions: plan (once alloc gives Vint64 zeros)
---------------------------------------------------------------
After the WP fix, `alloc u64, n` gives `Varr (repeat (Vint64 Int64.zero) n)`
= `Varr (map Vint64 (repeat Int64.zero n))` (rewrite with map_repeat).

num_mulshr (NumMulProof.v, group B), mirror Verif_mulshr.v:
1. p := alloc 12: p = repeat zero 12 (VST's first loop p = 0 is gone).
2. outer loop i = 0..5, invariant: length p = 12, limbs p,
   val32 p = val32 (firstn i a) * val32 b, nth k p = 0 for i + 6 <= k.
3. inner loop j = 0..5 (c carry), invariant: length p = 12, limbs p,
   c < 2^32, val32 p + c 2^(32 (i+j)) = val32 p0 + a_i val32 (firstn j b)
   2^(32 i), nth k p = nth k p0 for k >= i + j; step lemma outside the WP
   (val32_replace for the write at i + j).
4. p[i+6] = c ends the outer step (nth (i+6) p0 = 0).
5. copy loop r[i] = p[i+5], i < 6: r = firstn 6 (skipn 5 p); value
   val32 p / 2^160 by VST's valZ_shift (p < 2^352 from the precondition).
6. free p.

mul_ln2 (ReduceProof.v, group B), mirror Verif_reduce body_mul_ln2:
1. p := alloc 7 (zeros, length 7).
2. call num_mul_small(p, LN2, n) through its spec: p' with length 7,
   limbs, val32 p' = val32 LN2w * n (LN2w_num for LN2's length/limbs,
   n < 2^32 from the precondition).
3. copy loop i = 0..5, invariant: length q' = 6, forall j < i,
   nth j q' = nth (S j) p'.
4. end: copy_shift gives q' = skipn 1 p'; limbs_skipn1; mul_ln2_value
   gives val32 q' = q n.  free p.

guess_n (ReduceProof.v, group B), mirror body_guess_n:
1. p := alloc 7; call num_mul_small(p, X, 3098164009): INV_word gives the
   word bound and its value INV; val32 p' = val32 X * INV.
2. g = (p[5] >> 25) | (p[6] << 7): bits185 gives
   Int64.repr (val32 p' / 2^185); guess_value turns it into guess X.
3. keep the return value with `have := _OUTR_` before apply_WP_stmt.

exp_encl_bits (ExpTopProof.v), mirror TopLemmas body_exp_encl_bits:
1. 8 allocs (7 of 6 words, hs of 1 word): all zeros of the right length,
   which are exp_core's length preconditions.
2. call exp_core through its spec (tables_ok passed on): rc.
3. rc <> 0: the `if rc == 0` is false; return rc; encl_fail.
4. rc = 0: ys', hN with core_Z = inr (val32 ys', signed hN); packing loop
   i = 0..2, invariant: length M' = 3, forall j < i, unsigned (nth j M')
   = y_(2j) + 2^32 y_(2j+1) (or_shl32, limbs ys'); then
   s[0] = hs[0] - 160: signed_sub160 with core_bounds; pack_value gives
   valW (map unsigned M') = val32 ys'; encl_ok.
5. the frees, then return rc (the return value kept with `have := _OUTR_`).

maybe_hard_bits (ExpTopProof.v), mirror Verif_top (the decision itself is
decide's spec now):
1. 8 allocs, res = 1, call exp_core through its spec.
2. rc <> 0: res stays 1: hard_fail.
3. rc = 0: decide(y, hs[0], X, q, q1, r): its preconditions are the
   lengths (arr6 from exp_core's spec, arr6_inv), limbs ys', and
   ExpModelBounds.core_bounds on core_Z = inr (val32 ys', signed hN);
   result = repr (decide_Z ...); hard_ok.
4. frees, return res.

rocq-mcp on the top functions
-----------------------------
- Every response carries the context (the function record, about 10 kB
  shown, truncated) and the goal grows to 100-400 kB: probe with `summ`
  (feedback field) and wrap risky tactics in `first [ ... | idtac "fail" ]`,
  since an error message prints the whole goal (one reached 150 kB).
- A call is limited to about 30 s whatever the timeout: cut the proof in
  chunks (intro to first wpauto; the call of exp_core; the rest).
- An argument read from an array (hs[0]) comes as `nth 0 _lv_` with a
  hypothesis `env ? x = Varr _lv_`: `move: CALL; move: H1; rewrite /=;
  case=> <- CALL` substitutes it in the call.
