exp100 in Capla, group A: where the work stands
===============================================

Directory: code/APaul/capla/exp100/proof/ (switch capla). Nothing committed.

Proved (Qed, file builds with `nice -n 19 make <File>.vo`)
----------------------------------------------------------

| file             | specs                                         |
|------------------|-----------------------------------------------|
| NumBasicProof.v  | num_zero_spec, num_copy_spec, num_pow2_spec, num_low_spec |
| NumSubProof.v    | num_sub_spec                                  |
| NumLtProof.v     | num_lt_spec                                   |
| NumBitsProof.v   | num_bitlen_spec, num_scale_spec               |

None of these functions uses `alloc`. Build times and Print Assumptions:
see the report (to be re-measured after the Capla rebuild).

Files of group A
----------------
- GroupALemmas.v: tactics `tidy` (drops exec and the let-bound records),
  `wsimpl` (evaluates sem_binarith/sem_cmp/divu64/shl64/...), `peek`
  (clearbody of FUNC, for `Show` probes only); pure lemmas: list6_ext,
  index1, eq32, val32_replace, limbs_replace, zeros6_aux, pow2_limbs,
  list_split, limbs_firstn, mod_shift, low_limbs, val32_lt_top,
  bitlen_top, bitlen_step, val32_write2, val32_write3, scale_pos; word
  lemmas (Section Words): amt_unsigned, shl_amt, shr_amt, divu32, modu32,
  and_low, mask_eq, mask_and, bit_amt, unsigned_signed_nonneg,
  unsigned_neg, split_word.
- ReduceLemmas.v (pure, for mul_ln2 / guess_n): INV_word, val32_drop1,
  limbs_skipn1, copy_shift, mul_ln2_value, lor_shift7, bits185,
  guess_value. NOT YET COMPILED (written during the Capla rebuild).
- TopLemmasCapla.v (pure, for maybe_hard_bits / exp_encl_bits):
  encl_fail, encl_ok, hard_fail, hard_ok, core_rc_range, signed_sub160,
  or_shl32, pack_value, arr6_inv. NOT YET COMPILED.
- Makefile: rules for GroupALemmas.vo, ReduceLemmas.vo, TopLemmasCapla.vo,
  NumBitsProof.vo: NumBasicProof.vo.

Not mine any more: DecideProof.v (another agent). Waiting: ExpTopProof.v.

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
