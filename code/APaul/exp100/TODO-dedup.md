Shared lemmas for exp100: Rocq, VST and Capla
=============================================

The same pure Z facts about ExpModel.v are proved in several files, by
agents that worked in parallel.  Found by comparing lemma names, then by
reading the statements of CoreBounds.v; a duplicate under another name
may still be missing from this list.

| fact                                | rocq/ (Rocq 9.1)            | vst/exp100/CoreBounds.v (T5)     | vst/exp100/Verif_top.v (T6)           |
|-------------------------------------|-----------------------------|----------------------------------|---------------------------------------|
| X < 2^170                           | xfix_lt (ExpBudget.v)       | xfix_bound                       | xfix_bound                            |
| n < 2^17                            | n_bound (ExpBudget.v)       | checked_n_bound                  | n_bound                               |
| C_i: C_0 = 2^160, 0 <= C_i <= 2^160 | Cv0, Cv_ge0 (ExpBudget.v)   | Cv_bound                         | Cv0, Cv_all                           |
| T_j: 2^160 <= T_j < 2^161           | Tv_ge (ExpBudget.v)         | Tv_bound, Ts_bound               | Tv_all, Ts_bound                      |
| the Horner values                   | horner_ge (lower bound)     | horner_step, horner_from_S       | horner_from_S, horner_from_bound, horner_bound, mulshr_bound |
| RMAX < 2^154, LN2 >= 2^185          | --                          | RMAXv_lt, LN2v_ge                | RMAXv_lt, LN2v_ge                     |
| y - D, y + D have the bit length of y | bitlen_range (ExpFilter.v) | --                              | bitlen_range                          |

The plan
--------
The two program proofs hold numbers differently, so only the pure
mathematics is shared; the loop proofs of VST serve as a canvas for Capla.

|                          | VST (vst/exp100)                     | Capla (capla/exp100/proof)              |
|--------------------------|--------------------------------------|-----------------------------------------|
| Rocq                     | 9.0, switch vst                      | 9.0, switch capla (mathcomp ssreflect)  |
| limbs                    | list Z, valZ, Znth/sublist/upd_Znth  | list int64, val32, List.nth/firstn/replace |
| arithmetic in the proof  | fine                                 | in separate lemmas (nia hangs in the WP) |

1. Shared, pure Z, Stdlib only (no VST, no Capla, no mathcomp), built in
   Rocq 9.1 (switch native) and copied and built in Rocq 9.0 by the
   Makefiles of vst/exp100 and capla/exp100/proof, as ExpModel.v is:
   - rocq/ExpModelBounds.v: each fact of the table above once, in the
     strongest form any user needs (both bounds of Horner, of T_j and of
     C_i; X < 2^170; n < 2^17; the sizes of RMAX and LN2; y; bitlen_range).
   - rocq/ExpLimbs.v: valZ on list Z (valZ_app, valZ_upd, the shift by
     limbs valZ_shift and valZ_drop1, valZ_bounds); or = + on disjoint bits
     (or_shl, lor_shift7, bits185); the packing of 6 limbs into 3 words
     (pack, valW_pack); the carry facts (carry_end and the like).
2. VST: ExpBudget.v, ExpFilter.v (rocq/), CoreBounds.v, Verif_top.v and
   the other Verif_*.v import the shared files and drop their own copies;
   CoreBounds.v keeps only what is about the steps of exp_core
   (reduce_some, core_Z_ok, ...).
3. Capla: one bridge lemma, val32 l = valZ (map Int64.unsigned l), then
   the shared lemmas; each Capla loop proof copies the invariant and the
   order of steps of the VST proof of the same function; the per-step
   arithmetic is a separate lemma, as in NumAddProof.v (num_add_step).
   Not shared: the step lemmas themselves (they would need bridges between
   sublist/upd_Znth and firstn/replace on both sides).
4. Check: every file builds in its switch, no Admitted, Print Assumptions
   unchanged.

When: after T2, T5 and T6 end, not while their agents edit these files.

Follow-ups found by the Capla bridge (capla/exp100/proof/Bridge.v)
------------------------------------------------------------------
Done for Rocq and Capla:
1. rocq/ExpNum.v (Stdlib ZArith/List only) holds limb_bits, NL, limb,
   valZ, num and limb_base k := 2 ^ (limb_bits * Z.of_nat k).
   ExpConsts.v exports it; ExpLimbs.v imports it alone, so the limb
   proofs load no reals.  ExpLimbs.v states its lemmas with limb_base;
   limb_baseE unfolds it.
2. Capla: base32_limb is base32 k = limb_base k; proof/Makefile copies
   ExpNum.v with the other model files.
3. carry_end is only in ExpLimbs.v; NumAddProof.v imports it.
4. valZ_upd is on firstn k xs ++ v :: skipn (S k) xs; Capla converts with
   replace_unsigned (Bridge.v).

Left for VST (vst/exp100):
- Done as text, build NOT yet checked (the vst switch is being rebuilt):
  Exp100.ExpConsts.X became Exp100.ExpNum.X for X in valZ, limb,
  limb_bits, num, NL (63 lines of Common.v, Verif_*.v, TopLemmas.v), and
  the Makefile builds ExpNum.v.  Check: make in vst/exp100.
- To use valZ_upd: one lemma, upd_Znth i l v = firstn (Z.to_nat i) l ++
  v :: skipn (S (Z.to_nat i)) l when 0 <= i < Zlength l.
- Step 2 above: CoreBounds.v and TopLemmas.v to use ExpModelBounds.v and
  ExpLimbs.v instead of their own copies.
