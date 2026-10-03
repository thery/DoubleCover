Pick-up: the common part of the exp100 proof (2026-10-03)
==========================================================

The common part is what the program proofs (VST, Capla) and the pure
proofs share: exp100.c written as functions on Z, in
rocq/ExpModel.v.  A program proof shows that the C computes these
functions; the pure proofs (S1, S2, S3 below) are about these functions.

Done (S0)
---------
- rocq/ExpModel.v, built with Rocq 9.1 (switch native), 3 s.
    core_Z xb        exp_core: inl rc (1: |x| >= 1024, inf, NaN;
                     2: the check q(n) <= X < q(n+1) fails; 3: r >= RMAX)
                     or inr (y, hN)
    exp_encl_Z xb    exp_encl_bits: inr (M, s) with s = hN - P
    exp_core_Z xb    the same as an option
    maybe_hard_Z xb  maybe_hard_bits: 0 or 1
    decide_Z y hN    the filter once exp_core returned 0
    core_rel, core_relP   what core_Z = inr (y, hN) says, step by step,
                     in the readable form (/ 2^k, mod 2^k, valZ)
    exp_core_ZE, maybe_hard_ZE   the enclosure and the filter read core_Z
  The functions compute with shifts (shr, pow2), the k last bits of a
  positive (low) and precomputed constants (LN2v, RMAXv, Cs, Ts), which
  vm_compute runs 5.6x faster than / 2^k (core_Z: 10.6 ms against
  59 ms, measured on 100 calls).  Each helper has its lemma back to the
  readable form: shrE, lowE, pow2E, LN2vE, RMAXvE, CvE, TvE, xsignE,
  xbexpE, xmant0E, scaleE, qE, guessE, jidxE, hidxE, mulshrE.
- rocq/model_test: the model against the C.
    gen_tests.c   includes ../../exp100.c; writes Tests<i>.v, 7 chunks of
                  the 6718 inputs: specials (0, subnormals, inf, NaN,
                  +-1024), the doubles near k ln2/64 and their neighbours,
                  random bits; `make stats` prints the paths taken
                  (rc 0: 6538, rc 1: 180, rc 2 and 3: never; the guess of
                  n raised 1590 times, never lowered: INV is rounded down)
    Check.v       ok: same return code, M, s and maybe_hard
    Tests<i>.v    forallb ok tests = true by vm_compute
  Tests0 (959 inputs) passed: 18 s vm_compute + 18 s Qed.
  Tests1..6 are to be run on roquableu.

Run the test
------------
  cd code/APaul/exp100/rocq && make && cd model_test && make -j7

Next
----
- S1  bits -> real x: Flocq b64_of_bits / B2R, X = floor(|x| 2^160),
      the sign, the subnormals.
- S2  |exp x - y 2^s| <= 16 2^s, from ExpConsts (LN2_ok, ltZ_rmax, T_ok,
      C_ok, taylor_rem_le) and taylor_exp of exptablekl/ExpTaylor.v; one
      lemma per line of the error budget.
- S3  maybe_hard_Z xb = 0 -> ~ hard x (exptablekl/ExpHard.v).
- The build with Rocq 9.0 (switch vst) is left for later.
