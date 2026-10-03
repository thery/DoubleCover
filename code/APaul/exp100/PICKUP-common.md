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
  All 7 chunks pass: the model agrees with the C on the 6718 inputs
  (33 to 50 s and 0.8 GB a chunk, one process, measured).

Done (S1, S2, S3)
-----------------
- ExpBits.v (S1)   xreal xb, the double of the bits; is_x xb x: the sign
                   bit gives the sign of x and xfix xb = floor(|x| 2^P);
                   xreal_is_x.
- ExpTaylor.v      sumR and taylor_exp (Coquelicot).
- ExpBudget.v      one lemma per line of the error budget (u = 2^-160):
                   red_arg_err 2u, horner_err 2.0219u, taylor_err 1.6122u,
                   table_err u/2, budget_total 12.8582u <= 16u.
- ExpBound.v (S2)  core_bound: |exp x - y 2^(hN-P)| <= D 2^(hN-P);
                   core_y_ge: 2^P <= y.
- ExpHard.v        hard, binade, vof, vexp, bp (as in ExpHard.v of
                   code/exptablekl, written with ExpModel's constants).
- ExpFilter.v (S3) decide_ok: decide_Z y hN = 0 and y > D put every z
                   within D 2^(hN-P) of y 2^(hN-P) at distance >= 2^-43
                   of the integers, in units of v.
- ExpSpec.v        exp_encl_ok: exp_encl_Z xb = inr (M, s) ->
                   |exp (xreal xb) - M 2^s| <= D 2^s;
                   maybe_hard_ok: maybe_hard_Z xb = 0 -> ~ hard (xreal xb).
  `make` builds the chain in 28 s (Rocq 9.1).  Print Assumptions of the
  two theorems: the axioms of the reals and the primitive integer, float
  and array axioms (BigZ and Interval); nothing of exp100.

Run
---
  cd code/APaul/exp100/rocq && make                 (the proofs)
  cd model_test && make                             (the test, ~5 min)

Next
----
- The program proof (VST, code/APaul/vst/exp100, Rocq 9.0): exp100.c
  computes exp_encl_Z and maybe_hard_Z; see PICKUP-vst.md.
- ExpTable.v, ExpConsts.v and ExpModel.v also build in Rocq 9.0 (switch
  vst): 0.97 s, 4.08 s, 2.83 s.
