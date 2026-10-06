exp100 in Capla (new Capla, forward proofs on eval_func)
=========================================================

exp100.b is exp100.c (../../exp100/) written in Capla; `make test` runs it
next to the C on 10^6 inputs (0 differences).  Scratch arrays are stack
arrays, except the 12 words of num_mulshr (heap: a stack array cannot be
written directly).  The variable X of the C is named xf: CaplaProof's
enter_loop fails on a variable named X (probe_enter_loop/, minimal case).

proof/: the proof, in the opam switch capla3 (Rocq 9.0.0, mathcomp 2.6.0,
Interval 4.11.5, Bignums, Coquelicot, coq-lsp; the new Capla installed in
it).  Build: `eval $(opam env --switch=capla3) && cd proof && make`.

- Specs.v: the statement of each of the 17 functions, on eval_func, arrays
  as {ffun 'I_n -> int64}, against the model ExpModel.v (m_hard = 42).
- Bridge.v, LimbLemmas.v: from arrays to numbers, words and limbs.
- One file per function (NumAddProof.v ... ExpCoreProof.v, MaybeHardProof.v):
  `X_ok`, with the specs of the callees as hypotheses.
- CaplaFinal.v: the callees plugged in; maybe_hard_bits_correct and
  exp_encl_bits_correct (if a run returns 0: x is not hard / the enclosure
  of exp x holds), and the same on Capla's small-step semantics
  (*_sem_correct, through starN_interp_eval_func).  Print Assumptions:
  classical logic, the reals, functional extensionality, the primitive
  integers, floats and arrays, and Capla's parameters for external
  functions.

ExpCoreProof.vo is heavy: about 30 min and 17.5 GB to build (measured).
The exp100 model is copied from ../../exp100/rocq into proof/exp100-model/.
