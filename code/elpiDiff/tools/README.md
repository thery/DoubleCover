# Tools for checking elpiDiff against the reference cases

The reference cases are not in the repository: every tool reads them from the
directory `$CASES` (default `~/claudeExp/elpi/cases`), one subdirectory per
case. The `[code dir]` argument defaults to the elpiDiff code next to this
directory (`..`), and `[rocq dir]` to `../rocq`.

- `regress.sh [code dir]` regenerates every case with the elpiDiff code and
  compares with the expected headers, modulo the names of the generated
  locals (`canon.py`); any Elpi warning counts as a failure.
- `numtest.sh [code dir]` compiles each case's `test.cpp` against the
  regenerated headers and runs it, with `shim/check.hpp`, a stand-in for the
  real `check.hpp` (no dpllmad, autodiff or catch2): tangent and adjoint against
  dual numbers, adjoint against finite differences, dot-product test.
- `evaltest.py [code dir]` checks the L0 evaluator against the C++ of every
  case at random points: over floats against the primal (`primal.hpp`), and
  over dual numbers, along random tangents, against the generated tangent
  (`tangent.hpp`). It needs an Elpi with
  `fexp`, `pow` and `string_to_real` (LPCIC/elpi#459): `ELPI` is its binary,
  by default the one built in `~/git/elpi`.
- `l2test.py [code dir]` executes the derivative programs in L2 (tangent,
  adjoint, adjoint-value, before and after simplification) with the evaluator
  of L2, and checks them against the evaluator of L0 over dual numbers: the
  tangent, and the dot-product test for the adjoints; and that simplification
  leaves exactly the same floats.
- `passtest.py [code dir]` checks that `normalize` and `annotate` preserve the
  semantics exactly: the evaluators of L0 and L1 give the same floats on the
  source, its A-normal form and its annotated form.
- `torocq.elpi` prints the primal functions of a case as Rocq terms (the PHOAS
  syntax of `code/elpiDiff/rocq/Syntax.v`).
- `rocqtest.py [rocq dir] [stage..]` compares the passes written in Rocq with
  the Elpi ones on every case: the diagnostics, the derivative programs in L2
  (`pr_dfunction` against `dump`), the complete C++ headers, and the Gallina files (`gallina` mode).
- `gallinatest.py [code dir]` checks the Gallina output (`gallina` mode, for
  CertiRocq) against the C++ output, on every case and mode, at random points:
  the generated functions run in Rocq (`vm_compute`, primitive floats) and
  compiled from C++ must give the same results; the axioms `fsin`, `fcos`,
  `fexp`, `flog` are replaced for the test by series accurate to about 1e-12.
- `adjspectest.py [rocq dir]` checks the statement of the adjoint theorem
  (`rocq/AdjointMode.v`) on every well-formed case, symbolically: Rocq runs the
  simplified tangent and adjoint programs over the reals on symbolic arguments,
  adjoints, seed and tangent, and proves with `ring` the dot-product identity
  <tangent, yb> = <seed dx, g> on the layout of `rocq/AdjointSpec.v`.
