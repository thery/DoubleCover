# elpiDiff in Rocq

The definitions of elpiDiff in Rocq, mimicking the Elpi code: the same
languages, the same constructors with their arguments in the same order, and
the same evaluators, over the reals of Rocq instead of floats, and all the
passes, one function per Elpi predicate, down to the C++ text, and the proofs
that the passes are correct, with the evaluators as their semantics: the
tangent mode is proved correct (below). The passes compute:
`Compute (main ModeAdjoint "f.elpi" [f])` gives the header Elpi writes.

```
make            # Rocq 9.1; the development is the logical directory ElpiDiff
```

## Theorems

The adjoint modes are stated (`adjoint_mode_correct`, `AdjointMode.v`), not
yet proved: it is the one `Admitted`. The proof is in progress
(`AdjointCorrect.v`, below). `Print Assumptions tangent_mode_correct` lists only the axioms
of the reals of the standard library (`sig_forall_dec`, `sig_not_dec`,
`functional_extensionality_dep`, `classic`), which Coquelicot uses as well.

| Theorem | File | Statement |
|---|---|---|
| `normalize_correct` | `Correctness.v` | where the source computes a value, in any domain, its A-normal form computes the same (for a parametric source) |
| `annotate_correct` | `Correctness.v` | the annotated function computes what the function computes |
| `normalize_parametric` | `AnfEquiv.v` | the normal form of a parametric source is parametric: its instances are related |
| `simplify_correct_tapes` | `SimplifyCorrect.v` | simplify preserves the execution over the reals of a program that follows the scoping discipline `good`, tapes included |
| `duals_derive` | `DualsDerive.v` | where f is `defined`, it is Fréchet-differentiable as a function of the reals of its arguments (Coquelicot's `filterdiff` on `Rn`), and the dual numbers compute its derivative |
| `simulation` | `TangentLoops.v` | the statements tangent generates for a body compute, over the reals, the value and the tangent of its dual evaluation; the activity analysis is sound |
| `scoping` | `TangentGood.v` | those statements follow the discipline `good` |
| `tangent_simulates_duals_with` | `TangentTop.v` | theorem 1 for a function: the tangent function, run over the reals on the primal arguments, the seeded tangents and any initial values in its output-only tangent parameters (`tangent_inputs_with`), gives the value and the tangent of the dual evaluation of the normal form of f; `tangent_simulates_duals` is its instance with zeros there |
| `tangent_mode_correct` | `TangentMode.v` | the tangent mode is correct: where a parametric, well-formed f is defined at x, it is differentiable at x with a linear derivative df, and `simplify (tangent (annotate false (normalize f)))`, run over the reals on `tangent_inputs (decls f) x dx`, gives the value of f and df applied to the seed of dx (dx on the independent and inout reals, 0 elsewhere); `tangent_mode_correct_with` is the same for any initial values of the output-only tangent parameters (`result_dot`, the tangent of a written dependent argument), which are not read |

### The adjoint proof, in progress

The adjoint program is related to the dual evaluation of the source in an
arbitrary direction dx (the `pv` instance of the tangent proof). The reverse
sweep keeps the *pairing*: the sum, over the storages that carry an adjoint
(the owners), of the tangent of the variable they hold times its adjoint.
Transposing `let x = e` moves the adjoint of x to the operands of e weighted
by the partial derivatives, which keeps the pairing since the tangent of x is
the same combination of the tangents of the operands. A body is simulated by
one lemma for its two sweeps (`asim_body`): its forward sweep computes the
values its reverse sweep reads (the to-be-recorded analysis, `needs`), and its
reverse sweep, run from any store that agrees on them, changes the pairing by
the tangent of the body times the seed.

| Milestone | State |
|---|---|
| M1, straight-line bodies (operations, `a[i]`, in-place update) | done: `asim_straight` (`AdjointCorrect.v`) and the top level `adjoint_simulates_duals`, `adjoint_straight_duals` (`AdjointTop.v`), before `simplify`; no `Admitted` |
| M2, branches | done: a branch is replayed in the reverse sweep (`arev_ite`, `AdjointBranch.v`), and the top level `adjoint_branchy_duals` (`AdjointTop.v`, now a corollary of `adjoint_nesty_duals` through the inclusions `straight_branchy`, `branchy_foldy`, `foldy_nesty`), for bodies of straight lets and branches with no assignment in a branch; no `Admitted`. The proof found that adjoint-value lost the original value of an inout array (see `BUGS.md`, fixed in deed0ef) |
| M3, maps | done: `afwd_map`, `arev_map` (`AdjointBranch.v`): the reverse loop replays the body at each index and transposes it from the adjoint of the element, the written array, dependent, having a zero tangent; `adjoint_branchy_duals` now covers maps at the end of the function; no `Admitted` |
| M4, scalar folds and tapes | done: `afwd_fold`, `arev_fold` (`AdjointBranch.v`): the forward sweep pushes the state on a tape before each step when the reverse loop reads it (`fold_tape`); the reverse loop pops it, replays the body and transposes it with the state as an extra owner, and the initial value receives the adjoint of the first state; `adjoint_branchy_duals` now covers scalar folds at the top level; no `Admitted` |
| M5, in-place array folds | done: `afwd_fold_inplace`, `arev_fold_inplace` (`AdjointFold.v`): the forward sweep pushes on the tape of the array the element each step overwrites, when the reverse loop reads it; the reverse loop pops it back before replaying the step; `adjoint_foldy_duals` (`AdjointTop.v`) covers them at the top level. Nests of any depth (`AdjointNBody.v`): an in-place fold whose steps end with a set, with an in-place fold of their state whose steps are again such bodies, or with the state itself (`nbody`); a state whose step ends with a fold or gives it back is never read by the reverse sweep (`nbody_state_dead`, `nbody_ret_dead`), and each step's reverse sweep restores the state and pops what its inner fold pushed (`tail_back`, `arev_fold_nbody`); `adjoint_nesty_duals` covers them; no `Admitted`, only the axioms of the reals |
| M6, `simplify` with tapes, the scoping of the adjoint code | in progress: `simplify_correct_tapes` (`SimplifyCorrect.v`) done, simplify is correct on programs with tapes (a push or a pop now writes its tape, in `simplify.elpi` as well); the scoping discipline `good` of the adjoint code to do |
| M7, adjoint-value at the top, `adjoint_mode_correct` | to do |

Proved in `AdjointCorrect.v`: the operations are linear in the tangents with
the spelled partial derivatives as coefficients; the forward sweep of each
operation computes its value (pushing the overwritten element on the tape of a
recorded storage); the reverse sweep of each operation transposes it, reading
only scalars that occur in it; typing and activity of the values (a value not
varied has a zero tangent); the let, with a fresh variable or updated in
place; returns, with the value adjoint-value leaves; the reverse sweep keeps the
value adjoint-value leaves (`vo_kept`: the reverse code of a straight value
writes only adjoints); `asim_straight`.

Proved in `AdjointTop.v` (`adjoint_simulates_duals`, Qed, for any body
simulated by `asim_body`): the arguments of the adjoint function laid out in
the store, the forward context, the prologue and the seed of each result (a
returned real; a written real, dependent or inout; a written array), the
reverse sweep from the owners (the arguments with an adjoint), the final
adjoints read back as the gradient, `<tangent v, yb> = <seed dx, g>`, and the
value in adjoint-value. Its hypothesis `length dx = in_dim x` was added, and
the Boolean arguments that carry an adjoint are excluded by well-formedness.

## Files

| Rocq | Elpi | Contents |
|---|---|---|
| `Syntax.v` | `syntax.elpi` (and the operators of `operations.elpi`) | L0: `unary`, `binary`, `term`, `ty`, `role`, `result`, `definition`, `function`, `decl`; `written_role`, `varied_role` |
| `Anf.v` | the types of `anf.elpi` | L1 and L1ᵃ: `atom`, `value`, `anf`, `aresult`, `adefinition`, `afunction`, `pexpr`; the annotations `bare` and `ann` |
| `Derivative.v` | the types of `derivative.elpi` | L2: `dvar`, `dexpr`, `dsort`, `dstmt`, `dpass`, `dparam`, `dreturn`, `dbody`, `scoped`, `dfunction` |
| `Target.v` | `target.elpi` | L3: `expr`, `stmt`, `cfunction` |
| `Domain.v` | `numbers.elpi` | `domain`; the reals (`reals`), for Elpi's floats; dual numbers over any domain (`duals`) |
| `Eval.v` | `eval.elpi` | `val`; the evaluator of L0 (`eval`, `eval_function`) |
| `Smooth.v` | — | the partial semantics of Abadi and Plotkin: the domain `smooth_reals`, the predicate `defined` |
| `EvalAnf.v` | `eval-anf.elpi` | the evaluator of L1 and L1ᵃ (`aeval`, `aeval_function`) |
| `Exec.v` | `exec.elpi` | the evaluator of L2 (`exec`, `exec_dfunction`) |
| `Operations.v` | the table of `operations.elpi` | `operation1`, `operation2` (the rows, first row or first match), `extra_arguments`, `partial1`, `partial2`, `unary_name`, `binary_name` |
| `Normalize.v` | the pass of `anf.elpi` | `normalize` (L0 to L1: `norm`, `norm_body`, `normalize_definition`), `expressible`, `declarations` |
| `WellFormed.v` | `well-formed.elpi` | `diagnostic`; `well_formed`, `typecheck`, `typecheck_value`, `type_of`, `occurs`, `reads_around_inner_loop` |
| `Atoms.v` | the atom sets and `atoms-of` of `anf.elpi` | `avar` (the variables of the analyses), `same_term`, `atom_member`, `atom_remove`, `atom_union`, `atoms_of_*` |
| `Activity.v` | `activity.elpi` | `varied`, `varied_value`, `varied_anf`, `fold_varied`, `let_binder`, `fold_binders` |
| `Tbr.v` | `tbr.elpi` | `sweep`; `needs`, `value_needs`, `read_by`, `records`, `records_in`, `state_live` |
| `Annotate.v` | `annotate.elpi` | `annotate` (L1 to L1ᵃ), in two traversals |
| `Transform.v` | the helpers of `derivative.elpi` | `tvar` (the variables of the transformations), `sbind`, `sflatten`, `spell`, `dot`, `bar`, `scale`, `sum`, `with_storage`, the opening of binders, `with_arguments`, `type_of` |
| `Tangent.v` | `tangent.elpi` | `tangent` (L1ᵃ to L2): `tan`, `tan_value`, `tangent_result`, … |
| `Dump.v` | the printer of L2 in `dump.elpi` | `pr_dfunction`: the lines of `dump -- derivative <mode>` |
| `Adjoint.v` | `adjoint.elpi` | `adjoint` (L1ᵃ to L2), modes `adjoint` and `adjoint-value`: `prim` and `fwd_value`, then `adj` and `rev_value` |
| `Simplify.v` | `simplify.elpi` | `simplify` (L2 to L2′): `simplify_expr`, `simplify_stmts`, `fuse`, with a fuel |
| `Lower.v` | `lower.elpi` | `lower` (L2′ to L3), the counter of the names threaded; `lower_all`, the functions of a file |
| `Cxx.v` | `cxx.elpi` | `function_string`, `header_string`: the C++ text |
| `Gallina.v` | `gallina.elpi` | `gallina_file`: the derivative programs after simplification as Gallina, for CertiRocq (assignments threaded as lets, loops `for_up`/`for_down`, reals primitive floats) |
| `Adjudge.v` | the driver of `adjudge.elpi` | `mode`, `check`, `differentiate`, `transform`, `main`: the header and the diagnostics of a case |
| `Scoping.v` | — | `open_pairs`, the opening of a generated function with the numbers simplify and the evaluator use; `good`, the scoping discipline of L2 |
| `SimplifyCorrect.v` | — | theorem 2: `simplify_correct_tapes` |
| `Correctness.v` | — | `parametric` (PHOAS relations of L0); `normalize_correct`, `annotate_correct` |
| `AnfEquiv.v` | — | `anf_eq`, the relation of two instances of L1; `normalize_parametric` |
| `Euclidean.v` | — | `Rn`, R^n as a normed module of Coquelicot; vectors and lists |
| `DualsDerive.v` | — | theorem 3: the domain of the functions of a point with their derivative; `value_of`, `dual_args`; `duals_derive` |
| `TangentCorrect.v` | — | theorem 1, the simulation: `pv`, the record of the four instances; the invariants (`static_ok`, `store_ok`, `ctx_ok`); the cases of returns, lets, operations, branches |
| `TangentLoops.v` | — | the loops of the simulation (map, scalar fold, in-place fold); `simulation` |
| `TangentGood.v` | — | the scoping discipline of the tangent code: `scoping` |
| `TangentTop.v` | — | the layout of the tangent function (`seed`, `tangent_inputs`, `tangent_inputs_with`, `tangent_output`); `tangent_simulates_duals_with`, `tangent_simulates_duals` |
| `TangentMode.v` | — | `tangent_mode_correct_with`, `tangent_mode_correct` |
| `AdjointSpec.v` | — | the layout of the adjoint function: `adjoint_inputs` (primal arguments, initial adjoints xb or the seed yb, the seed of a returned value), `adjoint_output` (the gradient: final minus initial adjoints), `value_given` |
| `AdjointMode.v` | — | `adjoint_mode_correct`, stated (`Admitted`): where f is defined, for every tangent dx, <df (seed dx), yb> = <seed dx, g>, and adjoint-value gives the value back unless f writes an inout argument |

## From Elpi to Rocq

- **Binders.** Elpi's λ-tree syntax (`let E (x\ B)`) becomes PHOAS, parametric
  higher-order abstract syntax: a type of terms is parameterized by the type V
  of its variables, a binder is a Rocq function, `Let_ (e : term V) (b : V ->
  term V)`, and a variable is `Var x`. A closed program is quantified over V:
  `fdef : forall V, definition V`. As in Elpi, no term names a variable with a
  string.
- **Evaluators.** An Elpi evaluator opens a binder with a hypothesis
  (`value-of x V`); a Rocq evaluator instantiates V with the values and applies
  the binder, `eval (b v)`. The evaluator of L2 instantiates V with numbers,
  allocated in order, as Elpi opens the binders with fresh variables (`pi`), so
  that the store can compare them.
- **Relations become functions into `option`.** `None` where the Elpi predicate
  fails: an ill-typed program, an index out of an array, an unknown operator.
- **Comparisons return an option.** A comparison is decided by an `if` in
  Elpi, which never fails. In Rocq it returns an `option bool`, so that a
  domain may refuse a tie: the partial semantics of Abadi and Plotkin (POPL
  2020), where a comparison of two equal reals is undefined (`smooth_reals`,
  in `Smooth.v`). `reals` and `duals` never refuse: the evaluators of Elpi are
  mimicked as before.
- **Numbers.** Elpi's floats become the reals of Rocq (`R`); a literal, a
  string as in Elpi (`"0.9"`, `"13.0 / 12.0"`), is read exactly, as a rational
  number. Elpi's `int` becomes `Z`.
- **Names.** The constructors keep their Elpi names, capitalized (`num` →
  `Num`, `op1` → `Op1`); the prefixes `a-` and `d-` become `A` and `D`
  (`a-let` → `ALet`, `d-for-back` → `DForBack`); the three reserved words of
  Rocq take an underscore (`set` → `Set_`, `let` → `Let_`, `function` →
  `Function_`). A predicate keeps its name with `_` for `-` (`eval-function` →
  `eval_function`).
- **Passes.** An Elpi pass that opens a binder with a hypothesis relating it
  to its image (`as-atom x a` in `normalize`) instantiates, in PHOAS, the
  variables of its input with the terms of its output: `normalize` takes a
  `term (atom V)`, so a source variable is its atom. A continuation-passing
  predicate (`norm T K R`) becomes a function taking its continuation.
- **Hypotheses on variables.** Where Elpi opens a binder with hypotheses on
  its variable (`of x T`, `argument x N R` in `well-formed`), the variables are
  instantiated with the record of that information (`vinfo`), whose identity,
  numbered in order, is what Elpi's `same_term` and `occurs` compare.
- **A pass whose input and output need different variables.** `annotate`
  reads its input with the variables of the analyses (`avar`: an identity and
  whether it is varied) and builds a term over any variables V. Elpi does both
  in one traversal; in PHOAS the closed input is instantiated twice: a first
  traversal computes the annotations into a tree that follows the lets and
  folds, a second rebuilds the term with them.
- **The transformations.** The variables of L1ᵃ are instantiated with what
  Elpi's hypotheses say of them (`tvar`: the variable of the generated code
  that holds it, its type, whether it is varied, its argument), whose stored
  variable is a variable of the output: a transformation is one traversal.
  `recorded N`, on a storage, becomes a flag inherited by the variables stored
  in the storage of another; `written Y`, compared with an atom, an identity
  of the arguments.
- **A counter global to the run.** Elpi's `new-name` draws the numbers of the
  locals from `new_int`, global to the run, so they are numbered across the
  functions of a file: `lower` threads the counter.
- **Relations queried in several modes.** `operation2` has several rows per
  operator and a cut on the first: the table is kept as rows, with one
  function per use (`operation2`, the first row; `operation2_typed`, the
  first row matching given operand types).
- **One declaration per type.** `comparison`, defined in `activity.elpi` from
  the operations table, is in `Operations.v`, with the same definition, so that
  the evaluators use it too. A Rocq inductive is declared in one place:
  the operators of `operations.elpi` are in `unary` and `binary` with
  `unknown1` and `unknown2` of `syntax.elpi`; `v-tape` of `exec.elpi` is in
  `val` with the values of `eval.elpi`; the key `returned` of `exec.elpi` is a
  constructor of the keys of the store, next to the variables.


## Checking against Elpi

`~/claudeExp/elpi/tools/rocqtest.py` (outside the repository, with the reference
cases) prints the functions of every case as Rocq terms (`torocq.elpi`), and
compares what Rocq computes with what Elpi prints: the diagnostics, and the
derivative programs printed by `pr_dfunction` against `dump -- derivative|simplified
<mode>`, and the complete C++ headers against those `main` writes, for the three
modes: 141 comparisons on the reference cases, all identical, line for line and
character for character.
