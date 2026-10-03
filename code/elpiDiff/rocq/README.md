# elpiDiff in Rocq

The definitions of elpiDiff in Rocq, mimicking the Elpi code: the same
languages, the same constructors with their arguments in the same order, and
the same evaluators, over the reals of Rocq instead of floats, and the passes,
one function per Elpi predicate. They are meant to state, then prove, that the
passes of elpiDiff are correct. There are no theorems yet. The passes written
so far: the operations table, `normalize`, `well-formed`, the analyses
(`activity`, `tbr`), `annotate` and `tangent`, with the printer of L2; still to
come: `adjoint`, `simplify`, `lower`, `cxx`. The passes compute: `Compute` runs them on a function written
in Rocq.

```
make            # Rocq 9.1; the development is the logical directory ElpiDiff
```

## Files

| Rocq | Elpi | Contents |
|---|---|---|
| `Syntax.v` | `syntax.elpi` (and the operators of `operations.elpi`) | L0: `unary`, `binary`, `term`, `ty`, `role`, `result`, `definition`, `function`, `decl`; `written_role`, `varied_role` |
| `Anf.v` | the types of `anf.elpi` | L1 and L1ᵃ: `atom`, `value`, `anf`, `aresult`, `adefinition`, `afunction`, `pexpr`; the annotations `bare` and `ann` |
| `Derivative.v` | the types of `derivative.elpi` | L2: `dvar`, `dexpr`, `dsort`, `dstmt`, `dpass`, `dparam`, `dreturn`, `dbody`, `scoped`, `dfunction` |
| `Target.v` | `target.elpi` | L3: `expr`, `stmt`, `cfunction` |
| `Domain.v` | `numbers.elpi` | `domain`; the reals (`reals`), for Elpi's floats; dual numbers over any domain (`duals`) |
| `Eval.v` | `eval.elpi` | `val`; the evaluator of L0 (`eval`, `eval_function`) |
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
  A comparison is decided by an `if` in Elpi, which never fails: it returns a
  `bool`.
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
derivative programs printed by `pr_dfunction` against `dump -- derivative
<mode>`. They are identical, line for line, on all the reference cases.
