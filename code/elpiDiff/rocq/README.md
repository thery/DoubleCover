# elpiDiff in Rocq

The definitions of elpiDiff in Rocq, mimicking the Elpi code: the same
languages, the same constructors with their arguments in the same order, and
the same evaluators, over the reals of Rocq instead of floats. They are meant
to state, then prove, that the passes of elpiDiff are correct. There are no
theorems yet, and the passes (`normalize`, the analyses, `annotate`, `tangent`,
`adjoint`, `simplify`, `lower`, `cxx`) are still to be written.

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
- **One declaration per type.** A Rocq inductive is declared in one place:
  the operators of `operations.elpi` are in `unary` and `binary` with
  `unknown1` and `unknown2` of `syntax.elpi`; `v-tape` of `exec.elpi` is in
  `val` with the values of `eval.elpi`; the key `returned` of `exec.elpi` is a
  constructor of the keys of the store, next to the variables.
