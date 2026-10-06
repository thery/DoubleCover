# elpiDiff

Algorithmic differentiation in [Elpi](https://github.com/LPCIC/elpi): from a
small functional description of a C++ function, generate its tangent (forward
mode) and its adjoint (reverse mode) as C++ templates.

**Starting point.** This directory starts from the prototype as it was on
2026-10-02 (commit `c6117b6`). It works: on the reference test cases it
regenerates the expected headers byte for byte, and the generated code passes
the derivative tests (tangent and adjoint against dual numbers, adjoint against
finite differences, dot-product test). The plan below restructures it as a
compiler with explicit intermediate languages; all four steps are done.

**Reference cases.** The test cases (one directory per case: `primal.elpi`,
the expected `tangent.hpp`, `adjoint.hpp` or `diagnostics.txt`, and a
`test.cpp`) are kept outside this repository. Their expected headers were
regenerated after step 4, the only step that changes the generated code. Every
change is checked in two ways:

- the regression: every case is regenerated and compared with its expected
  headers, modulo the names of the generated locals (`t3`, `i7`, `r8`, …), and
  any Elpi warning counts as a failure;
- the derivative tests: each `test.cpp` is compiled against the regenerated
  headers and run.

## The pipeline, file by file

| File | Role |
|---|---|
| `syntax.elpi` | L0, the source language: a Wengert list with binders (λ-tree syntax). `arg`, `let`, `map` and `fold` bind Elpi variables; no variable is named by a string. Also roles (`independent`, `dependent`, `inout`, `passive`). |
| `anf.elpi` | L1, A-normal form, a language of its own (`atom`, `value I`, `anf I`), and the translation from L0. Every intermediate value is named by a `let`; that operations apply to atoms is a matter of typing. The index `I` is what binders are annotated with: `bare` for L1, `ann` for L1ᵃ. Also partial-derivative expressions over atoms and atom sets. |
| `operations.elpi` | The elementary operations: their types, C++ spelling and partial derivatives. The only calculus the tool knows. |
| `well-formed.elpi` | Typing and the supported language, on L1, as a judgment returning `ok` or `error Reason`. |
| `activity.elpi` | Forward activity analysis: `varied`, a value depends on an independent argument. |
| `tbr.elpi` | Backward analysis and to-be-recorded: `useful` values, values the reverse sweep reads, when a fold must record its state. |
| `annotate.elpi` | L1 to L1ᵃ: runs the analyses once and records them on every let (varied, active, computed) and fold (state varied, state recorded, records). |
| `derivative.elpi` | L2, the derivative IR: an imperative program over variables bound by Elpi binders, with no C++ names or types. Also how the transformations open the binders of the object language. |
| `tangent.elpi` | Forward mode: the linearization, from L1ᵃ into L2. |
| `adjoint.elpi` | Reverse mode: the transposition, with forward sweep, tapes and replay, from L1ᵃ into L2; what to compute, transpose and record is read from the annotations. |
| `simplify.elpi` | L2 to L2 (L2′): algebra on literals, accumulations that start at zero fused into definitions, literal constants propagated, dead constants removed. |
| `target.elpi` | L3, the target language: C++ statements, names as strings. |
| `lower.elpi` | L2 to L3: the only pass that names variables and chooses C++ types. |
| `cxx.elpi` | Printing the target language as C++. |
| `show.elpi` | Printing a generated function as an Elpi term. |
| `dump.elpi` | Readable printers for L1, L1ᵃ and L2, to debug the passes (`dump` mode). |
| `numbers.elpi` | Domains of numbers for the evaluators: the record of the operations on the reals of a domain; floats, and dual numbers over any domain. |
| `eval.elpi` | The evaluator of L0, polymorphic in the domain of numbers. |
| `eval-anf.elpi` | The evaluator of L1 and of L1ᵃ, polymorphic in the annotations. |
| `exec.elpi` | The evaluator of L2: executes the derivative programs (tangent, adjoint) with a store indexed by their variables. |
| `evaluate.elpi` | Running the functions of a case with the evaluators (`run`, `tangent`, `signatures`, `l1-run`, `passes`, `l2-run`, `l2-signature`, `l2-same`); not loaded by `adjudge.elpi`. |
| `adjudge.elpi` | The driver: accumulates everything, `main` and `terms`. |

## In Rocq

`rocq/` holds the whole tool in Rocq, mimicking the Elpi code: the same
languages with the same constructors (binders in PHOAS), the same evaluators
over the reals of Rocq instead of floats, and every pass, one function per Elpi
predicate, from `normalize` down to the C++ text, chained by `main` as in
`adjudge.elpi`. The passes compute: `Compute (main ModeAdjoint "f.elpi" [f])`
gives the header Elpi writes.

The Rocq passes are checked against the Elpi ones on all the reference cases
(`rocqtest.py`, with the cases): the diagnostics, the derivative programs in L2
for the three modes before and after simplification, and the complete C++
headers are identical, 141 comparisons. There are no theorems yet: the
definitions are meant to state, then prove, that the passes are correct, with
the evaluators as their semantics. `rocq/README.md` gives the correspondence,
file by file, and how each construction of Elpi is rendered in Rocq.

## The languages and their Elpi types

Each intermediate language is a family of Elpi types, so that Elpi's
typechecker checks that every pass produces a term of the next language. A
function goes through:

```
  L0            L1                L1ᵃ              L2            L2′           L3           C++
function ──▶ afunction bare ──▶ afunction ann ──▶ dfunction ──▶ dfunction ──▶ cfunction ──▶ string
      normalize          annotate        tangent/adjoint    simplify       lower     function-string
```

and each arrow is a predicate whose `func` declaration states it:

```elpi
func normalize function -> afunction bare.                 % anf.elpi
func well-formed afunction bare -> diagnostic.             % well-formed.elpi, a check on L1
func annotate bool, afunction bare -> afunction ann.       % annotate.elpi
func tangent afunction ann -> dfunction.                   % tangent.elpi
func adjoint bool, afunction ann -> dfunction.             % adjoint.elpi
func simplify dfunction -> dfunction.                      % simplify.elpi
func lower dfunction -> cfunction.                         % lower.elpi
func function-string cfunction -> string.                  % cxx.elpi
```

The `bool` of `annotate` and `adjoint` says whether the adjoint also computes
the value of the function (mode `adjoint-value`).

| Language | File | Its types | A variable is |
|---|---|---|---|
| L0, the source | `syntax.elpi` | `function`, `definition`, `result`, `term` | an Elpi variable of type `term` |
| L1, A-normal form | `anf.elpi` | `afunction bare`, `adefinition bare`, `aresult`, `anf bare`, `value bare`, `atom` | an Elpi variable of type `atom` |
| L1ᵃ, annotated | `anf.elpi` | the same, indexed by `ann` instead of `bare` | an Elpi variable of type `atom` |
| L2 and L2′, the derivative IR | `derivative.elpi` | `dfunction`, `scoped`, `dbody`, `dparam`, `dpass`, `dreturn`, `dstmt`, `dsort`, `dexpr`, `dvar` | an Elpi variable of type `dvar` |
| L3, the target | `target.elpi` | `cfunction`, `stmt`, `expr` | a `string`, its C++ name |

Some types are shared by several languages: `ty` (`real`, `integer`,
`boolean`, `array N`), `role` (`independent`, `dependent`, `inout`,
`passive`), the operators `unary` and `binary` (`operations.elpi`), and `decl`,
an argument as plain data.

### L0: `function`, `term`

The input, written by the user. A `term` nests expressions freely; `let`,
`map` and `fold` bind Elpi variables of type `term` (λ-tree syntax):

```elpi
type function string -> definition -> function.
type arg  string -> ty -> role -> (term -> definition) -> definition.
type body result -> term -> definition.
type returns ty -> result.          type writes term -> result.
type num string -> term.            type nat int -> term.
type op1 unary -> term -> term.     type op2 binary -> term -> term -> term.
type get term -> term -> term.      type set term -> term -> term -> term.
type let term -> (term -> term) -> term.
type ite term -> term -> term -> term.
type map  term -> term -> (term -> term) -> term.
type fold term -> term -> term -> (term -> term -> term) -> term.
```

### L1: `afunction bare`, `anf bare`, `value bare`, `atom`

A-normal form: the constructors mirror those of L0, prefixed with `a-`, but
the types separate what L0 mixes. A binder binds an `atom`, an operation takes
`atom`s, a `let` binds a `value` in a body `anf`:

```elpi
type a-num string -> atom.          type a-nat int -> atom.
type a-op1 unary -> atom -> value I.
type a-op2 binary -> atom -> atom -> value I.
type a-get atom -> atom -> value I. type a-set atom -> atom -> atom -> value I.
type a-ite atom -> anf I -> anf I -> value I.
type a-map atom -> atom -> (atom -> anf I) -> value I.
type a-fold I -> atom -> atom -> atom -> (atom -> atom -> anf I) -> value I.
type a-let I -> value I -> (atom -> anf I) -> anf I.
type a-ret atom -> anf I.
```

So `a-op2 mul (a-op1 sin x) y`, an operation applied to an operation, is
ill-typed: that operands are atoms is not a property to check, it is a
consequence of the types. The partial derivatives of the operations are
expressions over atoms, of their own type `pexpr` (`p-atom`, `p-num`, `p-op1`,
`p-op2`).

### L1ᵃ: `afunction ann`

The same constructors, with the index `I` instantiated to `ann` instead of
`bare`: the slot `I` of every `a-let` and `a-fold` holds the results of the
analyses,

```elpi
type bare bare.                                    % L1: nothing
type let-ann  bool -> bool -> bool -> ann.         % varied, active, computed
type fold-ann bool -> bool -> bool -> ann.         % state varied, state recorded, records
```

`tangent` and `adjoint` take `afunction ann`: the typechecker refuses to
differentiate a term that has not been annotated.

### L2 and L2′: `dfunction`

The derivative program, imperative but still without names: its variables are
Elpi variables of type `dvar`, all bound at the head of the function by
`scoped`, in the order of their creation, since an adjoint is used far from its
value. A tangent, an adjoint or a tape is derived from its variable:

```elpi
type dfunction string -> scoped dbody -> dfunction.
type named string -> (dvar -> scoped A) -> scoped A.    % an argument, with its C++ name
type fresh string -> (dvar -> scoped A) -> scoped A.    % a local, with the prefix of its name
type done  A -> scoped A.
type dbody dreturn -> list dparam -> list dstmt -> dbody.
type dot-of dvar -> dvar.   type bar-of dvar -> dvar.   type tape-of dvar -> dvar.
```

Statements (`d-define`, `d-assign`, `d-increment`, `d-branch`, `d-for`,
`d-for-back`, `d-push`, `d-pop`, `d-return`) and expressions (`d-var`,
`d-real`, `d-int`, `d-at`, `d-op1`, `d-op2`) carry no C++: a type is
`d-constant ty` or `d-mutable`, an argument is passed `by-value`, `by-ref`,
`by-cref` or `by-ref-unused`. L2′ is not a new type: `simplify` maps
`dfunction` to `dfunction`.

### L3: `cfunction`

C++ statements, first order, every name a string, every type spelled:

```elpi
type cfunction string -> string -> list string -> list stmt -> cfunction.   % result type, name, arguments, body
type declare string -> string -> expr -> stmt.      % type name = init;
type id string -> expr.  type lit string -> expr.  type call string -> list expr -> expr.
```

`lower` is the pass where the Elpi variables of type `dvar` become strings
(`t3`, `t3_bar`, `t1_tape`) and the sorts become C++ types (`const T`,
`std::vector<T>`); `cxx.elpi` only prints.

## Usage

A case is a file that accumulates `adjudge` and declares its `primal`
functions. For instance, `void rescale(T& x, T w) { x = w * x * x; }`:

```elpi
accumulate adjudge.
primal (function "rescale" (arg "x" real inout x\ arg "w" real independent w\
  body (writes x) (op2 mul (op2 mul w x) x))).
```

From this directory:

```
elpi -I . <case>/primal.elpi -exec main -- <case> tangent|adjoint|adjoint-value [<output directory>]
```

writes `<case>/tangent.hpp`, `<case>/adjoint.hpp` or `<case>/adjoint-value.hpp`,
one header for all the well-formed functions, and `<case>/diagnostics.txt` for
the refused ones. There are two reverse modes: `adjoint` computes the
derivative only (`f_adjoint`), with the smallest forward sweep; `adjoint-value`
computes the value of the function as well (`f_adjoint_value`): it returns the
returned value, and writes the dependent argument.

```
elpi -I . <case>/primal.elpi -exec terms -- tangent|adjoint|adjoint-value
```

prints the generated programs as Elpi terms (L3) instead.

```
elpi -I . <case>/primal.elpi -exec dump -- anf|annotated
elpi -I . <case>/primal.elpi -exec dump -- annotated|derivative|simplified|target tangent|adjoint|adjoint-value
```

prints each function of the case at one stage of the pipeline, in a readable
form: L1, L1ᵃ, L2 before and after simplification, or the C++. Diffing two
stages shows what a pass does. The printer numbers the locals per function, so
its names may differ from those of the generated C++.

## Evaluating

`eval.elpi` gives L0 a semantics: `eval D T V` says that the term T has the
value V, computing its reals in the domain D. It is a big-step evaluator, one
rule per construct; a binder is opened with the hypothesis `value-of x V`, as
in the transformations. It is the first step towards checking the generated
code against the source, and towards a proof in Rocq.

The evaluator is **polymorphic in the domain of numbers**. A domain is a record
of operations (`numbers.elpi`): how a literal reads, how the operations and the
comparisons of `operations.elpi` compute. Elpi does not let a clause fix the
type of a polymorphic predicate, hence a record rather than one clause per
domain. The domain of floats computes as the C++ doubles do. Integers
(bounds, indices) and booleans are exact in every domain.

**The tangent, for free.** `duals B` is the domain of dual numbers over any
domain B: a pair `dual X DX`, a value and its tangent, where each operation
computes its value in B and its tangent by the chain rule, with the partial
derivatives of `operations.elpi` computed in B. Evaluating a function in
`duals floats`, with inputs `dual x dx`, gives its value and its tangent
dy = J dx: forward differentiation by the evaluator itself, with no
transformation of the program. Over `duals (duals floats)` the same evaluator
gives second derivatives.

The evaluator uses float functions that Elpi 3.7.1 lacks (`fexp`, `pow`,
`string_to_real`, proposed in LPCIC/elpi#459), so it lives in files that
`adjudge.elpi` does not load: the tool itself still runs with Elpi 3.7.1. A case
is evaluated through a file that accumulates `evaluate` and the case,

```
accumulate evaluate.
accumulate primal.
```

```
elpi -I . -I <case> <that file> -exec run -- f 2.0 3.0         % 6.90929742683
elpi -I . -I <case> <that file> -exec tangent -- f 2.0 3.0 / 1.0 0.0
                                                               % 6.90929742683   the value
                                                               % 2.58385316345   ∂f/∂x1 = x2 + cos x1
elpi -I . -I <case> <that file> -exec signatures               % f x1:real:independent x2:real:independent -> returns real
```

An argument is a real literal, an integer, or, for an array of N reals, N real
literals in a row; the result is the returned value, or the new value of the
written argument. For `tangent`, the tangents after `/` are one real for each
real of an argument that is not passive; a passive real has a zero tangent.

**The derivative programs, executed.** `exec.elpi` is the evaluator of L2.
L2 is imperative, so it threads a store: a list of pairs of a variable and its
value, where a variable is a `dvar`, an Elpi variable bound by the function,
or one derived from it (`bar-of v`, `tape-of v`); the store needs no names. Its
values and its operations are those of the evaluator of L0, in the same domains
of numbers; a tape is a list of reals. One evaluator runs every program the tool
generates, tangents and adjoints, before and after simplification:

```
elpi … -exec l2-signature -- adjoint simplified f       % x1:value:real x2:value:real x1_bar:ref:real …
elpi … -exec l2-run -- adjoint simplified f 2.0 3.0 0.0 0.0 1.0
                                                         % x1_bar = 2.58385316345, x2_bar = 2
```

The parameters come in the order of the generated C++; `l2-run` prints the
final value of each, then the returned value. The derivative programs are thus
checked against the source without any C++: at random points, the tangent gives
the value and the tangent of the source over dual numbers, the adjoint passes
the dot-product test ⟨ȳ, J ẋ⟩ = ⟨x̄, ẋ⟩ with J ẋ from the dual numbers, and
the adjoint-value also gives the value of the source, each before and after
simplification; and the simplified program leaves exactly the same floats as
the original one (740 checks on the reference cases).

**Every pass, checked by evaluation.** Each language has an evaluator,
polymorphic in the domain of numbers and sharing the operations of the evaluator
of L0, so each pass is checked by evaluating its input and its output:

| Pass | From → to | Evaluators | Check |
|---|---|---|---|
| `normalize` | L0 → L1 | `eval.elpi`, `eval-anf.elpi` | the same floats, bit for bit (`passes`) |
| `annotate` | L1 → L1ᵃ | `eval-anf.elpi` on both | the same floats, bit for bit (`passes`) |
| `tangent` | L1ᵃ → L2 | L0 over dual numbers, `exec.elpi` | the value and the tangent of the source |
| `adjoint` | L1ᵃ → L2 | L0 over dual numbers, `exec.elpi` | the dot-product test ⟨ȳ, J ẋ⟩ = ⟨x̄, ẋ⟩ |
| `simplify` | L2 → L2′ | `exec.elpi` on both | the same floats, bit for bit (`l2-same`) |
| `lower`, `cxx` | L2′ → C++ | L0 and dual numbers, compiled C++ | the primal and the tangent of the source |

L1 and L1ᵃ share one evaluator, polymorphic in the index of L1, since the
annotations do not change what a program computes. `simplify` is exact on
finite numbers (it rewrites `x * 0` to `0`). On the reference cases, at random
points: `normalize` and `annotate` 140 points, the derivative programs and
`simplify` 740 checks, the compiled C++ 420 checks, all passing. The last line compiles the
generated C++; L3, the C++ statements, has no evaluator of its own: `lower`
only names the variables and spells the types.

This checks the generated code against a semantics of the source. On the
reference cases, at 140 random points and random tangents, the evaluator over
floats agrees with the compiled C++ primal, and over dual numbers with the
compiled tangent that the tool generates, value and tangent (relative tolerance
1e-10, since Elpi prints 12 significant digits).

## The passes on an example

Each example ends with how the generated code is called; the conventions are
summed up in the next section.

### The simplest: `xsin(x) = x * sin x`

```elpi
primal (function "xsin" (arg "x" real independent x\ body (returns real) (op2 mul x (op1 sin x)))).
```

**`anf`: L1.** The nested `sin x` gets a name, `t1`; every operand is now an
atom.

```
xsin(x: real independent) returns real:
    let t1 = sin(x)
    let t2 = x * t1
    return t2
```

**`annotated`: L1ᵃ.** Both values depend on `x` (*varied*) and the result
depends on both (*active*). `t1` is also *computed* by the forward sweep of the
adjoint: the partial derivative of `x * t1` with respect to `x` is `t1`, which
the reverse sweep reads. `t2` is not: nothing reads it.

```
xsin(x: real independent) returns real:
    let t1 = sin(x)    [varied, active, computed]
    let t2 = x * t1    [varied, active]
    return t2
```

**`derivative tangent`: L2.** Each value, then its tangent: the sum, over the
operands, of the partial derivative times the tangent of the operand.

```
xsin_tangent(x: real, x_dot: real, result_dot: ref real) returns real:
    const real t1 = sin(x)
    const real t1_dot = cos(x) * x_dot
    const real t2 = x * t1
    const real t2_dot = (t1 * x_dot) + (x * t1_dot)
    result_dot := t2_dot
    return t2
```

**`derivative adjoint`: L2.** The other way round. The forward sweep computes
`t1`, as the annotation says. The reverse sweep starts from the seed
`result_bar` and transposes the lets in reverse order: `t2 = x * t1` sends its
adjoint to both operands, `t1 = sin(x)` sends its own to `x`. `x` is read twice,
so `x_bar` receives two contributions.

```
xsin_adjoint(x: real, x_bar: ref real, result_bar: real):
    const real t1 = sin(x)
    var real t1_bar = 0
    var real t2_bar = 0
    t2_bar += result_bar
    x_bar += t1 * t2_bar
    t1_bar += x * t2_bar
    x_bar += cos(x) * t1_bar
```

**`simplified adjoint`: L2′.** The accumulators that start at zero and are
incremented once become constants:

```
xsin_adjoint(x: real, x_bar: ref real, result_bar: real):
    const real t1 = sin(x)
    const real t2_bar = result_bar
    x_bar += t1 * t2_bar
    const real t1_bar = x * t2_bar
    x_bar += cos(x) * t1_bar
```

**`target`: the C++ of both modes.**

```cpp
template <typename T>
T xsin_tangent(T x, T x_dot, T& result_dot)
{
    using std::sin;
    using std::cos;

    const T t1 = sin(x);
    const T t1_dot = cos(x) * x_dot;
    const T t2 = x * t1;
    const T t2_dot = (t1 * x_dot) + (x * t1_dot);
    result_dot = t2_dot;
    return t2;
}

template <typename T>
void xsin_adjoint(T x, T& x_bar, T result_bar)
{
    using std::sin;
    using std::cos;

    const T t1 = sin(x);
    const T t2_bar = result_bar;
    x_bar += t1 * t2_bar;
    const T t1_bar = x * t2_bar;
    x_bar += cos(x) * t1_bar;
}
```

**Calling it.** The tangent computes the value and its derivative along
`x_dot`; the adjoint accumulates into `x_bar` the derivative times the seed
`result_bar`. With one input, both give `sin x + x cos x`:

```cpp
{
    double x = 0.5, y_dot;
    double y = adjudge::xsin_tangent(x, 1.0, y_dot);  // y = 0.239713, y_dot = sin x + x cos x = 0.918217
    double x_bar = 0;                                 // accumulated into: start at 0
    adjudge::xsin_adjoint(x, x_bar, 1.0);             // seed 1: x_bar = 0.918217
}
```

**`adjoint-value`: the value and the gradient in one call.** `xsin_adjoint`
computes only the derivative: its forward sweep stops at what the reverse sweep
reads, and the caller who also wants `xsin(x)` must call it. In mode
`adjoint-value` the forward sweep reads the result as well, so everything the
result depends on is *computed*, `t2` included:

```
xsin(x: real independent) returns real:
    let t1 = sin(x)    [varied, active, computed]
    let t2 = x * t1    [varied, active, computed]
    return t2
```

and the adjoint returns the value:

```cpp
template <typename T>
T xsin_adjoint_value(T x, T& x_bar, T result_bar)
{
    using std::sin;
    using std::cos;

    const T t1 = sin(x);
    const T t2 = x * t1;
    const T result = t2;
    const T t2_bar = result_bar;
    x_bar += t1 * t2_bar;
    const T t1_bar = x * t2_bar;
    x_bar += cos(x) * t1_bar;
    return result;
}
```

```cpp
{
    double x = 0.5, x_bar = 0;
    double y = adjudge::xsin_adjoint_value(x, x_bar, 1.0);  // y = 0.239713, x_bar = 0.918217
}
```

### `f(x1, x2) = x1 * x2 + sin x1`

The example of the Wikipedia article on automatic differentiation
(`00-wikipedia`). The source, L0, is already a Wengert list, written with
binders:

```elpi
primal (function "f" (arg "x1" real independent x1\ arg "x2" real independent x2\ body (returns real)
  (let (op2 mul x1 x2) w3\
   let (op1 sin x1)    w4\
   let (op2 add w3 w4) w5\
   w5))).
```

**`anf`: L1.** Every intermediate value is named by a `let` and every operand
is an atom. Here the list does not change; what changes is its type: an operand
can no longer be an expression.

```
f(x1: real independent, x2: real independent) returns real:
    let t1 = x1 * x2
    let t2 = sin(x1)
    let t3 = t1 + t2
    return t3
```

**`annotated`: L1ᵃ.** The analyses, recorded on each binder. The three values
depend on the independent arguments (*varied*) and the result depends on them
(*active*). None is *computed* by the forward sweep of the adjoint: the partial
derivatives read only `x1` and `x2`, arguments that are never overwritten.

```
f(x1: real independent, x2: real independent) returns real:
    let t1 = x1 * x2    [varied, active]
    let t2 = sin(x1)    [varied, active]
    let t3 = t1 + t2    [varied, active]
    return t3
```

**`derivative tangent`: L2.** The linearization: each value, then its tangent,
the sum over the operands of the partial derivative times their tangent. No
names or types of C++ yet: `ref` says how an argument is passed, not how C++
spells it.

```
f_tangent(x1: real, x2: real, x1_dot: real, x2_dot: real, result_dot: ref real) returns real:
    const real t1 = x1 * x2
    const real t1_dot = (x2 * x1_dot) + (x1 * x2_dot)
    const real t2 = sin(x1)
    const real t2_dot = cos(x1) * x1_dot
    const real t3 = t1 + t2
    const real t3_dot = t1_dot + t2_dot
    result_dot := t3_dot
    return t3
```

**`derivative adjoint`: L2.** The transposition, rule by rule: an accumulator
starting at zero for each active value, then the lets in reverse order, each
sending its adjoint to its operands through the partial derivatives. The
forward sweep is empty, as the annotations said.

```
f_adjoint(x1: real, x2: real, x1_bar: ref real, x2_bar: ref real, result_bar: real):
    var real t1_bar = 0
    var real t2_bar = 0
    var real t3_bar = 0
    t3_bar += result_bar
    t1_bar += t3_bar
    t2_bar += t3_bar
    x1_bar += cos(x1) * t2_bar
    x1_bar += x2 * t1_bar
    x2_bar += x1 * t1_bar
```

**`simplified adjoint`: L2′.** An accumulator whose first use is an
increment becomes a definition, a constant when nothing else writes it. These
are the lines of the reverse table of the article.

```
f_adjoint(x1: real, x2: real, x1_bar: ref real, x2_bar: ref real, result_bar: real):
    const real t3_bar = result_bar
    const real t1_bar = t3_bar
    const real t2_bar = t3_bar
    x1_bar += cos(x1) * t2_bar
    x1_bar += x2 * t1_bar
    x2_bar += x1 * t1_bar
```

**`target adjoint`: L3, printed as C++.** `lower` chooses the names and the
types, `cxx` prints.

```cpp
template <typename T>
void f_adjoint(T x1, T x2, T& x1_bar, T& x2_bar, T result_bar)
{
    using std::cos;

    const T t3_bar = result_bar;
    const T t1_bar = t3_bar;
    const T t2_bar = t3_bar;
    x1_bar += cos(x1) * t2_bar;
    x1_bar += x2 * t1_bar;
    x2_bar += x1 * t1_bar;
}
```

**Calling it.** One call of the adjoint gives the whole gradient; the tangent
needs one call per input:

```cpp
{
    double x1 = 2, x2 = 3;
    double x1_bar = 0, x2_bar = 0;
    adjudge::f_adjoint(x1, x2, x1_bar, x2_bar, 1.0);  // x1_bar = x2 + cos x1 = 2.58385, x2_bar = x1 = 2
    double d1, d2;
    adjudge::f_tangent(x1, x2, 1.0, 0.0, d1);         // d1 = 2.58385
    adjudge::f_tangent(x1, x2, 0.0, 1.0, d2);         // d2 = 2
}
```

### A value the reverse sweep reads: `x = 2 * x; return x * x`

In the Wikipedia example the forward sweep is empty, because the partial
derivatives read only arguments. Here (`02-overwrite`), as in `xsin`, they read
an intermediate value, which the adjoint must store:

```cpp
template <typename T>
T overwrite(T x)
{
    x = T(2) * x;
    return x * x;
}
```

In the source, the overwritten `x` is a new version, hence a new binder:

```elpi
primal (function "overwrite" (arg "x" real independent x\ body (returns real)
  (let (op2 mul (num "2") x) x\
   op2 mul x x))).
```

**`annotated`: L1ᵃ.** The partial derivatives of `t1 * t1` are `t1`: the
reverse sweep reads it, so `t1` is *computed* by the forward sweep. `t2` is
not: nothing reads it.

```
overwrite(x: real independent) returns real:
    let t1 = 2 * x    [varied, active, computed]
    let t2 = t1 * t1    [varied, active]
    return t2
```

**`derivative adjoint`: L2.** The forward sweep stores `t1`, the reverse sweep
reads it. Storing needs no tape: in A-normal form a value is never overwritten,
so storing it is computing it into a constant that is still in scope when the
reverse sweep reads it. `t1_bar` receives one contribution per operand.

```
overwrite_adjoint(x: real, x_bar: ref real, result_bar: real):
    const real t1 = 2 * x
    var real t1_bar = 0
    var real t2_bar = 0
    t2_bar += result_bar
    t1_bar += t1 * t2_bar
    t1_bar += t1 * t2_bar
    x_bar += 2 * t1_bar
```

**`target adjoint`: C++,** after simplification. `t1_bar` stays a variable,
since it is accumulated twice.

```cpp
template <typename T>
void overwrite_adjoint(T x, T& x_bar, T result_bar)
{
    const T t1 = T(2) * x;
    const T t2_bar = result_bar;
    T t1_bar = t1 * t2_bar;
    t1_bar += t1 * t2_bar;
    x_bar += T(2) * t1_bar;
}
```

**Calling it.** The function is `(2x)^2`, its derivative `8x`:

```cpp
{
    double x = 3, x_bar = 0;
    adjudge::overwrite_adjoint(x, x_bar, 1.0);        // x_bar = 8x = 24
}
```

A tape is needed only when storage is overwritten, which A-normal form leaves
to two constructs: the state of a `fold`, next, and an array updated in place
(`09-array-state`).

### A recurrence: `acc = 1; for i: acc *= x[i]`

The product of an array (`07-fold-product`), a `fold`:

```elpi
primal (function "prodx" (arg "x" (array 3) independent x\ body (returns real)
  (fold (nat 0) (nat 3) (num "1") i\ acc\
     op2 mul acc (get x i)))).
```

**`annotated`: L1ᵃ.** The partial derivative of `acc * x[i]` with respect to
`x[i]` is `acc`, the state of the fold: the reverse loop reads it, so the
state is *recorded* before each overwrite, and the fold is *computed* by the
forward sweep. Inside the reverse loop, `x[i]` is *computed* again (replayed),
since the other partial derivative reads it; the product is not, nothing reads
it.

```
prodx(x: real[3] independent) returns real:
    let t1 = fold i2 in [0, 3) from s2 = 1:    [varied, active, computed]    [state varied, state recorded, records]
        let t3 = x[i2]    [varied, active, computed]
        let t4 = s2 * t3    [varied, active]
        return t4
    return t1
```

**`simplified adjoint`: L2′.** The forward loop pushes the state on a tape; the
reverse loop pops it, replays `x[i]`, then transposes the body. The state's
adjoint `t1_bar` is moved into `r6_bar` and reset before the body accumulates
into it again.

```
prodx_adjoint(x: const ref real[3], x_bar: ref real[3], result_bar: real):
    var real t1 = 1
    tape t1_tape
    for i2 in [0, 3):
        push t1 onto t1_tape
        const real t3 = x[i2]
        const real t4 = t1 * t3
        t1 := t4
    var real t1_bar = result_bar
    for i5 in [0, 3) downward:
        t1 := pop t1_tape
        const real t7 = x[i5]
        const real r6_bar = t1_bar
        t1_bar := 0
        const real t8_bar = r6_bar
        t1_bar += t7 * t8_bar
        const real t7_bar = t1 * t8_bar
        x_bar[i5] += t7_bar
```

**Calling it.** The adjoint of an array argument is an array, the gradient;
the tangent along the first unit vector gives its first component:

```cpp
{
    std::array<double, 3> x{2, 3, 5}, x_bar{};
    adjudge::prodx_adjoint(x, x_bar, 1.0);            // x_bar = (15, 10, 6)
    double d;
    adjudge::prodx_tangent(x, {1, 0, 0}, d);          // d = 15
}
```

## Tangent or adjoint

### Seeds: dx, and the coefficients of dL

The derivative of a program at a point is a linear map, its Jacobian J, and
neither mode computes J itself: each applies it to one vector, the *seed*.

- The **tangent** pushes a vector forward. Its seed `x_dot` is dx, a direction
  in the inputs, and it computes `y_dot`, which is dy = J dx.
- The **adjoint** pulls a linear form back. Take the scalar L you finally care
  about; its differential in terms of the outputs is dL = ȳ · dy. The seed
  `y_bar` is ȳ = ∂L/∂y, the coefficient of dy, and the adjoint computes
  x̄ = Jᵀ ȳ = ∂L/∂x, the coefficient of dx in dL = x̄ · dx. With ȳ = 1, L is
  the output itself and x̄ its gradient; with ȳ = 2, L is twice the output;
  inside a larger computation L = h(f(x)), ȳ = h′(f(x)).

An adjoint therefore accumulates (`x_bar +=`): when x reaches L along several
paths, its coefficient in dL is the sum of their contributions.

### Two inputs, one output: `g(x, y) = sin(x * y)`

dg = cos(xy) · (y dx + x dy). The generated tangent follows dt1, then dt2, for
one choice of (dx, dy):

```cpp
template <typename T>
T g_tangent(T x, T y, T x_dot, T y_dot, T& result_dot)
{
    using std::sin;
    using std::cos;

    const T t1 = x * y;
    const T t1_dot = (y * x_dot) + (x * y_dot);
    const T t2 = sin(t1);
    const T t2_dot = cos(t1) * t1_dot;
    result_dot = t2_dot;
    return t2;
}
```

The generated adjoint starts from the coefficient of dg and rewrites it as a
coefficient of dt1, then splits it between dx and dy; going backwards, it reads
`t1`, which its forward sweep stores:

```cpp
template <typename T>
void g_adjoint(T x, T y, T& x_bar, T& y_bar, T result_bar)
{
    using std::cos;

    const T t1 = x * y;
    const T t2_bar = result_bar;
    const T t1_bar = cos(t1) * t2_bar;
    x_bar += y * t1_bar;
    y_bar += x * t1_bar;
}
```

At (x, y) = (2, 3), the gradient (y cos(xy), x cos(xy)) is
(2.880511, 1.920341):

```cpp
g_tangent(x, y, 1.0, 0.0, gx);           // dx = 1, dy = 0: gx = ∂g/∂x = 2.880511
g_tangent(x, y, 0.0, 1.0, gy);           // dx = 0, dy = 1: gy = ∂g/∂y = 1.920341
g_adjoint(x, y, x_bar, y_bar, 1.0);      // both: x_bar = 2.880511, y_bar = 1.920341
```

The `1.0` of the three calls is a unit vector each time, but of different
spaces: the tangent's seed lives in the inputs, of dimension 2, so it takes two
unit vectors, (1, 0) and (0, 1), to read the two partial derivatives (with
(1, 1) the tangent gives their sum, 4.800851, and they cannot be told apart);
the adjoint's seed lives in the output, of dimension 1, whose only unit vector
is 1.

The tangent gives a *number*, dg for one (dx, dy); the adjoint gives a
*formula*, dg = x_bar · dx + y_bar · dy, valid for every (dx, dy): one adjoint
call predicts every tangent call, for instance dg = −0.480085 for
(dx, dy) = (0.3, −0.7). This is the dot-product test that every case runs,
ȳ · (J ẋ) = (Jᵀ ȳ) · ẋ. Seeding the adjoint with 2 gives the same numbers as the
tangent with (2, 0) and (0, 2), by linearity, but the factor is on the other
side: the tangent moves the input by 2, the adjoint differentiates L = 2g.

### Cost

For `y = f(x)` with n inputs and m outputs, a call of the tangent with the
i-th unit vector gives column i of J, a call of the adjoint with the j-th unit
vector gives row j. Each call costs a small constant times the cost of f,
whatever n and m:

| | gradient of f: ℝⁿ → ℝ | whole Jacobian |
|---|---|---|
| tangent | n calls | n calls (columns) |
| adjoint | 1 call | m calls (rows) |

A gradient is one row: the adjoint gives it in one call, the tangent in n. This
is why the adjoint is the mode of optimization and machine learning, where a
single real output depends on many parameters (backpropagation is the adjoint
mode). The tangent wins when there are more outputs than inputs, and it needs no
memory: the adjoint runs the computation backwards, so it must store or
recompute the values of the forward run (the to-be-recorded analysis, below).

### The adjoint as the maximal sharing of the tangents

Partially evaluating the tangent of `g` on its two unit seeds gives two
programs, one per partial derivative (`y * 1 + x * 0` becomes `y`):

```cpp
T g_dx(T x, T y, T& result_dot)            T g_dy(T x, T y, T& result_dot)
{                                          {
    const T t1 = x * y;                        const T t1 = x * y;
    const T t2 = sin(t1);                      const T t2 = sin(t1);
    result_dot = cos(t1) * y;                  result_dot = cos(t1) * x;
    return t2;                                 return t2;
}                                          }
```

Merging them, computing once what they share, gives

```cpp
const T t1 = x * y;
const T t2 = sin(t1);
const T c = cos(t1);
gx = c * y;
gy = c * x;
```

which is the adjoint of `g`, partially evaluated with seed 1: `c` is `t1_bar`.

It is not always so direct. With one more level, `h(x, y) = sin(sin(x * y))`:

```
h(x: real independent, y: real independent) returns real:
    let t1 = x * y
    let t2 = sin(t1)
    let t3 = sin(t2)
    return t3
```

the merged tangents, sharing identical subexpressions only, carry one
derivative per input through every intermediate value:

```cpp
const T c1 = cos(t1), c2 = cos(t2);
const T dx = c2 * (c1 * y);      // 4 multiplications:
const T dy = c2 * (c1 * x);      // nothing more is identical
```

The common factor is hidden by the bracketing. Multiplication being
associative, `c2 * (c1 * y)` is `(c2 * c1) * y`, and maximal sharing computes
the factor once:

```cpp
const T k = c2 * c1;             // 3 multiplications
const T dx = k * y;
const T dy = k * x;
```

This is the generated adjoint, where `k` is `t1_bar`, ∂h/∂t1:

```
h_adjoint(x: real, y: real, x_bar: ref real, y_bar: ref real, result_bar: real):
    const real t1 = x * y
    const real t2 = sin(t1)
    const real t3_bar = result_bar
    const real t2_bar = cos(t2) * t3_bar
    const real t1_bar = cos(t1) * t2_bar
    x_bar += y * t1_bar
    y_bar += x * t1_bar
```

In general, the Jacobian is the product of the local Jacobians of the
operations, J = J₃ · J₂ · J₁. The merged tangents bracket it from the inputs,
J₃ · (J₂ · (J₁ · [dx dy])), carrying one column per input; the adjoint
brackets it from the output, ((ȳ · J₃) · J₂) · J₁, carrying one row per
output. Associativity makes the results equal; the widths make the costs
differ. For one output, the adjoint is the bracketing that computes each shared
factor once, the maximal sharing of the vector tangents. Three things go beyond
what a symbolic sharing of the tangents would do:

- **Distributivity.** When a value is used several times, its derivative is a
  sum over paths: in `xsin`, ∂/∂x of `x * sin x` is `sin x * 1 + x * cos x`.
  The accumulations `x_bar +=` factor these sums where the paths meet,
  a·u + a·v = a·(u + v).
- **No symbolic search.** Partial evaluation needs the whole computation laid
  out, then reassociated. A loop whose length is known at run time only
  (`prodx`), or a branch taken on the data (`03-branch`), cannot be unrolled:
  the adjoint achieves the same sharing at run time, by running the
  computation backwards.
- **Memory.** Going backwards needs the values of the forward run: `t1` kept in
  `g`, the tape of `prodx`. The merged tangents keep nothing. The
  to-be-recorded analysis (next section) decides what to store.

Choosing the cheapest bracketing on an arbitrary computation graph is the
optimal Jacobian accumulation problem, which is NP-complete (Naumann, 2008);
forward and reverse are two fixed strategies, each optimal at one extreme: one
input for the tangent, one output for the adjoint.

## What the adjoint keeps: the to-be-recorded analysis

The reverse sweep multiplies adjoints by partial derivatives, and a partial
derivative may read values of the primal computation: `t1` in `xsin`, the state
`acc` in `prodx`. Those values must be available when the reverse sweep runs.
`tbr.elpi` decides which ones, `annotate.elpi` records the decision on L1ᵃ.

**What a partial derivative reads.** It is fixed by the table of
`operations.elpi`, and only matters when the operand is *varied* (a passive
operand gets no adjoint, so its partial derivative is never computed):

| Operation | Partial derivatives | The reverse sweep reads |
|---|---|---|
| `a + b`, `a - b`, `-a` | `1`, `±1` | nothing |
| `a * b` | `b` for `a`, `a` for `b` | `b` if `a` is varied, `a` if `b` is varied |
| `a / b` | `1 / b`, `-(a / (b * b))` | `b` if `a` is varied; `a` and `b` if `b` is varied |
| `sin a`, `cos a`, `exp a`, `log a`, `sqrt a`, `pow(a, k)` | `cos a`, `-sin a`, `exp a`, `1 / a`, `1 / (2 sqrt a)`, `k pow(a, k-1)` | `a` (nothing for `pow(a, 0)`) |
| `a[i]`, `a with [i] = v` | | the index `i` |
| `if c then … else …` | | the condition `c`, and what the branches read |
| `map`, `fold` over `[lo, hi)` | | the bounds, and what the body reads |

**The analysis.** One pass over each body, from its end to its start, computes
two sets of atoms:

- *useful*: the atoms the result depends on through derivatives. A let is
  *active* when its value is varied and useful: only active lets are
  transposed, so only their partial derivatives are read.
- *read*: the atoms the reverse sweep of the rest of the body reads. A let
  whose atom is read is *computed*: its value must be available, and so must
  the atoms it is computed from, which become read in turn.

At a let `x = E`, from the sets of the rest of the body: if `x` is active, the
atoms its partial derivatives read are added to *read*, its operands to
*useful*; if `x` is read, it is computed, and its operands are added to *read*.

In mode `adjoint-value` the result itself is read at the end of the forward
sweep, so every value it depends on is computed: the analysis then matters for
what the loops record and replay, not for the body of the function.

**Where the values come from.** In A-normal form no value is ever overwritten,
so keeping a value costs nothing: the forward sweep computes it into a constant
that is still in scope during the reverse sweep. This is what *computed* means
for a let of the function's body: `t1 = sin(x)` in `xsin` and `t1 = 2 * x` in
`overwrite` are computed by the forward sweep and read by the reverse one; in
the Wikipedia example the partial derivatives read only the arguments, so the
forward sweep computes nothing. Only two things are overwritten, and only they
are recorded on a tape:

- **the state of a `fold`**, when the reverse loop reads it: it is pushed
  before each iteration and popped back in reverse (`state recorded` on the
  fold, `prodx`: the partial derivative of `acc * x[i]` with respect to `x[i]`
  is `acc`);
- **an array updated in place**, when the reverse loop reads the element
  overwritten: it is pushed before the update and popped back
  (`09-array-state`).

Inside a loop or a branch, the other values the reverse sweep reads are
*recomputed* (replayed) from the restored state rather than recorded: `x[i]` in
`prodx`, marked *computed* inside the fold, is read again in the reverse loop.
The analysis of a loop body or a branch is the same, run for this replay. A
fold that records is run by the forward sweep even when its value is not read
(`records` on the fold), so that its tape is filled.

## Using the adjoint: computing a gradient

The adjoint of `f` has the arguments of `f`, then the adjoint `x_bar` of each
argument that carries a derivative, then the *seed*, the adjoint of the result:

- the adjoint of an `independent` argument is **accumulated into**: the caller
  sets it to zero first (or to a value it wants to add to);
- the seed is the adjoint of the result: `1` for a real result, so that the
  call computes the gradient;
- a `dependent` argument is not touched by `f_adjoint`, and receives the value
  from `f_adjoint_value`; its adjoint `y_bar` is the seed;
- an `inout` argument is passed by value; its adjoint is the seed on entry and
  the gradient on exit; its new value is not given back, even by
  `f_adjoint_value`, since the reverse sweep reads the value on entry;
- `f_adjoint_value` returns the value of a function that returns one.

One call of the adjoint gives the whole gradient, whatever the number of
inputs, where the tangent gives one directional derivative per call: see the
examples above. An `inout` argument carries the seed in its own adjoint:

```cpp
{   // rescale(x, w): x = w * x * x, x inout (02-reference).
    double x = 2, w = 3;
    double x_bar = 1, w_bar = 0;                      // seed in x_bar
    adjudge::rescale_adjoint(x, w, x_bar, w_bar);     // x_bar = 2 w x = 12, w_bar = x * x = 4
}
```

For a function with an array result, `y = F(x)`, the adjoint computes
`x_bar += J^T y_bar`, where J is the Jacobian of F: seeding `y_bar` with the
j-th unit vector gives row j of J, so m calls give the whole Jacobian of a
function with m outputs (n calls of the tangent give it column by column):

```cpp
{   // square_scaled(x, y): y[i] = (2 * x[i])^2, y dependent (05-map).
    std::array<double, 4> x{1, 2, 3, 4}, y{};
    for (int j = 0; j < 4; ++j) {
        std::array<double, 4> x_bar{}, y_bar{};
        y_bar[j] = 1;
        adjudge::square_scaled_adjoint(x, y, x_bar, y_bar);   // x_bar = row j: 8 x[j] at j, 0 elsewhere
    }
}
```

The generated functions are templates: `T = double` computes numbers, and an
instantiation with dual numbers is what the derivative tests use to check them.

## The supported language

- Types: `real`, `integer`, `boolean`, `array N` (reals, static extent).
- Operations: `neg`, `sin`, `cos`, `exp`, `log`, `sqrt`, `pow K`; `add`, `sub`,
  `mul`, `divide`; comparisons `lt`, `le`, `gt`, `ge`.
- A function either returns a real, or writes a single `dependent` or `inout`
  argument (a real or an array). An `independent` or `inout` argument is a
  real or an array: an integer carries no derivative. An array the function
  computes is built, never just another array argument.
- `ite C T E`: the condition is a comparison, both branches compute a real.
- `map`: only at the end of the function, from index 0 to an integer literal,
  writing its output array, which is `dependent` (the map computes all of it).
- `fold`: a scalar recurrence at the top level of the body, or an in-place
  update of the written array (possibly nested), ending with `set` at the loop
  index.

Current limits:

- no calls to other functions (no inter-procedural differentiation);
- no branch inside an in-place loop, no scalar recurrence inside a loop body or
  a branch;
- an in-place loop that contains another one cannot read its array before it;
  an in-place loop nested in another cannot read the state of the outer one;
- the unused `dependent` array of `f_adjoint` is passed as a non-const
  reference;
- `f_adjoint_value` does not give back the new value of an `inout` argument;
- a generated function may not use all its arguments (`-Wunused-parameter`).

## Plan: a compiler with intermediate languages

In the starting point, `tangent.elpi` and `adjoint.elpi` differentiated,
chose C++ names and chose C++ types in one go, producing C++ statements
directly. The goal is to separate these concerns into passes between explicit
languages, each its own Elpi `kind`, so that Elpi's typechecker guarantees the
shape of every pass's output.

| Language | Content | Invariant | Produced by |
|---|---|---|---|
| L0 Source | `term`, nested expressions | — | `primal` |
| L1 ANF | own types `atom`, `value`, `anf` | operands are atoms, by typing | `anf` |
| L1ᵃ Annotated ANF | L1 indexed by `ann`: each `let` and `fold` carries the analyses | analyses done once, as data | `annotate` |
| L2 Derivative IR | imperative `prog` with binders (`zero`, `accum`, `push`, `pop`, `for-down`, …) | differentiated, no names, no C++ | `tangent` / `adjoint` |
| L2′ Optimized | same `prog` | — | simplifications |
| L3 Target | `stmt`, names as strings | names and C++ types fixed | `lower` |
| C++ text | | | `cxx` |

Steps, in this order, each checked against the reference cases:

1. **Done.** L2 and `lower`: differentiation produces the derivative IR, with
   no C++ names or types; `lower` names the variables and spells the types. The
   generated C++ is unchanged modulo the names of the generated locals (here it
   is even unchanged byte for byte).
2. **Done.** L1, typed ANF: the analyses and the transformations work on L1
   only; a partial derivative is an expression over atoms (`pexpr`). The
   generated C++ is unchanged byte for byte.
3. **Done.** L1ᵃ: `annotate` records the analyses on the term; `tangent` and
   `adjoint` read the annotations and call no analysis, so the adjoint is the
   plain transposition. The generated C++ is unchanged byte for byte.
4. **Done.** L2′, simplifications: the partial derivative of `pow 0` is 0 (it
   was `0 * pow(x, -1)`, NaN at 0), and `simplify` cleans up what the naive
   differentiation rules produce together. The C++ changes: the adjoints of the
   reference cases shrink from 640 to 489 lines, the tangents are unchanged;
   checked by the derivative tests (tangent and adjoint against dual numbers,
   adjoint against finite differences, dot-product test).

In L2, every variable of a generated function is bound at its head, in the
order of creation (`scoped`, composed with `sbind`): the adjoint of a value is
computed far from the value, in the reverse sweep, so a variable cannot be bound
where it is first used.
