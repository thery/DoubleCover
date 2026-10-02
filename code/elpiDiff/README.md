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
| `adjudge.elpi` | The driver: accumulates everything, `main` and `terms`. |

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
elpi -I . <case>/primal.elpi -exec main -- <case> tangent|adjoint [<output directory>]
```

writes `<case>/tangent.hpp` or `<case>/adjoint.hpp`, one header for all the
well-formed functions, and `<case>/diagnostics.txt` for the refused ones.

```
elpi -I . <case>/primal.elpi -exec terms -- tangent|adjoint
```

prints the generated programs as Elpi terms (L3) instead.

```
elpi -I . <case>/primal.elpi -exec dump -- anf|annotated
elpi -I . <case>/primal.elpi -exec dump -- derivative|simplified|target tangent|adjoint
```

prints each function of the case at one stage of the pipeline, in a readable
form: L1, L1ᵃ, L2 before and after simplification, or the C++. Diffing two
stages shows what a pass does. The printer numbers the locals per function, so
its names may differ from those of the generated C++.

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

## Using the adjoint: computing a gradient

The adjoint of `f` has the arguments of `f`, then the adjoint `x_bar` of each
argument that carries a derivative, then the *seed*, the adjoint of the result:

- the adjoint of an `independent` argument is **accumulated into**: the caller
  sets it to zero first (or to a value it wants to add to);
- the seed is the adjoint of the result: `1` for a real result, so that the
  call computes the gradient;
- a `dependent` argument is not touched; its adjoint `y_bar` is the seed;
- an `inout` argument is passed by value; its adjoint is the seed on entry and
  the gradient on exit.

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
  argument (a real or an array).
- `ite C T E`: the condition is a comparison, both branches compute a real.
- `map`: only at the end of the function, with integer literal bounds, writing
  its output array.
- `fold`: a scalar recurrence at the top level of the body, or an in-place
  update of the written array (possibly nested), ending with `set` at the loop
  index.

Current limits:

- no calls to other functions (no inter-procedural differentiation);
- no branch inside an in-place loop, no scalar recurrence inside a loop body or
  a branch;
- an in-place loop that contains another one cannot read its array before it;
- the unused `dependent` array of an adjoint is passed as a non-const reference;
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
