# elpiDiff

Algorithmic differentiation in [Elpi](https://github.com/LPCIC/elpi): from a
small functional description of a C++ function, generate its tangent (forward
mode) and its adjoint (reverse mode) as C++ templates.

**Starting point.** This directory starts from the prototype as it was on
2026-10-02 (commit `c6117b6`). It works: on the reference test cases it
regenerates the expected headers byte for byte, and the generated code passes
the derivative tests (tangent and adjoint against dual numbers, adjoint against
finite differences, dot-product test). The plan below restructures it as a
compiler with explicit intermediate languages.

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
| `target.elpi` | L3, the target language: C++ statements, names as strings. |
| `lower.elpi` | L2 to L3: the only pass that names variables and chooses C++ types. |
| `cxx.elpi` | Printing the target language as C++. |
| `show.elpi` | Printing a generated function as an Elpi term. |
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
- `pow 0` differentiates to `0 * pow(x, -1)`, NaN at `x = 0`;
- the unused `dependent` array of an adjoint is passed as a non-const reference;
- the generated code has redundant patterns (`T x_bar = T(0); x_bar += e;`,
  `pow(x, 1)`).

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
4. L2′, simplifications (and the `pow` fixes): the C++ changes, checked by the
   derivative tests.

In L2, every variable of a generated function is bound at its head, in the
order of creation (`scoped`, composed with `sbind`): the adjoint of a value is
computed far from the value, in the reverse sweep, so a variable cannot be bound
where it is first used.
