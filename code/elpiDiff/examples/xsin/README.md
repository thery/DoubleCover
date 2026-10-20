# xsin: from C++ to C++, through Elpi and through Rocq

`xsin(x) = x * sin x`, differentiated in tangent and adjoint mode by two
paths that must give the same C++:

```
                xsin.hpp (C++)
                    │  clang++ -Xclang -ast-dump=json        tools/clang2elpi.py
                    ▼
            clang's AST as an Elpi term                       out/ast.elpi
                    │  translation to L0                     cxxfront.elpi
                    ▼
                L0 in Elpi                                    out/primal.elpi
           ┌────────┴──────────────────┐
           │ Elpi passes               │ printed as a Rocq term (tools/torocq.elpi)
           │                           ▼
           │                       L0 in Rocq                 Xsin.v
           │                           │ Rocq passes (normalize, annotate,
           │                           │ tangent / adjoint, simplify)
           ▼                           ▼
       L2′ in Elpi   ══ equal? ══  L2′ in Rocq ─ printed as an Elpi term (rocq/ToElpi.v)
           │                           │ read back by Elpi     tools/fromrocq.elpi
           │ lower, cxx                │ lower, cxx
           ▼                           ▼
   out/elpi/<mode>.hpp ══ same? ══ out/rocq/<mode>.hpp
```

The cut between Rocq and Elpi is L2′, the simplified derivative programs:
that is what the theorems of [Main.v](../../rocq/Main.v) are about. Lowering
and printing to C++ are not proved, so they are left to Elpi.

## Running it

```sh
make -C ../../rocq      # once: the Rocq development (opam switch `native`)
./run.sh
```

It needs `clang++`, `elpi` and `rocq`, and prints:

```
% examples/xsin/xsin.hpp in L0, from clang's AST (cxxfront.elpi)
accumulate adjudge.

primal (function "xsin" (arg "x" real independent x\ body (returns real)
  (op2 mul x (op1 sin x)))).

Xsin.v: its L0 is the one from the C++
xsin_tangent: the L2′ from Rocq is the L2′ of Elpi
xsin_adjoint: the L2′ from Rocq is the L2′ of Elpi
tangent.hpp: the same C++ from Elpi and from Rocq
adjoint.hpp: the same C++ from Elpi and from Rocq
```

The two L2′ programs are compared as Elpi λ-terms, so up to the names of
their binders. Everything is written into `out/`: the AST, the L0, the C++ of
both paths, and in `out/rocq/` what Rocq printed (`Xsin.out`) and the L2′ terms
read back by Elpi (`l2.elpi`).

## The files

- [`xsin.hpp`](xsin.hpp): the C++ source.
- [`Xsin.v`](Xsin.v): the Rocq side.
  - `xsin_fn`: the L0 term. `run.sh` checks that it is the one printed from the C++.
  - `xsin_tangent` and `xsin_adjoint`: the L2′ programs, shown readably
    (`pr_dfunction`) and as Elpi terms (`to_elpi`).
  - The theorems on xsin. `xsin_accepted` says that xsin is accepted at every
    x. `xsin_tangent_correct` says that the tangent program gives the value
    `x * sin x` and the derivative applied to `dx`. `xsin_adjoint_correct` says
    that the adjoint program gives a gradient `g` with ⟨D dx, yb⟩ = ⟨[dx], g⟩.
    Each is one application of `tangent_correct` and `adjoint_correct`.
- [`run.sh`](run.sh): both paths and the checks.

## The C++ front end

[`cxxfront.elpi`](../../cxxfront.elpi) works on any file, not only xsin:

```sh
python3 tools/clang2elpi.py f.hpp > dir/ast.elpi
elpi -I . -I dir cxxfront.elpi -exec cxx-to-l0 -- f.hpp
```

It accepts the following C++:

- Template functions over `T`.
- Locals, with every assignment making a new version (`x = …`, `x += …`, `a[i] = …`).
- `if`/`else` that assigns one variable, or where both branches return.
- `for (i = lo; i < hi; ++i)` loops:
  - a `map` when the loop writes `y[i]` of an array `y` it never reads;
  - otherwise a `fold` over the one variable the loop assigns.
- Calls to `sin`, `cos`, `exp`, `log`, `sqrt` and `pow(e, k)`.

It decides the roles from the types:

- `T` is independent.
- `double` is a passive real.
- `int` and `bool` are passive.
- A `T&` or `std::array<T, N>&` is dependent when it is never read, inout otherwise.

Anything else is refused with a reason, for example `goto`, a call statement
such as `std::swap`, or a branch or loop that assigns several variables (L0
has no tuples).

[`tools/fronttest.sh`](../../tools/fronttest.sh) runs the front end on the
`primal.hpp` of every reference case. It compares the headers generated from
clang's L0 with those from the hand-written terms:

- 20 headers are the same.
- `04-activity` differs by design: its C++ declares `T nu`, the hand-written
  term makes `nu` passive.
- `11-weno5` (`std::swap`) and `12-goto` (`goto`) are refused.
- `10-call` has no hand-written term to compare with.
