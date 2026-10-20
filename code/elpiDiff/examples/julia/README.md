# Julia: differentiating Julia functions, from Julia to Julia

The Julia wrapper of elpiDiff is independent of the C++ one. The two only
share the core of the tool, from L0 to L2′:

```
functions.jl (Julia)
    │  Meta.parseall, printed untouched as Elpi terms   tools/julia2elpi.jl
    ▼
Julia's AST as an Elpi term                              out/ast.elpi
    │  translation to L0                                jlfront.elpi
    ▼
L0                                                       out/primal.elpi
    │  normalize, annotate, tangent / adjoint, simplify (the core)
    ▼
L2′, the simplified derivative program
    │  printed as Julia                                 julia.elpi
    ▼
out/tangent.jl, out/adjoint.jl
```

## Running it

In a browser, without installing anything: <https://thery.github.io/DoubleCover/elpiDiff/>
([../../demo](../../demo/README.md)). From the command line:

```sh
./run.sh               # functions.jl, then the numeric test
./run.sh my.jl         # any file: prints out/primal.elpi, out/tangent.jl, out/adjoint.jl
./run.sh --passive f:x2,advect!:c   # x2 of f and c of advect! are not differentiated
OUT=/tmp/o ./run.sh …  # writes into /tmp/o instead of out/
```

It needs `julia` with the StaticArrays package (`JULIA=…` to choose the
binary) and `elpi`.

On `functions.jl`, [`tools/juliatest.jl`](../../tools/juliatest.jl) then
runs the generated code at random points:
- the tangent gives the value of the function, and its derivative along
  `dx` agrees with central finite differences;
- the adjoint passes the dot-product test against the tangent,
  ⟨dy, ȳ⟩ = ⟨dx, gradient⟩.

The result is 818 checks with 0 failures (780 numeric, 38 on the signatures).
Breaking one derivative by hand makes the test fail on that function. With
`--passive`, the test varies only the differentiated arguments, and checks
that the passive ones get no `_dot` and no `_bar`: for example
`OUT=/tmp/o ./run.sh --passive f:x2,transcend:y,advect!:c,damped:nu` also
gives 818 checks with 0 failures.

## Choosing the arguments to differentiate

By default every real and every array argument the function reads is
differentiated. `--passive F:X` makes the argument `X` of `F` passive: a
parameter, not differentiated. `F` is the name in the source, its trailing `!`
optional. It adds the fact `jl-passive "F" "X"` (declared in
[`jl-ast.elpi`](../../elpi/front/jl-ast.elpi)) to the AST, and
[`jlfront.elpi`](../../elpi/front/jlfront.elpi) gives `X` the role `passive`
in L0. With `f:x2`:

```julia
function f_tangent(x1, x2, x1_dot)            # no x2_dot
function f_adjoint(x1, x2, x1_bar, result_bar)  # no x2_bar
```

The front end refuses, with a reason:
- an `Int` or a `Bool` argument: it is passive already;
- an `MVector` the function writes: its derivative is the output, and a
  passive argument is never written;
- a function or an argument that the program does not have.

Making every argument passive gives zero derivatives. The output side is not
a choice: a function has one result.

## The generated code

```julia
xsin(x) = x * sin(x)
```
gives
```julia
function xsin_tangent(x, x_dot)
    t1 = sin(x)
    t1_dot = cos(x) * x_dot
    t2 = x * t1
    t2_dot = (t1 * x_dot) + (x * t1_dot)
    result_dot = t2_dot
    return t2, result_dot
end

function xsin_adjoint(x, x_bar, result_bar)
    t1 = sin(x)
    t2_bar = result_bar
    x_bar += t1 * t2_bar
    t1_bar = x * t2_bar
    x_bar += cos(x) * t1_bar
    return x_bar
end
```

- **Tangent:** it takes the arguments, then a tangent for each argument that
  carries one. It returns the value and the tangent of the result.
- **Adjoint:** it takes the arguments, the adjoints to accumulate into (start
  them at 0), and the seed `result_bar`. It returns the accumulated adjoints:
  `x_bar + result_bar * f'(x)`.
- **Reals:** Julia passes reals by value, so a real output is returned. The
  return value is a tuple of the result, if any, then each real output in the
  order of the arguments. A real that the program reads before writing it
  (an adjoint it accumulates into) is also an argument.
- **Arrays:** an array output is updated in place, so pass a `Vector` or an
  `MVector`. An array passed by value is copied first.
- **Indices:** the loops keep the indices of L2, which count from 0, and
  `a[i]` is printed `a[i + 1]`.

## What the front end accepts

[`jlfront.elpi`](../../elpi/front/jlfront.elpi) decides everything the Julia code means:

- **Functions:** `function f(…) … end` and `f(…) = …`.
- **Locals:** every assignment makes a new version (`x = …`, `x += …`,
  `a[i] = …`).
- **`if`:**
  - `if`/`elseif`/`else` that sets one variable, which may be first set
    inside the branches;
  - an `if` at the end whose branches both give a value;
  - `c ? a : b`.
- **`for i in lo:hi`:** a `map` when it writes `y[i]` of an array `y` it
  never reads, and a `fold` over the one variable it assigns otherwise.
  Julia counts from 1 and L0 from 0, so Julia's `i` is `i′ + 1`, and `x[i]`
  is `x[i′]`.
- **Operations:** `+ - * /`, the comparisons, `x^k` with an integer literal
  `k`, `sin cos exp log sqrt`.
- **Roles, from the type annotations:**
  - no annotation, `Real`, `Float64` or `Number` is independent;
  - `Int` and `Bool` are passive;
  - `SVector{N}` is an independent array;
  - an `MVector{N}` the function writes is dependent when it is never read,
    inout otherwise.

  A function that returns `nothing` writes its one `MVector`. A real or an
  array that the function reads can be made passive with `--passive`
  (above).
- **Integer literals:** `2 * x` reads `2` as a real. A literal is an integer
  only as an index, as a loop bound, or with an integer.

Anything else is refused with a reason, for example `while`, a loop or branch
that assigns several variables (L0 has no tuples), or `float(i)` of an integer
variable (L0 has no conversion from integers to reals).
