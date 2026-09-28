#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

// The listings are read from the sources, so the note cannot drift from the
// code.  Build from the repository root: typst compile --root . doc/htr-plan.typ
#let listing(path, lang: "c") = block(width: 100%, fill: luma(245),
  inset: 6pt, text(size: 7.5pt, raw(read(path), lang: lang, block: true)))

#align(center)[
  #text(size: 17pt)[*Proving the hard-to-round search*]
]

#v(0.5em)

Code: `code/APaul/htr.c` and `code/APaul/htrplan/`. Numbers are marked
*read* (off the code), *measured* (a run) or *computed*.

= Definitions

- $e$ is the exponent of $exp x$: $2^(e - 1) <= exp x < 2^e$.
- $Y(x) = exp(x) dot 2^(54 - e)$, in $[2^53, 2^54)$. The integers of this
  scale are the doubles and the midpoints between them: the *grid*.
- $x$ is *hard to round at level $m$* when $"dist"(Y(x), ZZ) < 2^(-m)$: the
  $m$ bits after the round bit of $exp x$ are all equal.
- $u$ is the ulp of $x$: the distance from $x$ to the next double.

= The theorem

For an interval $[x_0, x_1)$ and a level $m$:

$ (T) #h(2em) forall x in [x_0, x_1), #h(0.5em) x "hard to round at level"
  m #h(0.5em) => #h(0.5em) x "is printed". $

The program may print false cases, never miss a true one.

= How the search works

The search cuts $[x_0, x_1)$ into *chunks* of $n = 2^20$ consecutive doubles
$x + i u$, $0 <= i < n$. On a chunk, $Y$ is close to a *line*, since the
derivative of $exp$ is $exp$:

$ Y(x + i u) approx Y(x) + i dot Y(x) u. $

Only the fractional parts matter. They are kept as 64-bit integers (the
unit is $2^(-64)$):

- `A` $approx$ the fractional part of $Y(x)$, `B` $approx$ that of the slope
  $Y(x) u$;
- the *drift* is how far $Y$ moves away from the line over the chunk, at
  most $Y(x) u^2 n^2 slash 2$;
- the *window* is `E` = $2^(64 - m)$ + drift.

The inner loop adds `B` to `A` $n$ times. Each $i$ where `A` is within `E` of
an integer is a *candidate*: it is passed to `report`, which checks it
with a precise evaluation and prints it if it is hard.

*Why it works.* If $x + i u$ is hard, $Y$ is within $2^(-m)$ of an
integer, so the line is within $2^(-m)$ + drift + errors of it. If the
window covers that, $i$ is a candidate.

= The three programs

- *Program 1*, `htr.c`: evaluates $exp$ with MPFR in three functions.
  Not proved; it is the reference (@annex-p1).
- *Program 2*, the generic search: `htr.c` with the three functions as
  parameters `eval`, `expo`, `report`, which must meet a contract E1–E4.
  Proved once, for all parameters that meet it. With MPFR's functions as
  parameters, it is Program 1 again.
- *Program 3*: parameters for Program 2 in integer arithmetic, no MPFR,
  proved to meet E1–E4.

= The contract and the dependencies

*The contract.* `eval` returns $h + l + s approx exp x$ (three doubles);
`expo` returns $e$; `report` checks a candidate.

#table(
  columns: 3,
  stroke: 0.5pt,
  [], [*requirement*], [*used by*],
  [E1], [$|h + l + s - exp x| <= 2^(-kappa) exp x$], [2b],
  [E2], [$|l| < 2^(e - 53)$ and $|s| < 2^(e - 54)$], [2a],
  [E3], [`expo` returns exactly $e$], [2a],
  [E4], [`report` never rejects a hard $x$], [(T)],
)

*$kappa$* is the number of correct bits of `eval`. The code of Program 2
does not fix it; the proof of 2b does, since `eval`'s error is one of the
errors the window must cover. About 118 is enough (*computed*): `eval`'s
error is then below the last bit of `A`. Program 3 gives 158.

*The dependencies.* Each line needs the lines below it.

#block(breakable: false, width: 100%, fill: luma(245), inset: 8pt, text(size: 8.5pt)[```
(T) every hard x in [x0, x1) is printed
 |-- (S) the search passes every hard x to report          needs E1 E2 E3
 |    |-- 2a the conversions to 64 bits      needs E2 E3    to do
 |    |-- 2b the window covers the errors    needs E1       to do, the hard point
 |    |-- 2c the inner loop                                 done, Scan.v
 |    `-- 2d the chunks cover [x0, x1)                      done, ScanAll.v
 `-- report prints every hard x it is given               needs E4

E1..E4 for Program 3
 |-- (E) the integer y is within 2^-160 of exp x            to do
 |-- 3a (E) + the split of y           => E1 with kappa = 158, E2
 |-- 3b (E) + an assert on y           => E3
 `-- 3c (E) + the distance test        => E4
```])

= Program 2: the generic search <sec-p2>

*Interface*, `search.h`:

#listing("/code/APaul/htrplan/search.h")

*Code*: `htr.c`'s `search` with four changes (`make search.diff`):

#listing("/code/APaul/htrplan/search.diff", lang: "diff")

*Obligations.*

- *2a.* `h`, `l`, `s` are scaled by $2^(54 - e)$ and cut into 64-bit
  integers (`get_uint64`), with sums modulo $2^64$. This reads the right bits
  only if $e$ is exact (E3) and $l$, $s$ are small (E2).
- *2b.* The code's window is $2^(64-m)$ + drift (*read*). Four errors are
  not in it: `eval`'s ($kappa$); the drift uses the curvature at the start of
  the chunk, not its maximum; the truncations of `B` add up over $n$ steps;
  `A` is truncated. The proof must show they fit in the margin, or add a
  term to `E`.
- *2c, 2d.* Done: `Scan.v`, `ScanAll.v`.

= Program 3: the proved evaluator <sec-p3>

`eval_fix.c` provides `eval_fix`, `expo_fix` and `check_fix` (the check in
`report`). All three start from `fix_exp`, which computes an integer $y$
and an integer $k$ with $exp x approx y dot 2^(k - 200)$, by Tang's method:

+ write $x = N ln 2 slash 256 + r$, with $N$ an integer and
  $|r| <= 2^(-9.5)$; then $N = 256 k + j$ with $0 <= j < 256$;
+ compute $exp r$ with its Taylor polynomial of degree 13;
+ multiply by $2^(j slash 256)$, taken from a table of 256 constants; then
  $exp x = 2^k dot 2^(j slash 256) dot exp r$.

Every quantity is an integer $Z$ standing for $Z dot 2^(-200)$. `check_fix`
answers hard, not hard, or *undecided* when the error of $y$ does not allow
to decide; undecided cases are printed. Code: @annex-code.

*The one bound:*

$ (E) #h(2em) |y dot 2^(k - 200) - exp x| <= 2^(-160) dot 2^k. $

*From (E) to E1–E4.*

- *3a.* $h$, $l$, $s$ are the first three blocks of 53 bits of $y$: they lose
  less than $2^(-158)$ relative (E1, $kappa = 158$), and each is below the
  last bit of the one before (E2).
- *3b.* The code asserts that $y$ is not within its error of a power of 2,
  so $y$ and $exp x$ have the same exponent (E3).
- *3c.* `check_fix` answers "not hard" only if the distance of $y$ to the
  grid, minus $2^(-160)$, is still at least $2^(-m)$ (E4).

*Proof of (E).* One lemma per step of `fix_exp`. Errors in units of
$2^(-200)$, *computed*:

#table(
  columns: 3,
  stroke: 0.5pt,
  [*step*], [*error*], [*proof*],
  [$r$], [2 units], [$ln 2 slash 256$ certified by `interval`],
  [$|r| <= 2^(-9.5)$], [—], [an `assert` in the code],
  [Horner], [about 4 units], [one floor per step],
  [Taylor remainder], [$2^(-169)$], [one `interval` call],
  [$times 2^(j slash 256)$], [1.5 units], [256 constants, each certified by
    `interval`],
  [total], [$<= 2^(-160)$], [8 bits to spare],
)

= What to do

+ 2a and 2b: proves (S) for any parameters, and fixes $kappa$.
+ (E) and 3a–3c: Program 3 meets the contract.
+ The whole range: Program 2 only works for $|x| < 1 slash 2$, one binade at a
  time, and above $x = -634$ (@annex-limits).
+ Tie the Rocq models to the C (or its Capla port): not tried yet.

#counter(heading).update(0)
#set heading(numbering: "A.1")

= Annex: Program 1, `htr.c` <annex-p1>

MPFR is used in `dd_exp` (`eval`), `ref_exp` (`expo`) and `check` (in
`report`).

#listing("/code/APaul/htr.c")

= Annex: Program 3 <annex-code>

#listing("/code/APaul/htrplan/fix.h")

#listing("/code/APaul/htrplan/eval_fix.c")

The constants come from `gen_fix.c` (with MPFR); they are not trusted, since
each is certified.

= Annex: the test <annex-test>

`make test` compares, line by line, the candidates and the hard cases of
`htr.c`, Program 2 with MPFR, and Program 2 with Program 3 (`htr3`, linked
without MPFR). *Measured*, 2026-09-28:

#table(
  columns: 3,
  stroke: 0.5pt,
  [*slice, 10 000 chunks*], [*candidates*], [*result*],
  [from $0.25$ up], [410 325], [identical; one hard case; none undecided],
  [from $-0.25$ down], [498 078], [identical; one hard case; none undecided],
)

There are many candidates because the drift, about $2^48$ units, is much
wider than the target $2^29$ (*computed*): about 41 per chunk, as in
`htr.c`'s comment (*read*).

= Annex: limits <annex-limits>

- `get_uint64` needs the slope below 1: $|x| < 1 slash 2$ (*computed*).
  Fix: keep only its fractional part.
- $[x_0, x_1)$ must sit in one binade of $x$ and of $exp x$.
- Below $x approx -708$, $exp x$ is subnormal; above $709.78$, it overflows.
- Three doubles hold 158 bits only for $x >= -634$ (*computed*); at
  $x = -700.3$ they keep 66 (*measured*). Below, Program 2 must take $y$
  itself.
- `eval` is called once per chunk, 0.7 ms of inner loop (*computed*), so its
  speed does not matter; the whole range is about 12 core-years
  (*computed*).
