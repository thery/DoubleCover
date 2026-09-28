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

$ (S) #h(2em) forall x in [x_0, x_1), #h(0.5em) x "hard to round at level"
  m #h(0.5em) => #h(0.5em) (x, v) in "search"(x_0, x_1, m) "with" v != 0. $

`search` returns an array of candidates $(x, v)$, where the *verdict* $v$ is
1 (hard), 0 (not hard) or 2 (undecided). The array may hold false cases,
never miss a true one.

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
an integer is a *candidate*: it is checked with a precise evaluation and
added to the array with its verdict.

*Why it works.* If $x + i u$ is hard, $Y$ is within $2^(-m)$ of an
integer, so the line is within $2^(-m)$ + drift + errors of it. If the
window covers that, $i$ is a candidate.

= The three programs

- *Program 1*, `htr.c`: evaluates $exp$ with MPFR in three functions.
  Not proved; it is the reference (@annex-p1).
- *Program 2*, the generic search: `htr.c` with three *evaluators* of
  $exp$ as parameters, `eval_seed`, `eval_low`, `eval_check`. An evaluator
  only promises a bound on $exp x$. They are its only external functions:
  the exponent $e$ and the check of a candidate are code of Program 2, built
  on them, and the result is an array, not a printout. Proved once, for all
  evaluators that meet their specifications.
- *Program 3*: evaluators in integer arithmetic, no MPFR, proved to meet
  the specifications.

= The specifications and the dependencies

*The evaluators.*

- `eval_seed`$(x)$ gives the line at each chunk start, and `eval_check`$(x)$
  the value to decide a candidate. Both return three doubles
  $h + l + s approx exp x$.
- `eval_low`$(x)$ returns one double $d$, a lower bound of $exp x$.

#table(
  columns: 3,
  stroke: 0.5pt,
  [], [*specification*], [*of*],
  [E1], [$|h + l + s - exp x| <= 2^(-kappa) exp x$],
    [`eval_seed`, `eval_check`],
  [E2], [$|l| < 2^(e - 53)$ and $|s| < 2^(e - 54)$],
    [`eval_seed`, `eval_check`],
  [E3], [$d <= exp x < d + "ulp"(d)$], [`eval_low`],
)

*What each evaluator is for.* The three answer different questions, are
called at different rates, and need different precisions ($kappa$ is the
number of correct bits):

#table(
  columns: 4,
  stroke: 0.5pt,
  [*evaluator*], [*question*], [*calls*], [*precision needed*],
  [`eval_low`], [which binade is $exp x$ in?], [2 per interval],
    [a few bits, but from below],
  [`eval_seed`], [where does the line start, with what slope?],
    [1 per chunk], [its error must fit in the margin of the window (2c)],
  [`eval_check`], [is this candidate hard?],
    [1 per candidate, about 41 per chunk (*read*)],
    [about $54 + m$ bits and a margin: about 95 for $m = 35$ (*computed*)],
)

So the evaluator to make fast is `eval_check`, and it is not the one that
needs the most precision. A lower precision only widens the undecided band,
and undecided candidates are kept. The $kappa >= 118$ that `search.h` asks
of `eval_check` is a choice, not a requirement: it keeps the error below one
unit of $2^(-64)$, which makes 2d simple. Program 3 gives 158 for all
three.

*The dependencies.* Each line needs the lines below it.

#block(breakable: false, width: 100%, fill: luma(245), inset: 8pt, text(size: 8.5pt)[```
(S) every hard x in [x0, x1) is in the array, with a verdict v != 0
 |-- 2a the exponent e is exact               needs E3       to do, easy
 |-- 2b the conversions to 64 bits           needs E2, 2a   to do
 |-- 2c the window covers the errors         needs E1       to do, HARD
 |-- 2d the check never rejects a hard x     needs E1 E2    to do, easy
 |-- 2e the inner loop                                      done, Scan.v
 `-- 2f the chunks cover [x0, x1)                           done, ScanAll.v

E1..E3 for Program 3
 |-- (E) the integer y is within 2^-160 of exp x                 to do
 |-- 3a (E) + the split of y                 => E1 with kappa = 158, E2
 `-- 3b (E) + y - err cut to 53 bits          => E3
```])

= Program 2: the generic search <sec-p2>

*Interface*, `search.h`:

#listing("/code/APaul/htrplan/search.h")

*Code*: `htr.c`'s `search`, with the calls to MPFR replaced by the
evaluators, and a new function `check` on top of `eval_check`. The diff,
from `make search.diff`:

#listing("/code/APaul/htrplan/search.diff", lang: "diff")

*Back to Program 1.* `eval_seed` = `eval_check` = `htr.c`'s `dd_exp`
($kappa approx 158$), `eval_low` = `htr.c`'s `ref_exp` (rounding toward
zero meets E3). The candidates are then exactly `htr.c`'s. The decision may
differ from `htr.c`'s `check` only within `CHECK_ERR` of the threshold,
where Program 2 answers undecided; on the test slices the two agree
(@annex-test).

*Obligations.*

- *2a.* $e$ is the exponent of `eval_low`$(x)$, exact by E3, since
  $exp x < d + "ulp"(d) <= 2^e$.
- *2b.* `h`, `l`, `s` are scaled by $2^(54 - e)$ and cut into 64-bit
  integers (`get_uint64`), with sums modulo $2^64$. This reads the right bits
  only if $e$ is exact (2a) and $l$, $s$ are small (E2).
- *2c.* The code's window is $2^(64-m)$ + drift (*read*). Four errors are
  not in it: `eval_seed`'s ($kappa$); the drift uses the curvature at the
  start of the chunk, not its maximum; the truncations of `B` add up over $n$
  steps; `A` is truncated. The proof must show they fit in the margin, or
  add a term to `E`.
- *2d.* `check` reads the fractional part $F$ of $Y(x)$ as the search reads
  `A`, within `CHECK_ERR` = 3 units of $2^(-64)$: one for E1, two for the
  truncations. With $d$ the distance of $F$ to the nearest integer, it
  answers 1 if $d + 3 < 2^(64 - m)$, 0 if $d >= 2^(64 - m) + 3$, 2
  otherwise. So 0 means $"dist"(Y(x), ZZ) >= 2^(-m)$.
- *2e, 2f.* Done: `Scan.v`, `ScanAll.v`.

= Program 3: the proved evaluator <sec-p3>

`eval_fix.c` provides `eval_fix`, used as `eval_seed` and `eval_check`, and
`low_fix`, used as `eval_low`. Both start from `fix_exp`, which computes an
integer $y$ and an integer $k$ with $exp x approx y dot 2^(k - 200)$, by
Tang's method:

+ write $x = N ln 2 slash 256 + r$, with $N$ an integer and
  $|r| <= 2^(-9.5)$; then $N = 256 k + j$ with $0 <= j < 256$;
+ compute $exp r$ with its Taylor polynomial of degree 13;
+ multiply by $2^(j slash 256)$, taken from a table of 256 constants; then
  $exp x = 2^k dot 2^(j slash 256) dot exp r$.

Every quantity is an integer $Z$ standing for $Z dot 2^(-200)$. Code:
@annex-code.

*The one bound:*

$ (E) #h(2em) |y dot 2^(k - 200) - exp x| <= "err" dot 2^(k - 200), #h(2em)
  "err" = 2^40. $

*Why (E) is all that matters.* Program 3 never rounds in MPFR's sense:
every operation is on integers, with an explicit floor. Each decision is
taken on the interval $[y - "err", y + "err"]$, which contains the exact
value by (E): the exponent and `eval_low` stop on an `assert` when the
interval does not decide, and the check answers undecided. So a lack of
precision gives more undecided answers or a stop, never a wrong answer.
Correctness rests on (E) alone. (E) is not proved yet; the evidence so far
is the error budget below (*computed*), ten points against MPFR at 400
bits, and the test slices (*measured*, @annex-test).

*From (E) to E1–E3.*

- *3a.* $h$, $l$, $s$ are the first three blocks of 53 bits of $y$: they lose
  less than $2^(-158)$ relative (E1, $kappa = 158$), and each is below the
  last bit of the one before (E2). E2 is relative to $e$: `fix_exp` asserts
  that $y$ is not within `err` of a power of 2, so $y$ has the exponent of
  $exp x$.
- *3b.* $d$ is $y - "err"$ cut down to 53 bits, so $d <= exp x$. The code
  asserts that $y + "err"$ stays below the next 53-bit value, so
  $exp x < d + "ulp"(d)$ (E3).

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

+ 2a to 2d: proves (S) for any evaluators, and fixes $kappa$.
+ (E), 3a and 3b: Program 3 meets the specifications.
+ The whole range: Program 2 only works for $|x| < 1 slash 2$, one binade at a
  time, and above $x = -634$ (@annex-limits).
+ Tie the Rocq models to the C (or its Capla port): not tried yet.

#counter(heading).update(0)
#set heading(numbering: "A.1")

= Annex: Program 1, `htr.c` <annex-p1>

MPFR is used in `dd_exp` (`eval_seed`, `eval_check`), `ref_exp`
(`eval_low`) and `check`, which Program 2 replaces by its own check.

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

*Timing.* The three evaluators cost nothing: `htr3` takes 7.14 s on the
first slice, against 7.11 s with the previous interface, where Program 3
had its own `expo` and `check` (*measured*, medians of three alternated
runs, cpu0, turbo off). The check is one `fix_exp` per candidate in both.

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
