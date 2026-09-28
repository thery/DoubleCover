#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

// The listings are read from the sources, so the note cannot drift from the
// code.  Build from the repository root: typst compile --root . doc/htr-plan.typ
#let code(path) = block(width: 100%, fill: luma(245), inset: 6pt,
  text(size: 7.5pt, raw(read(path), lang: "c", block: true)))

#align(center)[
  #text(size: 17pt)[*Proving the hard-to-round search*]

  #v(0.4em)
  #text(size: 10pt)[From `htr.c` with MPFR to a search with a proved
  exponential]
]

#v(1em)

Names set in `monospace` are identifiers of `code/APaul/htr.c`, of the C
files in `code/APaul/htrplan/`, or of the Rocq files in `code/APaul/rocq/`. Every number is marked *read* (off the code
or a file), *measured* (a run), or *computed* (arithmetic on the other two).

= The goal

Let $x$ be a double and $e$ the exponent of $exp x$, so that
$Y(x) = exp(x) dot 2^(54 - e)$ lies in $[2^53, 2^54)$. The integers are the
*round-bit grid*: the doubles and the midpoints between them. We say that $x$
is *hard to round* at level $m$ when

$ "dist"(Y(x), ZZ) < 2^(-m), $

that is, when the $m$ bits after the round bit of $exp x$ are all equal.

*The theorem we want.* For an interval $[x_0, x_1)$, the list the program
prints contains every double of $[x_0, x_1)$ that is hard to round at level
$m$. We ask for a *superset*: the program may print a false case, it must not
miss a true one. The program works in two stages, a search that produces
*candidates* and a check that decides each candidate; the theorem covers
both.

The final aim is the whole range where $exp$ gives neither an infinity nor a
NaN, about $x in [-745, 709.78]$. Below $|x| < 2^(-54)$ the answer is known by
hand ($exp x$ rounds to 1 or just below). What is left is $64$ binades on
each side, $2 dot 64 dot 2^52 = 2^59 approx 5.8 dot 10^17$ doubles
(*computed*).

= How the search works

The search cuts $[x_0, x_1)$ into *chunks* of $n = 2^20$ consecutive doubles
(*read*, `search`). On a chunk starting at $x$, with $u$ the ulp of $x$,

$ Y(x + i u) approx Y(x) + i dot Y(x) u, #h(2em) 0 <= i < n, $

because the derivative of $exp$ is $exp$. Only the fractional part matters,
kept on 64 bits:

- `A` approximates the fractional part of $Y(x)$, times $2^64$;
- `B` approximates the fractional part of the slope $Y(x) u$, times $2^64$;
- `E` is a window: $2^(64-m)$, the target, plus a bound on how far the
  straight line drifts from the curve over the chunk, $Y(x) u^2 n^2 slash 2$.

The inner loop adds `B` to `A` $n$ times and reports every $i$ where `A` is
within `E` of an integer (the test `A < 2*E` after shifting by `E`). This loop,
a comparison and an addition, is the whole cost: $99.99%$ of the run on
$[0.25, 0.25001)$ (*measured*, the Capla benchmark).

*The one idea of the proof.* The true value and the line differ by at most
(drift + errors of `A`, `B`). If the window is at least target + drift +
errors, no hard case falls outside it.

= Three programs

- *Program 1, the initial program*, is `htr.c` as it is, with three calls to
  MPFR. It is not proved; it is the reference the others are tested against.
  It is shown in @annex-p1.
- *Program 2, the generic search*, is `htr.c`'s search with the calls to MPFR
  abstracted into parameters, and a contract on them. The proof starts here.
- *Program 3, the proved evaluator*, is an exponential in integer arithmetic
  that meets the contract, with no MPFR. Plugged into Program 2, it gives a
  search with nothing trusted but the arithmetic.

All the C is in `code/APaul/htrplan/`, and every listing below is read from
it.

= Program 2: the generic search <sec-p2>

Program 2 is `htr.c` with its three MPFR functions turned into parameters:
`dd_exp` becomes `eval`, `ref_exp` becomes `expo`, and `check` becomes
`report`. Its interface, with the contract on the parameters, is
`search.h`:

#code("/code/APaul/htrplan/search.h")

The search itself, `search.c`, is `htr.c`'s `search` line for line, except
for the three names:

#code("/code/APaul/htrplan/search.c")

== The instantiation that gives back Program 1

Take for the parameters `htr.c`'s own three functions, in `eval_mpfr.c`:

#table(
  columns: 2,
  stroke: 0.5pt,
  [*parameter*], [*instance*],
  [`eval`], [`eval_mpfr` = `htr.c`'s `dd_exp`, unchanged],
  [`expo`], [`expo_mpfr` = `htr.c`'s `ref_exp`, returning the exponent of its
    result instead of the result],
  [`report`], [`check_mpfr` = `htr.c`'s `check`, returning its verdict; the
    caller (`main.c`) prints the hard cases],
)

#code("/code/APaul/htrplan/eval_mpfr.c")

With them, Program 2 is Program 1 again: the test prints the same
candidates and the same hard cases as `htr.c` itself, line for line
(@sec-test).

== The obligations on the exp evaluator <sec-evalobl>

These are what any instance must prove; nothing here depends on how it is
implemented.

#table(
  columns: 2,
  stroke: 0.5pt,
  [*\#*], [*obligation*],
  [E1], [(C1) accuracy: $|h + l + s - exp x| <= 2^(-kappa) exp x$],
  [E2], [(C2) shape: $|l| < 2^(e - 53)$ and $|s| < 2^(e - 54)$, where $e$ is
    the exponent of $exp x$. After scaling, `l` must be in $(-2, 2)$ and `s`
    in $(-1, 1)$ (*read*, `htr.c` lines 110 and 115)],
  [E3], [`expo` returns the exponent of $exp x$ exactly. It is only used to
    check that $exp$ stays in one binade on $[x_0, x_1)$. `htr.c` rounds
    toward zero so that the result never rounds up to the next power of 2],
  [E4], [the check called from `report` never rejects a hard case. It may
    accept a false one, or answer "undecided", which is kept],
)

E4 is there because the theorem is about the printed list, not only the
candidates. If one only wanted the candidates, E4 would not be needed.

*How large must $kappa$ be.* An error of $2^(-kappa)$ relative is about
$2^(54 - kappa)$ on the grid, so it is below one unit of `A` (i.e.
$2^(-64)$) when $kappa >= 118$ (*computed*). With $kappa approx 120$, the
evaluator errors are small next to the drift, which is about $2^48$ units on
$[0.25, 0.25001)$ (*computed* from `htr.c`'s formula). MPFR at 161 bits gives
$kappa approx 158$, much more than needed.

== The obligations on the code of Program 2

These hold for any `eval`, `expo` and `report` that meet E1 to E4.

#table(
  columns: 3,
  stroke: 0.5pt,
  [*\#*], [*obligation*], [*state*],
  [2a], [the conversions to 64 bits: `ldexp`, `get_uint64`, the reduction of
    `l` into $[0, 1)$, the wrap modulo $2^64$], [to do, fiddly],
  [2b], [the window covers target + drift + the errors of E1 and 2a],
    [to do, *the hard point*],
  [2c], [the inner loop reports exactly the $i$ in the window],
    [done: `Scan.v`],
  [2d], [the chunks cover $[x_0, x_1)$], [done at the nat layer: `ScanAll.v`],
)

*On 2b.* `E` is target + drift and nothing else (*read*). Three errors are
not in it: the curvature is taken at the start of the chunk and not its
maximum over the chunk; the two truncations of `B` add up over $n$ steps; and
`A` itself is truncated. Our notes of 2026-08-01 say they fit inside the
margin; this has not been re-checked. The proof decides it. If they do not
fit, the fix is one term added to `E`.

*What the code does not handle.* Being `htr.c`'s search, Program 2 asserts
things that hold on $[0.25, 0.5)$ but not on the whole range (*read*):

- `get_uint64` asserts its argument is in $(-1, 1)$. The slope $Y(x) u$ is
  in $[2^(e_0), 2^(e_0 + 1))$ where $x in [2^(e_0 - 1), 2^(e_0))$, so it
  passes only for $|x| < 1 slash 2$ (*computed*). Only the fractional part of
  the slope matters, so the fix is to drop the integer part first.
- $[x_0, x_1)$ must sit in one binade of $x$ and of $exp x$ (asserted). The
  full range must be cut accordingly: about $2 dot 64$ binades of $x$ and a
  cut every $ln 2$ for $exp x$ (*computed*).
- Near the ends, $exp x$ becomes subnormal (below $x approx -708$) or
  overflows (above $x approx 709.78$). The definition of "hard to round"
  changes for subnormal outputs.
- The last chunk overruns $x_1$; the line `n = (x1 - x) / ux` is never used.
  This is harmless for a superset of $[x_0, x_1)$.

= Program 3: another instantiation of Program 2 <sec-p3>

Program 3 is Program 2 with other parameters: an exponential in integer
arithmetic, with no MPFR. The proof of Program 2 (2a to 2d) is used as it
is. What is left is to prove E1 to E4 for the new parameters.

#table(
  columns: 2,
  stroke: 0.5pt,
  [*parameter*], [*instance*],
  [`eval`], [`eval_fix`: $exp x$ as a fixed-point integer $y$, split into
    three doubles],
  [`expo`], [`expo_fix`: the exponent of $y$],
  [`report`], [`check_fix`: decides a candidate from the same $y$; the caller
    prints the hard and the undecided cases],
)

== The candidate evaluator

*How fast must it be? Not very.* `eval` is called once per chunk. The inner
loop runs about $1.5 dot 10^9$ steps a second (*measured*, one P-core, turbo
off), so a chunk takes about $0.7$ ms (*computed*). An evaluator of
$10 space mu s$ would add $1.4%$ (*computed*). On the full range there are
$2^59 slash 2^20 = 2^39 approx 5.5 dot 10^11$ chunks (*computed*), and the
whole search is about $3.9 dot 10^8$ core-seconds, 12 core-years
(*computed*), whatever the evaluator. So the evaluator is chosen for the
*proof effort*, not for speed.

*Three possible evaluators.*

#table(
  columns: 4,
  stroke: 0.5pt,
  [*evaluator*], [*how*], [*certificates*], [*difficulty*],
  [Tang, fixed point],
    [$x = k ln 2 + j slash 256 + r$; a table of 256 values $exp(j slash 256)$;
     one polynomial for $exp r$, $|r| <= 2^(-9.5)$: degree 10 gives
     $2^(-130)$, degree 13 gives $2^(-169)$ (*computed* from the Taylor
     bound); integers only],
    [1 polynomial, 256 table entries, 1 reduction],
    [3],
  [pieces + section 5],
    [one certified polynomial per piece, like `Cheb.v`; the chunk seeds by
     exact additions (`Shift.v`, `Pdir_exp`)],
    [$6 dot 10^5$ at degree 7, $4 dot 10^3$ at degree 15, for $2^(-100)$
     (*computed*, formula checked at one point)],
    [2 each, but volume],
  [short Taylor near 0],
    [for small $|x|$, $exp x = 1 + x + dots$ with few terms, no table],
    [1 polynomial per binade group], [1–2],
)

*The choice: Tang.* One proof, independent of the range. A different
evaluator may be used where it makes the proof simpler, for instance the
short Taylor series near 0, where no reduction is needed.

*The code*, `eval_fix.c`. It uses GMP's integers (`mpz`) and nothing else: no
MPFR, no floating point beyond reading $x$ and writing $h, l, s$. A
fixed-point number is an integer $Z$ standing for $Z slash 2^P$, with
$P = 200$. The polynomial has degree 13, so that the accuracy is that of
MPFR's 161 bits and the two instances can be compared candidate by
candidate; degree 10 would be enough for $kappa = 120$.

#code("/code/APaul/htrplan/fix.h")

#code("/code/APaul/htrplan/eval_fix.c")

The constants, the 256 values $2^(j slash 256)$ and $ln 2 slash 256$, are in
`fix_table.h`, produced with MPFR by `gen_fix.c`. That producer is not
trusted: each constant is certified in the proof. The coefficients
$1 slash i!$ are computed exactly from integers and need no certificate.

`check_fix` computes the distance $d$ of $Y(x)$ to the nearest integer from
$y$, and answers 1 (hard) when $d + "err" < 2^(-m)$, 0 (not hard) when
$d - "err" >= 2^(-m)$, and 2 (undecided) otherwise.

== The obligations on it

All four rest on one bound, on the fixed-point value $y$ *before* it is split
into doubles. `fix_exp` returns $y$ and $k$ with

$ (E) #h(2em) |y dot 2^(k - P) - exp x| <= "err" dot 2^(k - P), #h(2em)
  "err" = 2^(P - 160), $

where `err` is the constant of the code. From (E):

#table(
  columns: 3,
  stroke: 0.5pt,
  [*\#*], [*obligation*], [*from (E) and*],
  [3a], [E1 and E2 for `eval_fix`],
    [the split of $y$ into $h, l, s$ by `top53` truncates less than
     $2^(-158)$ relative, and each part is below the previous one's last
     bit],
  [3b], [E3 for `expo_fix`], [the second `assert` of `fix_exp`: $y$ is not
    within `err` of a power of 2, so $y$ and $exp x$ have the same exponent],
  [3c], [E4 for `check_fix`: it answers 0 only when $x$ is not hard],
    [the distance computation; answering 1 or 2 wrongly costs nothing],
)

(E) is stated on $y$, not on $h + l + s$. The check reads $y$ directly, so
3c does not suffer from the limit of three doubles below $x = -634$
(@sec-test); 3a does.

== How to prove it

The proof follows the computation of `fix_exp`, one step at a time. Each
step is an integer operation with a floor, and each lemma bounds what it
loses, in units of $2^(-P)$ (the numbers are *computed*, the proof is to
do):

#table(
  columns: 3,
  stroke: 0.5pt,
  [*step*], [*what to prove*], [*how*],
  [$X = x dot 2^P$], [exact], [$x$ is a 53-bit integer times a power of 2;
    the first `assert` in the code guarantees the shift is not negative],
  [$r = X - floor(N L slash 2^32)$], [within 2 units of
    $x - N ln 2 slash 256$], [$L$ is $ln 2 slash 256$ to $P + 32$ bits,
    certified by one `interval` call; $|N| < 2^19$],
  [$|r| < 2^(-9.5)$], [checked at run time], [the `assert` on `rmax`; the
    2 units of slack stay under the bound],
  [Horner], [within a few units of $sum_(i <= 13) r^i slash i!$],
    [one floor per step, each damped by $|r| < 2^(-9.5)$, so about 2 units;
     the $1 slash i!$ are floors of exact integers; the 2 units of $r$ add
     about 2 more],
  [Taylor], [$|exp r - sum_(i <= 13) r^i slash i!| <= 2^(-169)$],
    [one `interval` call over $|r| <= 2^(-9.5)$, like `cheb_valid`, or the
     remainder bound by hand],
  [$times T[j]$], [within 1.5 units], [each $T[j]$ is certified to half a
    unit: 256 `interval` calls at about 250 bits; one floor],
  [sum], [(E)], [$2^(-169)$ + a few units $<= 2^(-160)$, with about 8 bits to
    spare],
)

Then 3a, 3b and 3c are small lemmas on integers: the split into three
53-bit parts, the bit length of $y$, and the distance to the nearest integer.

*In Rocq.* The proof is about a model of `eval_fix.c` over `Z`, with
`Z.shiftr` for the floors, as in `Search.v`. The certificates are
`interval` calls, as in `Cheb.v`. The difficulty is the one of the table
below; the hardest part is the bookkeeping of the reduction.

#table(
  columns: 2,
  stroke: 0.5pt,
  [*part*], [*difficulty*],
  [the Taylor bound on $r$: one `interval` call], [1],
  [the 256 table entries and $ln 2 slash 256$: one interval check each], [1],
  [the reduction, $|k| <= 1075$], [3],
  [the sum of the truncation errors, one per product], [2–3],
  [3a to 3c], [1–2],
)

= The test <sec-test>

`make test` in `code/APaul/htrplan/` runs three programs on the same slice
and compares their output line by line: every candidate, then the hard cases
found.

- `htr_slice`: Program 1, `htr.c` itself, with its interval and $m$ taken
  from the command line by a `sed`;
- `htrp mpfr`: Program 2 with Program 1's functions (@sec-p2);
- `htr3`: Program 2 with Program 3, `check_fix` included. It is linked
  without MPFR, so it cannot call it.

All numbers here are *measured*, 2026-09-28, on this desktop:

#table(
  columns: 4,
  stroke: 0.5pt,
  [*slice*], [*chunks*], [*candidates*], [*result*],
  [$[0.25, 0.25 + 10^4 dot 2^(-34))$], [10 000], [410 325],
    [identical in all three; one hard case, `0x1.00002385331bep-2`, the first
     of `htr.c`'s five; no undecided],
  [$[-0.25 - 10^4 dot 2^(-34), -0.25)$], [10 000], [498 078],
    [identical in all three; one hard case; no undecided],
)

Program 3 was also compared directly with MPFR at 400 bits on ten points
between $-700.3$ and $700.1$: apart from the point below, its relative error
is between $2^(-159)$ and $2^(-188)$ (*measured*). The `h` of the two
evaluators is not always the same (Program 3 truncates where MPFR rounds);
the contract does not ask it to be.

*One limit found by the test.* At $x = -700.3$ the error of $h + l + s$ is
$2^(-66.5)$ for both evaluators (*measured*). There $exp x approx 2^(-1010)$,
so $l$ and $s$ fall below the smallest double and are lost. Three doubles
carry $159$ bits only while $exp x >= 2^(-1074 + 159) = 2^(-915)$, that is
$x >= -634$ (*computed*). Below that the interface of Program 2 must change,
for instance by passing the fixed-point value $y$ instead of three doubles.

= The number of candidates <sec-check>

About 41 per chunk on $[0.25, 0.25001)$ (*measured*: 7 056 503 over 171 799
chunks, `htr.c`'s own comment). The count comes from the width of the window,
$2 E slash 2^64 approx 2^(-14.6)$ per double (*computed*), which is almost all
drift. A smaller $n$ shrinks the drift quadratically and so the candidates,
at the price of more chunks.

= What to do, in order

+ *Program 2, 2a and 2b*, on $[0.25, 0.25001)$, where 2c and 2d are done.
  This settles the hard point, the window, for any evaluator that meets the
  contract.
+ *Generalise the search* to the whole range: the slope above 1, the cuts at
  binades, the subnormal and overflow ends, and an interface that passes $y$
  below $x = -634$.
+ *Program 3*: prove (E), then 3a to 3c, and certify the constants. The code
  is written and tested (@sec-test). Add the short Taylor series near 0 if it
  simplifies things.
+ *The link to the running program.* The proofs above are about a Rocq model
  of the search. Tying them to the code that runs is a separate step; with
  Capla (our port of `htr_plain.c`, `code/APaul/capla/`) the program has a
  formal semantics, but how a Capla program is linked to a Rocq proof has not
  been tried.

#counter(heading).update(0)
#set heading(numbering: "A.1")

= Annex: the initial program <annex-p1>

Program 1 is `code/APaul/htr.c`, by Paul Zimmermann. It is not proved: it is
the reference that Programs 2 and 3 are tested against. It uses MPFR in three
places (*read*):

#table(
  columns: 3,
  stroke: 0.5pt,
  [*function*], [*what it does*], [*becomes in Program 2*],
  [`dd_exp`], [$exp x$ at 161 bits, split into three doubles $h + l + s$],
    [`eval`],
  [`ref_exp`], [$exp$ at both ends, rounded toward zero, to check $e$ is the
    same on the interval], [`expo`],
  [`check`], [decides a candidate, at $53 + m$ bits], [the check in
    `report`],
)

#code("/code/APaul/htr.c")

How Program 2 gives it back is in @sec-p2.
