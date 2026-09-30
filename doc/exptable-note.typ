#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

// The listings are read from the source.  Build from the repository root:
// typst compile --root . doc/exptable-note.typ
#let listing(path) = block(width: 100%, fill: luma(245), inset: 6pt,
  text(size: 7.5pt, raw(read(path), lang: "coq", block: true)))

#align(center)[
  #text(size: 17pt)[*Checking a table for the search of $exp$ in Rocq*]

  #v(0.4em)
  #text(size: 10pt)[What `code/exptable` checks on each line, in the
  notation of `doc/htr.md`]
]

#v(1em)

Paul Zimmermann's search for the hard-to-round cases of $exp$ (`doc/htr.md`)
reads a table with one line per subrange of inputs. This note says what a
line holds, the six conditions under which the search on that line misses no
hard case, and how the Rocq files in `code/exptable/` check them all with one
boolean function whose answer `true` is proved to imply the six conditions.
Section 7 follows the first line of the table through every step, with its
numbers.

= Proof by a checker, for a reader who does not use Rocq

Rocq is a proof assistant: it accepts a theorem only with a proof it can
verify step by step. It is also a programming language, and it can run its
own programs. The files here use both sides:

- `check_table` is a *program*. It reads the table and answers `true` or
  `false`. It uses integers only, plus one call to a function of the
  Interval library that returns two numbers $L <= exp(x) <= U$.
- `check_tableP` is a *theorem* about that program: *if `check_table` answers
  `true` on a table, then every line of the table satisfies the six
  conditions.* It is proved once, for every possible table.
- To prove that `in_lt` satisfies the six conditions, Rocq runs the program
  on it, sees `true`, and applies the theorem.

So one does not need to trust the program, or to read it: the theorem is what
guarantees that it tests the right thing. What one must read is the
statement of the six conditions (section 4), because that is what is proved.
The run itself is done by an evaluator built into Rocq (`vm_compute`, or
`native_compute`, which compiles the program to machine code first).

Two words used below. The *binade* of a positive number $y$ is the interval
$[2^e, 2^(e+1))$ that contains it. An *enclosure* of $y$ is a pair of
numbers $L <= y <= U$, here with $U - L$ tiny compared with $y$.

= The notation of `doc/htr.md`

- $beta = 2^64$ is the machine word basis, $ell$ the number of words of a
  coefficient, so the coefficients are integers modulo $beta^ell$.
- A subrange is $[x_0, x_1]$ with $x_1 = x_0 + n u$, where $u = "ulp"(x)$ is
  the same for all $x$ in $[x_0, x_1]$. The search looks at the $n + 1$
  inputs $x_0 + j u$, $j = 0, dots, n$.
- $v = 1/2 "ulp"(exp x)$, the same for all $x$ in $[x_0, x_1]$: if
  $2^e <= exp x < 2^(e+1)$ then $v = 2^(e - 53)$.
- $a_i = exp(x_0) u^i slash i!$, $0 <= i < k$: the Taylor coefficients, so
  that $exp(x_0 + j u) = a_0 + a_1 j + dots + a_(k-1) j^(k-1) + r$ with
  $|r| <= exp(x_1) (n u)^k slash k!$.
- $A_i$ is an integer with $0 <= A_i < beta^ell$ and
  $|A_i - beta^ell "frac"(a_i slash v)| < 1$.
- $P(j) = A_0 + A_1 j + dots + A_(k-1) j^(k-1)$.
- $m$: an input is hard to round when $exp(x) slash v$ is within $2^(-m)$ of
  an integer. $E$ is the window of the search: $x_0 + j u$ is a candidate
  when $P(j)$ is within $E$ of a multiple of $beta^ell$.

= What a line of the table holds

A line of `in_lt` is $x_0$ (a double, in hexadecimal), then $n$, then $k$
integers $B_0, dots, B_(k-1)$ of $ell$ words each, the least significant word
first:
$ B_i = P(i) mod beta^ell, quad 0 <= i < k. $
This is the output of step 3 of the search in `doc/htr.md`, before the
differences of step 4. It is $P$ at $0, 1, dots, k - 1$, *not* the $A_i$:
only $B_0 = A_0$. For `in_lt`, $k = 8$, $ell = 5$, every $x_0$ is in
$[2^9, 2^10)$ so $u = 2^(-43)$, and there are 67 486 lines. On line 1,
$x_0 = #raw("0x1.4678ea18f304cp+9")$, $n = 7412951889$, $2^942 <= exp x_0 <
2^943$ so $v = 2^889$.

= The six conditions

For one line, the search misses no hard case when:

+ *$u$ is constant:* $x_0$ and $x_1$ are in the same binade $[2^9, 2^10)$;
+ *$v$ is constant:* $exp x_0$ and $exp x_1$ are in the same binade
  $[2^e, 2^(e+1))$;
+ *(H_A):* there are $A_0, dots, A_(k-1)$ with $0 <= A_i < beta^ell$ and
  $|A_i - beta^ell "frac"(a_i slash v)| < 1$, and the line holds
  $B_i = P(i) mod beta^ell$ for $i < k$;
+ *(H_T):* for $0 <= j <= n$,
  $ |exp(x_0 + j u) slash v - (a_0 + a_1 j + dots + a_(k-1) j^(k-1)) slash v|
    <= rho, quad rho = exp(x_1) (n u)^k / (k! v); $
+ *(H_E):* $E >= beta^ell (2^(-m) + rho) + (1 + n + dots + n^(k-1))$;
+ *the window is less than half the modulus:* $2 E < beta^ell$.

Conditions 3 to 6 are the hypotheses of `hscan_exp` in
`code/APaul/rocq/TaylorLink.v` (there $M = beta^ell$, and its $a_i$ is
$a_i slash v$ here). Conditions 1 and 2 make $u$ and $v$ single numbers on
the line, which the other four take for granted. Condition 6 is on the
search, not on a line: it is checked once.

In Rocq, the six conditions are `line_ok` and `table_ok` in `ExpCheck.v`
(annex A). $ell$ appears as `l`, and $x_0 = M_0 u$ with $M_0$ the integer
significand of $x_0$.

= The parameters

They are the first definitions of `ExpCheck.v`, and nothing else in the
files is a number about the table:

```coq
Definition beta : Z := 2 ^ 64.    (* the machine word basis            *)
Definition l : Z := 5.            (* words of an A_i or a B_i          *)
Definition k : nat := 8.          (* terms of the Taylor polynomial    *)
Definition m : Z := 43.           (* identical bits after the round bit *)
Definition E : Z := 2 ^ 278.      (* the window of the search (a guess) *)
Definition xbin : Z := 9.         (* x ranges over [2^xbin, 2^(xbin+1)) *)
Definition guard : Z := 64.       (* extra bits in the exp enclosure   *)
```

$E = 2^278$ is our choice, not a value read from the search: `doc/htr.md`
asks $E >= beta^ell (2^(-43) + 2^(-43.7) + 2^(-91))$, which is below
$2^278$, and line 1 needs $E >= 2^277.59$. The value the search uses must be
put here. `guard` is the number of bits beyond $beta^ell$ and $v$ at which
$exp$ is enclosed; it changes the cost, not the result.

= How one line is checked: `check_line`

`check_line` takes $M_0$, $n$ and $B_0, dots, B_(k-1)$ and computes with
integers only, except for one call to the certified $exp$ of the Interval
library.

+ *Condition 1* is three integer tests: $0 <= n$, $2^52 <= M_0$ and
  $M_0 + n < 2^53$.
+ *Enclosures of $exp$.* `encl` builds the point $M_0 u$ as a float of
  Interval and calls its $exp$ at precision $ell dot 64 + 53 + "guard"$
  bits. The answer is two floats $L_0 <= exp x_0 <= U_0$. The same is done
  at $x_1$: $L_1 <= exp x_1 <= U_1$.
+ *Condition 2.* $e$ is the exponent of $L_0$, so $2^e <= L_0 <= exp x_0$;
  the test is $U_1 < 2^(e+1)$.
+ *Condition 3.* For each $i < k$, $T = beta^ell a_i slash v$ is
  $exp(x_0)$ times the power of two $beta^ell u^i slash v$, divided by $i!$.
  The checker computes, at both ends $L_0$ and $U_0$, the nearest integer
  $R$ of $T$ and the integer part $q$ of $T slash beta^ell$, and requires
  the same $R$ and the same $q$ at both ends. Then they are those of the
  exact $T$, and $A_i = R - q beta^ell$ satisfies $0 <= A_i < beta^ell$ and
  $|A_i - beta^ell "frac"(a_i slash v)| = |R - T| <= 1/2$. Last, it
  computes $P(i) mod beta^ell$ from these $A_i$ and compares with $B_i$.
+ *Condition 4* needs no test: it is a theorem of analysis (the Taylor
  remainder of $exp$, `ExpTaylor.v`).
+ *Condition 5* is one integer inequality, with $exp x_1$ replaced by its
  upper bound $U_1$, which only makes $rho$ larger.

The $A_i$ are not in the table and cannot be read back from it: going from
the $B_i$ to the $A_i$ divides by $i!$, which has no inverse modulo
$beta^ell$. So the checker recomputes them from $exp x_0$ and compares the
$B_i$.

`check_table` tests condition 6, then `check_line` on every line.

= Line 1, step by step

The first line of `in_lt` is (the $B_i$ are shown by their most significant
word only; each has five):

$ x_0 = #raw("0x1.4678ea18f304cp+9") approx 652.94464, quad n = 7412951889, $

#align(center, table(columns: 2, stroke: 0.4pt, inset: 4pt,
  [$B_0$ = `0x3be38424e0f19a8a` ...], [$B_1$ = `0x3be384255a1916fa` ...],
  [$B_2$ = `0x3be384265340936b` ...], [$B_3$ = `0x3be38427cc680fdb` ...],
  [$B_4$ = `0x3be38429c58f8c4c` ...], [$B_5$ = `0x3be3842c3eb708bc` ...],
  [$B_6$ = `0x3be3842f37de852d` ...], [$B_7$ = `0x3be38432b106019d` ...],
))

The numbers below are the checker's own values when it says so; the others
are computed with `check_line.py` (a Python computation with exact integers,
not a proof), and give the orders of magnitude.

*Condition 1: $u$ is constant.* The significand of $x_0$ is
$M_0 = #raw("0x14678ea18f304c") = 5743361827745868$, so $x_0 = M_0 u$ with
$u = 2^(-43)$. Then $x_1 = x_0 + n u$ has significand $M_0 + n =
5743369240697757$, that is $x_1 = #raw("0x1.467905b67db9dp+9") approx
652.94549$. Both significands are between $2^52$ and $2^53$, so $x_0$ and
$x_1$ are in $[2^9, 2^10)$, where $"ulp"(x) = 2^(-43)$.

*Enclosures of $exp$ (checker's values).* Interval's $exp$ at 437 bits
returns, for $x_0$, two numbers $L_0 <= exp(x_0) <= U_0$ of the form
$L_0 = p dot 2^505$ with $p$ an integer of 438 bits, and $U_0 = L_0 +
2^505$: an enclosure of relative width about $2^(-437)$. The same holds at
$x_1$.

*Condition 2: $v$ is constant.* $L_0$ lies in $[2^942, 2^943)$, so
$2^942 <= exp(x_0)$ and $e = 942$; the upper end $U_1$ at $x_1$ is below
$2^943$. So all of $exp(x_0), dots, exp(x_1)$ are in $[2^942, 2^943)$ and
$v = 2^(942 - 53) = 2^889$. (Here $x_0 approx 942 ln 2$: this line starts
exactly where $exp$ enters that binade, $exp(x_0) approx 2^(942.000000)$,
and $exp(x_1) approx 2^(942.0012)$.)

*Condition 3: the $A_i$, then the $B_i$.* For each $i$, the checker forms
$T = beta^ell a_i slash v$ at both ends of the enclosure and finds the same
integer part of $T slash beta^ell$ ($q$ below) and the same nearest integer
$R$ of $T$; then $A_i = R - q beta^ell$. The distance $|R - T|$ is at most
$1 slash 2$, so (H_A) holds.

#align(center, table(columns: 4, align: (center, right, right, left),
  stroke: 0.4pt, inset: 4pt,
  [$i$], [$a_i slash v$], [$q$], [$A_i$, top word],
  [0], [$9.007199255 dot 10^15$], [$9007199254741449$], [`0x3be38424e0f19a8a`],
  [1], [$1024.0000$], [$1024$], [`0x39277c70`],
  [2], [$5.82 dot 10^(-11)$], [0], [`0x40000000`],
  [3], [$2.21 dot 10^(-24)$], [0], [`0x0`],
  [4], [$6.27 dot 10^(-38)$], [0], [`0x0`],
  [5], [$1.43 dot 10^(-51)$], [0], [`0x0`],
  [6], [$2.70 dot 10^(-65)$], [0], [`0x0`],
  [7], [$4.39 dot 10^(-79)$], [0], [`0x0`],
))

From the fourth on, $a_i slash v$ is below $2^(-64)$, so the top word of
$A_i$ is 0 and only the lower words are nonzero. The checker then computes
$P(0), dots, P(7)$ modulo $beta^ell$ from these $A_i$ and finds exactly the
eight $B_i$ of the line. Only $B_0 = P(0) = A_0$. The other $A_i$ are small
next to $A_0$ (the top word of $A_1$ is below $2^30$, that of $A_2$ is
$2^30$, the others are 0), so $P(i) = A_0 + A_1 i + dots$ changes only the
low half of the top word: this is why the eight top words look alike.

*Condition 4: (H_T).* Nothing to compute: the Taylor theorem gives the
bound, with
$ rho = exp(x_1) (n u)^k / (k! v) approx 2^(-44.00). $

*Condition 5: (H_E).* The three terms of the window are
$beta^ell 2^(-m) = 2^277$, $beta^ell rho approx 2^276.00$ and
$1 + n + dots + n^7 approx 2^229.51$, a total of about $2^277.59$. The
checker bounds $rho$ from above with $U_1$ and verifies that the total is at
most $E = 2^278$.

*Condition 6* is on the whole table: $2 E = 2^279 < beta^ell = 2^320$.

On this line `check_line` answers `true`; the line then satisfies the six
conditions, by the theorem.

= The theorem

```coq
Theorem check_tableP t : check_table t = true -> table_ok t.
```

It is proved once, in `ExpProof.v` (annex B), from four files:

- `ExpEncl.v`: what `encl` returns does enclose $exp$, from the correctness
  theorem `I.exp_correct` of Interval;
- `ExpArith.v`: each integer test of the checker, read in the real numbers;
- `ExpTaylor.v`: the Taylor remainder, condition 4.

No lemma is admitted. The theorem rests on the axioms of Rocq's real
numbers (`sig_forall_dec`, `sig_not_dec`), functional extensionality and the
excluded middle (`classic`), which the libraries bring in, and on the
declarations of the primitive 63-bit integers that the Interval library
computes with.

A table is then checked by one computation: `ExpRun.v` proves
`table_ok table` by `apply check_tableP` and evaluating `check_table table`
to `true`.

= Running it

`gen.py in_lt FIRST COUNT K L ExpData.v` writes lines $"FIRST" + 1$ to
$"FIRST" + "COUNT"$ of `in_lt` as the Rocq list `table` (it only parses; $K$
and $L$ must be `k` and `l`). `make` builds the files and `ExpRun.v`.

The table is in the repository as `code/exptable/in_lt.xz`; `xz -dk
in_lt.xz` gives `in_lt`, and `sha256sum -c in_lt.sha256` checks it.

The whole table is checked in slices. `mkslices.sh in_lt 15` cuts it into
15 slices of 4 500 lines. `ExpData00.v` to `ExpData14.v` hold the lines
*verbatim*, as primitive strings (`genraw.py`); the Rocq function `parse`
(`ExpParse.v`) reads each one into $(M_0, n, B)$ during the evaluation. For
each slice, `ExpRunNN.v` proves that `check_raw`, which parses every line
and runs `check_line` on it, answers `true`, with `native_compute`. These
files use `ExpCheck.v` and `ExpParse.v` only, so the proofs can change
without running them again. `make -j15 slices` runs them in parallel;
`make all-slices` then builds `ExpAll.v`: every line of every slice reads
as a line that satisfies the six conditions (`check_rawP`).

The text form matters for the cost. Measured on 300 lines on the desktop,
Rocq reads the lines as strings in 0.5 s (168 MB), but the same numbers
written as decimal integers in 55 s (1.1 GB), and in hexadecimal in 28 s:
building each 320-bit number as a Rocq term is what is slow. The check of
the 300 lines then takes 21.5 s with `native_compute`.

Measured on the first 10 lines, on the desktop: `check_table` evaluates to
`true` in 2.48 s with `vm_compute`, and in 0.75 s with `native_compute` once
the code is compiled (1.50 s the first time). That is 0.25 s and 0.075 s a
line. At 0.075 s a line, the 67 486 lines would take about 1.4 h on one core
(scaled, not measured). Changing one bit of a $B_i$, moving $x_0$ by one
ulp, or doubling $n$ makes `check_line` answer `false` on line 1.

`check_line.py` computes the same six conditions for one line in Python, with
its own integer $exp$ at 1200 bits. It is a reference, not a proof; it
agrees with the Rocq checker on the first 10 lines.

= What is not checked

- That the lines cover the whole range: each line is checked alone, and
  nothing relates $x_0$ of a line to $x_1$ of the previous one.
- The value of $E$ that the search actually uses (see the parameters).
- The search itself: that is `TaylorLink.v`, which this check feeds.

#pagebreak()
#counter(heading).update(0)
#set heading(numbering: "A.1")

= `ExpCheck.v`
#listing("../code/exptable/ExpCheck.v")

= `ExpProof.v`
#listing("../code/exptable/ExpProof.v")

= `ExpEncl.v`
#listing("../code/exptable/ExpEncl.v")

= `ExpArith.v`
#listing("../code/exptable/ExpArith.v")

= `ExpTaylor.v`
#listing("../code/exptable/ExpTaylor.v")
