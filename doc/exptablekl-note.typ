#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

// The listings are read from the source.  Build from the repository root:
// typst compile --root . doc/exptablekl-note.typ
#let listing(path) = block(width: 100%, fill: luma(245), inset: 6pt,
  text(size: 7.5pt, raw(read(path), lang: "coq", block: true)))

#align(center)[
  #text(size: 17pt)[*Checking the tables for the search of $exp$,
  with $k$ and $ell$ on each line*]

  #v(0.4em)
  #text(size: 10pt)[What `code/exptablekl` checks on each line, in the
  notation of `doc/htr.md`]
]

#v(1em)

Paul Zimmermann's search for the hard-to-round cases of $exp$
(`doc/htr.md`) reads tables with one line per subrange of inputs. This note
is about his tables for every binary64 input, where each line gives its own
number of terms $k$ of the Taylor polynomial and its own number of words
$ell$ of the coefficients. It says what the tables hold, the six conditions
under which the search misses no hard case on a line, and how the Rocq
files in `code/exptablekl/` check them with one boolean function whose
answer `true` is proved to imply the six conditions. The note is complete
by itself.

= Summary

- *Each line has its own $k$ and $ell$*, with $1 <= k <= 13$ and
  $1 <= ell <= 8$. In the archive each file has a single pair, and there
  are 12 pairs, from $(2, 2)$ for the tiny inputs to $(13, 8)$ for the
  largest ones (section 3).
- *The tables are half-open.* A line $(x_0, n, k, ell, B)$ is searched at
  $x_0 + j u$ for $j = 0, dots, n - 1$, as the search program does
  (`for (i = 0; i < N; i++)`); the checker has `closed` = `false`.
- *$E$ is the window of the search program*: `ERR = 0x600000` on the top
  word, so for a line of $ell$ words
  $E = #raw("0x600000") dot 2^(64(ell - 1)) = beta^ell dot 3 dot 2^(-43)$
  (section 6).
- *The whole archive passes.* All 2 203 files, 2 931 305 lines. Rocq proves
  that every line satisfies the six conditions, and that the lines cover
  every input from $x approx -745.133$ to $-2^(-53)$ and from $2^(-53)$ to
  $x approx 709.783$ (section 12). No line fails. The run took 256 min on
  `roquableu` (section 11).
- *The bit-flip test passes* (section 11): changing one bit of any
  coefficient $B_i$, or moving $x_0$, makes the check fail.
- *Not covered:* the inputs $-2^(-53) < x < 2^(-53)$, in no table
  (section 12).

= Proof by a checker, for a reader who does not use Rocq

Rocq is a proof assistant: it accepts a theorem only with a proof it can
verify step by step. It is also a programming language, and it can run its
own programs. The files here use both sides:

- `check_raw` is a *program*. It reads lines of a table, as text, and
  answers `true` or `false`. It uses integers only, plus one function of
  the Interval library that returns two numbers $L <= exp(x) <= U$.
- `check_rawP` is a *theorem* about that program: *if `check_raw` answers
  `true`, then every line satisfies the six conditions.* It is proved once,
  for every possible table.
- To prove that a table file satisfies the six conditions, Rocq runs the
  program on it, sees `true`, and applies the theorem.

So one does not need to trust the program, or to read it: what one must
read is the statement of the six conditions (section 5). The run is done
by the evaluator `native_compute`, which compiles the program to machine
code.

Two words used below. The *binade* of a positive number $y$ is the
interval $[2^e, 2^(e+1))$ that contains it. An *enclosure* of $y$ is a pair
of numbers $L <= y <= U$, here with $U - L$ tiny compared with $y$.

= The tables

The archive `all.tar.bz2` holds 2 203 files and 2 931 305 lines. The file
`in`$e$ is for the inputs $x$ with $exp(x)$ in $[2^(e-1), 2^e)$: from
`in1024`, where $exp(x)$ reaches the largest double, down to `in-1074`,
where $exp(x)$ is below the smallest positive subnormal double; around
$x = 0$, where the subranges are short, the binades are split into several
files (`in0-0`, `in0-1`, ...).

A line is $x_0$ (a double, in hexadecimal), then $n$, $k$ and $ell$ in
decimal, then $k$ integers $B_0, dots, B_(k-1)$ of $ell$ words of 64 bits
each, the least significant word first: $4 + k ell$ fields. For instance,
the first line of `in2` starts

#align(center)[`0x1.62e42fefa39fp-1 274877906945 7 5 0x6ac68b078499736f 0x6a7474e20960ac6b ...`]

with $k = 7$ and $ell = 5$, so 35 words follow.

The pairs $(k, ell)$ depend on the size of the inputs: small $|x|$ have
long subranges searched with few terms, large $|x|$ short subranges with
many. Over the whole archive (all measured with Python on the files):

#align(center, table(columns: 5, align: (center, right, right, center, right),
  stroke: 0.4pt, inset: 4pt,
  [$(k, ell)$], [files], [lines], [$|x_0|$ from .. to], [lines per file],
  [$(2, 2)$], [40], [655 380], [$2^(-53)$ .. $2^(-33)$], [16 384 -- 16 385],
  [$(3, 2)$], [32], [524 304], [$2^(-33)$ .. $2^(-17)$], [16 384 -- 16 385],
  [$(4, 3)$], [16], [262 152], [$2^(-17)$ .. $2^(-9)$], [16 384 -- 16 385],
  [$(5, 4)$], [10], [163 845], [$2^(-9)$ .. $2^(-4)$], [16 384 -- 16 385],
  [$(6, 4)$], [9], [130 514], [$2^(-4)$ .. $1.386$], [6 330 -- 19 547],
  [$(7, 5)$], [8], [65 588], [$0.693$ .. $4.159$], [5 075 -- 16 385],
  [$(8, 5)$], [36], [69 919], [$3.466$ .. $16.64$], [873 -- 5 028],
  [$(9, 6)$], [138], [79 628], [$15.94$ .. $64.46$], [512 -- 769],
  [$(10, 7)$], [184], [94 210], [$63.77$ .. $128.2$], [512 -- 513],
  [$(11, 7)$], [370], [189 442], [$127.5$ .. $256.5$], [512 -- 513],
  [$(12, 8)$], [738], [377 858], [$255.8$ .. $512.2$], [512 -- 513],
  [$(13, 8)$], [622], [318 465], [$511.5$ .. $745.1$], [512 -- 513],
  [all], [2 203], [2 931 305], [], [],
))

The ranges of $|x_0|$ overlap at the ends because a file is a binade of
$exp(x)$, not of $x$. Also:

- $x_0$ is always a normal double, positive or negative (1 480 391 lines
  are negative), with $|x_0|$ from $2^(-53)$ to $745.14$;
- 115 lines have no fraction digits, like `-0x1p-40`; every line has
  $n >= 1$, and $n$ goes from 1 to $2^38 + 1$;
- no subrange $[x_0, x_1]$ leaves the binade of $x_0$.

= The notation

- $beta = 2^64$ is the word basis, $ell$ the number of words of a
  coefficient, $k$ the number of terms; both are read on the line.
- A subrange goes from $x_0$ to $x_1 = x_0 + n u$, where $u = "ulp"(x)$ is
  the same for all $x$ in it. The parameter `closed` (section 6) says
  whether $x_1$ is in it. With $d = 0$ when `closed` is `true` and $d = 1$
  when it is `false`, the search looks at the inputs $x_0 + j u$,
  $j = 0, dots, n - d$: the subrange is $[x_0, x_1]$ ($n + 1$ inputs) or
  $[x_0, x_1)$ ($n$ inputs). The last input is
  $ x_l = x_0 + (n - d) u = S_L u, quad S_L = S_0 + n - d. $
  The tables are half-open: `closed` is `false`, $d = 1$ and
  $x_l = x_1 - u$.
- $x_0$ is a normal double: if $e_x$ is its exponent,
  $2^(e_x) <= |x_0| < 2^(e_x + 1)$, then $u = "ulp"(x_0) = 2^(e_x - 52)$,
  and
  $ S_0 = x_0 / u $
  is an integer, the significand of $x_0$ with its sign:
  $x_0 = S_0 u$, $2^52 <= |S_0| < 2^53$, and $S_0 < 0$ when $x_0 < 0$. The
  inputs are $x_0 + j u = (S_0 + j) u$. Both $e_x$ and $S_0$ are read from
  the text of the line (for `-0x1.74910d52d3051p+9`, $e_x = 9$ and
  $S_0 = -#raw("0x174910d52d3051")$). The search always goes upwards:
  $u > 0$ and $x_l >= x_0$, also when $x_0$ is negative, where it goes
  towards 0 ($|S_0 + j|$ decreases). Condition 1 checks it on every line:
  $S_0$ and $S_L$ have the same sign and both have 53 bits.
- $v = 1/2 "ulp"(exp x)$, the same for all $x$ in $[x_0, x_l]$. If
  $2^e <= exp(x) < 2^(e+1)$ with $e >= -1022$, the doubles near $exp(x)$
  are the multiples of $2^(e - 52)$, and $v = 2^(e - 53)$. Below
  $2^(-1021)$, the subnormal doubles and those of the smallest normal
  binade are all multiples of $2^(-1074)$: there $v = 2^(-1075)$ whatever
  $e$. Both cases are
  $ v = 2^(max(e, -1022) - 53). $
- $a_i = exp(x_0) u^i slash i!$, $0 <= i < k$, the Taylor coefficients.
- $A_i$ is an integer with $0 <= A_i < beta^ell$ and
  $|A_i - beta^ell "frac"(a_i slash v)| < 1$, and
  $P(j) = A_0 + A_1 j + dots + A_(k-1) j^(k-1)$.
- A line holds $B_i = P(i) mod beta^ell$ for $i < k$: the values of $P$ at
  $0, dots, k-1$, not the $A_i$ (step 3 of the search of `doc/htr.md`).
- $m = 43$: an input is hard to round when $exp(x) slash v$ is within
  $2^(-m)$ of an integer. $E$ is the window of the search.

= The six conditions

For one line, the search misses no hard case when:

+ *$u$ is constant:* $d <= n$ (so a line has at least one input), and
  $S_0$ and $S_L$ have the same sign and absolute values in
  $[2^52, 2^53)$, so every $x_0 + j u$ has exponent $e_x$;
+ *$v$ is constant:* $2^e <= exp(x_0)$ and
  $exp(x_l) < 2^(max(e, -1022) + 1)$, so $v = 2^(max(e, -1022) - 53)$
  fits every $exp(x)$ of the subrange;
+ *(H_A):* there are $A_0, dots, A_(k-1)$ with $0 <= A_i < beta^ell$ and
  $|A_i - beta^ell "frac"(a_i slash v)| < 1$, and the line holds
  $B_i = P(i) mod beta^ell$ for $i < k$;
+ *(H_T):* for $0 <= j <= n - d$,
  $ |exp(x_0 + j u) slash v - (a_0 + a_1 j + dots + a_(k-1) j^(k-1)) slash v|
    <= rho, quad rho = exp(x_l) (n u)^k / (k! v); $
  the power is $(n u)^k$, not $((n - d) u)^k$: it bounds $(j u)^k$ for
  every $j <= n$;
+ *(H_E):* $E >= beta^ell (2^(-m) + rho) + (1 + n + dots + n^(k-1))$;
+ *$k$ and $ell$ fit the search, and the window is less than half the
  modulus:* $1 <= k <= 13$, $1 <= ell <= 8$ and $2 E < beta^ell$.

Conditions 3 to 6 are the hypotheses of `hscan_exp` in
`code/APaul/rocq/TaylorLink.v`, which says the search then misses no
$x_0 + j u$ with $exp(x_0 + j u) slash v$ within $2^(-m)$ of an integer.
The bounds on $k$ and $ell$ are the sizes of the arrays of the search
program. In Rocq, the six conditions are `line_ok S0 ex n k l B` in
`ExpCheck.v` (annex A).

= The parameters, and the value of $E$

They are the first definitions of `ExpCheck.v`:

```coq
Definition beta : Z := 2 ^ 64.    (* the machine word basis            *)
Definition kmax : nat := 13.      (* the most terms k of a line        *)
Definition lmax : Z := 8.         (* the most words l of a line        *)
Definition m : Z := 43.           (* identical bits after the round bit *)
Definition ERR : Z := 0x600000.   (* the window, on the top word       *)
Definition guard : Z := 64.       (* extra bits in the exp enclosure   *)
Definition closed : bool := false. (* true: j = 0..n; false: j = 0..n-1 *)

Definition E (l : Z) : Z := ERR * beta ^ (l - 1).
```

`closed` says which inputs a line holds (section 4); everything else is
derived from it: `drop` is $d$, and the checker and the coverage both use
the last input $S_L = S_0 + n - d$. The tables are checked with `closed` =
`false`.

$E$ is not in the tables: it is a constant of the search program,
`code/APaul/capla/htr3/run/htr.c`, the same for every line:

```c
static uint64_t ERR = 0x600000; // ceil(2^64*(3*2^-43))
B[0][l-1] += ERR;
```

`ERR` is added to the top word of $B_0$, so
$E = #raw("0x600000") dot 2^(64(ell - 1)) = beta^ell dot 3 dot 2^(-43)$:
three terms of $2^(-43)$, for the target, the Taylor term and the rounding
of the $A_i$. The tables are made for it. For each pair, the two error
terms of condition 5, divided by $beta^ell$, reach at most (computed with
Python from $n$, $k$, $ell$ and $e_x$ alone, bounding
$exp(x_l) slash v < 2^54$):

#align(center, table(columns: 3, align: (center, right, right),
  stroke: 0.4pt, inset: 4pt,
  [$(k, ell)$], [$(1 + n + dots + n^(k-1)) beta^(-ell)$], [$rho <= 2^54 (n u)^k slash k!$],
  [$(2, 2)$], [$2^(-90.00)$], [$2^(-43.00)$],
  [$(3, 2)$], [$2^(-52.00)$], [$2^(-44.58)$],
  [$(4, 3)$], [$2^(-78.00)$], [$2^(-46.58)$],
  [$(5, 4)$], [$2^(-104.00)$], [$2^(-47.91)$],
  [$(6, 4)$], [$2^(-66.00)$], [$2^(-43.00)$],
  [$(7, 5)$], [$2^(-92.00)$], [$2^(-43.00)$],
  [$(8, 5)$], [$2^(-54.00)$], [$2^(-43.00)$],
  [$(9, 6)$], [$2^(-80.00)$], [$2^(-46.50)$],
  [$(10, 7)$], [$2^(-116.03)$], [$2^(-55.72)$],
  [$(11, 7)$], [$2^(-85.93)$], [$2^(-67.98)$],
  [$(12, 8)$], [$2^(-128.29)$], [$2^(-80.41)$],
  [$(13, 8)$], [$2^(-101.57)$], [$2^(-92.91)$],
))

Neither term goes above $2^(-43)$. The Taylor term reaches it for four
pairs; the sum term stays far below it: the choice of $ell$ leaves room.
Condition 5 is checked on every line, with the $E$ of its $ell$.

= How one line is checked: `check_line`

`check_raw` reads a line with `parse` into $(S_0, e_x, n, k, ell, B)$, then
runs `check_line`, with integers only, except for two calls to the
certified $exp$ of the Interval library.

+ *Condition 6, and condition 1:* integer tests on $k$, $ell$, $n$,
  $|S_0|$, $|S_L|$ and the sign of $S_0 S_L$. The test $2 E < beta^ell$ is
  proved for every $ell >= 1$ (`E_lt`), so it needs no run.
+ *Enclosures.* `encl` builds the double $S_0 2^(e_x - 52)$ as a float of
  Interval and calls its $exp$ at $64 ell + 53 + 64$ bits (629 bits for
  $ell = 8$): $L_0 <= exp(x_0) <= U_0$, and the same at $x_l$:
  $L_1 <= exp(x_l) <= U_1$.
+ *Condition 2.* $e$ is the exponent of $L_0$; the test is
  $U_1 < 2^(max(e, -1022) + 1)$.
+ *Condition 3.* For each $i$, $T = beta^ell a_i slash v$ is $exp(x_0)$
  times a power of two, divided by $i!$. At both ends of the enclosure the
  checker computes the nearest integer $R$ of $T$ and the integer part $q$
  of $T slash beta^ell$, and requires them equal; then
  $A_i = R - q beta^ell$ is within $1 slash 2$ of
  $beta^ell "frac"(a_i slash v)$. It computes $P(0), dots, P(k-1)$ modulo
  $beta^ell$ and compares them with the $B_i$. The factorials are binary
  integers (`factZ`): $13!$ is too big for Rocq's unary numbers.
+ *Condition 4* needs no test: it is the Taylor theorem (`ExpTaylor.v`).
+ *Condition 5* is one integer inequality, with $exp(x_l)$ replaced by
  $U_1$.

= Three lines

The first line of three files: the largest inputs, inputs near $1$, and
subnormal outputs. The rows $S_0$ to the enclosure, and the last one, are
the checker's own values; $x_0$ in decimal and the window terms are
computed with Python.

#align(center, table(columns: 4, align: (left, right, right, right),
  stroke: 0.4pt, inset: 4pt,
  [], [`in1024`], [`in2`], [`in-1074`],
  [$x_0$], [$709.089566$], [$0.693147$ ($ln 2$)], [$-745.133219$],
  [$S_0$], [$6237217781087073$], [$6243314768165360$], [$-6554261109157969$],
  [$e_x$, $u$], [$9$, $2^(-43)$], [$-1$, $2^(-53)$], [$9$, $2^(-43)$],
  [$n$], [$11908177889$], [$274877906945$], [$11908177889$],
  [$k$, $ell$], [$13$, $8$], [$7$, $5$], [$13$, $8$],
  [$e$], [$1023$], [$1$], [$-1075$],
  [$v$], [$2^970$], [$2^(-52)$], [$2^(-1075)$],
  [enclosure of $exp(x_0)$], [630 bits, width 1], [438 bits, width 2], [648 bits, width 265073],
  [$rho$], [$2^(-103.41)$], [$2^(-64.30)$], [$2^(-156.41)$],
  [$1 + dots + n^(k-1)$], [$2^401.65$], [$2^228.00$], [$2^401.65$],
  [window needed], [$2^469.0000$], [$2^277.0000$], [$2^469.0000$],
  [$E$], [$2^470.585$], [$2^278.585$], [$2^470.585$],
  [`check_raw`], [`true`], [`true`], [`true`],
))

The enclosure is $L_0 = p dot 2^f$ with $p$ of the number of bits shown,
and $U_0 = L_0 + w dot 2^f$ with $w$ the width shown. The window needed
is the right-hand side of condition 5. In all three it is the target term
$beta^ell 2^(-43)$ that counts ($2^469$ for $ell = 8$, $2^277$ for
$ell = 5$); the Taylor term and the sum are far below it, and
$E = 3 beta^ell 2^(-43)$ leaves a factor of 3.

= Line 1 of `in-1074`, step by step

The first line of `in-1074` is (the $B_i$ are shown by their most
significant word only; each has eight):

$ x_0 = #raw("-0x1.74910d52d3051p+9") approx -745.133219, quad n = 11908177889, quad k = 13, quad ell = 8, $

#align(center, table(columns: 4, stroke: 0.4pt, inset: 4pt,
  [$B_0$ = `0x1bec60` ...], [$B_1$ = `0x3bec60` ...], [$B_2$ = `0x5bec60` ...], [$B_3$ = `0x7bec60` ...],
  [$B_4$ = `0x9bec60` ...], [$B_5$ = `0xbbec60` ...], [$B_6$ = `0xdbec60` ...], [$B_7$ = `0xfbec60` ...],
  [$B_8$ = `0x11bec60` ...], [$B_9$ = `0x13bec60` ...], [$B_10$ = `0x15bec60` ...], [$B_11$ = `0x17bec60` ...],
  [$B_12$ = `0x19bec60` ...], [], [], [],
))

Here $x$ is negative and $exp(x)$ is below the smallest positive double.
The run of section 11 checks this line as it checks all the others:
`check_raw` reads the text with `parse`, then gives the numbers to
`check_line`. The numbers below are the checker's own values when it says
so; the others are computed with an integer $exp$ at 3000 bits (Python,
not a proof).

*Reading the line.* `parse` finds the sign `-`, the fraction digits
`74910d52d3051`, the exponent `+9`, then $n = 11908177889$, $k = 13$ and
$ell = 8$ in decimal, checks $1 <= k <= 13$ and $1 <= ell <= 8$, and reads
the $13 dot 8 = 104$ words `0x...`, grouped by eight, the least significant
first, into $B_0, dots, B_12$ (section 10 states and proves this reading).
So $S_0 = -(16^13 + #raw("0x74910d52d3051")) = -6554261109157969$ and
$e_x = 9$.

*Condition 1: $u$ is constant.* $u = 2^(9 - 52) = 2^(-43)$. The inputs are
$(S_0 + j) 2^(-43)$ for $j = 0, dots, n - 1$ (the tables are half-open),
from $x_0 approx -745.133219$ to the last input
$x_l = (S_0 + n - 1) 2^(-43) approx -745.131865$, with
$S_0 + n - 1 = -6554249200980081$. Both significands are negative with
absolute values in $[2^52, 2^53)$, so every input has exponent 9: the
search walks towards 0 without leaving the binade $(-2^10, -2^9]$.

*Enclosures of $exp$ (checker's values).* Interval's $exp$ at 629 bits
($beta^ell$, 512 bits, plus 53, plus `guard` = 64) returns, for $x_0$,
$L_0 = p_0 dot 2^(-1722)$ with $p_0$ an integer of 648 bits and
$U_0 = L_0 + 265073 dot 2^(-1722)$, a relative width of about $2^(-629)$;
at $x_l$, $L_1 = p_1 dot 2^(-1722)$, $p_1$ of 648 bits, and
$U_1 = L_1 + 395554 dot 2^(-1722)$.

*Condition 2: $v$ is constant.* $L_0$ is in $[2^(-1075), 2^(-1074))$, so
$e = -1075$ (checker's value): $exp(x_0)$ is below the smallest normal
double $2^(-1022)$, and $v = 2^(max(-1075, -1022) - 53) = 2^(-1075)$, half
the distance $2^(-1074)$ between two subnormal doubles. The test is
$U_1 < 2^(-1022 + 1)$; in fact $U_1 < 2^(-1074)$, so every $exp(x)$ of the
line stays in $[2^(-1075), 2^(-1074))$: between 0 and the smallest positive
double, $exp(x) slash v$ goes from $1$ to $exp(x_1) slash v approx
1.001355$.

*Condition 3: the $A_i$, then the $B_i$.* For each $i$ the checker forms
$T = beta^ell a_i slash v$ at both ends of the enclosure, finds the same
integer part $q$ of $T slash beta^ell$ and the same nearest integer $R$ of
$T$, and takes $A_i = R - q beta^ell$:

#align(center, table(columns: 4, align: (center, right, right, left),
  stroke: 0.4pt, inset: 4pt,
  [$i$], [$a_i slash v$], [$q$], [$A_i$, top word],
  [0], [$1 + 2^(-43.20)$], [1], [`0x1bec60`],
  [1], [$1.14 dot 10^(-13) approx 2^(-43)$], [0], [`0x200000`],
  [2], [$6.46 dot 10^(-27) approx 2^(-87)$], [0], [`0x0`],
  [3], [$2.45 dot 10^(-40)$], [0], [`0x0`],
  [4 .. 12], [from $6.96 dot 10^(-54)$ to $9.73 dot 10^(-165)$], [0], [`0x0`],
))

The top words of the $A_i$ are the checker's; the other columns are
Python's. Here $a_i slash v = (a_0 slash v) 2^(-43 i) slash i!$, and only
$A_0$ and $A_1$ reach the top word. The checker then computes
$P(0), dots, P(12)$ modulo $beta^ell$ and finds exactly the thirteen $B_i$
of the line (checker's value `true`): on the top word,
$P(i) = A_0 + i A_1 + dots$ is `0x1bec60` $+ i dot$ `0x200000`, which is
the column of top words above.

Note $a_0 slash v = exp(x_0) slash v = 1 + 2^(-43.20)$: $exp(x_0)$ is
within $2^(-43)$ of $v = 2^(-1075)$, the midpoint between 0 and the
smallest positive double. So $x_0$ itself is a candidate of the search
($j = 0$). This is expected: the file starts at the first double whose
$exp$ is at least $2^(-1075)$, and one step $u$ of $x$ moves $exp(x)$ by a
relative $2^(-43)$.

*Condition 4: (H_T).* The Taylor theorem gives the bound, with
$ rho = exp(x_l) (n u)^13 / (13! v) approx 2^(-156.41), $
tiny, because $exp(x_l) slash v$ is only about 1 here, where it is about
$2^53$ for a normal output.

*Condition 5: (H_E).* The three terms of the window are
$beta^ell 2^(-43) = 2^469$, $beta^ell rho approx 2^355.59$ and
$1 + n + dots + n^12 approx 2^401.65$: about $2^469.0000$ in all. The
checker replaces $exp(x_l)$ by $U_1 = q_1 dot 2^(-1722)$, with
$q_1 = p_1 + 395554$, and tests one integer inequality (`window_ok`). With
$beta^ell rho <= q_1 n^13 2^g slash 13!$ where
$g = -1722 + 512 - 43 dot 13 - (-1075) = -694$ (checker's value), and
$C = 2^469 + (1 + n + dots + n^12)$, it tests
$ q_1 n^13 + C dot 13! dot 2^694 <= E dot 13! dot 2^694, $
the window condition multiplied by $13! dot 2^694$, with
$E = #raw("0x600000") dot 2^448$ (checker's value `true`).

*Condition 6:* $k = 13 <= 13$, $ell = 8 <= 8$, and
$2 E = #raw("0xc00000") dot 2^448 < beta^8 = 2^512$.

On this line `check_line` answers `true`; the line then satisfies the six
conditions, by the theorem.

= The theorems

```coq
Theorem check_rawP ls : check_raw ls = true ->
  forall s, In s ls -> exists S0 ex n k l B,
    parse s = Some (S0, ex, n, k, l, B) /\ line_ok S0 ex n k l B.

Theorem parse_sound s S0 ex n k l B :
  parse s = Some (S0, ex, n, k, l, B) ->
  line_text (to_list s) S0 ex n k l B.
```

`line_text` (`ExpParseSpec.v`, annex D) says in plain definitions what the
text of a line means: an optional `-`, `0x1`, an optional `.` followed by
0 to 13 hexadecimal digits $F$ of value $f$, `p`, a signed decimal
exponent $e_x$, then $n$, $k$ and $ell$ in decimal, then the $k ell$ words
`0x...`; and
$S_0 = plus.minus (16^13 + f dot 16^(13 - |F|))$,
$B_i = w_(i ell) + w_(i ell + 1) beta + dots + w_(i ell + ell - 1)
beta^(ell - 1)$.

For each table file `in`$e$ given to `mksample.sh`, the generated file
`SampleAll.v` proves

```coq
Lemma lines_ok_N : forall s, In s Data_N.lines ->
  exists S0 ex n k l B,
    line_text (to_list s) S0 ex n k l B /\ line_ok S0 ex n k l B.
```

(`N` is the file name, with `in-1074` written `inm1074` and `in0-0`
written `in0_0`): *every line of the file, read as its text says, satisfies
the six conditions.* No lemma is admitted; the theorems rest on the axioms
of Rocq's real numbers, functional extensionality, the excluded middle, and
the primitive integers and strings.

`ExpHard.v` gives the words of the search a meaning on their own: `hard x`
says that $exp(x) slash v$ is within $2^(-43)$ of an integer, with $v$
half an ulp of $exp(x)$, and `vof_line` says that this $v$ is the $v$ of
condition 2 for every $x$ of the line. The proofs of the search program,
in Capla and in VST (`code/APaul/capla/htr3`, `code/APaul/vst`), state
their final theorems with it.

= The sample, and running it

`sample.tar.xz` holds the first 5 lines of 13 files, 65 lines, with every
pair $(k, ell)$ of the archive: `in0-40` $(2, 2)$, `in0-20` $(3, 2)$,
`in0-10` $(4, 3)$, `in0-4` $(5, 4)$, `in0-0` $(6, 4)$, `in2` $(7, 5)$,
`in-10` $(8, 5)$, `in24` $(9, 6)$, `in100` $(10, 7)$, `in-185`
$(11, 7)$, `in370` $(12, 8)$, `in1024` and `in-1074` $(13, 8)$.

```
mkdir -p sample; tar xJf sample.tar.xz -C sample
./mksample.sh sample/in*
make -j1 sample           # one Run_N.v per file, native_compute
make -j1 sample-all       # SampleAll.v and AllCover.v
```

`Run_N.v` depends on `ExpCheck.v` and `ExpParse.v` only, so the proofs can
change without running the tables again.

*The whole archive.* It is in the repository as thirteen parts,
`archive/tables0.tar.bz2` to `tables12.tar.bz2` (under 100 MB each), which
together hold exactly the files of Paul's archive, checked against
`archive/SHA256SUMS`; `archive/INDEX` gives the part of each file.
`./fullrun.sh 20` unpacks them, writes `Data_N.v`, `Run_N.v` and
`Cover_N.v` for each file, runs them with 20 workers, and builds
`SampleAll.v` and `AllCover.v`. It was run on `roquableu` (an Intel Xeon
E5-2667 server, 12 cores, 24 threads); all measured:

#align(center, table(columns: 2, align: (left, right),
  stroke: 0.4pt, inset: 4pt,
  [files, lines], [2 203, 2 931 305],
  [wall time, all of `fullrun.sh 20`], [256 min 4 s],
  [processor time (user + system)], [4 631 min + 111 min],
  [`Run_N.vo` built], [2 203],
  [exit status], [0],
))

`fullrun.sh` stops at the first failure (`set -e`), so exit status 0 means
that every `Run_N.v` and `Cover_N.v` passes, and that `SampleAll.v` and
`AllCover.v` are built: the theorems of sections 10 and 12 hold for the
whole archive.

*The bit-flip test* (`ExpMutate.v`, `make test`) makes sure every
coefficient and $x_0$ is really checked. On the first line of `in0-40`
$(2, 2)$, `in24` $(9, 6)$ and `in-1074` $(13, 8)$, which pass, it changes
one bit of one $B_i$ (the lowest bit, bit $32 ell$ and the top bit
$64 ell - 1$, for each of the $k$ coefficients), or moves $x_0$ by one ulp
either way, or changes bit 0, 20 or 51 of $|S_0|$ (for a negative $S_0$,
of its two's complement): $3 k + 5$ changes a line, 87 in all. Rocq checks
by evaluation that `check_line` answers `false` on each of them, in 14.4 s
on the desktop (measured, compilation of `ExpMutate.v`).

= The lines cover the inputs

Each line is checked alone; that the lines, put together, leave no input
out is checked by `ExpCover.v`. A line covers the doubles
$(S_0 + j) u$, $j = 0, dots, n - d$; the next line must start at the next
double after its last input $x_l = S_L u$, going upwards. Within a binade
that is $(S_L + 1) u$; at the top of a binade ($S_L + 1 = 2^53$) it is
$2^52 dot 2 u$, and for negative $x$ at the end of a binade
($S_L = -2^52$) it is $-(2^53 - 1) dot u slash 2$. So even for a half-open
line ($d = 1$) the next $x_0$ is not always $x_1 = x_0 + n u$: going up
from a negative binade, $u$ halves.

- `contig` checks this between consecutive lines of a file, by parsing
  only (no $exp$); one file `Cover_N.v` per table file, with
  `native_compute`.
- `mksample.sh` orders the files by their first $x_0$ and cuts them into
  runs of files that follow each other; `joins` checks the boundaries.
- `cover_ok` is the theorem: if the files of a run are contiguous, join,
  and all their lines satisfy the six conditions, then every normal double
  $y = S u'$ between the first $x_0$ and the last $x_l$ of the run lies in
  $[x_0, x_l]$ of one of its lines, with the same exponent, so
  $y = x_0 + j u$ for some $0 <= j <= n - d$. `AllCover.v` states it for
  each run, on the text of the lines, as the theorem `cover`$K$ for the run
  $K$.

On the archive every file is contiguous, and the files join everywhere
except around 0: the run reports a single boundary that does not join,
between `in0-52`, which ends at $-2^(-53)$, and `in1-52`, which starts at
$2^(-53)$. The order of the files is `in-1074`, ..., `in-1`, `in0-0`, ...,
`in0-52`, `in1-52`, ..., `in1-0`, `in2`, ..., `in1024` (`in0-`$j$ covers
$[-2^(-j), -2^(-j-1))$, `in1-`$j$ covers $[2^(-j-1), 2^(-j))$). So
`AllCover.v` has two theorems, one for each run:

#align(center, table(columns: 3, align: (left, left, left),
  stroke: 0.4pt, inset: 4pt,
  [run], [from], [to],
  [`in-1074` .. `in0-52` (1127 files)], [#raw("-0x1.74910d52d3051p+9") $approx -745.133$], [#raw("-0x1p-53")],
  [`in1-52` .. `in1024` (1076 files)], [#raw("0x1p-53")], [#raw("0x1.62e42fefa39efp+9") $approx 709.783$],
))

The doubles in neither run are those with $-2^(-53) < x < 2^(-53)$: the
tiny inputs, whose $exp$ is $1$ or a neighbour of $1$.

= What is not checked

- The inputs $-2^(-53) < x < 2^(-53)$, in no table (section 12).
- The search itself: that is `TaylorLink.v`, which this check feeds, and
  the proofs of the program in Capla and VST.

#pagebreak()
#counter(heading).update(0)
#set heading(numbering: "A.1")

= `ExpCheck.v`
#listing("../code/exptablekl/ExpCheck.v")

= `ExpParse.v`
#listing("../code/exptablekl/ExpParse.v")

= `ExpProof.v`
#listing("../code/exptablekl/ExpProof.v")

= `ExpParseSpec.v`
#listing("../code/exptablekl/ExpParseSpec.v")

= `ExpArith.v`
#listing("../code/exptablekl/ExpArith.v")

= `ExpEncl.v`
#listing("../code/exptablekl/ExpEncl.v")

= `ExpTaylor.v`
#listing("../code/exptablekl/ExpTaylor.v")

= `ExpCover.v`
#listing("../code/exptablekl/ExpCover.v")

= `ExpHard.v`
#listing("../code/exptablekl/ExpHard.v")
