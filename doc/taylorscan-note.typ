#set page(paper: "a4", margin: 2.4cm, numbering: "1")
#set text(font: "New Computer Modern", size: 10.5pt)
#set par(justify: true, leading: 0.62em)
#set heading(numbering: "1.1")
#show heading: it => block(above: 1.2em, below: 0.7em)[#it]
#show raw: set text(font: "DejaVu Sans Mono", size: 9pt)

// The listing is read from the source.  Build from the repository root:
// typst compile --root . doc/taylorscan-note.typ
#let listing(path) = block(width: 100%, fill: luma(245), inset: 6pt,
  text(size: 7.5pt, raw(read(path), lang: "coq", block: true)))

#align(center)[
  #text(size: 17pt)[*Reading `TaylorScan.v`*]

  #v(0.4em)
  #text(size: 10pt)[Zimmermann's hard-to-round search in Rocq, for a
  beginner]
]

#v(1em)

The file is `code/APaul/rocq/TaylorScan.v`. It states the search of
`doc/htr.md` and proves that the search part of it misses nothing. This note
explains the idea, then the file line by line. The full file is in the
annex.

= The problem

A double $x$ is *hard to round* when $exp x$ is extremely close to a point
where rounding changes its mind. Measured in a unit $v$ (half the distance
between two doubles near $exp x$), the rounding points are the integers, so
$x$ is hard to round at level $m$ when $exp(x) slash v$ is within $2^(-m)$ of
an integer. We want every such $x$ in a given range, without evaluating $exp$
at each of the billions of doubles.

= Zimmermann's idea in four steps

+ *Cut the range* into subranges of $n$ consecutive doubles
  $x_0, x_0 + u, dots, x_0 + (n-1) u$, where $u$ is the distance between two
  doubles. We number them $j = 0, dots, n - 1$.
+ *Replace $exp$ by a polynomial in $j$.* On a subrange, $exp(x_0 + j u)
  slash v$ is very close to a polynomial of small degree in $j$ (its Taylor
  polynomial). Multiply by a large power of 2, $M = 2^(64 ell)$, and round
  the coefficients: we get a polynomial with *integer* coefficients,
  $ P(j) = A_0 + A_1 j + dots + A_(k-1) j^(k-1). $
  Only the part of $P(j)$ modulo $M$ matters, because only the distance to
  an integer matters.
+ *Test each $j$.* $x_0 + j u$ is a *candidate* when $P(j)$ is within a
  margin $E$ of a multiple of $M$. $E$ is chosen to cover everything we
  neglected: the target $2^(-m)$, the Taylor remainder, and the rounding of
  the coefficients.
+ *Compute $P(0), P(1), P(2), dots$ with additions only*, by the table of
  differences (next section). This is what makes the search fast.

*The test in one formula.* "$b$ is within $E$ of a multiple of $M$" is
checked as

$ (b + E) mod M <= 2 E. $

Example with $M = 100$ and $E = 5$: $b = 197$ is within 3 of $200$, and
$(197 + 5) mod 100 = 2 <= 10$: a candidate. $b = 150$ gives
$(150 + 5) mod 100 = 55 > 10$: not a candidate. Adding $E$ shifts the
interval $[-E, E]$ around a multiple of $M$ to $[0, 2E]$, which a single
comparison can test.

= The table of differences

The *difference* of a sequence $f$ is $Delta f (j) = f(j+1) - f(j)$. For a
polynomial of degree $d$, taking $d$ differences leaves a constant, and
$d + 1$ differences leave 0. The *table* at $j$ is the list
$f(j), Delta f(j), Delta^2 f(j), dots$.

Example with $f(j) = j^2$: the table at $j = 0$ is $[0, 1, 2]$ (the value
0, then $1 - 0 = 1$, then $(4 - 1) - (1 - 0) = 2$). *One step* adds each
row to the one below it:

#table(
  columns: 4,
  stroke: 0.5pt,
  [*$j$*], [*$f(j)$*], [*$Delta f(j)$*], [*$Delta^2 f(j)$*],
  [0], [0], [1], [2],
  [1], [0 + 1 = 1], [1 + 2 = 3], [2],
  [2], [1 + 3 = 4], [3 + 2 = 5], [2],
  [3], [4 + 5 = 9], [5 + 2 = 7], [2],
)

The first column gives $0, 1, 4, 9$: the squares, with additions only. This
is `Shift.v`, already proved:

- `dtab d f j` is the table of $f$ at $j$, with $d + 1$ rows;
- `tstep` is one step;
- `tstepE`: if $f$ has degree at most $d$ (`degle d f`), one step turns the
  table at $j$ into the table at $j + 1$.

= The file, line by line

*Notations used.* `int` is the type of integers of the library mathcomp.
`x *+ n` is $x$ added $n$ times, that is $n x$. `(a %% M)%Z` is $a mod M$,
between 0 and $M - 1$. #raw("`|x|") is the absolute value. `iota 0 n` is the
list $0, 1, dots, n - 1$, and `[seq j <- s | p j]` keeps the elements $j$
of $s$ for which `p j` holds. `j \in s` means $j$ is in the list $s$.
`(j < n)%N` is a comparison of natural numbers.

*The data.* One subrange is described by four values:

```coq
Variables (A : seq int) (M E : int) (n : nat).
```

the coefficients $A_0, dots, A_(k-1)$ as a list, the modulus $M$, the margin
$E$, and the number $n$ of doubles.

*The polynomial.*

```coq
Definition P : nat -> int := hpoly A.
```

`hpoly` (from `Shift.v`) is the polynomial with coefficients `A` in Horner
form: $A_0 + j (A_1 + j (A_2 + dots))$. Its degree is at most the length of
`A`:

```coq
Definition dg := size A.
Lemma degleP : degle dg P.
```

*The test*, the formula of section 2:

```coq
Definition hit (b : int) : bool := ((b + E) %% M)%Z <= E *+ 2.
```

*The walk*, step 6 of the note. It keeps the current table `t` and the
current index `j`, tests the first row, then takes one step; `c` counts the
doubles left:

```coq
Fixpoint walk (j : nat) (t : seq int) (c : nat) : seq nat :=
  if c is c'.+1 then
    let rest := walk j.+1 (tstep t) c' in
    if hit (nth 0 t 0) then j :: rest else rest
  else [::].
```

`nth 0 t 0` is the first row, the current value $P(j)$. The result is the
list of candidates.

*The search* starts the walk from the table of $P$ at 0:

```coq
Definition scan : seq nat := walk 0 (dtab dg P 0) n.
```

= What is proved

*The walk computes the right thing.*

```coq
Lemma scanE : scan = [seq j <- iota 0 n | hit (P j)].
```

The walk returns exactly the $j < n$ whose $P(j)$ passes the test: the fast
computation with additions gives the same answer as evaluating $P$ at every
$j$. The proof (`walkE`) goes by induction on the number of doubles left;
at each step `tstepE` says the table after one step is the table at the next
index, whose first row is $P(j+1)$.

*The test catches every $b$ close to a multiple of $M$.*

```coq
Lemma hitP (b w : int) : E *+ 2 < M -> `|b - M * w| <= E -> hit b.
```

If $|b - M w| <= E$, then $b - M w + E$ is between 0 and $2 E$, which is
less than $M$, so it is $(b + E) mod M$. The condition $2 E < M$ makes sure
the interval $[0, 2 E]$ does not wrap around.

*The main theorem.*

```coq
Theorem scan_complete j (w : int) :
  E *+ 2 < M -> (j < n)%N -> `|P j - M * w| <= E -> j \in scan.
```

If $P(j)$ is within $E$ of a multiple of $M$, then $j$ is a candidate. It
is `scanE` and `hitP` put together. The file has no `Admitted`.

= What is not proved yet

`scan_complete` talks about $P$, not about $exp$. To reach $exp$, one more
statement is needed: *if $x_0 + j u$ is hard to round, then $P(j)$ is
within $E$ of a multiple of $M$*. It holds under the three assumptions of the
note:

- (H_A) each $A_i$ is within 1 of $M$ times the fractional part of the
  exact coefficient $a_i = exp(x_0) u^i slash (i! v)$: this is the
  evaluation of $exp$, done once per subrange;
- (H_T) the Taylor remainder is at most a known $rho$;
- (H_E) $E >= M (2^(-m) + rho) + (1 + n + dots + n^(k-1))$.

Its proof is arithmetic on real numbers: $M a_i j^i$ and $M "frac"(a_i) j^i$
differ by a multiple of $M$, because $j^i$ is an integer; each $A_i$ adds an
error below $j^i < n^i$; the remainder adds at most $M rho$. It is written
at the end of the file as a comment.

Two details also separate the file from the C program `htr2_fix.c`:

- the C builds the first table in place from $P(0), dots, P(k-1)$ (steps 3
  and 4 of the note), where the file takes `dtab` directly; and the file's
  table has one more row, which is 0;
- the C reduces every number modulo $M$ after each addition, where the file
  keeps exact integers and reduces only in the test; the two give the same
  test, because reduction modulo $M$ commutes with addition.

#counter(heading).update(0)
#set heading(numbering: "A.1")

= Annex: `TaylorScan.v`

#listing("/code/APaul/rocq/TaylorScan.v")
