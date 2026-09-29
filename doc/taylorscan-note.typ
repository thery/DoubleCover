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
  #text(size: 17pt)[*Reading `TaylorScan.v`, `TaylorReal.v` and `TaylorLink.v`*]

  #v(0.4em)
  #text(size: 10pt)[Zimmermann's hard-to-round search in Rocq, for a
  beginner]
]

#v(1em)

Three files in `code/APaul/rocq/` state the search of `doc/htr.md` and prove
that it misses no hard-to-round case, assuming the evaluation of $exp$ and
its Taylor bound:

- `TaylorScan.v`: the search over the integers, and that it returns every
  $j$ where the integer polynomial is close to a multiple of $M$;
- `TaylorReal.v`: the step from $exp$ to that integer polynomial, on the
  real numbers;
- `TaylorLink.v`: the two put together, in the final theorem `hscan_exp`.

This note explains the idea, then the files. The three files are in the
annexes. None has an `Admitted`.

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

The *difference* of a sequence $f$ is the sequence
$ Delta f (j) = f(j+1) - f(j). $
Applying it again gives the higher differences, each one the difference of
the previous one:
$ Delta^0 f = f, #h(2em) Delta^(i+1) f (j) = Delta^i f (j+1) - Delta^i f (j). $
For a polynomial of degree $d$, each difference lowers the degree by one. So
the $d$-th difference $Delta^d f(j)$ does not depend on $j$: it is $d!$
times the leading coefficient; and the $(d+1)$-th difference is 0 for every
$j$. The *table* at $j$ is the list $f(j), Delta f(j), Delta^2 f(j), dots$.

Example with $f(j) = j^2$:

- $Delta f (j) = (j+1)^2 - j^2 = 2 j + 1$;
- $Delta^2 f (j) = (2 (j+1) + 1) - (2 j + 1) = 2$, which does not depend
  on $j$ ($2!$ times the leading coefficient 1);
- $Delta^3 f (j) = 2 - 2 = 0$.

So the table at $j = 0$ is $[0, 1, 2]$. Below, each line is the table at one
$j$. *One step* computes the line of $j + 1$ from the line of $j$: each entry
is the entry above it plus its right neighbour in the line above.

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

- `dtab d f j` is the table of $f$ at $j$, the line
  $f(j), Delta f(j), dots, Delta^d f(j)$ of $d + 1$ entries;
- `tstep` is one step: it computes the line of $j + 1$ from the line of $j$;
- `is_poly b d f` says that $f$ is a polynomial of degree at most $d$ in the
  basis $b$: $f(j) = l_0 b_0(j) + dots + l_d b_d(j)$ for some coefficients
  $l_i$. The usual basis `U_basis` is $1, j, dots, j^d$; the binomial basis
  `C_basis` is $C(j, 0), dots, C(j, d)$, where
  $C(j, i) = j (j-1) dots (j-i+1) slash i!$ is a polynomial of degree $i$
  in $j$ ($C(j, 2) = (j^2 - j) slash 2$). A polynomial in the usual basis is
  one in the binomial basis (`is_poly_UC`), not conversely: $C(j, 2)$ has
  no integer coefficients in the usual basis. `is_polyCbP` says that $f$ is
  a polynomial in the binomial basis exactly when $Delta^(d+1) f$ is zero
  everywhere;
- `tstepE`: if $f$ is a polynomial of degree at most $d$ (`is_poly C_basis d f`),
  one step turns the table at $j$ into the table at $j + 1$.

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
Lemma is_polyCb_P : is_poly C_basis dg P.
```

*The walk*, step 6 of the note, for any test `p` on the first entry. It
keeps the current table `t` and the current index `j`, tests the first
entry, then takes one step; `c` counts the doubles left:

```coq
Fixpoint walk (p : int -> bool) (j : nat) (t : seq int) (c : nat) :
    seq nat :=
  if c is c'.+1 then
    let rest := walk p j.+1 (tstep t) c' in
    if p (nth 0 t 0) then j :: rest else rest
  else [::].
```

`nth 0 t 0` is the first entry, the current value $P(j)$. The result is the
list of candidates.

*The scan* with a test `p` starts the walk from the table of $P$ at 0:

```coq
Definition scan p : seq nat := walk p 0 (dtab dg P 0) n.
```

*The test of the note*, the formula of section 2, and the search of the
note, the scan with this test:

```coq
Definition hit (b : int) : bool := ((b + E) %% M)%Z <= E *+ 2.
Definition hscan : seq nat := scan hit.
```

`walk` and `scan` work with any test; `hscan` is the search of the note, and
the results that depend on its test are stated on it.

= What is proved

*The walk computes the right thing, whatever the test.*

```coq
Lemma walkE p i c :
  walk p i (dtab dg P i) c = [seq j <- iota i c | p (P j)].
Lemma scanE p : scan p = [seq j <- iota 0 n | p (P j)].
```

The walk returns exactly the $j < n$ whose $P(j)$ passes the test: the fast
computation with additions gives the same answer as evaluating $P$ at every
$j$. The proof of `walkE` goes by induction on the number of doubles left;
at each step `tstepE` says the table after one step is the table at the next
index, whose first entry is $P(j+1)$. It never looks at the test.

*The test of the note catches every $b$ close to a multiple of $M$.*

```coq
Lemma hitP (b w : int) : E *+ 2 < M -> `|b - M * w| <= E -> hit b.
```

If $|b - M w| <= E$, then $b - M w + E$ is between 0 and $2 E$, which is
less than $M$, so it is $(b + E) mod M$. The condition $2 E < M$ makes sure
the interval $[0, 2 E]$ does not wrap around.

*The main theorem.*

```coq
Theorem hscan_complete j (w : int) :
  E *+ 2 < M -> (j < n)%N -> `|P j - M * w| <= E -> j \in hscan.
```

If $P(j)$ is within $E$ of a multiple of $M$, then $j$ is a candidate. It is `scanE` and `hitP` put together. The file has no
`Admitted`.

= From $exp$ to the scan: `TaylorReal.v`

`hscan_complete` talks about $P$, not about $exp$. `TaylorReal.v` makes the
step between them: *if $x_0 + j u$ is hard to round, then $P(j)$ is within
$E$ of a multiple of $M$*. It holds under the three assumptions of the note.
With $a_i = exp(x_0) u^i slash (i! v)$ the exact coefficients and $rho$ a
bound on the Taylor remainder:

- (H_A) each $A_i$ is within 1 of $M$ times the fractional part of $a_i$:
  this is the evaluation of $exp$, done once per subrange;
- (H_T) $exp(x_0 + j u) slash v$ is within $rho$ of
  $a_0 + a_1 j + dots + a_(k-1) j^(k-1)$;
- (H_E) $E >= M (2^(-m) + rho) + (1 + n + dots + n^(k-1))$.

The file is plain Rocq on real numbers (the Stdlib library, no mathcomp).
In it, $exp$ does not appear: the value $exp(x_0 + j u) slash v$ is a real
$y$, and $2^(-m)$ a real $epsilon$. Two definitions:

- `sumR k f` is $f(0) + dots + f(k-1)$;
- `Pz A k j` is the integer $A_0 + A_1 j + dots + A_(k-1) j^(k-1)$.

The lemma:

```coq
Lemma real_lemma (k n j : nat) (M E : Z) (a : nat -> R) (A : nat -> Z)
    (rho eps y : R) :
  (0 < M)%Z -> (j <= n)%nat ->
  (forall i, (i < k)%nat -> Rabs (IZR (A i) - IZR M * frac_part (a i)) < 1) ->
  Rabs (y - sumR k (fun i => a i * INR j ^ i)) <= rho ->
  IZR M * (eps + rho) + sumR k (fun i => INR n ^ i) <= IZR E ->
  (exists z : Z, Rabs (y - IZR z) < eps) ->
  exists w : Z, (Z.abs (Pz A k j - M * w) <= E)%Z.
```

`IZR` and `INR` turn an integer and a natural number into a real;
`frac_part r` is $r$ minus its integer part. The three middle hypotheses are
(H_A), (H_T) and (H_E); the last one says $y$ is within $epsilon$ of an
integer $z$.

*The proof in four lines.* Write each $a_i$ as its integer part plus its
fractional part.

+ $M a_i j^i$ and $M "frac"(a_i) j^i$ differ by $M$ times an integer,
  because $j^i$ is an integer. So $M times sum a_i j^i$ is
  $sum M "frac"(a_i) j^i$ plus $M K$ for an integer $K$.
+ Replacing each $M "frac"(a_i)$ by $A_i$ costs less than $j^i <= n^i$, by
  (H_A): the total error is at most $1 + n + dots + n^(k-1)$.
+ Replacing $sum a_i j^i$ by $y$ costs at most $M rho$, by (H_T); and $y$ is
  within $epsilon$ of $z$, so $M y$ is within $M epsilon$ of $M z$.
+ Take $w = z - K$: $P(j) - M w$ is the sum of the three errors, at most
  $E$ by (H_E).

The file proves it with five small lemmas on `sumR`: two sums can be added,
multiplied by a constant, compared term by term, bounded by the triangle
inequality, and `Pz` read in the reals is the real sum (`IZR_Pz`).

= The final theorem: `TaylorLink.v`

`TaylorScan.v` is written with the mathcomp library, whose integers are the
type `int` and whose polynomial is `hpoly A`; `TaylorReal.v` uses Rocq's `Z`
and `Pz`. `TaylorLink.v` connects them:

- `hpoly_Pz`: `hpoly A j` and `Pz` compute the same integer (`Z_of_int`
  turns a mathcomp `int` into a `Z`);
- `hscan_completeZ`: `hscan_complete`, restated with `Z` and `Pz`;
- `hscan_exp`: `real_lemma` followed by `hscan_completeZ`.

```coq
Theorem hscan_exp (A : seq int) (M E : int) (n j : nat) (a : nat -> R)
    (rho eps y : R) :
  Z.lt 0 (Z_of_int M) -> Z.lt (Z.mul 2 (Z_of_int E)) (Z_of_int M) ->
  (j < n)%N ->
  (H_A) -> (H_T) -> (H_E) ->
  (exists z : Z, Rlt (Rabs (Rminus y (IZR z))) eps) ->
  j \in hscan A M E n.
```

(written here with (H_A), (H_T), (H_E) for the three hypotheses; the file
spells them out). In words: *if $exp(x_0 + j u) slash v$ is within $2^(-m)$
of an integer, then $j$ is a candidate*. The search misses no hard-to-round
case. The file writes the real and `Z` operations as functions (`Rle`,
`Rplus`, `Z.add`, ...) because mathcomp takes over the infix notations
$<=$, $+$, ... for its own types.

`Print Assumptions hscan_exp` lists only the two axioms Rocq's real numbers
are built on.

= What is assumed

- (H_A), the evaluation of $exp$: for `htr2_fix.c`, it is the bound of its
  Tang evaluator at 448 bits, not yet proved.
- (H_T), the Taylor bound for $exp$ with its remainder: a theorem of
  analysis, not yet proved here.
- Two details separate the files from the C program `htr2_fix.c`:
  - the C builds the first table in place from $P(0), dots, P(k-1)$ (steps
    3 and 4 of the note), where `TaylorScan.v` takes `dtab` directly; and
    its table has one more entry, which is 0;
  - the C reduces every number modulo $M$ after each addition, where the
    file keeps exact integers and reduces only in the test; the two give
    the same test, because reduction modulo $M$ commutes with addition.

#counter(heading).update(0)
#set heading(numbering: "A.1")

= Annex: `TaylorScan.v`

#listing("/code/APaul/rocq/TaylorScan.v")

= Annex: `TaylorReal.v`

#listing("/code/APaul/rocq/TaylorReal.v")

= Annex: `TaylorLink.v`

#listing("/code/APaul/rocq/TaylorLink.v")
