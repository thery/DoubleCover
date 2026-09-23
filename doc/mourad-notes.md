# Fortin–Gouicem–Graillat, *Correctly rounding elementary functions on GPU* — the `d` side

`doc/mourad.pdf`, hal-00751446. §3.2 and §4.1 are an **analysis of Lefèvre's
algorithm via continued fractions, with proofs**. That is the part neither
Slater nor the thesis gives us in usable form, and it is exactly what the
three remaining admits in `Alg2.v` need.

Companions: `slater-notes.md` (the three-distance side, now proved),
`lefevre-these-notes.md` (what the variables mean), `alg2-notes.md`
(measurements).

## 1. Their Algorithm 1 vs our `step`

Their variables are ours, unscaled (`Alg2.v` multiplies by `M`):

| paper | `Alg2.v` |
|---|---|
| `p = {a}`, `q = 1 - {a}` | `p`, `q` |
| `u`, `v` — counts of intervals | `u`, `v`, with `p*u + q*v = 1` = `inv_bez` |
| `d` = distance from `{b}` **down to the nearest point on its left** | `d` |
| `n = u + v` | `u + v` |

Note their Algorithm 1 branches on **`d < p`**, which they state is exactly
the test "`{b}` is in an interval of length `p`". Ours branches on `p < q`
and batches the reduction. Same algorithm, different factoring; the case
analysis below is what has to be transported.

## 2. Property 3 — the directed reduction (the missing ingredient)

> **Property 3.** Let `(p,q)` be a two-length configuration with `p < q`
> (resp. `q < p`). When going to the next two-length configuration,
> intervals of length `q` (resp. `p`) are split into a left one of length `p`
> (resp. `p-q`) and a right one of length `q-p` (resp. `q`).
>
> Moreover, with `r = q - ⌊q/p⌋·p` (resp. `r = p - ⌊p/q⌋·q`), intervals of
> length `q` are split into `k` intervals of length `p` and one of length
> `r` **in this order, left to right** (resp. one of length `r` and `k` of
> length `q`, **right to left**).

The proof is short: a new interval carrying a new length always has `0` as an
endpoint, so the `r`-interval is the new leftmost (resp. rightmost) one;
apply that to the construction of Property 2.

**This directionality is what I never had.** Our `invx_p1`/`invx_p2` say
which index succeeds which, but not *from which end the new points enter a
gap*. Every one of the three open lemmas asks precisely that: where the new
minimum lands relative to `b`.

## 3. The six cases for `d`

Their §4.1, verbatim in structure:

| branch | where `{b}` is | what happens to `d` | why |
|---|---|---|---|
| `p < q` | in a `p`-interval | unchanged | no point is added in the interval containing `{b}` |
| `p < q` | in a `q`-interval, `d < p` | unchanged | only `q`-intervals are split, by `p`-intervals; with `d < p` **no point can be added to the left of `{b}`** |
| `p < q` | in a `q`-interval, `d > p` | `d - p` | one point enters to the left |
| `q < p` | in a `q`-interval | unchanged | no point is added in the interval containing `{b}` |
| `q < p` | in a `p`-interval, `d < p` | unchanged | points enter `p`-intervals **from the right**; `{b}` still in a `p`-interval |
| `q < p` | in a `p`-interval, `d > p` | `d - p` | points entered from the right one by one, so **the last point added is the nearest one on the left of `{b}`** |

That last row is the argument I was missing. It is *directionality plus
"one by one"* that identifies the new nearest point, not any arithmetic on
`Inf`.

## 4. What it gives our three admits

All three are in the `q <= p` branch and all three are about "where does the
new minimum land". Our batched `d'` in that branch is

    d' = if r <= d then (d - r) %% q else d      (r = p - ⌊p/q⌋·q)

Read against Property 3, this **is** the geometry: walking down from `{b}`
inside its `p`-interval, the interval has been cut, from the right, into `k`
gaps of length `q` and then one gap of length `r` at the left end. So

- if `d < r`, `{b}` lies in that leftmost `r`-gap and **no point was added
  below it** — `d` is unchanged, and `Inf` need not drop. That is the
  right-hand disjunct of `ge_inf_cases` (`Inf (u+v) < q` — measured
  12352/12352, now explained);
- if `r <= d`, `{b}` lies in one of the `k` `q`-gaps, the nearest point below
  it is `(d - r) %% q` away, and that is exactly `d'`. That is the left-hand
  disjunct, and it is also the equality `ge_wrap_tight` asks for, and the
  congruence `inf_cong_ge` asks for (`d' ≡ Inf` mod `r`, since the walk down
  moves in steps of `q` from a point `r` above the gap boundary).

So the three are one statement: **`d'` is the distance from `b` to the
nearest point below it in the new configuration**, which is Property 3 plus
the observation that the `r`-gap sits at the left end.

## 5. Caveats before formalising

- Their proofs assume `a` irrational, and they say explicitly the arguments
  stay valid for rational `a` **as long as neither `p` nor `q` is `0`** —
  which is our `inv_p0`/`inv_q0`. Good.
- Their split is one point at a time (Property 1) or one batch
  (Property 2); ours is always the batch. Property 3 is stated for the
  batch, so it is the one to port.
- Property 3's proof leans on "0 has no preimage", i.e. `Pt k ≠ 0` for
  `0 < k <= N` — our `pt_neq0`, already proved.
- What we would have to state in Rocq is an *ordered* version of
  `invx_p1`/`invx_p2`: not merely which index follows which, but that within
  a split `p`-gap the residual `r`-gap is the leftmost. In `Dst` terms
  (distance to `b`) that is a statement about which index attains the
  minimum, which is what `gap_walk` now lets us reason about.

## 6. Section 5 — generating the polynomials (formalised in `code/APaul/rocq/Shift.v`)

§5 is a different subject from §3.2/§4.1 above: not the search, but the
*production* of the polynomial that the search runs on.  For every interval
of `N` consecutive arguments the search needs `P_i(x) = P(x + iN)`, and §5
builds all of them from one polynomial with **additions only**.

Everything in §5 is exact — the coefficients are fixed-point integers and
no step rounds.  (The paper says so explicitly and defers error
propagation to [5], [27].)  So the whole section is algebra over an
abelian group, which is how `Shift.v` states it.

### The four pieces and where they are

| paper | `Shift.v` |
|---|---|
| Definition 5, `Delta_h` | `dif`, `difn i` (and `difh h` for the stride-`N` difference) |
| Newton interpolation, Fig. 7 | `dif_shiftn` / `dif_shift`, then `newton` |
| `Delta^d P` constant for `deg P = d` | `degle_const` |
| tabulated difference shift, Fig. 8 | `tstep`, `tstepE`, `tstep_iter` |
| straightforward shift, the `C(k, j-i)` Toeplitz matrix | `sstep`, `sstepE`, `sstep1` |
| hybrid CPU/GPU split by `tS + s` (§5.2) | `hybridE` |
| hierarchical method, `P(kN+m) = sum_j a_j(k) C(m,j)` | `acoef`, `hierarchicalE`, `acoef_deg` |

"Degree at most `d`" is `degle d f`, i.e. `difn d.+1 f n = 0` for all `n`.
That is the only notion of degree in the file, and it is the one every
statement needs.  There is **no functional extensionality**: `difn` looks
at its argument on finitely many points, so `difn_ext` rewrites under it
pointwise.  `Shift.v` is admit-free and closed under the global context.

### The two things the proofs actually turn on

- **Newton without a degree hypothesis.**  `dif_shiftn` says
  `f (n + k) = sum_(i < k+1) (dif^i f n) * C(k, i)` for *every* `f` and
  `k` — shifting is `(1 + Delta)^k`.  Both shifts of the paper are that
  one identity: the tabulated one is `k = 1`, the straightforward one is
  the general `k`.  The degree hypothesis only truncates the sum
  (`dif_shift_deg`).
- **The stride-`N` difference lowers the degree.**  `difh_deg`: written in
  the binomial basis, a shift by `h` is a combination of the differences
  of order `1..h` — the constant term is gone, so the degree drops by one.
  Iterating (`difhn_deg`) kills a degree-`d` polynomial in `d+1` shifts,
  and that is exactly why each `a_j` is again a polynomial in `k`
  (`acoef_deg`).  This is the step the paper leaves implicit.

### Degree of a concrete polynomial

To use any of this on a polynomial written down with coefficients, the
file carries a small toolkit: `degleD`, `degle_sum`, `degle_scale`,
`degle_shift`, `degle_mulX` (multiplying by the argument raises the degree
by exactly one), `degle_linX` (a power of a monic linear factor), and
`degle_hpoly` for a Horner form.

## 7. The application: `code/APaul/rocq/ShiftExp.v`

§5.2 deploys a **degree-2** Taylor polynomial over `N = 2^15` arguments,
which is nowhere near what a hard-to-round search at `m = 35` needs.
`ShiftExp.v` runs the same machinery on the polynomial `htr.c` actually
requires: the degree-7 near-minimax approximation `Cheb.v` certifies over
the whole search interval `[0.25, 0.25001)`, within `2^-160` of `exp`, and
`htr.c`'s own interval length `N = 2^20`.

- `Pdir n` is that polynomial evaluated exactly at grid point `n`, as an
  integer over `2^598` (the scaling `Cheb.v` already uses);
- `Pdir_deg : degle 7 Pdir` — eight entries in the difference table;
- `PdirE` is the hierarchical identity, `aexp_tab` the tabulated walk,
  `aexp_hybrid` the §5.2 split;
- `Pdir_exp` : every value the shifts generate is within `2^-160` of
  `exp`.  **This is the point of the section**: the shifts do not round,
  so the single certificate `Cheb.cheb_valid` covers every interval the
  search will visit — no new approximation and no new error term.

`Pdir_chebE` (the integer form equals `Cheb.P_R` on the grid) is **proved**.
It carries no mathematics: both sides are the same polynomial, one with the
powers of two inside the integer and one with them in the denominator.  The
content is an exponent count -- the integer holds `54(7-k)` powers of two and
the denominator `598`, what is left is `220 + 54k`, and those add to `598`
whatever `k` is.  That is `term_bridge`.

It lives in a third file, `code/APaul/rocq/ShiftBridge.v`, which loads **no
mathcomp on purpose**: the statement is about `Z` and `R` only, and with
mathcomp loaded the `pow` rewriting lemmas pick up the wrong subterms (the
goal fills with `2 ^ (7 - k)`).  Apart, it compiles in 1.6 s instead of 25.

Nothing is admitted in the three files, and `Pdir_exp` rests on exactly the
55 axioms `cheb_valid` already carries: 25 `PrimInt63` operation
declarations, 26 `Uint63Axioms` specifications, and the 4 classical axioms of
Stdlib's reals.  It adds none.  The proof work of `ShiftExp.v` measures
4.2 s -- 2.1 s for the eight `term_bridge` rewrites and 1.0 s for the final
`field`; still nothing evaluates a value of the polynomial.

### Scope traps in `ShiftExp.v`

Mixing mathcomp with `ZArith`/`Reals` costs three delimiters: `%N` is
`N_scope` (ZArith) rather than `nat_scope`, `%Z` is mathcomp's `int_scope`
rather than `Z_scope`, and `%R` is mathcomp's `ring_scope` rather than
`R_scope`.  The file uses `%nat` for nat arithmetic and spells `Z`
operations out (`Z.add`, `Z.mul`, `Z.pow`).
