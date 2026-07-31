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
