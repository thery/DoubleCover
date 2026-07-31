# Slater 1967, *Gaps and steps for the sequence nθ mod 1* — what we use

`doc/slater.pdf`, Proc. Camb. Phil. Soc. 63 (1967) 1115–1123. Only §2
("Simple results for steps") matters for `Alg2.v`; §3–§5 (gaps, continued
fractions) are the same content from the dual side and we do not need them.

Companion: `lefevre-these-notes.md` (what the algorithm's variables mean),
`alg2-notes.md` (measurements and open holes).

## 1. Dictionary

Slater works with `{rθ}`, the fractional part, on `[0,1]`. We work with
`Pt r = (A*r) %% M` on `[0,M)`, i.e. `θ = A/M` scaled by `M`.

| Slater | here | in `Alg2.v` |
|---|---|---|
| `θ` | `A/M` | |
| `{rθ}` | `Pt r` | `pt M A r` |
| `P_r`, the point at `OP_r = {rθ}` | index `r` | |
| `N` (largest index) | `u + v - 1` | the range is `n = u+v` |
| `a` = index of the **smallest** `{rθ}` | `v` | |
| `b` = index of the **largest** `{rθ}` | `u` | |
| `α = {aθ}` | `p` | `inv_pv : p = Pt v` |
| `β = 1 - {bθ}` | `q` | `inv_qu : q = M - Pt u` |
| basic formula (8) `bα + aβ = 1` | `u*p + v*q = M` | `inv_bez` |
| (9) `aB - bA = 1` | the Bézout pair | |

His `N ≥ max(a,b)` and `N ≤ a+b-1` (4)–(5) are, at `N = u+v-1`, exactly
`u+v-1 ≥ max(u,v)` and `u+v-1 ≤ u+v-1` — the second is **tight**, which is
why our configuration is the clean one (see §3).

## 2. (6) — two points are never closer than a gap

> `P_r P_s ≥ α if s > r`, `≥ β if s < r`, with equality iff `s-r = a`
> resp. `r-s = b`.

Here: for `m1 < m2 < u+v`, if `Pt m1 ≤ Pt m2` then `p ≤ Pt m2 - Pt m1`;
if the value order *inverts* the index order then the gap is at least `q`.
These were `pt_gap_min` / `pt_gap_max` (removed in round 7 as unused — they
are Slater (6) and they come back for §4).

Both follow from `invx_min` / `invx_max` and `pt_sub`, so in our development
(6) is a *consequence* of the invariant rather than a lemma proved first.

## 3. (7) — the step structure, and why our case is the clean one

Slater's three types of point, with `next(r)` the index of the point
immediately above `P_r`:

| type | range of `r` | `next(r)` | length | how many |
|---|---|---|---|---|
| (i) | `0 ≤ r ≤ N-a` | `r + a` | `α` | `N+1-a` |
| (ii) | `N-a < r < b` | `r + a - b` | `α+β` | `a+b-N-1` |
| (iii) | `b ≤ r ≤ N` | `r - b` | `β` | `N+1-b` |

At `N+1 = u+v`, `a = v`, `b = u` the counts are

- (i) `N+1-a = u` steps of length `p`, from `r < u`, `next(r) = r+v`
- (ii) `a+b-N-1 = 0` — **no combined gap at all**
- (iii) `N+1-b = v` steps of length `q`, from `r ≥ u`, `next(r) = r-u`

So at exactly `u+v` points the circle is tiled by `u` gaps of `p` and `v`
gaps of `q`, and the successor map is

    next(r) = r + v   if r < u        (value rises by p)
    next(r) = r - u   if u ≤ r < u+v  (value rises by q, mod M)

which is **precisely `invx_p1` and `invx_p2`**. Those two fields of `invx`
are Slater (7) instantiated at our `n`; that is why the loop maintains them
and why the "no `α+β` gap" case is the one the algorithm stays in.

## 4. The two equations — what unlocked `invx_gap`

`invx_gap` says every `Dst y` is `Inf + a*p + b*q` with `a ≤ u`, `b ≤ v`.
The proof is a walk: iterate `next` from `y` until reaching the index `z`
that realises `Inf`. Each step lowers `Dst` by exactly one gap, so

    (value) a*p + b*q = Dst y - Dst z

where `a` counts the (i)-steps and `b` the (iii)-steps. The point missed
for several rounds is that the **same walk gives a second equation**, from
the index halves of (7) — each (i)-step adds `v` to the index, each
(iii)-step subtracts `u`:

    (index) a*v + y = b*u + z

With only the value equation the bounds `a ≤ u`, `b ≤ v` are false as an
arithmetic statement (measured: no greedy or extremal witness works, and
representability itself fails 9322/16336 — `alg2-notes.md` §1). With both,
they are **free**, and that is `gap_bounds` in `Alg2.v`:

> if `u < a` then the index equation gives `u*v + v ≤ b*u + z < b*u + u + v`,
> hence `u*v < u*(b+1)`, i.e. `v ≤ b`; then
> `a*p + b*q ≥ u*p + v*q = M`, which no distance reaches.

Symmetrically for `b`. `gap_count_aux` is the shared counting step.

## 5. What is left to port

`gap_bounds` (§4) is proved. The walk itself — "iterating `next` from `y`
reaches `z` and both equations hold" — is the remaining piece:

- by induction on `Dst y - Dst z`, which drops by `p` or `q` at each step;
- the step is `invx_p1` / `invx_p2` (Slater (7));
- no overshoot, because a point strictly between would violate (6) (§2),
  so `pt_gap_min` / `pt_gap_max` come back;
- the base case needs `Pt` injective on `[0, u+v)`, which follows from
  `pt_neq0` (proved) since `u+v ≤ N`.

Once that lands, `lt_gap_count`, `lt_gap_new` and `invx_step_ge_gap` are
all the same one-line corollary — a walk to the argmin of the *new* state,
whose `invx_p1`/`invx_p2` are already proved obligations.

## 6. What Slater does **not** give us

The `d`-side of the algorithm (`invd`, `ge_wrap_tight`, `inf_cong_ge`) is
Lefèvre's batching, not Slater's structure: the loop advances by whole
batches and so "considers more points than wanted" (`lefevre-these-notes.md`),
which is why `d` is only a lower bound for `Inf`. Slater tells us where the
points are; he does not tell us what the algorithm knows about them.
