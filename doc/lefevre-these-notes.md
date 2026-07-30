# Lefèvre's thesis, chapter 2 — the part that matters for `Alg2.v`

Source: Vincent Lefèvre, *Moyens arithmétiques pour un calcul fiable*, thèse,
ENS Lyon 2000. <https://www.vinc17.net/research/papers/these.pdf>

Chapter 2, *Distance entre un segment de droite et Z²*, is the algorithm we
are formalising. §2.3 is the mathematics, §2.4 the algorithm (Algorithme 2.1).
The published version of the same material is reference [8] of RR-4044:
*An Algorithm That Computes a Lower Bound on the Distance Between a Segment
and Z²*, Developments in Reliable Computing, pp. 203–212.

Everything below is quoted or paraphrased from the thesis; the last section
says what it changes for us. Notation is translated into `Alg2.v`'s.

## 1. The setting

The segment is `y = a·x - b` for `0 <= x < N`. Write `E_n` for the first `n`
points of the sequence `k·a mod 1`:

> `E_n = {k·a ∈ R/Z : k ∈ N, k < n}`

`E_n` is obtained from `E_{n-1}` by adding one point, the previous one
translated by `a` (§2.3).

The **three-distance theorem** (Slater; refs [1,7,47,48,49] in the thesis):

> *"pour chaque valeur de n, il y a au plus trois distances possibles entre
> deux points consécutifs"* — and for some `n`, only two.

## 2. What the variables MEAN (§2.4)

This is the part I had been guessing at, and it is stated outright:

> *"Nous définissons deux nouvelles variables `u` et `v`, qui contiendront le
> **nombre d'intervalles de longueurs respectives `x` et `y`**"*

> *"La variable `d` sera modifiée de façon à ce qu'elle contienne toujours la
> **distance du point considéré à la borne inférieure de l'intervalle**"*

with `x = d_{n,0}` and `y = d_{n,n-1}` the two current interval lengths
(`ℓ` and `h` in whichever order), and initial values

> `x = {a}`, `y = 1 - {a}`, `d = {b}`, `u = v = 1`.

Translated to `Alg2.v` (everything scaled by `M`, so lengths are integers):

| `Alg2.v` | thesis | meaning |
|---|---|---|
| `p`, `q` | `x`, `y` | the **two** interval lengths |
| `u`, `v` | `u`, `v` | **how many** intervals of length `p`, resp. `q` |
| `inv_bez : u*p + v*q = M` | — | the circle is *partitioned*: `u` gaps of size `p`, `v` of size `q` |
| `d` | `d` | distance from `b` down to the lower endpoint of **its own** interval |
| `u + v` | `n` | the number of points, hence the number of gaps |

So `inv_bez` is not an accident of Bézout bookkeeping: it is the statement
that the gaps tile the circle. And `inv_u0`/`inv_v0` (`0 < u`, `0 < v`) say
both interval lengths actually occur.

## 3. The step rule (§2.3)

The construction of `S_n` (a sequence of quadruplets `(d,r,j,k)`: length,
rank, two group indices) has this as its transformation, with
`h_n = max D_n` and `ℓ_n = min D_n`:

> *"Le quadruplet `(d_{n,i}, r_{n,i}, j_{n,i}, k_{n,i})` est remplacé par deux
> quadruplets consécutifs … Les distances des deux nouveaux quadruplets sont
> `ℓ_n` et `h_n - ℓ_n`"*

i.e. **intervals of length `h` are split into `ℓ` and `h - ℓ`; intervals of
length `ℓ` are left untouched**. That is exactly one Euclid step on `(p,q)`,
and it is `invx_step`.

The order of the two pieces is governed by a sign `s_n`, and the ranks `r`
exist only to make the choice of which `h`-interval to split next unique.
§2.4 then *eliminates* `s` by duplicating the loop body — which is why our
`step` has two branches and no state variable.

## 4. The index form of the invariant

Slater's theorem, as formalised in `CFrac/slater.v` (`get_min n` = our `v`,
`get_max n` = our `u`), gives the successor of a point by index:

- `get_nextDmin` : `m + get_min n <= n  ->  get_next n m = m + get_min n`
- `get_minD`     : `{(m + get_min n)·a} = {m·a} + {get_min n·a}`
- `get_nextDmax` : `get_max n <= m <= n  ->  get_next n m = m - get_max n`
- `get_maxD`     : `{m·a} = {(m - get_max n)·a} + {get_max n·a} - 1`

Scaled by `M` and written with our `Pt k = (A*k) %% M`, this is:

```
P1   forall z, z < u        ->  Pt (z + v) = Pt z + p
P2   forall z, u <= z < u+v ->  Pt (z - u) = (Pt z + q) %% M
```

The successor of point `z` is `z + v` across a gap of length `p` when `z < u`,
and `z - u` across a gap of length `q` otherwise — so there are exactly `u`
gaps of length `p` and `v` of length `q`, as §2.4 says. The `%% M` in P2 is
needed only for the single point with `Pt z = M - q`, whose successor is the
origin.

Measured over M in {24,32,45,48,60,64}, all A, every reachable state
(`partition_probe.py`): **P1 0 violations / 2362, P2 0 / 2362**.

## 5. Why `d <= Inf` and not `d = Inf`

The thesis flags this explicitly:

> *"avec cet algorithme, nous considérons plus de points que voulu, car nous
> nous arrêtons non pas à N mais à la plus petite valeur de φ(N) supérieure ou
> égale à N"*

The batched loop overshoots the configuration. That is why `d` can be
*smaller* than `Inf (u+v)`: it already refers to a point beyond the current
`u+v`. Measured: 314 of 17608 states have `d < Inf (u+v)`, all of them in the
`p < q` branch. In the `q <= p` branch `d = Inf (u+v)` exactly, which is our
`ge_d_eq_inf` — and now we know why the two branches differ.

## 6. What this changes for us

`invx_gap` (every distance is `Inf + a*p + b*q`) was the wrong shape: it is an
existential, the decomposition is **not unique**, and a lemma quantifying over
an arbitrary decomposition is false — this is what sank `ge_wrap_au`
(1941 violations / 4690, PR #122). P1/P2 replace it with a *walk over an
actual partition*, where the coefficients are determined rather than guessed.

Not in the thesis, and still to be settled: the algorithm is stated but its
invariant is not proved there in the form we need — §2.3 proves the
three-distance theorem via the `S_n`/rank construction. The two routes are
therefore to port that construction, or to bridge to `slater.v`, which has it
already over `R`.
