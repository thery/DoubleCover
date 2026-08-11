# Rubik 3x3x3 — the measured figures

Every number here was measured or counted, not estimated. Each says where it
came from. **Add to this file rather than re-measuring.**

Unless stated otherwise: `vm_compute`, on the desktop, 2026-08-04/05, and
after the `of_nat` work of 2026-08-04 (see "Primitive costs").

---

## Sizes

| | |
|---|---|
| phase 1 space | 2 217 093 120 states = ntwist 2187 x nfs 1 013 760 |
| nfs | 1 013 760 = 2048 flip x 495 slice |
| ntwist | 2187 = 3^7 |
| slice ranks | 495 (masks with four bits set) |
| phase 1 table, packed | 4 bits an entry, 15 to an int63 word = 147 806 208 words = **1.18 GB** |
| the same in OCaml | one byte an entry = **2.06 GB** (`p1gen` prints it) |
| flip x slice move table | 6 082 560 words, 3 chunks (PArray.max_length is 4 194 303) |
| phase 1 table chunks | 71 of at most 2 097 152 words |

### What the certificate guard actually admits (2026-08-05)

`srank` has **495** masks with four bits set; the other **3601** all return
exactly `nsrank` = 495, which is both the "impossible" value and the array
default. So for those, `fsidx x = (f + 1) * 495`, which is BELOW
`nfsi = 2048 * 495` for every `f < 2047`.

| | |
|---|---|
| values passing `fsidx x <? nfsi` | 495*2048 + 3601*2047 = **8 385 007** of 2^24, i.e. **50.0 %** |
| values that are genuine summaries | 2048 * 495 = **1 013 760**, i.e. 6.0 % |

The comment in `Farp1.v` saying the guard "leaves only the 6 %" was wrong by
**8.3x**, and the extra values are exactly the ones that made `fsmoveC`
false. Fixing the guard is therefore a correctness fix AND the largest
single saving available on the certificate.

### The sixteen symmetry fold (`p1gen 9 sym16`, 2026-08-05)

| | |
|---|---|
| symmetries preserving the U/D facelet blocks | **16** of 48 |
| induced maps on twist and flip x slice | well defined — 0 bad of 39 366 per symmetry |
| flip x slice orbits | **64 430** of 1 013 760 |
| fold factor | **15.73x** |
| folded phase 1 table | 140 908 410 entries against 2 217 093 120 |

---

## Primitive costs (100 000 calls each)

**The rule of thumb: an int63 operation is ~0.05 us, a unary nat operation
~1 us.** Most of the work of this development is not letting the second
happen.

| | |
|---|---|
| raw `PArray.get` | 0.04 us |
| nested `PArray.get` | 0.06 us |
| `of_nat n` | ~0.07 us per unit — `of_nat 21` 1.53, `of_nat 495` **36.4** |
| `to_nat n` | ~0.9 us per unit — `to_nat 9` **7.97**. Thirteen times `of_nat` |
| `nth` over an 18 element seq | 7.3 us (a unary fixpoint walking cons cells) |
| the 18 move loop, `iota 0 18` + `of_nat k` | **15.7 us** a pass |
| the same with the indices already int63 | **1.18 us** — 13.3x |

The last two are 2026-08-05, 100 000 iterations, **vm**. `p1stepFr` makes
TWO of those passes for every checked packed value (`acttwi` converts, and
`actfsr` converts again) against about 6 us of actual array reads, so its
inner loop is mostly conversion. Whether `native_compute` narrows the gap is
NOT measured — do not turn 13.3x into a predicted slice time.

**So: when a test compares an int63 with a nat, convert the NAT side.**

### Before and after the `of_nat` work

| | before | after |
|---|---|---|
| `p1get` | 2.99 us | **0.13** (chunk shift as an int63 literal) |
| `actfsr` | 4.60 us | **0.12** (same, plus the move index as int63) |
| `fsidx` | 32.0 us | **0.10** (`nsranki`, the literal five lines above it) |
| `acttwi` | 1.29 us | 0.09 (int move index) |
| `h3` | 19.7 us | ~3 (compare the depth int-ward, `h3i`) |
| `step3` | 13.8 us | 3.1 |

`fsidx` is the guard of every certificate — 2^24 evaluations in each, and
2187 x 2^24 in `p1checkStep`.

### Others

| | |
|---|---|
| `actf` (recomputes the flip x slice action) | **6.2 us** |
| `Dfsri`, `Dtsi` | 0.07, 0.09 us |
| `eq_tabi` (48 entries) | 11.8 us |
| `comp_tabi` (fresh 48 entry array) | 8.3 us |
| `allowedr` | **50 us** — rebuilds `iota 0 18` and filters with unary `%/` and `%%`, per expanding node, for an answer depending only on `p` (7 values) |

---

## The search

### Node counts — `bench/p1gen 9 pieces N J`, matched exactly by Rocq

| depth | piece 0 | all 18 pieces |
|---|---|---|
| 12 | 146 | |
| 13 | 3 140 | |
| 14 | 42 320 | 784 572 |
| 15 | 547 580 | 10 185 576 |
| 16 | 7 100 612 | 130 430 424 |
| 17 | 91 377 680 | |

Growth factor **12.9** (12.98 and 12.80 between the three measured totals).

`pieces` is not `search`: `search` fixes only the first move and carries the
redundancy filter, `countp1` fixes the first two and restarts it at nfcube.
The counts are not comparable between them.

### A `rep`-STYLE MICRO BENCHMARK OVERSTATES CLOSED SUBTERMS

`rep n (fun _ => e) acc` re-evaluates `e` every iteration. The real search
runs under `native_compute`, which **lifts closed subterms and evaluates them
once**. So the harness measures a cost that does not exist for anything not
depending on a variable.

MEASURED, and this is how it was found (2026-08-06): `of_nat 48` inside
`comp_tabi` (3.21 us in the harness) and `id_tabi 47` inside `eq_tabi`
(7.13 us) predicted a further 1.76x on `searchz3f`. The real run gave
34.3 s -> 32.3 s, **6 %, inside the noise** — `oldrun` moved 78.4 -> 69.8 s,
11 %, with no change to it at all. Both were reverted.

The first batch DID deliver, because `allowedr p`, `nth _ mtis k` and
`of_nat d` all depend on a VARIABLE and so cannot be lifted.

**Only trust a `rep` measurement when the expression depends on the loop's
input.**

### The OCaml, for comparison (2026-08-06, desktop, `bench/p1gen 9 pieces N 0`)

| depth | nodes | OCaml search |
|---|---|---|
| 14 | 42 320 | 0.0 s |
| 15 | 547 580 | **0.4 s** |
| 16 | 7 100 612 | **5.6 s** |

**14x a depth** -- exponential, the same shape as ours -- and **0.79 us a
node**. Each invocation also spends ~120 s rebuilding the 2.06 GB table,
which is why the totals are all ~2 min; the printed search seconds exclude it.

**WE ARE STILL 209x THE OCAML** after the 11x: our depth 16 search is 1174 s
for 7 100 612 nodes = 165 us a node. The "29.7 us a node" recorded below
must be measuring something else -- do not use it.

### The fast search on the real chain (2026-08-06, roquableu)

`Runp1_NN.v` with `searchz3n`, native, MEASURED per piece:

| n | search depth | CPU a piece | |
|---|---|---|---|
| 17 | 15 | **117 s** | 18 pieces, 13 m 5 wall at -j4 |
| 18 | 16 | **1200 s** | |

**10.3x a depth**, measured -- against a node growth of 12.97x, so the fixed
cost and whatever else takes a little off.

**CORRECTED using the OCaml's factor.** Ours is 10.3x where the OCaml is
14x, so a fixed per piece cost is depressing it. Solving the two points
against the known node ratio 12.97:

    117  = f + s        f ~ 27 s fixed, s ~ 90 s of search at depth 15
    1200 = f + 12.97 s

which puts depth 17 at 12.87 x 1174 + 27 = **~4.2 h a piece**, not 3.4 --
about 25 % more. n = 19 is then ~13 h at -j6, ~21 h at -j4.

**THE WHOLE n = 18 RUN, MEASURED (2026-08-06, roquableu, 18 pieces):**

    real 8177 s = 2 h 16      user 23299 s = 6 h 28      sys 88 s

so **1294 s a piece** on average -- the 1200 s single piece above was
representative -- and an effective parallelism of 23299 / 8177 = **2.85**,
not the -j it was launched at. Piece 11 alone took 30 min against the 20 min
average: the pieces vary by about 1.5x, which is worth remembering before
reading anything into a single one.

Redone from that average, search part 1294 - 27 = 1267 s at depth 16:

    depth 17 = 12.87 x 1267 + 27 = 16 335 s = **4.54 h a piece**
    18 pieces = **82 CPU-h**

At the 2.85 effective parallelism just measured that is **~29 h wall**, not
one night. Six workers, if the memory holds (mkrunp1.sh's header says six on
62 GB), would be ~14 h.

For comparison, the OLD search took 4 min a piece at depth 14, where the new
one takes 117 s at depth 15 -- 12.97x the nodes in half the time.

### Making searchz3 faster (2026-08-06, roquableu)

One piece at depth 14, `native_compute`, every variant answering `true`,
all within ONE run so the ratios mean something (the baseline alone has
read 78.4 / 69.8 / 66.6 / 66.5 / 70.0 s across runs -- a 23 % spread).

| | s | |
|---|---|---|
| `searchz3` | 70.0 | |
| `searchz3f` | 39.1 | nat out of the inner loop |
| `searchz3g` | 16.5 | h3i tested BEFORE comp_tabi |
| `searchz3h` | 13.4 | eq_tabi stops at the first mismatch |
| `searchz3k` | 9.7 | the nine heuristic lookups short circuited |
| `searchz3m` | 8.0 | the three views computed one at a time |
| `searchz3n` | **5.9** | the move path carried instead of the table |
| | | **11.9x** |

**FOUR OF THE SIX ARE ONE BUG: Rocq is strict, so work happens that a lazy
evaluator would skip.** `orb` in the certificate guards, `andb` in `eqi`,
the recursive call's own argument (a 48 entry array built for children that
one lookup rejects), and `maxi` over nine lookups when the first settles it.
The others were constants recomputed from unary, and maintaining a 48 entry
table that is only ever compared against the identity.

### searchz3 against searchz3f (nat taken out of the inner loop)

MEASURED on roquableu 2026-08-06, `FastBench.vo`, one piece at depth 14,
**native for both**, and both answers `true`:

| | |
|---|---|
| `searchz3` | **78.4 s** |
| `searchz3f` | **34.3 s** |
| | **2.28x** |

That is the nat removal alone. The overnight n = 19 run was **vm**, so the
vm -> native 1.5x is ADDITIONAL to this.

After it, `comp_tabi` dominates -- 8.3 us a child, ~125 us a node, a fresh
48 entry array per child -- and it is NOT nat.

### Per node

| | |
|---|---|
| OCaml | 0.6–0.8 us |
| Rocq, before 2026-08-04 | 89.8 us |
| Rocq, after the `of_nat` work | **29.7 us** (vm) |
| native_compute | 1.5x on wall, 1.9x on CPU — depth 16, 236.4 s -> 157.5 s |

**Take the SLOPE between two depths, never total time / nodes**: a run carries
a fixed cost of about 24 s for materialising the table. Dividing gave 680 us
and a 1150x gap, which was wrong.

**And never count nodes in a unary nat**: `n + m` costs O(n), counts reach
millions. Measured 56 % overhead at depth 10, growing with depth. `countp1`
counts in int63.

---

## Storage and footprint

One chunk, 2 097 152 int63 words (16.8 MB of data):

| | compile | `.vo` | load (term only) | load + evaluate |
|---|---|---|---|---|
| `seq int` | 7:53 | 37.83 MB | 877 MB | 898 MB |
| **array literal** | 12:04 | **6.00 MB** | **281 MB** | 313 MB |
| `seq` inside a `let` | 8:30 | 37.83 MB | | |

**The value costs ~20–30 MB — i.e. just the data. The TERM is the whole
footprint**, and the evaluator is irrelevant to it: summing the same array is
480 MB under vm and 476 MB under native. A `let` changes nothing, because it
targets the value.

Full table, depth 16 count run:

| | |
|---|---|
| chunks as `seq int` | **21.5 GB** resident, flat for the last 55 s (nothing leaks) |
| chunks as array literals | **5 GB** — 4.3x |
| workers on 64 GB | 2 -> **12** |
| a `P1Chk` slice | 3.0 GB (no search state) |

---

## Build costs

| | |
|---|---|
| **`Phase1.vo`** | **41 s** on roquableu, **44.9 s** on the desktop (2026-08-05, `-time`) |
| **`Farp1.vo`** | **1 m 30** on roquableu with the real tables (2026-08-05) |
| **`FsmChk.vo`** | **1 m 20** on roquableu, native (2026-08-05) — the fsmoveC certificate, 2^24 values |
| **`SlrChk.vo`** | **12 m 7**, of which the `Qed` is **719.7 s** (2026-08-05) |

### These certificates are Qed-bound

`native_cast_no_check` does NOT evaluate: it records the cast, and the whole
2^24 evaluation happens in the KERNEL at `Qed`. So the `Time` line inside the
file always reads 0 s and is useless — `time make` is the only measure.
`-time` still earns its keep by splitting tactic from `Qed`, which is how the
`||` below was found.

**`||` IS STRICT UNDER NATIVE.** `orb` is a function call, native compiles it
to OCaml, and OCaml evaluates both arguments. So a guard written
`~~ fsok x || A` runs `A` on all 2^24 values, where
`if ~~ fsok x then true else A` runs it only on the 1 013 760 admitted.
MEASURED: `SlrChk` (with `||`) 719.7 s against `FsmChk` (with `if`) ~80 s —
9x, against 16.5x predicted. Fixed: every `fsok` guard in `Farp1.v` and
`Phase1.v` is an `if` now. One is left, `Fold.v:235`, where the orbit guard
`(norbi <=? i) || foldstepF tw i` still runs the body on all 2 ^ 17 indices
instead of the 64 430 admitted.

### A P1Chk slice, after the guard fix

| | |
|---|---|
| memory | **3.2 GB** each, 9 in parallel = 29 GB of 64 |
| per twist, ARITHMETIC from measured primitives | `sok` on 2^24 ~0.7 s + **`fpar` on 2.03 M ~16 s** + the 18 move work on 1.01 M ~6 s = ~22 s |
| a slice of 81 twists | ~30 min |

**`fpar` dominates and should be a 4096 entry table** like `srank`: it is
`odd (count (nbit x) (iota 0 nedge))`, a NAT computation at ~8 us a call. A
lookup would be 0.04 us and cut the slice to ~9 min. Designed, not built.
| `P1TsChk.vo` | 35 s (its header still says 4.7 min — that predates the `of_nat` work) |

The two machines are within 10 % of each other on `Phase1.vo`, so do NOT
assume roquableu is faster per core — it has the RAM and the cores, not the
clock. Its slowest sentences, all over a second:

| | |
|---|---|
| `by rewrite !permM (eqP (cm _))...` | 7.5 s |
| the `all_ssreflect` import | 6.9 s |
| a `by vm_compute` at char 25096 | 6.0 s |
| `rewrite /p1stepF; case: ifP` in `p1stepF_dummy` | 5.0 s |
| `Farp1.vo` | ~30 s |
| `Farp1main.vo` | 8 s, and needs **no data at all** |
| `Farp1chk.vo` | ~1m25 through `make` (builds the chain beneath it) |
| the 71 chunks | JOBS=3, ~5 h wall as array literals |

`Far_00.v .. Far_17.v` are gone, deleted with the old five view search. What
is in `_CoqProject` now is `Runp1_00.v .. Runp1_17.v`, one eighteenth of the
phase 1 search each at whatever depth `./mkrunp1.sh` last set -- 1200 s of CPU
a piece at n = 18, measured above. **Never run bare `make`.**

## Working interactively: use DUMMY tables (2026-08-05)

`rocq-mcp` opening a file in this development, MEASURED cold:

| tables | `rocq_start` on a small file requiring the chain |
|---|---|
| the real `P1Ts.v` + `P1Fs.v` (2.75 MB) | **over 120 s** — `Farp1.v` itself over 290 s, past the server cap |
| both replaced by `[:: 0]` | **under 30 s** |

So develop against dummies. It is NOT raw size: a synthetic 4.2 MB
`seq int` and the file requiring it cost pet under 25 s cold, against 8.3 s
for `coqc` — so pet handles a big table fine and the cause here is
something else, not yet identified.

`P1Ts.v` and `P1Fs.v` are **tracked**, unlike `P1Fsm.v`, so a local dummy
must be hidden from git:

    git update-index --skip-worktree P1Ts.v P1Fs.v     # dummy locally
    git update-index --no-skip-worktree P1Ts.v P1Fs.v  # and back

Keep the real ones somewhere before overwriting. See the note about never
checking a dummy in under a generated file's name.

---

## The real runs, at -j9 (2026-08-07/08, roquableu, 62 GB, 12 cores)

| n | search depth | wall | CPU | jobs |
|---|---|---|---|---|
| 17 | 15 | 13 m 05 | 35 m 29 | 3 |
| 18 | 16 | 2 h 16 | 6 h 28 | 3 |
| 18 | 16 | **54 m 37** | **6 h 57** | 9 |
| 19 | 17 | **11 h 13 42** | **85 h 11** | 9 |

- n = 18 at -j9 against -j3: **2.49x on wall**, effective parallelism
  **7.63** of 9, CPU up 7.4 % for the contention.  n = 19 gave 7.59.
- The depth 16 -> 17 CPU ratio is **12.26**, a little under the 12.87 node
  ratio.  Predicting n = 19 as (n = 18 wall) x 12.87 came in 4 % high.
- **Piece 11 is the tail**, at both depths: ~1.4x the average.

### A search piece is 4.15 GB, whatever the depth

MEASURED during the n = 18 run: nine workers at **4.15 GB each**, identical
to three decimals, flat from t+110 s to the sample before the first exited at
t+1221 s — the `Qed` included, where under native the evaluation happens.
The same 4.1 GB at depth 15.  It is the loaded table, not search state:
`searchz3n` is a DFS returning a bool that tail calls `go l'`, so nothing is
retained per position but the path, at most `d` deep.

The old figures — "1.6 GB at depth 14, 15.3 GB at 16" in `runp1.sh`, "about
8 GB resident" in `mkrunp1.sh` — are from when the chunks were `seq int`.

Hence `P1RUN_GB=6` -> **-j9**, which is also optimal: 18 equal pieces balance
only at j = 18, 9 or 6; j = 18 wants 74 GB, and j = 12 still runs 12 + 6.

## `fpar` as a table (2026-08-08, desktop, `vm_compute`, 2^20 values)

| | total | a value |
|---|---|---|
| `sok x && ~~ fpar x`, the old guard | 9.624 s | **9.2 us** |
| `fsok x`, an `if` over `fparr` | 0.346 s | **0.33 us** |
| `fpar` alone | 9.432 s | 9.0 us |
| `fparr` alone | 0.320 s | 0.31 us |

**27.8x on the guard.** Two separate causes, both removed: `fpar` was a nat
`count` over `iota 0 nedge`, and the `&&` in front of it is a function, so it
ran on all 2^24 rather than the 12.1 % that pass `sok`.  Under
`native_compute`, which is what the certificates use, the absolute numbers
are lower and the ratio has still to be timed on a slice.

The certificate `fparCP` costs **1.05 s** in `Phase1.vo`, and the whole
addition under 2.5 s.

## The certificate, after the search optimizations were applied to it

MEASURED on roquableu, 2026-08-08.  The first figure is the 27 slices alone;
the second is `DEPTH=16 make test` from a clean tree, which builds P1Fsm,
FsData, P1Rank, Fstab, P1Table, the 27 slices, the 18 searches, the three
certificates and Farp1inst -- strictly more work.

| | wall | CPU |
|---|---|---|
| the 27 slices, before | 2 h 21 13 | 20 h 05 |
| the whole chain, after `fpar` | **1 h 04 06** | **6 h 33** |

So a slice went from 44.6 min to about 12, at least **3.1x** and about 3.7x.
Of the 64 min wall, **20 were the single-threaded `cmxs` of P1Fsm**, which is
now the largest serial step in a build that starts from clean.

### The loop itself (vm_compute, 2 ^ 22 values, trivial predicate)

| driver | time | |
|---|---|---|
| `all_pow` -- rebuilds `1 << of_nat k1` at each of the 2 ^ k nodes | 0.989 s | |
| offset carried as an int, `&&` kept | 0.458 s | **2.16x**, the of_nat |
| offset as an int, nested `if` | **0.346 s** | a further **1.32x**, the `&&` |

The `&&` gains here for a different reason than in the search: a certificate
is true everywhere, so nothing is being skipped -- it is purely that `andb`
is a function call made 2 ^ 24 times a twist.

### What is NOT worth changing

`p1get` divides by 15 and `actfsri` by 3, 37 times per admitted value.
MEASURED: a division costs **0.008 us more than a shift** (0.047 against
0.039 a call), so the lot is ~0.3 s a twist.  A magic-number division is not
worth its proof.

After this, an admitted value costs 18 x (4 array reads, 2 divisions, ~6
multiplications) and that is the floor for this data layout.  The one lever
left is the 16 symmetry fold: it removes 15.73x of the table and therefore
15.73x of the certificate, which is one check per slot.

## The same check in OCaml — `bench/p1gen 9 check` (2026-08-08, desktop)

```
check over packed values: 0 violations, 821.6 s (0.38 s a twist, 0.5 min for 81)
check over ranks:         0 violations, 140.0 s (0.06 s a twist, 0.1 min for 81)
the guard costs 5.87x
```

| | a slice (81 twists) | all 2187 twists |
|---|---|---|
| Rocq, roquableu, after #263 and #265 | ~8 min | ~4.3 CPU-h |
| **OCaml, the same loop** | **30 s** | **13.7 min** |
| OCaml over ranks, not packed values | 5 s | 2.3 min |

**Rocq is ~16x the OCaml** on identical work, ~19x correcting for roquableu
being the faster machine.  So the check is nowhere near the machine, and the
claim that it was at the memory latency floor -- 0.23 us a check against
~80 ns a DRAM access -- was wrong.

**The `fsok` guard costs 5.87x, measured.**  Rocq walks all 2^24 packed
values a twist because `all_powP` hands the instance back at `x`; walking the
1 013 760 ranks directly needs `fsidx` injective on the summaries, which
`Coordfs` does not give.  Against the other lever:

| lever | worth | cost |
|---|---|---|
| `fsidx` injective on summaries, then iterate over ranks | **5.87x** | one lemma, no table changes |
| the 16 symmetry fold | 15.73x | a soundness lemma plus regenerating every table |
