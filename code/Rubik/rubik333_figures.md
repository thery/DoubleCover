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

`Far_00.v .. Far_17.v` are in `_CoqProject` and each is a **65 hour** depth 15
run of the old five view search. **Never run bare `make`.**

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
