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
| `P1TsChk.vo` | 35 s (its header still says 4.7 min — that predates the `of_nat` work) |
| `Farp1.vo` | ~30 s |
| `Farp1main.vo` | 8 s, and needs **no data at all** |
| `Farp1chk.vo` | ~1m25 through `make` (builds the chain beneath it) |
| the 71 chunks | JOBS=3, ~5 h wall as array literals |

`Far_00.v .. Far_17.v` are in `_CoqProject` and each is a **65 hour** depth 15
run of the old five view search. **Never run bare `make`.**
