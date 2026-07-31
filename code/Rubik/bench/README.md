# Can the kernel hold the table?

The superflip lower bound (see `../ocaml/`) prunes with a table of
2 217 093 120 values, one per class of Kociemba's phase-1 coordinate.  Two
things stand in the way of putting that in Rocq:

  * `PArray.max_length` is 4 194 303, so the table cannot be one array.  It
    has to be two level: `b.[i / n].[i mod n]`, with `n` a power of two so the
    index is a shift and a mask.
  * the values are in 0..10, so nibble packed the table is 1.5e8 `int63` --
    but that is still a term the kernel has to build, hold, and possibly
    serialise.

These files measure exactly that, on `b.[i / n].[i mod n] = i`, whose maximum
is `n*n - 1` and so checks every entry.

```
make          the 1M and 268M entry tables (about a minute)
make huge     the 1G entry table -- needs about 9 GB free
make store    compute a table and put the VALUE in a .vo
make read     Require that .vo and read the table back
```

## The trap

Rows must each be their own array.  The obvious

```coq
PArray.make n (PArray.make n 0)
```

shares ONE row between all n slots; the first write turns it into a diff node
and every later read has to re-root through it, so O(1) access silently
becomes O(n) and nothing ever finishes.  `mkrows` allocates each row
separately.  Given that, the naive `b.[i <- b.[i].[j <- x]]` per element is
just as fast as filling a row and storing it once (0.19 s vs 0.17 s per
million writes) -- the two-level indirection costs about 2.3x on reads and
nothing else.

## Measured

On a 14 core desktop, `vm_compute`:

| table | entries | build + full scan |
|---|---:|---:|
| 1024 x 1024 | 1 048 576 | 0.18 s |
| 16384 x 16384 | 268 435 456 | 59.5 s |

268 M entries is 2.1 GB of `int63` -- more than the 1.5e8 words the real
packed table needs -- built and scanned in under a minute, with the memory
returned afterwards.  Size is not the obstacle.

Storing a computed table in a `.vo` and reading it back from another file:

| | time | artifact |
|---|---:|---:|
| `make store`, 1 048 576 entries | 69.5 s | 15.6 MB `.vo` |
| `make read` | 0.11 s | max = 1048575 |

So the value really is stored, not recomputed -- which is what lets one file
build the table and several hundred per-prefix proof files `Require` it
instead of each rebuilding it.  Note the asymmetry: serialising runs at about
15 000 entries/s, so the one-off cost of a `.vo` for the real table is hours,
while every consumer then gets it for free.

# Why is the Rocq search slower than the OCaml one?

Measured 2026-07-31.  Two files, and the answer is in two independent halves.

## Per node: a flat ~35x, and no culprit ingredient

`Ladder.v` and `ladder.ml` build the SAME search five times, adding one
ingredient at a time, walking the SAME tree (fixed depth, no pruning, same
redundancy rule).  Both report node counts, which agree exactly -- 624 124 for
V0..V3, 138 886 for V4 -- so the comparison is valid.  Depth 5, single
threaded, `native_compute` against `ocamlopt`:

    version                          Rocq n/s     OCaml n/s    ratio
    ---------------------------------------------------------------
    V0  skeleton, no state             399 057    39 019 881     98x
    V1  + compose the 48 entry cube    126 648     4 420 304     35x
    V2  + goal test                     77 004     2 889 663     38x
    V3  + coordinate + heuristic         37 323     1 407 278     38x
    V4  + prune (real search shape)      42 061     1 477 337     35x

**The ratio is flat.**  Adding every ingredient in turn changes nothing: Rocq
costs ~35x on this workload and that is the whole per-node story.  Two things
this rules out, both of which looked plausible beforehand:

  * **allocation is not the cost.**  Preallocating the per-depth arrays takes
    OCaml from 101.6 to 3.5 words/node and gains *nothing* (1.096M vs 1.109M
    nodes/s).  The minor heap is a bump pointer.
  * **no single ingredient dominates.**  Arrays, coordinate and table are all
    within the same band.

At `-j18` on twelve cores (a measured 11.4x) that 35x is very nearly paid for.

## Per tree: ~20x, and this one is ours

`SymHeur.v`.  Rocq prunes with one lookup in the flip x slice table; the OCaml
reference takes the max over three symmetry conjugates of the SAME table.  A
max of admissible heuristics is admissible, and it prunes far harder:

    views                            nodes    time     nodes    time
    ---------------------------------------------------------------
    1   (what Far.v does today)     94 762   4.16 s      1x      1x
    3   {1, Sy, Sx}                 11 353   1.06 s     8.3x    3.9x
    5   {1, Sy, Sx, Sy.Sx, Sx.Sy}    4 918   0.895 s   19.3x    4.6x

Confirmed against the reference: `rubik_lb` with `heur` cut to one symmetry
needs 24 081 446 nodes at depth 12 where three needs 1 106 390 -- 21.8x.

No new table is involved.  See SymHeur.v's header for the certificate
obligations, which are short, and for why the wall-clock gain plateaus at
~4.6x while the node gain keeps growing (each view rebuilds the coordinate
where OCaml steps it -- i.e. Far.v's `searchz`/`actf`, which composes with
this).

## The upshot

    ~35x   Rocq is slower at everything          the VM -- covered by -j18
    ~4x    we compose permutations where OCaml
           steps coordinates                     ours: searchz (proved)
    ~20x   we explore far more tree              ours: symmetry heuristic

Only the first is the language's.
