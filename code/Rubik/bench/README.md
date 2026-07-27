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
