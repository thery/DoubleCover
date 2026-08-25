# One row: the two programs and the table

Where the OCaml side stands, 2026-08-25.

## The two programs

Both do the same computation — one row of the upper bound, which is what
Rokicki's `hcoset` does — and both give the same answer.

| | `rubik_row_nofold.ml` | `rubik_row_fold.ml` |
|---|---|---|
| the heuristic | written out state by state | folded |
| what it reads | 2.2 GB, or 17.7 GB with the moves | **563 MB** |
| the row of H to depth 10, cap 9 | 173.7 s | **121.9 s** |
| positions looked at | 279 M | 69 M |

The old one is kept untouched as the baseline. Every level count agrees
between the two: 151 625 494 members either way.

## The table

The heuristic says how far a position is from H, and which moves take it
nearer. There are 2 217 093 120 positions to say it about.

Sixteen renamings of the cube leave H alone and change no distance, so only
one position of each group of sixteen has to be stored. That is the fold:
1 013 760 flip×slice ranks fall into **64 430 orbits, 15.73 times fewer**.

Each entry is four bytes, which is Rokicki's own packing: the three moves of
one face cannot differ by more than one step in effect, so a face needs 15
combinations rather than 27 — four bits. Six faces and four bits of distance
make 28.

| the same information | ours, unfolded | ours, folded | Rokicki |
|---|---|---|---|
| | 17.7 GB | **563 MB** | 650 MB |

`phase1f<K>.tbl`, where K is the cap: distances beyond K are reported as
K+1. Distances really go to 12, so cap 12 is the exact table and anything
below it prunes less well for the same 563 MB. The plain 2.2 GB table is
needed to build it and for nothing else.

## Running it

    make foldtab ROWCAP=12          build the table, once
    make foldchk ROWCAP=12          the folded reads against the plain ones
    make rowf ROWCAP=12 ROW="R U F L D B R U F L"

`foldchk` must print no disagreement: the renamings are permutations, they
commute with the moves, and the distances and moves match the plain table.
Five million random states were checked at cap 9.

## Against hcoset, on the same row

MEASURED on roquableu, 2026-08-25: the row of H (`ROW=""`), his production
recipe on both sides (`-F`, ours `ROWSEARCH=16 ROWENOUGH=auto`), ONE CORE.
Every level count identical -- 329 352 128 solutions at depth 12 on both
sides, which is his published number.

| | hcoset | ours | |
|---|---|---|---|
| search, depth 9 | 2.4 s | 68.8 s | 28x |
| search, depth 10 | 0.9 s | 11.8 s | 14x |
| search, depth 11 | 6.2 s | 86.3 s | 14x |
| search, depth 12 | 45.8 s | 539 s | 12x |
| **the prepass** | 9.2 s | 1.4-2.9 s | **ours is 3-6x faster** |

So the search is about **twelve times his**, and the prepass is FASTER than
his -- that is the map fold, which he does not do.

## And on the superflip row, which is the one that matters

MEASURED on roquableu the same evening, same recipe, one core.  **Every level
count identical on the two sides** -- 3072 at depth 10, 86 144, 1 438 464,
19 186 816, 87 830 784.

| | hcoset | ours |
|---|---|---|
| search, depth 13 | 1.2 s | 27.7 s |
| search, depth 14 | 8.0 s | 135.0 s |
| search, depth 15 | 86.0 s | -- |
| a prepass | 8.6 s | **1.4 s** |
| the whole row | **150 s** | -- |

So the search is 17-22x his here, and the prepass 6x FASTER than his.  His
150 s is more than a third prepass (~54 s of it), which is where our map fold
pays.

**THIS ROW IS CHEAP AND THE ROW OF H IS NOT**: 150 s against hours, for him.
The superflip row is the one the Rocq proof is about, and it is the one to
run.  His `-F` run cannot say what is left over, because `-F` turns bit
counting off; ours prints it at every level.

**hcoset's move syntax**: an explicit twist digit and no bare letters --
`U1R2F1B1R1B2R1U2L1B2R1U3D3R2F1R3L1B2U2F2` is the superflip, and written
without spaces it survives any shell.

**AND THE ROW OF H IS NOT THE SUPERFLIP ROW.**  `ROW=""` is the row of H
itself; the superflip row is
`U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2`, and it is the one the
Rocq proof is about.  The table above is the row of H, on both sides.

## What is not settled

The two programs have only been compared at cap 9, where the old one reads
2.2 GB and has no move information at all. The comparison that counts is cap
12, where the old one drags 17.7 GB about — that is the cost the fold exists
to remove, and none of it shows in the 1.4× above. It needs roquableu.
