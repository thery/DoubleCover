# The superflip lower bound, prototyped in OCaml

The lower bound is one computation:

```coq
superflip \notin ball Sset 19
```

It is proved in Rocq, by the search of `Farp1inst.v`; `Diam20.v` turns it into
God's number being at least 20.  These two programs are its prototype.  They are
not part of the proof: they exist to measure how big the job is, and to be the
reference the Rocq version is checked against, node for node.

## The programs

| file | what it does |
|---|---|
| `rubik_lb.ml` | iterative deepening from the superflip, depths 1..N, one core |
| `rubik_par.ml` | the same search, split over the root prefixes, N processes |

`rubik_par.ml` also has a `dump` mode that emits the three coordinate move
tables as a Rocq file of `int63` lists.

```
make                 # build both programs
make check           # depths 1..14 on one core, a couple of minutes
make run             # the full depth 19 search, all cores, hours
make MoveTables.v    # the coordinate move tables, as a Rocq file
make clean           # remove the binaries
make distclean       # also remove the 2.2 GB pruning table
```

`make run` takes `JOBS` (default `nproc`), `DEPTH` (19) and `CAP` (9), so
`make run JOBS=24 DEPTH=17` does what it says.  `OPT` is `-O3` and can be
emptied for a switch without flambda.  Underneath, the programs are:

```
./rubik_lb 14                        # depths 1..14, printing nodes and time
./rubik_par 19 9 build               # build the phase-1 table (cap 9) once
seq 0 13 | xargs -P 14 -I{} ./rubik_par 19 9 {} 14
./rubik_par 1 9 dump > MoveTables.v  # the move tables, as Rocq
```

The phase-1 table is written to `phase1_cap<K>.tbl` (2.2 GB) and every worker
maps it read only, so the N processes share one copy.

## The algorithm

IDA\*: depth first search with an admissible heuristic, deepening the bound
until the tree is exhausted.  The heuristic is the distance in a quotient of
the cube group, which is a lower bound on the distance in the group itself.

Three quotients are used, all classical:

  * `flip x slice`, 1 013 760 states
  * `twist x slice`, 1 082 565 states
  * `twist x flip x slice`, 2 217 093 120 states -- Kociemba's phase-1
    coordinate, the strongest of the three

and each is read along the three coordinate axes, so `h` is the max of nine
lookups.  The superflip is fixed by all 48 symmetries, so the three axes agree
at the root and diverge as the search descends.

Two things make it affordable:

  * **The BFS that builds the phase-1 table is stopped at depth 9.**  Anything
    not reached by then is at distance >= 10, so handing it 10 is still a lower
    bound.  Going to depth 11 instead costs 5x the build and buys 0.6% fewer
    nodes -- most of the 2.2e9 states sit at the last levels.
  * **The first move is taken to be U or U2.**  The superflip is fixed by the
    48 symmetries and is its own inverse, so every maneuver is equivalent to
    one starting with a quarter turn or a half turn of a fixed face.  That is a
    factor of 9.

## What it measured

Nodes to exhaust each depth from the superflip, first move restricted:

| depth | pair tables only | + phase-1 (cap 9) |
|---:|---:|---:|
| 12 | 692 462 | 2 102 |
| 13 | 8 715 926 | 25 598 |
| 14 | 107 448 038 | 340 658 |
| 15 | | 4 390 586 |
| 16 | | 55 223 354 |
| 17 | | 688 234 334 |

The growth settles at about 12.4x per level.  The full run:

```
depth 19 : 104 561 988 516 nodes, no solution
           2h20m on 14 cores, 24.0 CPU-hours, 1.21e6 nodes/s/core
```

which is the computational content of the lower bound.

The 20-move maneuver `U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2` is
applied to the solved cube at start up and checked to produce the superflip;
that validates the six move tables end to end.  The three coordinate encodings
are checked by a decode/encode round trip over their whole range.

## Against the Rocq version

The same search was written on `int63` + `PArray` and run in the kernel.  It
returns the same node counts to the unit (46 322 at depth 11, 692 462 at 12,
8 715 926 at 13, 107 448 038 at 14), and runs

  * 4.9x slower than this OCaml under `native_compute`
  * 11x slower under `vm_compute`

so the full depth-19 computation projects to about 9 hours on 14 cores.

## Reid's 1998 table, `rubik_h.ml`

His post of 31 July 1998 (`doc/reid-1998-optimal-solver.md`) describes the
pruning table his optimal solver used, and it is not one of ours.  Take the
subgroup `H` in which the four middle-slice edges are home and unflipped, the
four U corners are on the U face, and every corner has its U or D facelet on
the U or D face.  A coset is then a triple:

| coordinate | what it is | size |
|---|---|---|
| `e` | where the four slice edges sit, and how they are flipped | 190 080 |
| `cl` | which four corner places hold the U corners | 70 |
| `ct` | the corner orientations | 2 187 |

which is 29 099 347 200 cosets, 680 times the 42.6 million states of the edge
database that was our best quarter-turn heuristic.  His table reaches distance
14 in quarter turns; the mean is 11.55.

```
make hcheck     # the coordinates, the angles, the sixteen symmetries
make hroots     # Reid's six positions, no table needed
make hbuild     # the table, JOBS workers
make hcount     # node counts from position HPOS up to depth HDEPTH
make hrun       # the real search of position HPOS, JOBS workers
make hall       # all six positions, which is the lower bound
make hfold      # the table folded by symmetry, 883 MB, for Rocq
```

The table is read along **three axes**.  `H` is built around the up-down axis,
so turning the whole cube asks it about another axis, and every answer is a
lower bound on the same distance.  No symmetry acting on cubies is needed: a
rotation relabels the faces, so the position seen along another axis is the
relabelled word, and along the search a move becomes another move, which the
same tables follow with a permuted index.

What makes that sound is only that the relabelling is a rotation.  If it is
not, a view can read higher than the distance, the search cuts the branch
holding the solution, and the run says no -- which is the one kind of mistake
a search cannot report.  `make hcheck` therefore tests it twice: opposite
faces stay opposite and the signed permutation has determinant one, so it is
a rotation and not a mirror; and on twenty thousand random words, conjugating
must leave the cycle structure of the corner and edge permutations alone.

**The table goes on tmpfs, not on a disk.**  From the tenth level on, a level
of the sweep dirties the whole table, so a file on a disk is written back in
full at every level: measured on the reference machine, eighteen workers idle
at 65% iowait while the disk took 60 MB a second.  `/dev/shm` has to hold
28 GB, which is more than the usual half of memory allows, so

```
df -h /dev/shm
sudo mount -o remount,size=32G /dev/shm
```

`HTBL` says where the table goes and defaults to `/dev/shm/h_cap14.tbl`.  It
does not survive a reboot; copy it to the disk afterwards if that matters.
One byte a coset and no symmetry folding: Reid stores nibbles and folds the
sixteen symmetries of the U-D axis into 883 MB, which is four times smaller
and a great deal more code.  Time is an estimate, not a measurement: about
3.5e11 random writes, so one to two hours on eighteen workers.

`make hcheck` is what to run first.  It round trips the three coordinates,
checks that every move permutes each of them, and prints

```
from solved: 8 cosets at distance 1, fixed by U U' D D'
```

which is the first line of Reid's distance column, and says that the four
turns of the U and D faces lie in `H`.  It then builds the two small tables
`(cl, ct)` and `(e, cl)` -- the same sweep, the same forks, the same shared
file -- and fails if any state is left unreached.

`make hbuild` prints the number of cosets at each distance as it goes.  Those
numbers have to be Reid's quarter-turn column, coset for coset:

```
 0 1          4 6418       8 38304572     12 14800845359
 1 8          5 57912      9 308312232    13 2014724044
 2 76         6 514318    10 2142297548   14 291026
 3 696        7 4496206   11 9789496784
```

If they are not, the coordinate is wrong and nothing below it means anything.

`make hcount HPOS=0 HDEPTH=18` then counts nodes from `superflip . fourspot .
R U`, the position Reid searched through 22 quarter turns.

## What it measured

The build, 18 workers, table in `/dev/shm`: **9 min 50 wall, 103 processor
minutes**, and the fifteen level counts are Reid's quarter-turn column to the
unit, 1, 8, 76, 696, 6418, 57912, 514318, 4496206, 38304572, 308312232,
2142297548, 9789496784, 14800845359, 2014724044, 291026.  So the coordinate is
his.

That build is the one job he timed, which makes the two machines comparable
for once:

| | cosets swept | processor time | per coset |
|---|---|---|---|
| Reid, 1998, one processor | 1 851 470 460, folded | 85 min | 2.75 us |
| here, 18 workers | 29 099 347 200, flat | 103 min | 0.21 us |

Sixteen times the states for 1.2 times the processor time, so 13 times faster
a coset.  A sweep has good locality and gets the clock speed; the search below
is random access and gets only what memory latency has gained, which is far
less.

The search from position 0, one viewing angle, table read from `/dev/shm`:

| depth | nodes | two levels up |
|---:|---:|---:|
| 14 | 1 991 576 | |
| 15 | 6 736 696 | |
| 16 | 82 974 159 | 41.7 |
| 17 | 350 463 408 | 52.0 |
| 18 | 3 719 942 325 | 44.8 |

at a steady **8.4 million nodes a second on one core**, seven times the
half-turn search, because this heuristic is one random read and that one is
three.  Depths alternate because the corner permutation fixes the parity of
the distance, so the ratio to read is the one two levels up.

Extrapolating each chain on its own ratio, and letting the ratio drift up as
it has been doing -- it must end at the canonical 8.9 squared -- position 0 at
depth 22 is about **9e12 nodes** and each of the other five at depth 21 about
**1.2e12**, so Reid's six searches are around **1.5e13 nodes, 500 processor
hours, a day and a half on eighteen cores**.

That is the whole point of the exercise.  The same six searches with the
tables we had were 1.25e14 nodes and some 3 300 processor hours, and the
quarter-turn bound was written down as blocked.  It is not blocked.

## What the run measured

Position 0, `superflip . fourspot . R U`, searched to depth 22 -- Reid's
deepest of the six -- on eighteen cores with the table in `/dev/shm`:

```
145 625 923 490 nodes, 22.2 processor-hours, 89 minutes wall, no solution
```

which is 1.82 million nodes a second a core.  The eighteen jobs came out
within 25% of each other, from 6.00 to 10.38 billion nodes, so the two-move
prefixes even out at depth even though they differ by thirty times at depth
16.

The other five are one level shallower, so about a tenth of that each.  The
whole lower bound is therefore some **35 processor-hours, two and a half
hours of wall clock**, against Reid's 153 hours in 1998.

## The fold, for the sake of Rocq

Every symmetry of the cube that keeps the up-down axis carries a coset onto
one the same distance from solved, so one entry serves a family.  There are
sixteen such symmetries -- rotations about the axis, the flip that exchanges
up and down, and the mirrors -- and they sort the 190 080 values of `e` into
**12 094 families**, Reid's number, a factor of 15.72.

`make hcheck` computes that count, and it needs no distance table, so it is
the cheap check on the whole construction.  `make hfold` then writes the
folded table from the flat one: 12 094 x 70 x 2187 entries at four bits,
883 MB, and it verifies 200 000 random positions through the fold against
the flat table before renaming the file into place.

A mirror is allowed here where it would not be in the search: the fold only
needs the distance to be preserved, and the mirror image of a maneuver solves
the mirror image of the position.  A mirror does turn a clockwise turn into
an anticlockwise one, which the relabelling carries.

Three things the run's figure does not include.  It is **one viewing angle**, and
`H` is symmetric about the U-D axis, so the same table can be read along all
three -- which is where the rest of Reid's advantage must lie.  It is OCaml,
and Rocq measured 3.3 times slower on the half-turn search.  And nothing here
says how the table would be written down in Rocq: folded by the sixteen
symmetries it is 1 851 470 460 entries, which at four bits and sixteen to an
`int63` word is 116 million cells, fewer than the 149 million the phase 1
table already loads.
