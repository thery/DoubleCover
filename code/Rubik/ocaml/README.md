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
make hcheck     # the coordinates and two small tables, a few seconds
make hroots     # Reid's six positions, no table needed
make hbuild     # the table, JOBS workers
make hcount     # node counts from position HPOS up to depth HDEPTH
```

**The build wants 29.1 GB of free disk and the memory to keep it cached.**
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
R U`, the position Reid searched through 22 quarter turns.  What the same
estimate that reproduces his 153 hours predicts, for the one viewing angle
this program uses:

| depth | nodes |
|---:|---:|
| 15 | 1.0e5 |
| 16 | 8.9e5 |
| 17 | 7.9e6 |
| 18 | 7.1e7 |

so depths 15 to 18 are seconds and the curve, not the estimate, is what
should decide whether the quarter-turn bound is affordable.
