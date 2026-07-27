# The superflip lower bound, prototyped in OCaml

`Diameter.v` leaves one `[COMPUTATION]` admitted:

```coq
Lemma superflip_far : superflip \notin ball Sset 19.
```

These two programs are the prototype of the computation behind it.  They are
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

which is the computational content of `superflip_far`.

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
