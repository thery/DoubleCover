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
| `rubik_row.ml` | one row of the upper bound, the search half of Rokicki's `hcoset` |

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

`make hdump CHUNK=0` writes one chunk of it as a Rocq array literal, in the
shape `bench/p1gen.ml` emits: fifteen four bit entries to an `int63` word,
two million words a chunk.  The folded table is 123 431 364 words, so 59
chunks, against the five that hold the folded phase 1 table.  `../HProbe.v`
says what to measure with one of them, and that measurement decides whether
the Rocq side is possible at all.

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

## One row of the upper bound

`rubik_row.ml` is the start of the other half: that twenty moves always
suffice.  Rokicki, Kociemba, Davidson and Dethridge prove it a row at a time,
and their program is `hcoset`, a literate C++ program at
<http://cube20.org/src/>.

A row is a coset of H, the group generated by U, D and the four half turns
F2 B2 L2 R2.  It has 19 508 428 800 members and the cube splits into
2 217 093 120 rows.  The row is named by a move sequence: play it from solved
and call the result p, and the row is every word w with p * w in H.  A word
of length d is a member solved in d moves, so a row where every member has
been found by depth 20 needs no more than twenty moves.

    make rowcheck              the checks, no big memory
    make hball N=4             the prepass alone, against a one at a time BFS
    make row ROW="U R2 F'"     one row
    make row                   the row of H itself

Every level does two things.  The **search** finds the words of that length
whose last move is not in H.  The **prepass** takes everything found so far
and plays each of the ten moves of H on all of it at once, which accounts for
every word whose last move is in H -- and that is nearly all of them.  A word
that ends in H is a shorter word of the same row followed by moves of H, so
one prepass a level is exactly right, and reading and writing the same map
would count a member a level too soon.  That is why there are two.

The layout is `hcoset`'s, because it is what makes the prepass fast.  A page
is one corner permutation.  Inside a page a **group** of twenty-four bits is a
pair of outer edge permutations, the pair being the two that differ by
exchanging the cubies 0 and 1; the twenty-four bits are the twenty-four middle
permutations, the twelve even ones in the low half and the twelve odd ones in
the high half.  Which member of the pair a bit means is settled by parity, so
nothing is lost, and the numbering carries the parity in its low bit.  Two
things follow, and the prepass needs both: a move sends a pair to a pair,
because exchanging two cubies before a move is the same as exchanging them
after it, and the middle bits are numbered so that F2 is the exchange of the
two halves and nothing else.  Six of the ten moves leave the middle four
alone and so leave all twenty-four bits where they are; the other four
rearrange twelve bits by a table of 4096 entries.

So one move of H over the whole row is 812 851 200 groups of two reads, a
table lookup and two ORs -- no position is ever taken apart.  The map is kept
as its low halves and its high halves apart, sixteen bits at a time, which
costs 6.5 GB for the two maps against `hcoset`'s 4.9, and buys a machine word
that needs no unpacking.

`make rowcheck` verifies, with no big memory and in five seconds: that the
outer numbering is one to one and carries the parity in its low bit, that each
middle permutation gets its own bit and lands in the half its parity says,
that exactly ten of the eighteen moves keep a position in H, that F2 is the
exchange of the two halves and moves no bit within them, and that the move
rule counts 18, 243, 3240, 43254 and 577368 canonical sequences, which
`Canseq.v` proves.

Then the check that matters: for 200 000 members of H and each of the ten
moves, **where the prepass tables send the bit is where the move sends the
position** -- page, group and bit compared against multiplying the position
out.  That is two million comparisons and it is what says the prepass plays
the right moves.

`make hball N` is the other end of it: the prepass alone from the solved
position, so level n is every member of H that n moves of H reach.  For the
first five levels the same thing is worked out one position at a time with a
table of what has been seen, and the two counts must agree.  That check is on
the loop -- the blits, the swap and the indexing -- which the tables check
cannot see.

The pruning table is the prototype's own, `phase1_cap9.tbl`, 2.2 GB, one byte
a state.  It is capped at nine and phase 1 distances go to twelve, so
everything at ten or beyond reads ten: weaker pruning, never a lie.  Rokicki's
own table is exact to twelve and carries, for each state, which moves change
the distance; it is symmetry reduced to 170 311 680 entries of four bytes.

### The first row, measured

The row of H itself, on roquableu, one core, 2026-08-20:

    ./rubik_row 9 20 "" 11
    depth 11 : 1487553320 nodes, 45573536 solutions,  582017108 new,   733642602 done
    depth 12 : 0 nodes, 0 solutions,  2257346454 new,  2990989056 done
    depth 13 : 0 nodes, 0 solutions,  5725571470 new,  8716560526 done
    depth 14 : 0 nodes, 0 solutions,  7182132183 new, 15898692709 done
    depth 15 : 0 nodes, 0 solutions,  3430240810 new, 19328933519 done
    depth 16 : 0 nodes, 0 solutions,   178843181 new, 19507776700 done
    depth 17 : 0 nodes, 0 solutions,      651828 new, 19508428528 done
    depth 18 : 0 nodes, 0 solutions,         272 new, 19508428800 done
    row "": 19508428800 of 19508428800 after depth 18, 725.7 s

**12 min 11 on one core**: 307 s of search, 394 s of prepass, 25 s of
counting.  So every position of H is within eighteen face turns, and the run
exhibits a word for each.  The search stopped at eleven and the prepass found
96% of the members on its own.  The levels close rather than trail off: the
last two add 651 828 and then 272.

Where the search stops is a free choice, and a cheap one.  Searching to 16,
which is what hcoset does, is out of reach with this table: the cut search
grows 7.3 a level from 26.7 s at depth 10, which puts depth 16 at about
forty seven days on one core.  Stopping at eleven costs nine prepass levels
at twenty to sixty seconds each.  Both are safe, so the only question is
which one fills the map.

The cuts were checked against the plain search at two levels: depth 10 and
depth 11 give 151 625 494 and 733 642 602 members either way, to the unit,
while the cut search does one nineteenth of the work.

**This is the easiest row there is** -- Rokicki says the trivial coset is the
one the prepass helps most.  A row named by a real move sequence starts with
an empty map and a search that begins around depth 10 rather than 0.

The prepass is not an optimisation, it is what makes a row possible at all.
`hcoset.w` gives the size of the thing it removes: for the row of H itself
there are 16 019 916 192 canonical sequences that solve phase 1 at depth 12,
and only 329 352 128 of them -- one in fifty -- end in a move outside H.
Rokicki calls it the key operation for a bound of 20 and the one that takes
the bulk of the time.
