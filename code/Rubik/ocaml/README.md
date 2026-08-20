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
    make mask                  the exact table and its move masks, once
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
everything at ten or beyond reads ten: weaker pruning, never a lie.  **Cap 12
is the exact table**, in the same 2.2 GB and with no new code, and it matters
because most of the 2.2 billion states sit at ten, eleven or twelve -- the
range cap 9 collapses to one value.

`make mask` builds the second table, which is what `hcoset`'s `phase1prune`
carries: beside the distance, **which moves go closer**.  A node then tries
only the moves the table names instead of all eighteen, which Rokicki says
"eliminates almost all false paths in the search".  Ours is a word a state --
five bits of distance, eighteen of the moves that drop it, eighteen of those
that do not raise it -- so 17.7 GB against his 650 MB, because he folds by
the sixteen symmetries and we do not.  A row then wants 2.2 + 17.7 + 6.5 =
26.4 GB.

The sweep that builds it is cheap because of how the index is laid out: with
a twist and a flip held fixed, the eighteen children of all 495 slice values
sit in eighteen runs of 495 bytes, so the whole sweep works out of cache.

The mask search does NOT need the exact table.  What it needs is that the
table never over-estimates and never changes by more than one per move, and a
capped table has both: the smaller of the distance and the cap is still a
lower bound, and taking the smaller of two things with a constant cannot make
two neighbours differ by more than they did.  So a move the table rules out
leads nowhere whatever the cap.

`make mask` uses cap 12 anyway, for a reason that has nothing to do with
soundness: **the cap does not change the table's size.**  The 17.7 GB is the
two masks, not the distance, so cap 9 and cap 12 cost the same to store and
cap 12 prunes strictly better.  The two improvements are independent -- exact
distances buy pruning, masks buy one table read a node instead of eighteen --
and there is no reason to take the weaker half of the first.

If the 17.7 GB is the problem, the answer is not a lower cap but the fold
Rokicki uses and `fold.md` already describes: the sixteen symmetries of the
U/D axis, 15.7x, about 1.1 GB, at the price of a fold on every lookup.

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

### A real row, measured

`R U F L D B R U F L`, the same machine, one core, 2026-08-20.  Its
representative is already 10 from H, so the search starts at depth 10:

    ./rubik_row 9 20 "R U F L D B R U F L" 16
    depth 15 :   641980912 nodes,  19245852 solutions,     19508974 done, search  118.2 s
    depth 16 :  8393815854 nodes, 148553182 solutions,    294431520 done, search 1490.7 s
    depth 17 : 0 nodes, 0 solutions,   2244383965 done, prepass 55.8 s
    depth 18 : 0 nodes, 0 solutions,  10567926928 done, prepass 73.6 s
    depth 19 : 0 nodes, 0 solutions,  19313324832 done, prepass 46.4 s
    depth 20 : 0 nodes, 0 solutions,  19508428800 done, prepass 43.9 s
    row: 19508428800 of 19508428800 after depth 20, 1880.4 s

**31 min 26 on one core**, and 86% of it is the search, of which depth 16
alone is 79%.  The prepass is 249 s of the 1880.

Where the search stops decides everything, and the three runs price it:

| search to | wall | reached |
|---|---|---|
| 11 | 3 min 30 | 3 460 129 724, 17.7% |
| 15 | 6 min 43 | 19 508 275 803, short by **152 997** |
| 16 | 31 min 26 | **19 508 428 800, full** |

The last hundredth of a percent cost five times the rest.  That is the whole
problem in one table, and it is why Rokicki's pruning table, and the symmetry
fold under it, are not optional at scale.

### What the exact table and the masks bought

The same row again with `ROWCAP=12` and `phase1m12.tbl` in place.  Every
`new` and every `done` matched the run above to the unit at all eleven
levels, which is the check: it is a different search over a different table.

| | cap 9, no masks | cap 12 and masks | |
|---|---|---|---|
| the row | 1 880.4 s | **725.3 s** | 2.6x |
| processor time | 1 871 s | 668 s | 2.8x |
| the search | 1 617 s | 447 s | 3.6x |
| depth 16 | 1 490.7 s | 347.6 s | 4.3x |
| nodes at depth 16 | 8 393 815 854 | 819 640 367 | 10.2x |

The nodes fell tenfold and the time only 3.6, so a node costs 2.8 times what
it did: 17.7 GB touched at random against 2.2 GB.  92 s of the wall is not
processor time at all, purely paging.  **The fold is the missing factor** --
Rokicki holds the same table in 650 MB by the sixteen symmetries of the U/D
axis, and `fold.md` already does that fold for the Rocq side.

The balance flipped with it: the prepass is now 263 s of the 725, 36% of the
row, where before it was 13%.  That is the split Rokicki describes.

Building the two tables is 350 s for the exact distances and 396 s for the
masks, **12 min 26 once**, and every row after that reuses them.

### How this compares with hcoset, in the paper's own units

`doc/rubik20.pdf` fixes the convention where it sets its hardware baseline:
"a Nehalem X3460 ... with **four cores** and hyperthreading enabled.  We
distinguish **core seconds** (execution on one core) and **CPU seconds**
(execution on the entire CPU).  Our primary metric throughout is CPU
seconds."  So its 19.5 s a coset is a whole four core CPU, about **78 core
seconds**, against our 725 on one core: **about nine times**, one order of
magnitude.  Dividing the paper's billion CPU seconds by the coset count and
calling the answer one core gives four times too large a gap.

Its own split is 3 s of search, 15 s for five prepasses and 1.5 s of
overhead.  Its search runs at 25 million positions a second and its prepass
at 65 billion group operations a CPU second.

### Checked against hcoset itself

`bigdist.tar.gz` on cube20.org ships the sources already untangled, so no
CWEB tools are needed and it builds with a modern compiler unchanged:

    g++ -DHALF -O3 -Wall -DLEVELCOUNTS -o hcoset hcoset.cpp phase1prune.cpp \
        kocsymm.cpp cubepos.cpp -lpthread
    ./hcoset -t 1 -S 15 -d 20 R1U1F1L1D1B1R1U1F1L1

which is our `ROW="R U F L D B R U F L" ROWSEARCH=15 ROWDEPTH=20` on one
core.  **It prints our numbers.**

| level | hcoset | rubik_row |
|---|---|---|
| 15 | 19 508 974 | 19 508 974 |
| 16 | 159 930 336 | 159 930 336 |
| 17 | 1 044 849 952 | 1 044 849 952 |
| 18 | 5 886 166 750 | 5 886 166 750 |
| 19 | 17 282 758 082 | 17 282 758 082 |
| 20 | 19 508 275 803 | 19 508 275 803 |

Eleven levels to the unit, solution counts included, by an implementation
that shares no code with ours.  **So hcoset also leaves 152 997 on this
coset**, and the paper's 345 is an average over 55 882 296 cosets from which
this row is 443 times out.  There is nothing wrong with either program.

The same run gives the speed, one core, identical work:

| | hcoset | rubik_row | |
|---|---|---|---|
| search to 15 | 5.11 s | 37.6 s | 7.4x |
| five prepasses | 38.16 s | 252 s | 6.6x |
| **the coset** | **44.44 s** | **311 s** | **7.0x** |

**Seven times.**  Converting the paper's CPU seconds gave 4.2x, which was too
generous; this measurement supersedes it.

Its prepass is 7.5 to 7.8 s at every level, flat.  Ours is 24 s when the map
is sparse and 88 s when it is full, because we skip empty groups and it does
not.  Our best level is 3.1x its and our worst 11.8x, so the variance is all
on our side.

### Its production recipe, and the 345

hcoset's real setting is `-F`, and it is neither of the two above.  It selects
`-S 16 -d 20` and sets `enoughbits = 167000000 + uniq/3` **after** the depth
16 prepass, so the depth 16 search runs only until the map holds 220 310 448
and then stops.  That one difference is the whole story of the leftover
count, measured on `R U F L D B R U F L`:

| recipe | leftover |
|---|---|
| full depth 15 then five prepasses | 152 997 |
| depth 16 stopped at 220 310 448, which is `-F` | **318** |
| the paper's average | 345 |

So the row is entirely typical and there was never anything to explain;
comparing a depth 15 run against the paper's 345 is comparing two different
computations.  `ROWENOUGH` is the same stop, and on the same recipe:

| | hcoset | rubik_row |
|---|---|---|
| depth 16 solutions | 65 975 234 | 66 009 955 |
| stopped at | 220 310 498 | 220 310 448 |
| **leftover** | **318** | **316** |
| the coset, one core | 72.2 s | 445.4 s |

316 against 318: once the stop is armed the answer depends on the order bits
are found, and the two search the moves in different orders.  Everything up
to that point still agrees to the unit.  **6.2x** on the whole coset.

`ROWLEFT=200` then settles two hundred of the leftovers, each by a word that
is checked by playing it:

    200 settled, 0 without a word of 20, longest 20
       17 moves : 1
       18 moves : 2
       19 moves : 11
       20 moves : 186

93% of them need exactly twenty moves.  They are the deepest members of the
row, which is why phase one reaches H with too few moves to spare and why
Rokicki solves them on six axes rather than one.

### Running its recipe rather than ours -- a full depth 15 search then five
prepasses, `ROWSEARCH=15 ROWCAP=12` -- the row takes 324.1 s and the two are
directly comparable:

| | his, core seconds | ours, core seconds | |
|---|---|---|---|
| the search | ~12 | 37.3 | 3.1x |
| five prepasses | ~60 | 272 | 4.5x |
| overhead | ~6 | ~15 | 2.5x |
| **total** | **~78** | **324** | **4.2x** |

**Four times, and the gap is the PREPASS, not the search.**  It is 272 s of
our 324 and it is pure memory work: our two maps are 3.25 GB against his
2.44, and his inner loop is 61 machine instructions handling 24 positions and
ten moves at once, which he clocks at 65 billion group operations a CPU
second.  Ours works out at 4.5 times less per group operation, which for
OCaml against hand tuned C on a memory bound loop is about what one expects.

Comparing our depth 16 run against his depth 15 recipe gives 9x and is not
the same computation.

**And it does not fill the coset.**  "A full search to depth 15 followed by
five prepasses usually eliminates all but a few dozen positions ... on
average we find 345 positions left per coset, which we can then quickly solve
in 20 or fewer moves using Kociemba's two-phase algorithm."  Our
`ROWSEARCH=15` run is that recipe exactly -- full depth 15, then five
prepasses -- and it left **152 997**, not 345.  That is not a fault: hcoset
itself leaves 152 997 on the same coset, as the section above shows.  The 345
is an average, and the paper says the hard cosets get a partial depth 16
search, which is exactly what our `ROWSEARCH=16` run does.

`ROWLEFT=1` settles them the way hcoset does, a word each: phase one into H
over the mask table, then phase two the rest of the way.  Phase two is a
search inside H over its ten moves, bounded by two tables of 967 680 entries
-- the corners with the middle four, and the outer edges with the middle four
-- each built by breadth first search in seconds.  Neither is the whole
state, so each is a lower bound and the larger is the one to use.

**None of that has to be trusted.**  A leftover is discharged by exhibiting a
word, and the word is checked by playing it.  That is the reverse of the
lower bound, where a witness proves nothing and only exhaustiveness counts,
and it is why the leftovers are the easy half of the upper bound.

The exact distance distribution, which the build prints and which sums to
2 217 093 120: 1, 4, 50, 592, 7 156, 87 236, 1 043 817, 12 070 278,
124 946 368, 821 605 960, 1 199 128 738, 58 202 444, **476**.  Only 476
states of the 2.2 billion are at distance 12; the mass is at 9 and 10, which
is what cap 9 was flattening.

Note also how differently the two rows search.  The row of H itself does
1 487 553 320 nodes at depth 11; this one does 9 274, because its
representative is already 10 from H and there is no slack for the search to
waste.  The trivial row is the expensive one to search and the cheap one to
fill; a real row is the other way round.

**The row of H is the easiest row there is** -- Rokicki says the trivial coset is the
one the prepass helps most.  A row named by a real move sequence starts with
an empty map and a search that begins around depth 10 rather than 0.

The prepass is not an optimisation, it is what makes a row possible at all.
`hcoset.w` gives the size of the thing it removes: for the row of H itself
there are 16 019 916 192 canonical sequences that solve phase 1 at depth 12,
and only 329 352 128 of them -- one in fifty -- end in a move outside H.
Rokicki calls it the key operation for a bound of 20 and the one that takes
the bulk of the time.
