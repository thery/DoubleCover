# God's number is at least 20, in Rocq

A machine-checked proof that the superflip cannot be solved in nineteen face
turns, and hence that the diameter of the Rubik's cube group is at least
twenty.

```coq
Theorem superflip_p1far_real : superflip \notin ball Sset p1depth.  (* Farp1inst.v *)
Theorem rubik_diam_gt_19_real : ~~ diam_le Sset 19.                 (* Diam20.v    *)
```

`Diam20.v` also states `rubik_diameter`, which gives both halves — but the
upper half, that twenty moves always suffice, is not proved here. That theorem
takes it as a hypothesis, spelled out as exactly what an exhaustive search
would have to supply.

Nothing is admitted. `Print Assumptions` reports only the primitives of Rocq's
machine-integer and array interface.

**The written account of all this is `../../doc/rubik20-note.typ`**, with the
compiled `rubik20-note.pdf` beside it. It explains the method, the reductions
and the measurements in plain English, and is the place to start.

## The measurements

Radius 19, on a dual-socket Xeon with 24 cores and 62 GB.

| | |
|---|---|
| positions visited | 146 065 078 152 |
| the search | 6 h 36 of wall clock, 87 h 36 of processor time, 17 workers |
| building the tables, from clean | 1 h 02 of wall clock, 2 h 35 of processor time |
| a search worker | 0.85 GB |
| against the same search in OCaml | 3.3 times slower |

## Running it

```sh
DEPTH=16 make test      # a short run, the whole chain end to end, minutes
DEPTH=19 make test      # the real one, a night
make p1jobs             # what the above would use for -j, and why
make timed              # the same run with a time for every file
```

`make test` emits the folded table if it is missing, regenerates the seventeen
search pieces at the chosen depth, builds `Farp1inst.vo`, and at depth 19 goes
on to `Diam20.v`. Everything already on disk is kept, so an interrupted run
continues where it stopped.

**The job count is a memory question, not a processor one.** Each search piece
materialises the phase 1 table, so launching more of them than the RAM holds
does not run slowly, it stops running. `Makefile.local` computes the
concurrency from the RAM actually present; `P1RUN_GB` overrides the cost it
assumes per job. Raise the stack limit first: `ulimit -s unlimited`.

## What is where

### The cube, as mathematics

| | |
|---|---|
| `Cyc.v` | cyclic permutations, built from the list of points they move |
| `Rubik333.v` | facelets, the six faces, the eighteen moves, the cube group |
| `Sym.v`, `Sym16.v` | the 48 symmetries of the cube; the 16 the fold uses |
| `Ball.v` | balls of radius *d*, and what "the diameter is at most *d*" means |
| `Diameter.v` | the superflip, its 20-move word, and what an upper bound would need |

### The search, in the abstract

| | |
|---|---|
| `Search.v` | the search and its contract: a false answer is a proof |
| `Coord.v` | any summary plus any checked table gives a legal estimate |
| `Root.v` | the first move, up to symmetry: *U* or *U²* |
| `Searchr.v`, `Redun.v` | the rules that forbid redundant move sequences |

None of these five mentions the cube. They are proved once, over any group.

### Data structures

| | |
|---|---|
| `Table.v` | permutations written as the table of their images |
| `Tabi.v` | the same on machine integers and arrays, and the bridge between |
| `ssrint63.v` | the machine-integer toolbox used throughout |

### The summaries and their tables

| | |
|---|---|
| `Coordfs.v`, `Coordfsi.v` | the edge-flip and slice summary, packed into 24 bits |
| `Fstab.v`, `FsTable.v`, `Fsparity.v` | its table and the checks it must pass |
| `Phase1.v` | the phase 1 estimate, its table and its certificate |
| `Moves.v` | the eighteen moves and the superflip, as tables |
| `Fold*.v` | the 16-symmetry fold: a table 15.73 times smaller, and its proof |

### The search on the real data

| | |
|---|---|
| `Farp1.v` | the three viewing angles and the search built on them |
| `Far.v` | the assembly: the superflip is not within *d* moves |
| `Fast.v`, `FastP.v` | the fast search, and the proof that it is the same search |
| `Runp1_03.v` … `_17.v` | the seventeen pieces, written by `mkrunp1.sh` |
| `Farp1main.v` | the theorem over *any* table: 8 seconds, and no data at all |
| `Farp1inst.v` | the same at the real table, and the seventeen real runs |
| `Diam20.v` | and hence God's number is at least 20 |

### The certificates

The files that run the checks, each ending in its own `Qed`: `FsmChk.v`,
`FsrChk.v`, `SlrChk.v`, `P1TsChk.v` for the move and distance tables and the
second summary table, `Farp1chk.v` for the shape of the main table, and the
`Fold` group with its slices `FoldOrbit_00.v` … `FoldOrbit_26.v` for the folded
table.

The files holding the actual table data are deliberately kept out of
`_CoqProject`, since they do not exist until the generators have run and
`coqdep` would refuse the whole project.

## Scripts

| | |
|---|---|
| `mkp1.sh` | the phase 1 table: 71 chunks of Rocq literals, then `P1Table.v` |
| `mkfold.sh` | the folded table and its certificates |
| `mkfoldorbit.sh` | the twenty-seven slices of the orbit certificate |
| `mkfoldrun.sh` | the thirteen checks, as `FoldRun_00.v` and `FoldRun_01.v` |
| `mkfs.sh` | `Fs_00.v` … `Fs_15.v`, one slice of `checkStep` each |
| `mkrunp1.sh` | the seventeen search pieces, at a chosen depth |
| `mkrebuild.sh` | a full rebuild from nothing, timed |
| `runp1.sh` | the three-view search at depth *N* |
| `watchmem.sh` | sample the resident set of a run; where the GB figures come from |
| `rocqtime.sh` | time one file into `fold-timing.log` |
| `unusedreq.py` | report `Require Import` lines that contribute nothing |
| `split-comments.py`, `align-comments.py` | one `(* … *)` a line, closing on column 80 |

## Outside Rocq

`ocaml/` holds the reference implementation, `rubik_par.ml` and `rubik_lb.ml`,
with its own `README.md`. **It is the specification**: the Rocq search
reproduces its node counts exactly, which is how a discrepancy gets caught
early. It also counted the 146 billion positions above.

Its prefix filter was unsound until 2026-08-13 — it dropped the three
bottom-face second moves, searching 24 prefixes where 30 are needed, and so
skipped 29.6% of the tree while running to completion and reporting the answer
we expected. Writing the Rocq proof of that same cut is what found it.

`bench/` holds `p1gen.ml`, which generates the tables, and the experiments that
settled the design questions, each with its measurements.
