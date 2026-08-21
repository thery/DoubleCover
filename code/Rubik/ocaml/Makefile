# The superflip lower bound, prototyped in OCaml.  See README.md.
# Also rubik_qtm, the same experiment in the quarter-turn metric.
#
#   make            build both programs
#   make check      depths 1..14 on one core (a couple of minutes)
#   make run        the full depth 19 search on all cores (hours)
#   make MoveTables.v   the coordinate move tables, as a Rocq file
#   make clean      remove the binaries
#   make distclean  also remove the 2.2 GB pruning table

OCAMLFIND = ocamlfind
OPT      ?= -O3
OCAMLOPT  = $(OCAMLFIND) ocamlopt -package unix -linkpkg $(OPT)

JOBS     ?= $(shell nproc)
DEPTH    ?= 19
CAP      ?= 9

PROGS = rubik_lb rubik_par rubik_qtm rubik_h rubik_row

all: $(PROGS)

rubik_lb: rubik_lb.ml
	$(OCAMLOPT) $< -o $@

rubik_par: rubik_par.ml
	$(OCAMLOPT) $< -o $@

# Iterative deepening on one core.  Depth 14 is 107 448 038 nodes; the run
# also checks the move tables against the classical 20-move maneuver.
check: rubik_lb
	./rubik_lb 14

# The real thing: build the phase-1 table once (2.2 GB, a couple of minutes),
# then run JOBS workers over the root prefixes, all mapping that one table.
# Depth 19 is 104 561 988 516 nodes -- 2h20m on 14 cores.
run: rubik_par
	./rubik_par $(DEPTH) $(CAP) build
	seq 0 $$(($(JOBS) - 1)) | \
	  xargs -P $(JOBS) -I{} ./rubik_par $(DEPTH) $(CAP) {} $(JOBS)

MoveTables.v: rubik_par
	./rubik_par 1 $(CAP) dump > $@

clean:
	rm -f $(PROGS) *.cmi *.cmx *.o

distclean: clean
	rm -f phase1_cap*.tbl phase1m*.tbl qtm_cap*.tbl h_cap*.tbl MoveTables.v

.PHONY: all check run clean distclean

# ---- the quarter-turn metric --------------------------------------------- #
# Reid's lower bound: superflip composed with fourspot needs 26 quarter
# turns.  The target's corner permutation is EVEN, so its distance is even
# and exhausting depth 24 already proves 26 -- one level cheaper than 25.
#
#   make qtarget    print the position and stop, no table needed
#   make qverify    deepen until a solution appears: the UPPER bound
#   make qrun       the exhaustive run: the LOWER bound
QDEPTH ?= 24
QCAP   ?= 11

rubik_qtm: rubik_qtm.ml
	$(OCAMLOPT) $< -o $@

qtarget: rubik_qtm
	./rubik_qtm $(QDEPTH) $(QCAP) target

qverify: rubik_qtm
	./rubik_qtm $(QDEPTH) $(QCAP) build
	./rubik_qtm 26 $(QCAP) verify

# 120 prefixes of length two, one per job, so each line is one prefix.
qrun: rubik_qtm
	./rubik_qtm $(QDEPTH) $(QCAP) build
	seq 0 119 | xargs -P $(JOBS) -I{} ./rubik_qtm $(QDEPTH) $(QCAP) {} 120

# ---- Reid's 1998 table ---------------------------------------------------- #
# The subgroup of his "new optimal solver" post: 29 099 347 200 cosets, one
# byte each, so the file is 29.1 GB and the machine needs that much free disk
# and enough memory to keep it in the page cache.
#
#   make hcheck     the coordinates and two small tables, a few seconds
#   make hbuild     the table itself, JOBS workers (hours)
#   make hcount     node counts from one of Reid's six positions
HDEPTH ?= 18
HCAP   ?= 14
HPOS   ?= 0
# On tmpfs, NOT on the disk: the sweep dirties the whole table at every deep
# level, and a disk turns the build into 65% iowait.  /dev/shm must hold 28 GB
# -- check with df -h /dev/shm, and raise it if need be with
#   sudo mount -o remount,size=32G /dev/shm
HTBL   ?= /dev/shm/h_cap$(HCAP).tbl

rubik_h: rubik_h.ml
	$(OCAMLOPT) $< -o $@

hcheck: rubik_h
	./rubik_h 1 $(HCAP) check

hroots: rubik_h
	./rubik_h 1 $(HCAP) roots

hbuild: rubik_h
	H_TBL=$(HTBL) ./rubik_h 1 $(HCAP) build $(JOBS)

hcount: rubik_h
	H_TBL=$(HTBL) ./rubik_h $(HDEPTH) $(HCAP) count $(HPOS)

# The real thing for one of Reid's positions.  ONE JOB PER PREFIX, not one per
# core: the prefixes are unequal -- measured at depth 21, from 94 million to
# 520 million nodes -- so dealing them round robin to the cores leaves most of
# them idle at the end.  One job a prefix and xargs packs them.
#
# There are 120 prefixes: a first move of U, R or F leaves nine second moves
# and one of D, L or B leaves eleven, which is 6 * 9 + 6 * 11.
HJOBS  ?= 120
hrun: rubik_h
	seq 0 $$(($(HJOBS) - 1)) | xargs -P $(JOBS) -I{} \
	  env H_TBL=$(HTBL) ./rubik_h $(HDEPTH) $(HCAP) run $(HPOS) {} $(HJOBS)

# All six of Reid's positions, which together are the lower bound.  The first
# is searched to depth 22 and the others to 21, because the corner parity
# fixes the parity of the distance and their prefixes differ in length.
# The table folded by the sixteen symmetries of the up-down axis: 12 094
# families, 883 MB at four bits an entry.  It needs the flat table to be there.
hadmis: rubik_h
	H_TBL=$(HTBL) ./rubik_h 1 $(HCAP) admis $(JOBS)

hfold: rubik_h
	H_TBL=$(HTBL) ./rubik_h 1 $(HCAP) fold

# One chunk of the folded table as a Rocq array literal, in the shape
# bench/p1gen.ml emits: fifteen four bit entries to an int63 word, two million
# words a chunk.  59 chunks hold the whole thing.  See ../HProbe.v for what to
# measure with it.  It reads only the folded file, not the 29 GB table.
CHUNK  ?= 0
HFTBL  ?= h_fold$(HCAP).tbl
hdump: rubik_h
	H_FTBL=$(HFTBL) ./rubik_h 1 $(HCAP) dump $(CHUNK) \
	  > ../HFold_$$(printf %02d $(CHUNK)).v

# The three move tables and the two maps of the fold, as Rocq.  It needs
# neither the big table nor the folded one -- everything is recomputed.
mtabs: rubik_h
	./rubik_h 1 $(HCAP) mtabs > ../HTables.v

hall: rubik_h
	$(MAKE) hrun HPOS=0 HDEPTH=22
	for k in 1 2 3 4 5; do $(MAKE) hrun HPOS=$$k HDEPTH=21; done

.PHONY: hcheck hroots hbuild hcount hrun hall hfold hdump mtabs

# ---- one row of the upper bound ------------------------------------------ #
# A row is a coset of H, the group generated by U, D and the four half turns.
# It has 19 508 428 800 members and the cube splits into 2 217 093 120 rows.
# The row is named by a move sequence, written the usual way; the empty one
# is the row of H itself.  This is the search half only: it finds the words
# that reach H and marks the member each one gives.  Filling a row also needs
# the prepass, which is not written.
#
#   make rowcheck   the tables, against direct multiplication, no big memory
#   make hball N=4  the prepass alone from solved, against a one at a time BFS
#   make row        one row, ROW="U R2 F'"
#   make row ROWLEFT=1   the same, then a word for each member left over
#   make row ROWSEARCH=16 ROWENOUGH=173502991   hcoset's own quick proof of 20
#
# ROWDEPTH is where the row gives up, ROWSEARCH is where the SEARCH gives up
# and the prepass carries alone -- 20 and 16 are hcoset's own numbers.
#
# THE MAP IS 6.5 GB: four arrays of 812 851 200 sixteen bit words, a low and
# a high half for what is known now and for what is being built.  hball needs
# only that; row needs the 2.2 GB pruning table on top.
ROWCAP    ?= 9
ROWDEPTH  ?= 20
ROWSEARCH ?= 16
ROW       ?=
N         ?= 4

# ROWLEFT=1 settles the members a short row leaves over, a word each.  It is
# exported so that it works written either before or after `make'.
ROWLEFT   ?=
export ROWLEFT

# ROWPLACE="pg gr bt" attacks one leftover of the row on its own; ROWSOLVE
# gives the solver an ordinary scramble, which is the check on the solver.
ROWPLACE  ?=
ROWSOLVE  ?=
export ROWPLACE
export ROWSOLVE

# The leftovers are solved on SIX AXES -- the three axes of the cube, each
# way round -- because a position phase one cannot fit inside twenty from one
# side is often shallow from another.  ROWP1CAP is how many phase one
# solutions of a length are tried before going on to the next; a leftover is
# deep, so most of them lead to an element of H that will not finish in what
# is left.
ROWP1CAP  ?=
export ROWP1CAP

# hcoset's `enoughbits': stop the last search level once the map holds this
# many, and let the prepasses above it finish the row.  Its own rule at depth
# 16 is 167 000 000 plus a third of what the level started with.
ROWENOUGH ?=
export ROWENOUGH

rubik_row: rubik_row.ml
	$(OCAMLOPT) $< -o $@

rowcheck: rubik_row
	./rubik_row check

hball: rubik_row
	./rubik_row hball $(N)

# The table hcoset's phase1prune carries: beside the distance, WHICH MOVES GO
# CLOSER.  It needs the EXACT distances, so cap 12, and it is a word a state
# -- 17.7 GB, against Rokicki's 650 MB, because he folds by the sixteen
# symmetries and we do not.  Built once; the row uses it if it is there.
# A row then wants 2.2 + 17.7 + 6.5 = 26.4 GB.
mask: rubik_row
	./rubik_row 12 20 build
	./rubik_row 12 20 mask

row: rubik_row
	./rubik_row $(ROWCAP) $(ROWDEPTH) build
	./rubik_row $(ROWCAP) $(ROWDEPTH) "$(ROW)" $(ROWSEARCH)

.PHONY: rowcheck hball mask row
