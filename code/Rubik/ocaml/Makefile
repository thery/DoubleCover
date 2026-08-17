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

PROGS = rubik_lb rubik_par rubik_qtm rubik_h

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
	rm -f phase1_cap*.tbl qtm_cap*.tbl h_cap*.tbl MoveTables.v

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

hall: rubik_h
	$(MAKE) hrun HPOS=0 HDEPTH=22
	for k in 1 2 3 4 5; do $(MAKE) hrun HPOS=$$k HDEPTH=21; done

.PHONY: hcheck hroots hbuild hcount hrun hall hfold hdump
