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

PROGS = rubik_lb rubik_par rubik_qtm

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
	rm -f phase1_cap*.tbl MoveTables.v

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
