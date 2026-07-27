# The superflip lower bound, prototyped in OCaml.  See README.md.
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

PROGS = rubik_lb rubik_par

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
