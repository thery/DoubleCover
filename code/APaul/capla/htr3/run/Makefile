# htr3_new.c's search in Capla.  Needs the opam switch `capla` (Rocq 9.0) and
# the Capla compiler; run `eval $(opam env --switch=capla)` first.
CAPLA ?= $(HOME)/git/capla-compiler
CCOMP := $(CAPLA)/ccomp

all: htr3cap htr3gcc htr

.PHONY: all clean FORCE
.PRECIOUS: tables/% cut/%

# Compiled by Capla's verified compiler.
htr3cap: htr3.b main_htr3.c
	$(CCOMP) -O2 htr3.b main_htr3.c -lm -o $@

# The same Capla program, written out as C (unverified backend), then gcc.
htr3_capla.c: htr3.b
	cp htr3.b htr3_capla.b && $(CCOMP) -dcaplac -c htr3_capla.b && rm -f htr3_capla.b htr3_capla.o
htr3gcc: htr3_capla.c main_htr3.c
	gcc -O2 htr3_capla.c main_htr3.c -lm -o $@

# htr3_new.c, Paul Zimmermann's search in C, as htr.c (needs GMP, OpenMP).
htr: htr.c
	gcc -O3 -march=native htr.c -lgmp -fopenmp -lm -o $@

# Checking one file of the table:
#   make in1024.htr    with htr (htr3_new.c)
#   make in1024.htrc   with the Capla search, PROG=htr3cap (default) or htr3gcc
#   make in1024.cmp    both, and compares their candidates
# RANGE=a-b checks only lines a to b of the file, numbered from 1 (default:
# all the lines).  The file is taken from the archive into tables/.
ARCHIVE := ../../../../exptable9/archive
K := 9
L := 6
ERR := 0x600000
PROG := htr3cap
RANGE :=

tables/%:
	mkdir -p tables
	for P in $(ARCHIVE)/tables*.tar.bz2; do \
	  tar xjf $$P -C tables $* 2>/dev/null || true; done
	test -f $@

# The lines of the file in RANGE (rebuilt on every run, as RANGE may change).
cut/%: tables/% FORCE
	mkdir -p cut
	awk -v r=$(RANGE) 'BEGIN { a = 1; b = -1; \
	  if (r != "") { split(r, x, "-"); a = x[1]; b = x[2] } } \
	  NR >= a && (b < 0 || NR <= b)' $< > $@

%.htr: htr cut/%
	./htr cut/$* > $@

%.htrc: $(PROG) cut/%
	./$(PROG) cut/$* $(K) $(L) $(ERR) > $@

# Both, side by side: the candidates of htr and of the Capla search, sorted
# (htr prints them in thread order), must be the same.
%.cmp: %.htr %.htrc
	grep -v '^Processing\|^Done' $*.htr | sort > $*.htr.sorted
	sort $*.htrc | diff $*.htr.sorted - > $@ && echo "$*: same candidates"

FORCE:

clean:
	rm -f htr3cap htr3gcc htr htr3_capla.c *.o
	rm -rf cut
