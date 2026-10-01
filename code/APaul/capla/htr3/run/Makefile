# htr3_new.c's search in Capla.  Needs the opam switch `capla` (Rocq 9.0) and
# the Capla compiler; run `eval $(opam env --switch=capla)` first.
CAPLA ?= $(HOME)/git/capla-compiler
CCOMP := $(CAPLA)/ccomp

all: htr3cap htr3gcc htr

.PHONY: all clean capla-c FORCE
.PRECIOUS: tables/% cut/% %.htr %.htrc

# Compiled by Capla's verified compiler.
htr3cap: htr3.b main_htr3.c
	$(CCOMP) -O2 htr3.b main_htr3.c -lm -o $@

# The same Capla program, written out as C by Capla's unverified backend
# (htr3_capla.c, kept in the repository), then gcc: needs only gcc.
htr3gcc: htr3_capla.c main_htr3.c
	gcc -O2 htr3_capla.c main_htr3.c -lm -o $@

# htr3_new.c, Paul Zimmermann's search in C, as htr.c (needs GMP, OpenMP).
htr: htr.c
	gcc -O3 -march=native htr.c -lgmp -fopenmp -lm -o $@

# Checking one file of the table:
#   make in1024.htr    with htr (htr3_new.c)
#   make in1024.htrc   with the Capla search, PROG=htr3gcc (default) or htr3cap
#   make in1024.cmp    both, and compares their candidates
# RANGE=a-b checks only lines a to b of the file, numbered from 1 (default:
# all the lines); MAXN=n only the first n inputs of each line (default: all,
# a run with MAXN is a partial check).  The file is taken from the archive
# into tables/: INDEX says which part holds it.
ARCHIVE := ../../../../exptable9/archive
K := 9
L := 6
ERR := 0x600000
PROG := htr3gcc
RANGE :=
MAXN :=

tables/%:
	@mkdir -p tables
	@P=$$(awk -v f=$* '$$1 == f { print $$2 }' $(ARCHIVE)/INDEX); \
	  test -n "$$P" || { echo "$*: not in $(ARCHIVE)/INDEX"; exit 1; }; \
	  echo "$*: taken from $(ARCHIVE)/$$P"; \
	  tar xjf $(ARCHIVE)/$$P -C tables --occurrence=1 $*

# The lines of the file in RANGE, cut to MAXN inputs (rebuilt on every run,
# as RANGE and MAXN may change).
cut/%: tables/% FORCE
	@mkdir -p cut
	@awk -v r=$(RANGE) -v m=$(MAXN) 'BEGIN { a = 1; b = -1; \
	  if (r != "") { split(r, x, "-"); a = x[1]; b = x[2] } } \
	  NR >= a && (b < 0 || NR <= b) { \
	    if (m != "" && $$2 + 0 > m + 0) $$2 = m; print }' $< > $@
	@echo "$*: $$(wc -l < $@) lines, $$(awk '{s += $$2} END \
	  {printf "%.0f", s}' $@) inputs (RANGE=$(RANGE) MAXN=$(MAXN))"

# Each run is timed: the times are printed and kept in $@.time.
TIME = /usr/bin/time -f "$@: %e s wall, %U s user" -o $@.time

%.htr: htr cut/%
	@$(TIME) ./htr cut/$* > $@
	@cat $@.time

%.htrc: $(PROG) cut/%
	@$(TIME) ./$(PROG) cut/$* $(K) $(L) $(ERR) > $@
	@sed 's/^\([^:]*\):/\1 ($(PROG)):/' $@.time

# Both, side by side: the candidates of htr and of the Capla search, sorted
# (htr prints them in thread order), must be the same.
%.cmp: %.htr %.htrc
	@grep -v '^Processing\|^Done' $*.htr | sort > $*.htr.sorted
	@sort $*.htrc | diff $*.htr.sorted - > $@ && \
	  echo "$*: same candidates ($$(wc -l < $*.htrc))" || \
	  { echo "$*: DIFFERENT candidates, see $@"; exit 1; }

FORCE:

# Regenerates htr3_capla.c from htr3.b (needs the Capla compiler).
capla-c:
	cp htr3.b htr3_capla.b && $(CCOMP) -dcaplac -c htr3_capla.b && \
	  rm -f htr3_capla.b htr3_capla.o
	{ echo '/* Generated from htr3.b by Capla (`ccomp -dcaplac`, an unverified'; \
	  echo '   backend): the Capla search written out as C, so that htr3gcc'; \
	  echo '   needs only gcc.  Regenerate it with `make capla-c` (needs the'; \
	  echo '   Capla compiler).  Read htr3.b, not this file. */'; echo; \
	  cat htr3_capla.c; } > htr3_capla.tmp && mv htr3_capla.tmp htr3_capla.c

clean:
	rm -f htr3cap htr3gcc htr *.o
	rm -rf cut *.time
