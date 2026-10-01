# htr3_new.c's search in Capla.  Needs the opam switch `capla` (Rocq 9.0) and
# the Capla compiler; run `eval $(opam env --switch=capla)` first.
CAPLA ?= $(HOME)/git/capla-compiler
CCOMP := $(CAPLA)/ccomp

all: htr3cap htr3gcc

.PHONY: all clean
.PRECIOUS: tables/%

# Compiled by Capla's verified compiler.
htr3cap: htr3.b main_htr3.c
	$(CCOMP) -O2 htr3.b main_htr3.c -lm -o $@

# The same Capla program, written out as C (unverified backend), then gcc.
htr3_capla.c: htr3.b
	cp htr3.b htr3_capla.b && $(CCOMP) -dcaplac -c htr3_capla.b && rm -f htr3_capla.b htr3_capla.o
htr3gcc: htr3_capla.c main_htr3.c
	gcc -O2 htr3_capla.c main_htr3.c -lm -o $@

# Checking one file of the table: make in1024.htr [PROG=htr3gcc] extracts
# tables/in1024 from the archive and writes its candidates in in1024.htr.
ARCHIVE := ../../../../exptable9/archive
K := 9
L := 6
ERR := 0x600000
PROG := htr3cap

tables/%:
	mkdir -p tables
	for P in $(ARCHIVE)/tables*.tar.bz2; do \
	  tar xjf $$P -C tables $* 2>/dev/null || true; done
	test -f $@

%.htr: $(PROG) tables/%
	./$(PROG) tables/$* $(K) $(L) $(ERR) > $@

clean:
	rm -f htr3cap htr3gcc htr3_capla.c *.o
