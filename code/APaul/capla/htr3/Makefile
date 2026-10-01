# htr3.c's search in Capla.  Needs the opam switch `capla` (Rocq 9.0) and
# the Capla compiler; run `eval $(opam env --switch=capla)` first.
CAPLA ?= $(HOME)/git/capla-compiler
CCOMP := $(CAPLA)/ccomp

all: htr3cap htr3gcc

# Compiled by Capla's verified compiler.
htr3cap: htr3.b main_htr3.c
	$(CCOMP) -O2 htr3.b main_htr3.c -lm -o $@

# The same Capla program, written out as C (unverified backend), then gcc.
htr3_capla.c: htr3.b
	cp htr3.b htr3_capla.b && $(CCOMP) -dcaplac -c htr3_capla.b && rm -f htr3_capla.b htr3_capla.o
htr3gcc: htr3_capla.c main_htr3.c
	gcc -O2 htr3_capla.c main_htr3.c -lm -o $@

clean:
	rm -f htr3cap htr3gcc htr3_capla.c *.o
