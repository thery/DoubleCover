CC = gcc
CFLAGS = -Wall -Wextra -O3 -march=native -std=c11
LDFLAGS = -lmpfr -lgmp -lm

TARGETS = al htr htr_plain record cheb al_miss

all: $(TARGETS)

# htr: the hard-to-round search (current version: its window E covers the
# second-order drift over a chunk); al: the previous version, whose filter
# is unsound -- kept for reference, see al_miss; record: dumps the first
# dd_exp values as a Rocq array (rocq/Data.v); cheb: emits the degree-7
# polynomial coefficients for the search interval (rocq/Cheb.v).
htr: htr.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

# htr_plain: the whole search in one self-contained plain-C file -- the
# certified polynomial and the Lefevre scan on fixed-width integers, with no
# floating point and no MPFR.  Needs no -lmpfr.
htr_plain: htr_plain.c
	$(CC) $(CFLAGS) -o $@ $<

al: al.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

record: record.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

cheb: cheb.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

clean:
	rm -f $(TARGETS) *.o

.PHONY: all clean

al_miss: al_miss.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)
