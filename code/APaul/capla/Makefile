# Makefile for the Capla port of htr_plain.c.
#
# Capla is the Inria fresco language (git@gitlab.inria.fr:fresco/capla),
# compiled by a modified CompCert.  Point CCOMP at that compiler; the
# default assumes the no-global-install build described in its README:
#
#   git clone --recurse-submodules https://gitlab.inria.fr/fresco/capla/compiler.git
#   ./configure x86_64-linux -libdir $(pwd)/runtime -bindir $(pwd) && make
#
# Its Rocq sources need Rocq 8.15-9.0 (9.1 is refused by configure), so a
# dedicated opam switch is the simplest way to build it.

CCOMP  ?= $(HOME)/git/capla-compiler/ccomp
CC     ?= gcc
CFLAGS ?= -O2 -Wall

all: test_scan

# The Capla loop and its C driver, both through ccomp.
test_scan: scan.b test_scan.c
	$(CCOMP) $^ -o $@

# Same driver with the Capla side dropped, built by gcc: the baseline the
# ccomp timings are read against.
test_scan_gcc: test_scan.c scan_stub.c
	$(CC) $(CFLAGS) $^ -o $@

# The unverified C backend of ccomp, to read what Capla generates.
scan.c: scan.b
	$(CCOMP) -dbcaplac -c $< -o /dev/null

# The assembly of the loop, to compare the two code generators.
scan.s: scan.b
	$(CCOMP) -S $<

check: test_scan
	./test_scan

clean:
	rm -f test_scan test_scan_gcc scan.c scan.s *.o

.PHONY: all check clean
