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
#
# The port is in three layers:
#   scan.b  the Lefevre inner loop, pure wrapping u64 arithmetic
#   poly.b  the 21-limb integers and the certified polynomial
#   htr.b   the whole search, both as a producer and as a checker

CCOMP  ?= $(HOME)/git/capla-compiler/ccomp
CC     ?= gcc
CFLAGS ?= -O2 -Wall

all: test_scan test_poly test_htr

# The Capla code and its C drivers, both through ccomp.
test_scan: scan.b test_scan.c
	$(CCOMP) $^ -o $@

test_poly: poly.b test_poly.c
	$(CCOMP) $^ -o $@

test_htr: htr.b poly.b test_htr.c
	$(CCOMP) htr.b test_htr.c -o $@

# The scan driver with the Capla side dropped, built by gcc: the baseline
# the ccomp timings are read against.
test_scan_gcc: test_scan.c scan_stub.c
	$(CC) $(CFLAGS) $^ -o $@

# The unverified C backend of ccomp, to read what Capla generates.
%.c-gen: %.b
	$(CCOMP) -dcaplac -c $< -o /dev/null

# The assembly, to compare the two code generators.
%.s: %.b
	$(CCOMP) -S $<

# The fast checks: the inner loop and the polynomial layer against C.
check: test_scan test_poly
	./test_scan
	./test_poly

# The whole search over [0.25, 0.25001).  Minutes, not seconds.  Its
# output is meant to be identical to that of ../htr_plain.
check-full: test_htr
	./test_htr

# The same, as a checker against the five known cases.  Twice the work of
# check-full: one full pass, plus a short pass on a wrong oracle.
check-oracle: test_htr
	./test_htr -check

clean:
	rm -f test_scan test_poly test_htr test_scan_gcc *.s *.o
	rm -f scan.c poly.c htr.c

.PHONY: all check check-full check-oracle clean
