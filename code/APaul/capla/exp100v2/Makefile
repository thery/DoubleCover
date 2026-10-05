# The Capla exp100 on the new Capla (ccomp installed in the opam switch
# capla3, see PICKUP-install.md).
CCOMP ?= $(shell opam var bin --switch=capla3)/ccomp

all: test_capla

# The Capla program and exp100.c side by side, both through ccomp.
test_capla: exp100.b test_capla.c ../../exp100/exp100.c ../../exp100/exp100_table.h
	$(CCOMP) -O2 exp100.b test_capla.c -o $@

test: test_capla
	./test_capla 1000000

# The program as a Rocq term and the proofs: make -C proof all.

clean:
	rm -f test_capla *.o

.PHONY: all test clean
