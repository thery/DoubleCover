# ExpModel.v against exp100.c: gen_tests.c prints what the C returns on
# 6718 inputs, in NCHUNK files Tests<i>.v; each proves by vm_compute that
# the model returns the same.  Build ../ExpModel.vo first.
CC = gcc
CFLAGS = -Wall -O2 -std=c11 -D_DEFAULT_SOURCE
COQFLAGS := -R .. Exp100 -R . Exp100Test
NCHUNK := 7
CHUNKS := $(shell seq 0 $$(($(NCHUNK) - 1)))
TESTS := $(CHUNKS:%=Tests%.vo)

all: $(TESTS)

gen_tests: gen_tests.c ../../exp100.c ../../exp100.h ../../exp100_table.h
	$(CC) $(CFLAGS) -o $@ gen_tests.c

stats: gen_tests
	./gen_tests stats

Tests%.v: gen_tests
	./gen_tests $* $(NCHUNK) > $@

Check.vo: ../ExpModel.vo
$(TESTS): Check.vo

%.vo: %.v
	coqc $(COQFLAGS) $<

clean:
	rm -f gen_tests Tests*.v *.vo *.vok *.vos *.glob .*.aux

.PHONY: all stats clean
