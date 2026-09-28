CC = gcc
CFLAGS = -Wall -Wextra -O3 -march=native -std=c11 -D_DEFAULT_SOURCE

all: htr2_fix

# the constants, with MPFR; the producer is not trusted
tang_table.h: gen_tang.c tang.h
	$(CC) $(CFLAGS) -o gen_tang gen_tang.c -lmpfr -lgmp
	./gen_tang > $@

# the search: no MPFR, no GMP, no libm
htr2_fix: htr2_fix.c tang.h tang_table.h ../htrplan/dbl.h
	$(CC) $(CFLAGS) -o $@ htr2_fix.c

# the same hard cases as htr.c at m = 20 on two slices of 10^9 doubles,
# and htr.c's first hard case at m = 35
test: htr2_fix ../htrplan/htr_slice
	for s in "0x1p-2 0x1.000003e8p-2" "-0x1.000003e8p-2 -0x1p-2"; do \
	  set -- $$s; \
	  ./htr2_fix $$1 $$2 20 2>/dev/null | grep -v checks | sort > h2.out; \
	  ../htrplan/htr_slice $$1 $$2 20 | grep -v checks | sort > h1.out; \
	  cmp h1.out h2.out && echo "m = 20, [$$1, $$2): same `wc -l < h2.out` hard cases"; \
	done
	./htr2_fix 0x1p-2 0x1.0000271p-2 35 2>/dev/null

../htrplan/htr_slice:
	$(MAKE) -C ../htrplan htr_slice

clean:
	rm -f gen_tang tang_table.h htr2_fix h1.out h2.out

.PHONY: all test clean
