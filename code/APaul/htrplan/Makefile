CC = gcc
CFLAGS = -Wall -Wextra -O3 -march=native -std=c11 -D_DEFAULT_SOURCE
LDFLAGS = -lmpfr -lgmp -lm

all: htrp

fix_table.h: gen_fix.c fix.h
	$(CC) $(CFLAGS) -o gen_fix gen_fix.c $(LDFLAGS)
	./gen_fix > $@

htrp: main.c search.c search.h eval.h eval_mpfr.c eval_fix.c fix.h fix_table.h
	$(CC) $(CFLAGS) -o $@ main.c search.c eval_mpfr.c eval_fix.c $(LDFLAGS)

# the three programs on a slice of 10000 chunks around the first hard case:
# htr.c's own search, Program 2 with MPFR, Program 3; all three must print
# the same candidates
X0 = 0x1p-2
X1 = 0x1.0000271p-2
test: htrp htr_slice
	./htr_slice $(X0) $(X1) 35 -c > p1.out
	./htrp mpfr $(X0) $(X1) 35 -c > p2.out
	./htrp fix $(X0) $(X1) 35 -c > p3.out
	cmp p1.out p2.out && cmp p1.out p3.out && tail -1 p3.out

# htr.c itself, with its interval and its candidates on the command line
htr_slice: ../htr.c
	sed -e 's/^  checks ++;/  checks ++; if (print_all) printf ("c %la\\n", x);/' \
	    -e 's/^int main()/int print_all; int main(int argc, char *argv[])/' \
	    -e 's/^  double x0 = 0.25, x1 = 0.25001;/  double x0 = strtod (argv[1], 0), x1 = strtod (argv[2], 0); print_all = argc > 4;/' \
	    -e 's/^  int m = 35;/  int m = atoi (argv[3]);/' \
	    -e 's/^#include <stdio.h>/#include <stdio.h>\n#include <stdlib.h>/' \
	    -e 's/^unsigned long checks/int print_all; unsigned long checks/' \
	    $< > htr_slice.c
	$(CC) $(CFLAGS) -o $@ htr_slice.c $(LDFLAGS)

clean:
	rm -f gen_fix htrp htr_slice htr_slice.c p1.out p2.out p3.out

.PHONY: all test clean
