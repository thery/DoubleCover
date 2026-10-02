CC = gcc
CFLAGS = -Wall -Wextra -O2 -std=c11 -D_DEFAULT_SOURCE

all: test_exp100

# the constants, with MPFR; the producer is not trusted
exp100_table.h: gen_table.c exp100.h
	$(CC) $(CFLAGS) -o gen_table gen_table.c -lmpfr -lgmp -lm
	./gen_table > $@

budget: exp100_table.h
	./gen_table budget

# exp100.c alone needs no library
exp100.o: exp100.c exp100.h exp100_table.h
	$(CC) $(CFLAGS) -c exp100.c

test_exp100: test_exp100.c exp100.o
	$(CC) $(CFLAGS) -o $@ test_exp100.c exp100.o -lmpfr -lgmp

# random and boundary inputs (one process, a few seconds)
test: test_exp100
	./test_exp100

clean:
	rm -f gen_table exp100.o test_exp100

.PHONY: all budget test clean
