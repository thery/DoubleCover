CC = gcc
CFLAGS = -Wall -Wextra -O3 -march=native -std=c11
LDFLAGS = -lmpfr -lgmp -lm

TARGETS = al record

all: $(TARGETS)

# al: the hard-to-round search; record: dumps the first dd_exp values as
# a Rocq array (see rocq/Data.v).
al: al.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

record: record.c
	$(CC) $(CFLAGS) -o $@ $< $(LDFLAGS)

clean:
	rm -f $(TARGETS) *.o

.PHONY: all clean
