CC = gcc
CFLAGS = -Wall -Wextra -O3 -march=native -std=c11
LDFLAGS = -lmpfr -lgmp -lm

TARGETS = al record cheb al_miss

all: $(TARGETS)

# al: the hard-to-round search; record: dumps the first dd_exp values as a
# Rocq array (rocq/Data.v); cheb: emits the degree-7 polynomial coefficients
# for the al.c interval (rocq/Cheb.v).
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
