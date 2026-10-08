// Unverified driver of the Capla search_filter (htr_filter.b), after
// ~/git/exp-full-proof/filter/filter_main.c: reads a table file in htr.c's
// format, runs search_filter on each line and prints the kept inputs
// x0 + j u, one per line.  The external maybe_hard_bits of htr_filter.b is
// that of ../../exp100/exp100.c, which returns an int: it is renamed here
// and wrapped in a function that returns a uint64_t, as Capla expects.
// Usage: ./filter [-reduce R] FILE [ERR]   (ERR in hexadecimal, default
// 0x600000); -reduce R searches only the first N/R inputs of each line.
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#define maybe_hard_bits c_maybe_hard_bits
#include "../../exp100/exp100.c"
#undef maybe_hard_bits

uint64_t maybe_hard_bits(uint64_t xb) { return (uint64_t) c_maybe_hard_bits(xb); }

uint64_t search_filter(uint64_t *B, uint64_t m, uint64_t k, uint64_t l,
                       uint64_t n, uint64_t err, uint64_t *out, uint64_t cap,
                       uint64_t xb0, uint64_t neg);

#define CAP 4000000
#define KMAX 13                         // most coefficients in a line
#define LMAX 8                          // most words in a coefficient

int main(int argc, char *argv[]) {
  uint64_t reduce = 1;
  if (argc > 2 && strcmp(argv[1], "-reduce") == 0) {
    reduce = strtoull(argv[2], NULL, 0);
    argv += 2; argc -= 2;
  }
  if (argc < 2) { fprintf(stderr, "usage: filter [-reduce R] file [err]\n"); return 1; }
  FILE *fp = fopen(argv[1], "r");
  if (!fp) { perror(argv[1]); return 1; }
  uint64_t err = argc > 2 ? strtoull(argv[2], NULL, 16) : 0x600000;
  uint64_t B[KMAX * LMAX], *out = malloc(CAP * sizeof(uint64_t));
  double x0; uint64_t n; int k, l;
  while (fscanf(fp, "%la", &x0) == 1) {
    if (fscanf(fp, "%lu %d %d", &n, &k, &l) != 3) return 1;
    if (reduce > 1) n = n / reduce;
    assert(1 <= k && k <= KMAX && 1 <= l && l <= LMAX);
    for (int i = 0; i < k * l; i++) if (fscanf(fp, "%lx", &B[i]) != 1) return 1;
    uint64_t xb0; memcpy(&xb0, &x0, 8);
    uint64_t c = search_filter(B, k * l, k, l, n, err, out, CAP, xb0, x0 < 0);
    for (uint64_t i = 0; i < c; i++) {
      uint64_t xb = x0 < 0 ? xb0 - out[i] : xb0 + out[i];
      double x; memcpy(&x, &xb, 8); printf("%la\n", x);
    }
  }
  return 0;
}
