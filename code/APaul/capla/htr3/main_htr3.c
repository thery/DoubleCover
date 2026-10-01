// Read a table file in htr3.c's format (x0 n B_0 .. B_(k-1), each B_i as l
// 64-bit words, least significant first) and run the Capla search on each
// line; print the candidates x0 + j u, one per line, in htr3.c's format.
// Usage: htr3cap FILE K L ERR      (ERR in hexadecimal, e.g. 0x400001)
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

uint64_t search(uint64_t *B, uint64_t m, uint64_t k, uint64_t l, uint64_t n,
                uint64_t err, uint64_t *out, uint64_t cap);

#define CAP 4000000

int main(int argc, char *argv[]) {
  if (argc != 5) {
    fprintf(stderr, "usage: %s file k l err\n", argv[0]);
    return 1;
  }
  FILE *fp = fopen(argv[1], "r");
  uint64_t k = strtoull(argv[2], NULL, 10), l = strtoull(argv[3], NULL, 10);
  uint64_t err = strtoull(argv[4], NULL, 16);
  uint64_t *B = malloc(k * l * sizeof(uint64_t));
  uint64_t *out = malloc(CAP * sizeof(uint64_t));
  double x0;
  uint64_t n;
  while (fscanf(fp, "%la", &x0) == 1) {
    if (fscanf(fp, "%lu", &n) != 1) return 1;
    for (uint64_t i = 0; i < k * l; i++)
      if (fscanf(fp, "%lx", &B[i]) != 1) return 1;
    int e;
    frexp(x0, &e);                  // x0 = f 2^e with 1/2 <= |f| < 1
    assert(e >= -1021);             // no subnormal input, as htr3_new.c
    double u = ldexp(1.0, e - 53);  // u = ulp(x0)
    uint64_t c = search(B, k * l, k, l, n, err, out, CAP);
    if (c > CAP) { fprintf(stderr, "more than %d candidates\n", CAP); return 1; }
    for (uint64_t i = 0; i < c; i++)
      printf("%la\n", x0 + out[i] * u);
  }
  fclose(fp);
  return 0;
}
