// Read a table file in htr.c's format and run the Capla search on each line;
// print the candidates x0 + j u, one per line, in htr.c's format.  A line is
// x0 N k l B_0 .. B_(k-1), each B_i as l 64-bit words, least significant
// first, with 1 <= k <= K and 1 <= l <= L, as htr.c.
// Usage: htr3cap FILE ERR      (ERR in hexadecimal, e.g. 0x600000)
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

uint64_t search(uint64_t *B, uint64_t m, uint64_t k, uint64_t l, uint64_t n,
                uint64_t err, uint64_t *out, uint64_t cap);

#define CAP 4000000
#define K 13                            // most coefficients in a line
#define L 8                             // most words in a coefficient

int main(int argc, char *argv[]) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s file err\n", argv[0]);
    return 1;
  }
  FILE *fp = fopen(argv[1], "r");
  uint64_t err = strtoull(argv[2], NULL, 16);
  uint64_t *B = malloc(K * L * sizeof(uint64_t));
  uint64_t *out = malloc(CAP * sizeof(uint64_t));
  double x0;
  uint64_t n;
  int k, l;
  while (fscanf(fp, "%la", &x0) == 1) {
    if (fscanf(fp, "%lu", &n) != 1) return 1;
    if (fscanf(fp, "%d", &k) != 1) return 1;
    assert(1 <= k && k <= K);
    if (fscanf(fp, "%d", &l) != 1) return 1;
    assert(1 <= l && l <= L);
    // B_i is B[i*l .. i*l + l): the k*l words of the line, in file order
    for (int i = 0; i < k * l; i++)
      if (fscanf(fp, "%lx", &B[i]) != 1) return 1;
    int e;
    frexp(x0, &e);                  // x0 = f 2^e with 1/2 <= |f| < 1
    assert(e >= -1021);             // no subnormal input, as htr.c
    double u = ldexp(1.0, e - 53);  // u = ulp(x0)
    uint64_t c = search(B, k * l, k, l, n, err, out, CAP);
    if (c > CAP) {
      fprintf(stderr, "more than %d candidates\n", CAP);
      return 1;
    }
    for (uint64_t i = 0; i < c; i++)
      printf("%la\n", x0 + out[i] * u);
  }
  fclose(fp);
  return 0;
}
