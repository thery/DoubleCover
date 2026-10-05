// Compares the Capla exp100.b with exp100.c (code/APaul/exp100) on random
// bit patterns and on doubles in the range of the tables.  Build: make.
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#define exp_encl_bits ref_exp_encl_bits
#define maybe_hard_bits ref_maybe_hard_bits
#define exp_encl ref_exp_encl
#define maybe_hard ref_maybe_hard
#include "../../exp100/exp100.c"
#undef exp_encl_bits
#undef maybe_hard_bits

extern uint64_t exp_encl_bits(uint64_t xb, uint64_t *M, int64_t *s,
                              uint64_t **T, uint64_t **C,
                              uint64_t *LN2, uint64_t *RMAX);
extern uint64_t maybe_hard_bits(uint64_t xb, uint64_t **T, uint64_t **C,
                                uint64_t *LN2, uint64_t *RMAX);

static uint64_t Tc[TAB][NL], Cc[DEG + 1][NL], L2[NL], RM[NL];
static uint64_t *Tp[TAB], *Cp[DEG + 1];

static uint64_t st = 88172645463325252ULL;
static uint64_t rnd(void) { st ^= st << 13; st ^= st >> 7; st ^= st << 17; return st; }

static long n, bad;
static void cmp(uint64_t xb) {
  uint64_t M1[3] = {0}, M2[3] = {0};
  int64_t s1 = 0, s2 = 0;
  int r1 = ref_exp_encl_bits(xb, M1, &s1);
  uint64_t r2 = exp_encl_bits(xb, M2, &s2, Tp, Cp, L2, RM);
  int h1 = ref_maybe_hard_bits(xb);
  uint64_t h2 = maybe_hard_bits(xb, Tp, Cp, L2, RM);
  n++;
  if ((uint64_t) r1 != r2 || (r1 == 0 && (memcmp(M1, M2, sizeof M1) || s1 != s2))
      || (uint64_t) h1 != h2) {
    if (bad++ < 10) printf("differ: %016llx\n", (unsigned long long) xb);
  }
}

int main(int argc, char **argv) {
  long N = argc > 1 ? atol(argv[1]) : 1000000;
  memcpy(Tc, T, sizeof Tc); memcpy(Cc, C, sizeof Cc);
  memcpy(L2, LN2, sizeof L2); memcpy(RM, RMAX, sizeof RM);
  for (int i = 0; i < TAB; i++) Tp[i] = Tc[i];
  for (int i = 0; i <= DEG; i++) Cp[i] = Cc[i];
  long hard = 0;
  for (long i = 0; i < N; i++) {
    uint64_t xb = rnd();
    if (i % 3 == 1) {           // |x| < 1024: exponent below 1033
      xb = (xb & 0x800fffffffffffffULL) | ((rnd() % 1033) << 52);
    } else if (i % 3 == 2) {    // uniform in value on (-745.14, 709.79)
      double x = -745.14 + (709.79 + 745.14) * ((rnd() >> 11) * 0x1p-53);
      memcpy(&xb, &x, 8);
    }
    cmp(xb);
    hard += ref_maybe_hard_bits(xb) == 1;
  }
  printf("%ld inputs, %ld differ, %ld maybe hard\n", n, bad, hard);
  return bad != 0;
}
