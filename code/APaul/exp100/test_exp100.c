// Tests of exp100.c against MPFR at 300 bits.
//
//   test_exp100              random and boundary inputs
//   test_exp100 FILE...      the candidates printed by htr (one hex double
//                            a line; other lines are skipped)
//
// For each x: (i) MPFR's exp(x) lies in the enclosure M 2^s +- D 2^s;
// (ii) the error |exp(x) - M 2^s| / 2^s is at most D (its maximum is
// printed); (iii) maybe_hard(x) is 1 whenever MPFR says x is hard, and 0
// whenever MPFR says x is not hard with a margin (a distance to 2^-43 of
// more than 2^-100), except where the enclosure leaves the binade open.
// Then the time of a call, on the same inputs.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <gmp.h>
#include <mpfr.h>
#include "exp100.h"

#define WP 300

static long n_in, n_fail, n_out, n_hard, n_maybe, n_unsound, n_close,
  n_disagree;
static mpfr_t maxerr;

static void check(double x) {
  uint64_t M[3];
  int64_t s;
  mpfr_t E, A, z, d;
  mpfr_inits2(WP, E, A, z, d, (mpfr_ptr) 0);
  n_in++;
  int rc = exp_encl(x, M, &s);
  int mh = maybe_hard(x);
  mpfr_set_d(E, x, MPFR_RNDN);
  mpfr_exp(E, E, MPFR_RNDN);
  if (rc) n_fail++;
  else {
    // A = M, then |E 2^-s - M|
    mpfr_set_ui(A, 0, MPFR_RNDN);
    for (int i = 2; i >= 0; i--) {
      mpfr_mul_2ui(A, A, 32, MPFR_RNDN);
      mpfr_add_ui(A, A, M[i] >> 32, MPFR_RNDN);
      mpfr_mul_2ui(A, A, 32, MPFR_RNDN);
      mpfr_add_ui(A, A, M[i] & 0xffffffffUL, MPFR_RNDN);
    }
    mpfr_mul_2si(z, E, -s, MPFR_RNDN);
    mpfr_sub(z, z, A, MPFR_RNDN);
    mpfr_abs(z, z, MPFR_RNDN);
    if (mpfr_cmp(z, maxerr) > 0) mpfr_set(maxerr, z, MPFR_RNDN);
    if (mpfr_cmp_ui(z, EXP100_D) > 0) {
      n_out++;
      printf("OUT OF THE ENCLOSURE: %a\n", x);
    }
  }
  // the exact decision: e the binade, z = exp(x)/v, d its distance to Z
  long e = mpfr_get_exp(E) - 1;
  long ve = (e > EMIN ? e : EMIN) - PREC;
  mpfr_mul_2si(z, E, -ve, MPFR_RNDN);
  mpfr_rint(d, z, MPFR_RNDN);
  mpfr_sub(d, z, d, MPFR_RNDN);
  mpfr_abs(d, d, MPFR_RNDN);
  mpfr_set_ui_2exp(A, 1, -M_HARD, MPFR_RNDN);
  int hard = mpfr_cmp(d, A) < 0;
  mpfr_sub(A, d, A, MPFR_RNDN);
  mpfr_abs(A, A, MPFR_RNDN);
  int clear = mpfr_cmp_ui_2exp(A, 1, -100) > 0;
  if (hard) n_hard++;
  if (mh) n_maybe++;
  if (!clear) n_close++;
  if (hard && !mh) {
    n_unsound++;
    printf("UNSOUND: %a is hard, maybe_hard says 0\n", x);
  }
  if (clear && !hard && mh) n_disagree++;
  mpfr_clears(E, A, z, d, (mpfr_ptr) 0);
}

static double *inputs;
static long n_inputs, cap_inputs;

static void add(double x) {
  if (n_inputs == cap_inputs) {
    cap_inputs = cap_inputs ? 2 * cap_inputs : 1024;
    inputs = realloc(inputs, cap_inputs * sizeof(double));
  }
  inputs[n_inputs++] = x;
}

union bits { double d; uint64_t u; };

static double from_bits(uint64_t u) {
  union bits b;
  b.u = u;
  return b.d;
}

static uint64_t to_bits(double x) {
  union bits b;
  b.d = x;
  return b.u;
}

static uint64_t rnd64(void) {
  static uint64_t st = 0x9e3779b97f4a7c15UL;   // xorshift64*, fixed seed
  st ^= st >> 12; st ^= st << 25; st ^= st >> 27;
  return st * 0x2545f4914f6cdd1dUL;
}

static int in_range(double x) { return x > -745.14 && x < 709.79; }

// a random double with biased exponent in [lo, hi], random sign
static double rnd_expo(int lo, int hi) {
  uint64_t be = lo + rnd64() % (hi - lo + 1);
  uint64_t u = (rnd64() & 0x800fffffffffffffUL) | (be << 52);
  return from_bits(u);
}

static void random_inputs(long n) {
  long k = 0;
  while (k < n) {
    double x;
    switch (k % 3) {
    case 0:                  // uniform in value
      x = -745.14 + (709.79 + 745.14) * ((rnd64() >> 11) * 0x1p-53);
      break;
    case 1:                  // every binade of the normal doubles
      x = rnd_expo(1, 1023 + 9);
      break;
    default:                 // |x| in [2^-60, 2^10)
      x = rnd_expo(1023 - 60, 1023 + 9);
      break;
    }
    if (to_bits(x) << 1 >> 53 == 0 || !in_range(x)) continue;
    add(x);
    k++;
  }
}

// x and its neighbours, 8 doubles on each side
static void around(double x) {
  uint64_t u = to_bits(x);
  for (int d = -8; d <= 8; d++) {
    double y = from_bits(u + d);
    if (in_range(y) && to_bits(y) << 1 >> 53 != 0) add(y);
  }
}

static void boundary_inputs(void) {
  mpfr_t t;
  mpfr_init2(t, WP);
  around(-745.14);
  around(-745.13);
  around(-0x1.74910d52d3051p+9);       // -745.133...: exp(x) near 2^-1075
  around(-0x1.6232bdd7abcd2p+9);       // exp(x) near 2^-1022
  around(709.78);
  around(0x1.62e42fefa39efp+9);        // log(DBL_MAX)
  around(709.79);
  around(0x1p-53); around(-0x1p-53);
  around(0x1p-54); around(-0x1p-54);
  around(1.0); around(-1.0);
  around(0x1p-1022); around(-0x1p-1022);
  around(0x1p-60); around(-0x1p-60);
  // zero and subnormal x are accepted too
  add(0.0); add(-0.0); add(0x1p-1074); add(-0x1p-1074);
  add(0x1.fffffffffffffp-1023); add(-0x1.fffffffffffffp-1023);
  // the doubles nearest k ln2 / 64, k = -68800 .. 65500
  for (long k = -68800; k <= 65500; k += (k > -100 && k < 100) ? 1 : 37) {
    mpfr_const_log2(t, MPFR_RNDN);
    mpfr_mul_si(t, t, k, MPFR_RNDN);
    mpfr_div_ui(t, t, 64, MPFR_RNDN);
    double x = mpfr_get_d(t, MPFR_RNDN);
    if (k != 0) around(x);
  }
  mpfr_clear(t);
}

static void file_inputs(const char *name) {
  FILE *f = fopen(name, "r");
  char line[256];
  if (!f) { perror(name); exit(1); }
  while (fgets(line, sizeof line, f)) {
    if (strncmp(line, "0x", 2) && strncmp(line, "-0x", 3)) continue;
    add(strtod(line, NULL));
  }
  fclose(f);
}

static double now(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

static void run(const char *what) {
  n_in = n_fail = n_out = n_hard = n_maybe = n_unsound = n_close =
    n_disagree = 0;
  mpfr_set_ui(maxerr, 0, MPFR_RNDN);
  for (long i = 0; i < n_inputs; i++) check(inputs[i]);
  // the time of a call
  uint64_t M[3], acc = 0;
  int64_t s;
  double t0 = now();
  for (long i = 0; i < n_inputs; i++) {
    exp_encl(inputs[i], M, &s);
    acc += M[0];
  }
  double t1 = now();
  for (long i = 0; i < n_inputs; i++) acc += maybe_hard(inputs[i]);
  double t2 = now();
  printf("%s: %ld inputs, %ld rejected, %ld outside the enclosure,"
         " max error %.4f (D = %d)\n", what, n_in, n_fail, n_out,
         mpfr_get_d(maxerr, MPFR_RNDU), EXP100_D);
  printf("  MPFR: %ld hard, %ld within 2^-100 of the threshold;"
         " maybe_hard: %ld say 1, %ld unsound, %ld clear non-hard say 1\n",
         n_hard, n_close, n_maybe, n_unsound, n_disagree);
  printf("  time: exp_encl %.3f us, maybe_hard %.3f us (%lu)\n",
         1e6 * (t1 - t0) / n_in, 1e6 * (t2 - t1) / n_in,
         (unsigned long) (acc & 1));
}

int main(int argc, char **argv) {
  mpfr_init2(maxerr, 53);
  int bad = 0;
  if (argc == 1) {
    // rejected: |x| >= 1024, infinities, NaN
    double rej[] = { 1024.0, -1024.0, 1e300, -1e300, 1.0 / 0.0, -1.0 / 0.0,
                     0.0 / 0.0 };
    uint64_t M[3];
    int64_t s;
    int nrej = 0;
    for (int i = 0; i < 7; i++)
      nrej += exp_encl(rej[i], M, &s) != 0 && maybe_hard(rej[i]) == 1;
    printf("rejected: %d of 7 (|x| >= 1024, infinities, NaN)\n", nrej);
    bad |= nrej != 7;
    random_inputs(100000);
    run("random");
    bad |= n_fail || n_out || n_unsound;
    n_inputs = 0;
    boundary_inputs();
    run("boundaries");
    bad |= n_fail || n_out || n_unsound;
  }
  for (int i = 1; i < argc; i++) {
    n_inputs = 0;
    file_inputs(argv[i]);
    run(argv[i]);
    bad |= n_fail || n_out || n_unsound;
  }
  printf(bad ? "FAILED\n" : "passed\n");
  return bad;
}
