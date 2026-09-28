// htr2: search hard-to-round cases of exp in [x0, x1), following Paul
// Zimmermann's note doc/htr.md.
//
// The range is cut into subranges of at most NSUB consecutive doubles
// x0 + j u.  On a subrange, exp(x0 + j u) / v is its Taylor polynomial of
// degree k-1 in j, plus a remainder r / v; each coefficient is reduced
// modulo 1 and kept as an l-word integer A_i (words of 64 bits), and the
// polynomial is walked with a table of differences, exactly, modulo
// 2^(64 l).  The window E covers the target 2^-m, the remainder and the
// rounding of the A_i: there is no drift.  MPFR is used for the A_i, for
// E, and to check each candidate.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <math.h>
#include <gmp.h>
#include <mpfr.h>

#define LMAX 8           // at most 8 words of 64 bits
#define KMAX 24          // at most degree 23
#define NSUB 0x1p32      // at most 2^32 doubles a subrange
#define RSLACK 1         // the remainder is at most 2^-(m + RSLACK)
#define CSLACK 20        // the rounding of the A_i is at most 2^-(m + CSLACK)

static int L;                          // words of the integers
static int K;                          // number of coefficients, degree K-1
static uint64_t B[KMAX][LMAX];         // the table of differences
static uint64_t twoE[LMAX];            // 2 E

static unsigned long checks = 0, found = 0;
static int print_all = 0;

// htr.c's ref_exp: exp(x) rounded toward zero, for its exponent
static double
ref_exp (double x)
{
  mpfr_t y;
  mpfr_exp_t emin = mpfr_get_emin ();
  mpfr_set_emin (-1073);
  mpfr_init2 (y, 53);
  mpfr_set_d (y, x, MPFR_RNDN);
  int inex = mpfr_exp (y, y, MPFR_RNDZ);
  mpfr_subnormalize (y, inex, MPFR_RNDZ);
  double ret = mpfr_get_d (y, MPFR_RNDN);
  mpfr_clear (y);
  mpfr_set_emin (emin);
  return ret;
}

// htr.c's check: is x hard to round at level m
static void
check (double x, int m)
{
  checks ++;
  if (print_all) printf ("c %la\n", x);
  mpfr_t y, z;
  mpfr_init2 (y, 54);
  mpfr_init2 (z, 53 + m);
  mpfr_set_d (y, x, MPFR_RNDN);
  mpfr_exp (z, y, MPFR_RNDN);
  mpfr_set (y, z, MPFR_RNDN);
  if (mpfr_cmp (y, z) == 0) {
    printf ("%la\n", x);
    found ++;
  }
  mpfr_clear (y);
  mpfr_clear (z);
}

// a += b modulo 2^(64 L)
static inline void
add (uint64_t *a, const uint64_t *b)
{
  unsigned __int128 c = 0;
  for (int w = 0; w < L; w++) {
    c += (unsigned __int128) a[w] + b[w];
    a[w] = (uint64_t) c;
    c >>= 64;
  }
}

// a -= b modulo 2^(64 L)
static inline void
sub (uint64_t *a, const uint64_t *b)
{
  uint64_t borrow = 0;
  for (int w = 0; w < L; w++) {
    uint64_t t = a[w] - b[w] - borrow;
    borrow = (a[w] < b[w]) || (a[w] == b[w] && borrow);
    a[w] = t;
  }
}

// a <= b, both read as nonnegative
static inline int
le (const uint64_t *a, const uint64_t *b)
{
  for (int w = L - 1; w >= 0; w--)
    if (a[w] != b[w]) return a[w] < b[w];
  return 1;
}

// the L words of z mod 2^(64 L), lowest first
static void
to_words (uint64_t *a, mpz_t z)
{
  mpz_t t;
  mpz_init (t);
  mpz_fdiv_r_2exp (t, z, 64 * L);
  for (int w = 0; w < L; w++) {
    a[w] = 0;
    for (int h = 1; h >= 0; h--) {             // two halves of 32 bits
      mpz_t q;
      mpz_init (q);
      mpz_fdiv_q_2exp (q, t, 64 * w + 32 * h);
      mpz_fdiv_r_2exp (q, q, 32);
      a[w] = (a[w] << 32) | mpz_get_ui (q);
      mpz_clear (q);
    }
  }
  mpz_clear (t);
}

// The main loop on the n doubles x0 + j u, with k and l known at compile
// time: walk is always inlined, and called only with constants, so the
// compiler unrolls the loops on i and w and keeps the table in registers.
static inline __attribute__ ((always_inline)) void
walk (const int k, const int l, double x0, double u, uint64_t n, int m)
{
  uint64_t b[KMAX][LMAX], t[LMAX];
  for (int i = 0; i < k; i++)
    for (int w = 0; w < l; w++) b[i][w] = B[i][w];
  for (int w = 0; w < l; w++) t[w] = twoE[w];
  for (uint64_t j = 0; j < n; j++) {
    int below = 1;                             // b[0] <= 2 E
    for (int w = l - 1; w >= 0; w--)
      if (b[0][w] != t[w]) { below = b[0][w] < t[w]; break; }
    if (__builtin_expect (below, 0))
      check (x0 + j * u, m);
    for (int i = 0; i < k - 1; i++) {          // b[i] += b[i + 1]
      unsigned __int128 c = 0;
      for (int w = 0; w < l; w++) {
        c += (unsigned __int128) b[i][w] + b[i + 1][w];
        b[i][w] = (uint64_t) c;
        c >>= 64;
      }
    }
  }
}

// the bound r / v <= exp(xe) (n u)^k / k! / v, rounded up; xe = x0 + n u
static void
rbound (mpfr_t r, double x0, uint64_t n, int e0, int e, int k)
{
  mpfr_t t;
  mpfr_init2 (t, 64);
  mpfr_init2 (r, 64);
  mpfr_set_d (t, x0, MPFR_RNDU);
  mpfr_set_ui_2exp (r, n, e0 - 53, MPFR_RNDU); // n u
  mpfr_add (t, t, r, MPFR_RNDU);               // xe
  mpfr_exp (t, t, MPFR_RNDU);                  // exp(xe)
  mpfr_pow_ui (r, r, k, MPFR_RNDU);            // (n u)^k
  mpfr_mul (r, r, t, MPFR_RNDU);
  mpfr_fac_ui (t, k, MPFR_RNDD);
  mpfr_div (r, r, t, MPFR_RNDU);
  mpfr_mul_2si (r, r, -(e - 54), MPFR_RNDU);   // / v
  mpfr_clear (t);
}

// search the n doubles x0 + j u, 0 <= j < n; e0 is the exponent of x0 and
// e that of exp(x0)
static void
subrange (double x0, uint64_t n, int e0, int e, int m)
{
  // K: the smallest degree + 1 whose remainder is at most 2^-(m + RSLACK)
  mpfr_t r;
  for (K = 2; ; K++) {
    assert (K <= KMAX);
    rbound (r, x0, n, e0, e, K);
    if (mpfr_cmp_ui_2exp (r, 1, -(m + RSLACK)) <= 0) break;
    mpfr_clear (r);
  }
  // L: the fewest words making (1 + n + ... + n^(K-1)) 2^(-64 L) at most
  // 2^-(m + CSLACK)
  double lg = (K - 1) * log2 ((double) n) + log2 ((double) K);
  L = (int) ceil ((lg + m + CSLACK) / 64);
  assert (L <= LMAX);
  // the A_i: frac (exp(x0) u^i / i! / v), to 64 L bits after the point
  int prec = 64 * L + 128;
  mpfr_t t, a, f;
  mpfr_inits2 (prec, t, a, f, (mpfr_ptr) 0);
  mpfr_set_d (t, x0, MPFR_RNDN);
  mpfr_exp (t, t, MPFR_RNDN);
  mpfr_mul_2si (t, t, -(e - 54), MPFR_RNDN);   // exp(x0) / v, about 2^54
  mpz_t A[KMAX], z, p;
  mpz_init (z);
  mpz_init (p);
  for (int i = 0; i < K; i++) {
    mpfr_mul_2si (a, t, i * (e0 - 53), MPFR_RNDN); // times u^i
    mpfr_fac_ui (f, i, MPFR_RNDN);
    mpfr_div (a, a, f, MPFR_RNDN);             // / i!
    mpfr_frac (a, a, MPFR_RNDN);
    mpfr_mul_2ui (a, a, 64 * L, MPFR_RNDN);
    mpz_init (A[i]);
    mpfr_get_z (A[i], a, MPFR_RNDN);
  }
  // B_i = sum_m A_m i^m, then the table of differences
  for (int i = 0; i < K; i++) {
    mpz_set_ui (z, 0);
    for (int d = K - 1; d >= 0; d--) {         // Horner in i
      mpz_mul_ui (z, z, i);
      mpz_add (z, z, A[d]);
    }
    to_words (B[i], z);
  }
  for (int i = 1; i < K; i++)
    for (int j = K - 1; j >= i; j--)
      sub (B[j], B[j - 1]);
  // E = ceil (2^(64 L) (2^-m + r/v + (1 + n + ... + n^(K-1)) 2^(-64 L)))
  mpfr_set_ui_2exp (a, 1, -m, MPFR_RNDU);
  mpfr_add (a, a, r, MPFR_RNDU);
  mpfr_mul_2ui (a, a, 64 * L, MPFR_RNDU);
  mpz_set_ui (z, 1);
  mpz_set_ui (p, 1);
  for (int i = 1; i < K; i++) {
    mpz_mul_ui (p, p, n);
    mpz_add (z, z, p);
  }
  mpfr_add_z (a, a, z, MPFR_RNDU);
  mpfr_get_z (z, a, MPFR_RNDU);
  mpz_mul_2exp (p, z, 1);                      // 2 E
  assert (mpz_sizeinbase (p, 2) < (size_t) (64 * L));
  to_words (twoE, p);
  uint64_t Ew[LMAX];
  to_words (Ew, z);
  add (B[0], Ew);                              // B_0 + E
  for (int i = 0; i < K; i++) mpz_clear (A[i]);
  mpz_clear (z);
  mpz_clear (p);
  mpfr_clears (t, a, f, r, (mpfr_ptr) 0);
  fprintf (stderr, "subrange %la: n = %lu, k = %d, l = %d\n",
           x0, (unsigned long) n, K, L);
  // the main loop
  double u = ldexp (1.0, e0 - 53);
  switch (16 * K + L) {
#define CASE(k, l) case 16 * k + l: walk (k, l, x0, u, n, m); return;
    CASE (2, 1) CASE (2, 2) CASE (3, 1) CASE (3, 2) CASE (3, 3)
    CASE (4, 2) CASE (4, 3) CASE (4, 4) CASE (5, 2) CASE (5, 3) CASE (5, 4)
    CASE (6, 3) CASE (6, 4) CASE (6, 5) CASE (7, 3) CASE (7, 4) CASE (7, 5)
    CASE (8, 4) CASE (8, 5) CASE (8, 6) CASE (9, 5) CASE (9, 6)
#undef CASE
  }
  for (uint64_t j = 0; j < n; j++) {           // any other k and l
    if (__builtin_expect (le (B[0], twoE), 0))
      check (x0 + j * u, m);
    for (int i = 0; i < K - 1; i++)
      add (B[i], B[i + 1]);
  }
}

// search hard-to-round cases of exp in [x0, x1)
// with at least m identical bits after round bit
static void
search (double x0, double x1, int m)
{
  int e, e0, e1;
  // x0 and x1 in one binade, and so exp(x0) and exp(x1)
  frexp (x0, &e0);
  frexp (nextafter (x1, x0), &e1);
  assert (e0 == e1);
  frexp (ref_exp (x0), &e);
  frexp (ref_exp (nextafter (x1, x0)), &e1);
  assert (e == e1);
  double u = ldexp (1.0, e0 - 53);
  double x = x0;
  while (x < x1) {
    double nd = (x1 - x) / u;                  // exact in one binade
    uint64_t n = nd < NSUB ? (uint64_t) nd : (uint64_t) NSUB;
    subrange (x, n, e0, e, m);
    x += n * u;
  }
}

int
main (int argc, char *argv[])
{
  double x0 = 0.25, x1 = 0.25001;
  int m = 35;
  if (argc >= 4) {
    x0 = strtod (argv[1], NULL);
    x1 = strtod (argv[2], NULL);
    m = atoi (argv[3]);
  }
  print_all = argc > 4 && strcmp (argv[4], "-c") == 0;
  search (x0, x1, m);
  printf ("%lu checks, found %lu hard-to-round\n", checks, found);
  return 0;
}
