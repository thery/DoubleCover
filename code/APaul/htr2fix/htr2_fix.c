// htr2_fix: the search of doc/htr.md (Zimmermann) with no MPFR: every
// value of exp comes from a Tang evaluator on fixed-size integers, at 448
// bits.  Self-contained: no GMP, no MPFR, no libm; only the driver (main)
// uses libc, to read its arguments and print.
//
// The range is cut into subranges of at most NSUB consecutive doubles
// x0 + j u.  On a subrange, exp(x0 + j u) / v is its Taylor polynomial of
// degree k-1 in j, plus a remainder; each coefficient is reduced modulo 1
// and kept as an l-word integer A_i (words of 64 bits), and the polynomial
// is walked with a table of differences, exactly, modulo 2^(64 l).  The
// window E covers the target 2^-m, the remainder and the rounding of the
// A_i.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "../htrplan/dbl.h"
#include "tang.h"
#include "tang_table.h"

// ---------------------------------------------------------------------
// The integers: TG_NL limbs of 32 bits, lowest first.  Every operation is
// modulo 2^(32 TG_NL), so a signed number is in two's complement.

typedef uint32_t num[TG_NL];

static void
num_set (num r, const num a)
{
  for (int k = 0; k < TG_NL; k++) r[k] = a[k];
}

// r = v, for 0 <= v < 2^64
static void
num_set_u64 (num r, uint64_t v)
{
  for (int k = 0; k < TG_NL; k++) r[k] = 0;
  r[0] = (uint32_t) v;
  r[1] = (uint32_t) (v >> 32);
}

static void
num_add (num r, const num a, const num b)
{
  uint64_t c = 0;
  for (int k = 0; k < TG_NL; k++) {
    c += (uint64_t) a[k] + b[k];
    r[k] = (uint32_t) c;
    c >>= 32;
  }
}

static void
num_sub (num r, const num a, const num b)
{
  uint64_t c = 1;                              // a - b = a + ~b + 1
  for (int k = 0; k < TG_NL; k++) {
    c += (uint64_t) a[k] + (uint32_t) ~b[k];
    r[k] = (uint32_t) c;
    c >>= 32;
  }
}

static void
num_neg (num r, const num a)
{
  num z = { 0 };
  num_sub (r, z, a);
}

static int
num_isneg (const num a)
{
  return a[TG_NL - 1] >> 31;
}

// the sign of a - b, both read as nonnegative
static int
num_cmp (const num a, const num b)
{
  for (int k = TG_NL - 1; k >= 0; k--)
    if (a[k] != b[k]) return a[k] < b[k] ? -1 : 1;
  return 0;
}

// the number of bits of a >= 0; 0 for a = 0
static int
num_bitlen (const num a)
{
  for (int k = TG_NL - 1; k >= 0; k--)
    if (a[k]) {
      int b = 32;
      while (!(a[k] >> (b - 1))) b--;
      return 32 * k + b;
    }
  return 0;
}

// r = a 2^s, for a >= 0; the result must fit
static void
num_shl (num r, const num a, int s)
{
  assert (num_bitlen (a) + s < 32 * TG_NL);
  num t = { 0 };
  int q = s / 32, b = s % 32;
  for (int k = TG_NL - 1; k >= q; k--) {
    uint64_t v = (uint64_t) a[k - q] << b;
    if (k - q - 1 >= 0 && b) v |= a[k - q - 1] >> (32 - b);
    t[k] = (uint32_t) v;
  }
  num_set (r, t);
}

// r = floor (p / 2^s) for p >= 0 of n limbs, whose quotient fits in
// TG_NL limbs; returns 1 when the bits dropped are not all 0
static int
limbs_shr (num r, const uint32_t *p, int n, int s)
{
  int q = s / 32, b = s % 32, nz = 0;
  for (int k = 0; k < q && k < n; k++) nz |= p[k] != 0;
  if (b && q < n) nz |= (p[q] & ((1u << b) - 1)) != 0;
  for (int k = 0; k < TG_NL; k++) {
    uint64_t v = k + q < n ? p[k + q] >> b : 0;
    if (b && k + q + 1 < n) v |= (uint64_t) p[k + q + 1] << (32 - b);
    r[k] = (uint32_t) v;
  }
  if (TG_NL + q < n) assert ((p[TG_NL + q] >> b) == 0);
  for (int k = TG_NL + q + 1; k < n; k++) assert (p[k] == 0);
  return nz;
}

// r = floor (a b / 2^s), for a, b >= 0; returns 1 when the bits dropped
// are not all 0
static int
num_mulshr (num r, const num a, const num b, int s)
{
  uint32_t p[2 * TG_NL] = { 0 };
  for (int i = 0; i < TG_NL; i++) {
    uint64_t c = 0;
    for (int j = 0; j < TG_NL; j++) {
      c += (uint64_t) a[i] * b[j] + p[i + j];
      p[i + j] = (uint32_t) c;
      c >>= 32;
    }
    p[i + TG_NL] = (uint32_t) c;
  }
  return limbs_shr (r, p, 2 * TG_NL, s);
}

// r = floor (a b / 2^s), for a >= 0 and b of any sign
static void
num_mulshr_s (num r, const num a, const num b, int s)
{
  if (!num_isneg (b)) {
    num_mulshr (r, a, b, s);
    return;
  }
  num mb, one;
  num_neg (mb, b);
  int nz = num_mulshr (r, a, mb, s);           // floor (-v) = -(ceil v)
  num_set_u64 (one, nz);
  num_add (r, r, one);
  num_neg (r, r);
}

// r = floor (a / d), for a >= 0 and 0 < d < 2^32
static void
num_divu (num r, const num a, uint32_t d)
{
  uint64_t rem = 0;
  for (int k = TG_NL - 1; k >= 0; k--) {
    uint64_t v = (rem << 32) | a[k];
    r[k] = (uint32_t) (v / d);
    rem = v % d;
  }
}

// r = 2^s - 1, for 0 <= s < 32 TG_NL
static void
num_mask (num r, int s)
{
  num one;
  num_set_u64 (one, 1);
  num_shl (r, one, s);
  num_sub (r, r, one);
}

// ---------------------------------------------------------------------
// Tang's scheme: exp(x) = y 2^(k - TG_P), within 2^-TG_ERR relative.

static num C[TG_DEG + 1];     // 1/i!, rounded down
static num rmax;              // bound on |r|: 181/256 2^-9 < 2^-9.5
static num erry;              // bound on the error of y, in units of y

static void
tang_init (void)
{
  num_set_u64 (C[0], 1);
  num_shl (C[0], C[0], TG_P);
  for (int i = 1; i <= TG_DEG; i++)           // floor (floor (a/b) / c)
    num_divu (C[i], C[i - 1], i);             //   = floor (a / (b c))
  num_set_u64 (rmax, 181);
  num_shl (rmax, rmax, TG_P - 17);
  num_set_u64 (erry, 1);                      // y < 2^(TG_P + 1)
  num_shl (erry, erry, TG_P + 1 - TG_ERR);
}

// returns k; y is not within erry of a power of 2, so y 2^(k - TG_P) and
// exp(x) have the same exponent
static long
tang (num y, double x)
{
  num X, r, t, u;
  // |x| = m 2^(be - 1075) from the bits of x; X = |x| 2^TG_P, exactly
  union dbits b;
  b.d = x;
  int neg = b.u >> 63, be = (b.u >> 52) & 0x7ff;
  uint64_t mx = b.u & ((1ul << 52) - 1);
  assert (be != 0 || mx == 0);                 // x is 0 or normal
  if (be) mx |= 1ul << 52;
  int sh = be - 1075 + TG_P;
  assert (be == 0 || sh >= 0);
  num_set_u64 (X, mx);
  if (be) num_shl (X, X, sh);
  // N = floor (|x| 256/ln2 + 1/2) = (floor (2 |x| 256/ln2) + 1) / 2
  num_mulshr (t, X, tg_inv, TG_P + TG_LG - 1);
  long N = (long) (((uint64_t) t[0] | (uint64_t) t[1] << 32) + 1) >> 1;
  if (neg) { N = -N; num_neg (X, X); }
  // r = x - N ln2/256, checked small
  num_set_u64 (u, N < 0 ? -N : N);
  int nz = num_mulshr (t, tg_ln2, u, TG_LG);  // floor (|N| ln2/256)
  if (N < 0) {                                 // floor (-v) = -(ceil v)
    num_set_u64 (u, nz);
    num_add (t, t, u);
    num_neg (t, t);
  }
  num_sub (r, X, t);
  if (num_isneg (r)) num_neg (t, r); else num_set (t, r);
  assert (num_cmp (t, rmax) < 0);
  // exp(r) by Horner's rule, one truncation per product
  num_set (y, C[TG_DEG]);
  for (int i = TG_DEG - 1; i >= 0; i--) {
    num_mulshr_s (y, y, r, TG_P);
    num_add (y, y, C[i]);
  }
  assert (!num_isneg (y));
  // times 2^(j/256)
  long j = ((N % TG_TAB) + TG_TAB) % TG_TAB;
  num_mulshr (y, y, tg_T[j], TG_P);
  num_sub (t, y, erry);
  num_add (u, y, erry);
  assert (num_bitlen (t) == num_bitlen (u));
  return (N - j) / TG_TAB;
}

// the exponent e of exp(x): 2^(e-1) <= exp(x) < 2^e
static int
tang_expo (double x)
{
  num y;
  long k = tang (y, x);
  return num_bitlen (y) + k - TG_P;
}

// ---------------------------------------------------------------------
// The check of a candidate: is dist (exp(x) 2^(54-e), Z) < 2^-m?  The top
// 54 bits of y are the integer part of exp(x) 2^(54-e), the other f bits
// its fraction.  Returns 1 (hard), 0 (not hard), or 2 (undecided).

static unsigned long checks = 0, found = 0, undecided = 0;
static int print_all = 0;

static void
check (double x, int m)
{
  num y, hi, lo, d, t;
  tang (y, x);
  int f = num_bitlen (y) - 54;
  limbs_shr (hi, y, TG_NL, f);
  num_shl (hi, hi, f);
  num_sub (lo, y, hi);                         // the fraction, times 2^f
  num_set_u64 (t, 1);
  num_shl (t, t, f);
  num_sub (d, t, lo);                          // distance to the next integer
  if (num_cmp (lo, d) < 0) num_set (d, lo);    // d = the distance, times 2^f
  num_set_u64 (t, 1);
  num_shl (t, t, f - m);                       // the threshold 2^-m, times 2^f
  int v;
  num_add (hi, d, erry);
  if (num_cmp (hi, t) < 0) v = 1;
  else {
    num_sub (hi, d, erry);
    v = num_cmp (hi, t) >= 0 ? 0 : 2;
  }
  checks ++;
  if (print_all) printf ("c %la\n", x);
  if (v == 1) { printf ("%la\n", x); found ++; }
  else if (v == 2) { printf ("u %la\n", x); undecided ++; }
}

// ---------------------------------------------------------------------
// The table of differences, on L words of 64 bits, modulo 2^(64 L).

#define LMAX 5           // A_i to at most 320 bits: 64 LMAX + 54 + 20 <= TG_ERR
#define KMAX 9           // degree at most 8
#define NSUB 0x1p32      // at most 2^32 doubles a subrange
#define RSLACK 1         // the remainder is at most 2^-(m + RSLACK)
#define CSLACK 20        // the rounding of the A_i is at most 2^-(m + CSLACK)

static int L, K;
static uint64_t B[KMAX][LMAX], twoE[LMAX];

// the L words of a >= 0 modulo 2^(64 L), lowest first
static void
to_words (uint64_t *w, const num a)
{
  for (int i = 0; i < L; i++)
    w[i] = (uint64_t) a[2 * i] | (uint64_t) a[2 * i + 1] << 32;
}

static void
w_add (uint64_t *a, const uint64_t *b)
{
  unsigned __int128 c = 0;
  for (int w = 0; w < L; w++) {
    c += (unsigned __int128) a[w] + b[w];
    a[w] = (uint64_t) c;
    c >>= 64;
  }
}

static void
w_sub (uint64_t *a, const uint64_t *b)
{
  uint64_t borrow = 0;
  for (int w = 0; w < L; w++) {
    uint64_t t = a[w] - b[w] - borrow;
    borrow = (a[w] < b[w]) || (a[w] == b[w] && borrow);
    a[w] = t;
  }
}

// a = a q + b, for a small q
static void
w_muladd (uint64_t *a, uint64_t q, const uint64_t *b)
{
  unsigned __int128 c = 0;
  for (int w = 0; w < L; w++) {
    c += (unsigned __int128) a[w] * q + b[w];
    a[w] = (uint64_t) c;
    c >>= 64;
  }
}

// the main loop on n doubles x0 + j u, with k and l known at compile time
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

static int
bitlen64 (uint64_t v)
{
  int b = 0;
  while (v) { b++; v >>= 1; }
  return b;
}

// search the n doubles x0 + j u, 0 <= j < n; e0 is the exponent of x0 and
// e that of exp(x0)
static void
subrange (double x0, uint64_t n, int e0, int e, int m)
{
  double u = pow2 (e0 - 53);
  // K: the smallest degree + 1 with 2^54 (n u)^K / K! <= 2^-(m + RSLACK)
  double nu = (double) n * u, val = pow2 (54);
  for (K = 1; ; K++) {
    val = val * nu / K;
    if (K >= 2 && val <= pow2 (-(m + RSLACK))) break;
    assert (K < KMAX);
  }
  // L: the fewest words making 2 (1 + n + ... + n^(K-1)) 2^(-64 L) at most
  // 2^-(m + CSLACK)
  L = ((K - 1) * bitlen64 (n) + bitlen64 (K) + 1 + m + CSLACK + 63) / 64;
  assert (L <= LMAX);
  // A_i = floor (exp(x0) u^i / (i! v) 2^(64 L)) mod 2^(64 L), from y:
  // exp(x0) u^i / v 2^(64 L) = y 2^s with the s below
  num y, t;
  long k = tang (y, x0);
  assert (num_bitlen (y) + k - TG_P == e);
  uint64_t A[KMAX][LMAX];
  uint32_t fact = 1;
  for (int i = 0; i < K; i++) {
    if (i > 0) fact *= i;
    long s = k - TG_P + i * (e0 - 53) - (e - 54) + 64 * L;
    if (s >= 0) num_shl (t, y, s);
    else limbs_shr (t, y, TG_NL, -s);
    num_divu (t, t, fact);
    to_words (A[i], t);
  }
  // B_i = sum_d A_d i^d, then the table of differences
  for (int i = 0; i < K; i++) {
    for (int w = 0; w < L; w++) B[i][w] = 0;
    for (int d = K - 1; d >= 0; d--)           // Horner in i
      w_muladd (B[i], i, A[d]);
  }
  for (int i = 1; i < K; i++)
    for (int j = K - 1; j >= i; j--)
      w_sub (B[j], B[j - 1]);
  // E = 2^(64 L - m) + R + 2 (1 + n + ... + n^(K-1)) + 2, with
  // R = ceil (n^K 2^S / K!) >= 2^(64 L) 2^54 (n u)^K / K!
  num E, R, p, nn, q;
  num_set_u64 (E, 1);
  num_shl (E, E, 64 * L - m);
  num_set_u64 (nn, n);
  num_set_u64 (p, 1);
  num_set_u64 (q, 2);                          // 2 (1 + n + ... ) + 2
  for (int i = 0; i < K; i++) {
    num_add (q, q, p);
    num_add (q, q, p);
    num_mulshr (p, p, nn, 0);                  // p = n^(i+1)
  }
  num_add (E, E, q);
  long S = 64 * L + 54 + (long) K * (e0 - 53);
  if (S >= 0) num_shl (R, p, S);
  else {                                       // ceil (p / 2^-S)
    num_mask (q, -S);
    num_add (R, p, q);
    limbs_shr (R, R, TG_NL, -S);
  }
  uint32_t kf = 1;
  for (int i = 2; i <= K; i++) kf *= i;
  num_set_u64 (q, kf - 1);                     // ceil (R / K!)
  num_add (R, R, q);
  num_divu (R, R, kf);
  num_add (E, E, R);
  num_shl (t, E, 1);                           // 2 E
  assert (num_bitlen (t) < 64 * L);
  to_words (twoE, t);
  uint64_t Ew[LMAX];
  to_words (Ew, E);
  w_add (B[0], Ew);                            // B_0 + E
  fprintf (stderr, "subrange %la: n = %lu, k = %d, l = %d\n",
           x0, (unsigned long) n, K, L);
  switch (16 * K + L) {
#define CASE(k, l) case 16 * k + l: walk (k, l, x0, u, n, m); return;
    CASE (2, 1) CASE (2, 2) CASE (3, 1) CASE (3, 2) CASE (3, 3)
    CASE (4, 2) CASE (4, 3) CASE (4, 4) CASE (5, 2) CASE (5, 3) CASE (5, 4)
    CASE (6, 3) CASE (6, 4) CASE (6, 5) CASE (7, 3) CASE (7, 4) CASE (7, 5)
    CASE (8, 4) CASE (8, 5) CASE (9, 5)
#undef CASE
  }
  assert (0);                                  // no loop for this k and l
}

// search hard-to-round cases of exp in [x0, x1)
// with at least m identical bits after round bit
static void
search (double x0, double x1, int m)
{
  int e0 = dexpo (x0);
  assert (e0 == dexpo (dpred (x1)));
  int e = tang_expo (x0);
  assert (e == tang_expo (dpred (x1)));
  double u = pow2 (e0 - 53);
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
  if (argc < 4) {
    fprintf (stderr, "usage: htr2_fix x0 x1 m [-c]\n");
    return 1;
  }
  double x0 = strtod (argv[1], NULL), x1 = strtod (argv[2], NULL);
  int m = atoi (argv[3]);
  print_all = argc > 4 && strcmp (argv[4], "-c") == 0;
  tang_init ();
  search (x0, x1, m);
  printf ("%lu checks, found %lu hard-to-round\n", checks, found);
  return 0;
}
