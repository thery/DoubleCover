// Program 3, the proved evaluator: exp with integers only, self-contained:
// no library, not even libm; doubles are read and built from their bits
// (dbl.h).
// Tang's scheme:
//   x = N ln2/256 + r, N = 256 k + j, 0 <= j < 256, |r| <= 2^-9.5
//   exp(x) = 2^k * 2^(j/256) * exp(r)
// A fixed-point number is an integer X standing for X / 2^FIX_P.
// Designed error (not yet proved): 2^-169 on y, 2^-158 after the split.

#include "dbl.h"
#include "fix.h"
#include "eval.h"
#include "fix_table.h"

// ---------------------------------------------------------------------
// The integers: FIX_NL limbs of 32 bits, lowest first.  Every operation is
// modulo 2^(32 FIX_NL), so a signed number is in two's complement.  The
// sizes in fix_exp stay below 2^213, so nothing wraps.

typedef uint32_t num[FIX_NL];

static void
num_set (num r, const num a)
{
  for (int k = 0; k < FIX_NL; k++) r[k] = a[k];
}

// r = v, for 0 <= v < 2^64
static void
num_set_u64 (num r, uint64_t v)
{
  for (int k = 0; k < FIX_NL; k++) r[k] = 0;
  r[0] = (uint32_t) v;
  r[1] = (uint32_t) (v >> 32);
}

static void
num_add (num r, const num a, const num b)
{
  uint64_t c = 0;
  for (int k = 0; k < FIX_NL; k++) {
    c += (uint64_t) a[k] + b[k];
    r[k] = (uint32_t) c;
    c >>= 32;
  }
}

static void
num_sub (num r, const num a, const num b)
{
  uint64_t c = 1;                              // a - b = a + ~b + 1
  for (int k = 0; k < FIX_NL; k++) {
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
  return a[FIX_NL - 1] >> 31;
}

// the sign of a - b, both read as nonnegative
static int
num_cmp (const num a, const num b)
{
  for (int k = FIX_NL - 1; k >= 0; k--)
    if (a[k] != b[k]) return a[k] < b[k] ? -1 : 1;
  return 0;
}

// the number of bits of a >= 0; 0 for a = 0
static int
num_bitlen (const num a)
{
  for (int k = FIX_NL - 1; k >= 0; k--)
    if (a[k]) {
      int b = 32;
      while (!(a[k] >> (b - 1))) b--;
      return 32 * k + b;
    }
  return 0;
}

// r = a 2^s, for a >= 0
static void
num_shl (num r, const num a, int s)
{
  num t = { 0 };
  int q = s / 32, b = s % 32;
  for (int k = FIX_NL - 1; k >= q; k--) {
    uint64_t v = (uint64_t) a[k - q] << b;
    if (k - q - 1 >= 0 && b) v |= a[k - q - 1] >> (32 - b);
    t[k] = (uint32_t) v;
  }
  num_set (r, t);
}

// r = floor (p / 2^s) for p >= 0 of n limbs, whose quotient fits in
// FIX_NL limbs; returns 1 when the bits dropped are not all 0
static int
limbs_shr (num r, const uint32_t *p, int n, int s)
{
  int q = s / 32, b = s % 32, nz = 0;
  for (int k = 0; k < q && k < n; k++) nz |= p[k] != 0;
  if (b && q < n) nz |= (p[q] & ((1u << b) - 1)) != 0;
  for (int k = 0; k < FIX_NL; k++) {
    uint64_t v = k + q < n ? p[k + q] >> b : 0;
    if (b && k + q + 1 < n) v |= (uint64_t) p[k + q + 1] << (32 - b);
    r[k] = (uint32_t) v;
  }
  // the quotient fits: nothing above bit 32 FIX_NL + s
  if (FIX_NL + q < n) assert ((p[FIX_NL + q] >> b) == 0);
  for (int k = FIX_NL + q + 1; k < n; k++) assert (p[k] == 0);
  return nz;
}

// r = floor (a b / 2^s), for a, b >= 0; returns 1 when the bits dropped
// are not all 0
static int
num_mulshr (num r, const num a, const num b, int s)
{
  uint32_t p[2 * FIX_NL] = { 0 };
  for (int i = 0; i < FIX_NL; i++) {
    uint64_t c = 0;
    for (int j = 0; j < FIX_NL; j++) {
      c += (uint64_t) a[i] * b[j] + p[i + j];
      p[i + j] = (uint32_t) c;
      c >>= 32;
    }
    p[i + FIX_NL] = (uint32_t) c;
  }
  return limbs_shr (r, p, 2 * FIX_NL, s);
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
  for (int k = FIX_NL - 1; k >= 0; k--) {
    uint64_t v = (rem << 32) | a[k];
    r[k] = (uint32_t) (v / d);
    rem = v % d;
  }
}

// the len <= 64 bits of a >= 0 from bit pos up
static uint64_t
num_bits (const num a, int pos, int len)
{
  num t;
  limbs_shr (t, a, FIX_NL, pos);
  uint64_t v = t[0] | (uint64_t) t[1] << 32;
  return len == 64 ? v : v & ((1ul << len) - 1);
}

// ---------------------------------------------------------------------
// Tang's scheme on these integers.

static num C[FIX_DEG + 1];    // 1/i!, rounded down
static num inv;               // 256/ln2, with FIX_LG bits after the point
static num rmax;              // bound on |r|: 181/256 2^-9 < 2^-9.5
static num err;               // bound on the error of y: 2^-160

void
fix_init (void)
{
  num_set_u64 (C[0], 1);
  num_shl (C[0], C[0], FIX_P);
  for (int i = 1; i <= FIX_DEG; i++)          // floor (floor (a/b) / c)
    num_divu (C[i], C[i - 1], i);             //   = floor (a / (b c))
  num_set_u64 (rmax, 181);
  num_shl (rmax, rmax, FIX_P - 17);
  num_set_u64 (err, 1);
  num_shl (err, err, FIX_P - 160);
  num_set (inv, fix_inv);
}

// exp(x) = y / 2^FIX_P * 2^k; returns k
static long
fix_exp (num y, double x)
{
  num X, r, t, u;
  // |x| = m 2^(be - 1075) from the bits of x; X = |x| 2^FIX_P, exactly
  union dbits b;
  b.d = x;
  int neg = b.u >> 63, be = (b.u >> 52) & 0x7ff;
  uint64_t m = b.u & ((1ul << 52) - 1);
  assert (be != 0 || m == 0);                  // x is 0 or normal
  if (be) m |= 1ul << 52;
  int sh = be - 1075 + FIX_P;
  assert (be == 0 || sh >= 0);
  num_set_u64 (X, m);
  if (be) num_shl (X, X, sh);
  // N = floor (|x| 256/ln2 + 1/2) = (floor (2 |x| 256/ln2) + 1) / 2
  num_mulshr (t, X, inv, FIX_P + FIX_LG - 1);
  long N = (long) ((num_bits (t, 0, 64) + 1) >> 1);
  if (neg) { N = -N; num_neg (X, X); }
  // r = x - N ln2/256, checked small
  num_set_u64 (u, N < 0 ? -N : N);
  int nz = num_mulshr (t, fix_ln2, u, FIX_LG); // floor (|N| ln2/256)
  if (N < 0) {                                 // floor (-v) = -(ceil v)
    num_set_u64 (u, nz);
    num_add (t, t, u);
    num_neg (t, t);
  }
  num_sub (r, X, t);
  if (num_isneg (r)) num_neg (t, r); else num_set (t, r);
  assert (num_cmp (t, rmax) < 0);
  // exp(r) by Horner's rule, one truncation per product
  num_set (y, C[FIX_DEG]);
  for (int i = FIX_DEG - 1; i >= 0; i--) {
    num_mulshr_s (y, y, r, FIX_P);
    num_add (y, y, C[i]);
  }
  assert (!num_isneg (y));
  // times 2^(j/256)
  long j = ((N % FIX_TAB) + FIX_TAB) % FIX_TAB;
  num_mulshr (y, y, fix_T[j], FIX_P);
  // y is not within err of a power of 2, so its exponent is that of exp(x)
  num_sub (t, y, err);
  num_add (u, y, err);
  assert (num_bitlen (t) == num_bitlen (u));
  return (N - j) / FIX_TAB;
}

// the top 53 bits of y, as a double scaled by 2^sc; y keeps the rest
static double
top53 (num y, long sc)
{
  int sh = num_bitlen (y) - 53;
  if (sh < 0) sh = 0;
  uint64_t hi = num_bits (y, sh, 53);
  num t;
  num_set_u64 (t, hi);
  num_shl (t, t, sh);
  num_sub (y, y, t);
  return dscale ((double) hi, sh + sc);
}

void
eval_fix (double *h, double *l, double *s, double x)
{
  num y;
  long k = fix_exp (y, x);
  *h = top53 (y, k - FIX_P);
  *l = top53 (y, k - FIX_P);
  *s = top53 (y, k - FIX_P);
}

// exp(x) from below: y - err, cut down to 53 bits.  The assert checks
// that y + err stays below the next 53-bit value, so d + ulp(d) > exp(x).
double
low_fix (double x)
{
  num y, t;
  long k = fix_exp (y, x);
  num_sub (y, y, err);
  int sh = num_bitlen (y) - 53;
  uint64_t hi = num_bits (y, sh, 53);
  double d = dscale ((double) hi, sh + k - FIX_P);
  num_set_u64 (t, hi + 1);
  num_shl (t, t, sh);
  num_add (y, y, err);
  num_add (y, y, err);
  assert (num_cmp (y, t) < 0);
  return d;
}
