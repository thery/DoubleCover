// exp100: an enclosure of exp(x) by Tang's method on fixed-size integers,
// and the filter maybe_hard.  Plain C for VST: arrays of uint64_t, simple
// counted loops, no floating-point operation, no 128-bit type.  See
// exp100.h for the interface and README for the error budget.
//
// The method.  |x| < 1024 is read from its bits as X = floor(|x| 2^P).
// With n = floor(|x| 64/ln2) (found, then checked), x = N ln2/64 + r with
//   N = n,       r = |x| - n ln2/64        when x >= 0,
//   N = -(n+1),  r = (n+1) ln2/64 - |x|    when x < 0,
// so that 0 <= r < ln2/64 in both cases.  Writing N = 64 h + j with
// 0 <= j < 64, exp(x) = 2^h 2^(j/64) exp(r): exp(r) is its Taylor
// polynomial of degree DEG by Horner's rule, 2^(j/64) is read in a table.

#include "exp100.h"
#include "exp100_table.h"

// ---------------------------------------------------------------------
// Numbers: NL limbs of 32 bits, least significant first, in uint64_t.

// a = 0
static void num_zero(uint64_t *a) {
  for (int i = 0; i < NL; i++)
    a[i] = 0;
}

// a = b
static void num_copy(uint64_t *a, const uint64_t *b) {
  for (int i = 0; i < NL; i++)
    a[i] = b[i];
}

// a = a + b; the sum must fit in NL limbs
static void num_add(uint64_t *a, const uint64_t *b) {
  uint64_t c = 0;
  for (int i = 0; i < NL; i++) {
    c = c + a[i] + b[i];               // at most 2^33 - 1
    a[i] = c & MASK;
    c = c >> LIMB;
  }
}

// a = a - b, for a >= b
static void num_sub(uint64_t *a, const uint64_t *b) {
  uint64_t c = 0;                      // the borrow, 0 or 1
  for (int i = 0; i < NL; i++) {
    uint64_t t = b[i] + c;
    if (a[i] >= t) {
      a[i] = a[i] - t;
      c = 0;
    } else {
      a[i] = a[i] + (MASK + 1) - t;
      c = 1;
    }
  }
}

// 1 if a < b, else 0
static int num_lt(const uint64_t *a, const uint64_t *b) {
  for (int i = NL - 1; i >= 0; i--) {
    if (a[i] < b[i]) return 1;
    if (a[i] > b[i]) return 0;
  }
  return 0;
}

// p = a w, on NL + 1 limbs, for a limb w < 2^32
static void num_mul_small(uint64_t *p, const uint64_t *a, uint64_t w) {
  uint64_t c = 0;
  for (int i = 0; i < NL; i++) {
    c = a[i] * w + c;                  // at most 2^64 - 2^32
    p[i] = c & MASK;
    c = c >> LIMB;
  }
  p[NL] = c;
}

// r = floor(a b / 2^P); the quotient must fit in NL limbs
static void num_mulshr(uint64_t *r, const uint64_t *a, const uint64_t *b) {
  uint64_t p[2 * NL];
  for (int i = 0; i < 2 * NL; i++)
    p[i] = 0;
  for (int i = 0; i < NL; i++) {
    uint64_t c = 0;
    for (int j = 0; j < NL; j++) {
      c = a[i] * b[j] + p[i + j] + c;  // at most 2^64 - 1
      p[i + j] = c & MASK;
      c = c >> LIMB;
    }
    p[i + NL] = c;
  }
  for (int i = 0; i < NL; i++)
    r[i] = p[i + P / LIMB];
}

// the number of bits of a: 0 for a = 0, else 2^(b-1) <= a < 2^b
static int num_bitlen(const uint64_t *a) {
  int b = 0;
  for (int i = 0; i < NL; i++)
    for (int k = 0; k < LIMB; k++)
      if ((a[i] >> k) & 1) b = LIMB * i + k + 1;
  return b;
}

// a = 2^f, for 0 <= f < LIMB NL
static void num_pow2(uint64_t *a, int f) {
  num_zero(a);
  a[f / LIMB] = (uint64_t) 1 << (f % LIMB);
}

// a = b mod 2^f, for 0 <= f < LIMB NL
static void num_low(uint64_t *a, const uint64_t *b, int f) {
  for (int i = 0; i < NL; i++) {
    if (i < f / LIMB) a[i] = b[i];
    else if (i == f / LIMB) a[i] = b[i] & (((uint64_t) 1 << (f % LIMB)) - 1);
    else a[i] = 0;
  }
}

// a = floor(v 2^e), for v < 2^53 and -2^31 < e <= LIMB NL - 54
static void num_scale(uint64_t *a, uint64_t v, int e) {
  num_zero(a);
  if (e < 0) {
    if (e > -64) v = v >> (-e);
    else v = 0;
    a[0] = v & MASK;
    a[1] = v >> LIMB;
  } else {
    int q = e / LIMB, b = e % LIMB;
    uint64_t lo = (v & MASK) << b;     // at most 2^63
    uint64_t hi = (v >> LIMB) << b;    // at most 2^52
    a[q] = lo & MASK;
    hi = hi + (lo >> LIMB);            // at most 2^53
    a[q + 1] = hi & MASK;
    a[q + 2] = hi >> LIMB;
  }
}

// ---------------------------------------------------------------------
// The reduction.

// q = floor(n LN2 / 2^LIMB) = floor(n ln2/64 2^P) up to n 2^-33: the
// multiple n of ln2/64, for n < 2^32
static void mul_ln2(uint64_t *q, uint64_t n) {
  uint64_t p[NL + 1];
  num_mul_small(p, LN2, n);
  for (int i = 0; i < NL; i++)
    q[i] = p[i + 1];
}

// the first guess of n = floor(X / (ln2/64 2^P)): floor(X INV / 2^(P+25))
static uint64_t guess_n(const uint64_t *X) {
  uint64_t p[NL + 1];
  num_mul_small(p, X, INV);
  return (p[5] >> 25) | (p[6] << 7);   // bits 185 .. 223 of p
}

// The core: y and s with |exp(x) - y 2^(s-P)| <= EXP100_D 2^(s-P), from
// the bits xb of x.  Returns 0 on success.
static int exp_core(uint64_t xb, uint64_t *y, int64_t *s) {
  uint64_t X[NL], q[NL], q1[NL], r[NL], h[NL], t[NL];
  uint64_t neg = xb >> 63;
  int be = (int) ((xb >> 52) & 0x7ff);
  uint64_t mx = xb & (((uint64_t) 1 << 52) - 1);
  // |x| = mx 2^(be - 1075), with the implicit bit when x is normal
  if (be >= 1033) return 1;            // |x| >= 1024, infinity, NaN
  if (be == 0) be = 1;
  else mx = mx | ((uint64_t) 1 << 52);
  num_scale(X, mx, be - 1075 + P);     // X = floor(|x| 2^P)
  // n, then checked: q <= X < q1, q = n ln2/64, q1 = (n+1) ln2/64
  uint64_t n = guess_n(X);
  mul_ln2(q, n);
  if (num_lt(X, q) && n > 0) n = n - 1;
  mul_ln2(q1, n + 1);
  if (!num_lt(X, q1)) n = n + 1;
  mul_ln2(q, n);
  mul_ln2(q1, n + 1);
  if (num_lt(X, q) || !num_lt(X, q1)) return 2;
  // r, and N + 2^17 as an unsigned number
  uint64_t Nu;
  if (neg) {
    num_copy(r, q1);
    num_sub(r, X);
    Nu = 131072 - (n + 1);
  } else {
    num_copy(r, X);
    num_sub(r, q);
    Nu = 131072 + n;
  }
  if (!num_lt(r, RMAX)) return 3;      // r < ln2/64 + 3 2^-P
  // exp(r) by Horner's rule: h = C_DEG, then h = floor(h r) + C_i
  num_copy(h, C[DEG]);
  for (int i = DEG - 1; i >= 0; i--) {
    num_mulshr(t, h, r);
    num_add(t, C[i]);
    num_copy(h, t);
  }
  // times 2^(j/64), j = N mod 64; N = 64 hN + j
  uint64_t j = Nu & (TAB - 1);
  num_mulshr(y, T[j], h);
  *s = (int64_t) (Nu >> K) - 2048;     // hN
  return 0;
}

int exp_encl_bits(uint64_t xb, uint64_t *M, int64_t *s) {
  uint64_t y[NL];
  int64_t hN;
  int rc = exp_core(xb, y, &hN);
  if (rc) return rc;
  for (int i = 0; i < NL / 2; i++)
    M[i] = y[2 * i] | (y[2 * i + 1] << LIMB);
  *s = hN - P;
  return 0;
}

// ---------------------------------------------------------------------
// The filter.  With e the binade of exp(x) and v = 2^(max(e, EMIN) -
// PREC), exp(x)/v = y 2^(hN - P - (max(e, EMIN) - PREC)) = y / 2^f: its
// integer part is y >> f, its fraction the f low bits of y.

int maybe_hard_bits(uint64_t xb) {
  uint64_t y[NL], lo[NL], hi[NL], d[NL], t[NL];
  int64_t hN;
  if (exp_core(xb, y, &hN)) return 1;
  // the binade: y - D and y + D have the same number of bits b
  num_zero(d);
  d[0] = EXP100_D;
  num_copy(lo, y);
  num_sub(lo, d);
  num_copy(hi, y);
  num_add(hi, d);
  int b = num_bitlen(y);
  if (num_bitlen(lo) != b || num_bitlen(hi) != b) return 1;
  int64_t e = hN - P + b - 1;          // 2^e <= exp(x) < 2^(e+1)
  int64_t ve = (e > EMIN ? e : EMIN) - PREC;
  int64_t f = ve - (hN - P);
  if (f < 64 || f > LIMB * NL - 8) return 1;
  // d = the distance of y to the nearest multiple of 2^f
  num_low(lo, y, (int) f);
  num_pow2(hi, (int) f);
  num_sub(hi, lo);
  if (num_lt(lo, hi)) num_copy(d, lo);
  else num_copy(d, hi);
  // not hard when d > 2^(f-42) + D
  num_pow2(t, (int) f - M_HARD);
  num_zero(hi);
  hi[0] = EXP100_D;
  num_add(t, hi);
  if (num_lt(t, d)) return 0;
  return 1;
}

// ---------------------------------------------------------------------
// The doubles: their bits, outside the verified part.

union exp100_bits { double d; uint64_t u; };

int exp_encl(double x, uint64_t *M, int64_t *s) {
  union exp100_bits b;
  b.d = x;
  return exp_encl_bits(b.u, M, s);
}

int maybe_hard(double x) {
  union exp100_bits b;
  b.d = x;
  return maybe_hard_bits(b.u);
}
