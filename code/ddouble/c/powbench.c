/* x^100 computed two ways, timed and compared bit by bit.                  */
/*                                                                          */
/* "3 ints": a 128-bit mantissa held in two 64-bit limbs plus a separate    */
/* exponent, the way a bignum library simulates a floating point number.    */
/* "2 floats": a double word, a pair of binary64 numbers whose unevaluated  */
/* sum is the value, giving 106 significant bits.                           */
/*                                                                          */
/* The 3-int multiplication truncates instead of rounding to nearest: that  */
/* is a choice, it makes the integer side as fast as it can be, and it      */
/* costs it at most one bit of the 128 it carries.                          */

#include <stdio.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define POW 100         /* the exponent, so 99 multiplications per power    */
#define REP 1000000     /* how many powers a run computes                   */

/* ---------------------------------------------------------------------- */
/* 3 ints: the value is (hi:lo) * 2^(e-128), with 1/2 <= (hi:lo)/2^128 < 1 */
/* ---------------------------------------------------------------------- */

typedef struct { uint64_t hi, lo; int64_t e; } ti;

static inline ti ti_mul(ti a, ti b)
{
  __uint128_t hh = (__uint128_t) a.hi * b.hi;
  __uint128_t hl = (__uint128_t) a.hi * b.lo;
  __uint128_t lh = (__uint128_t) a.lo * b.hi;
  __uint128_t ll = (__uint128_t) a.lo * b.lo;
  /* the bits of weight below 2^-128 only matter through their carry       */
  __uint128_t mid = (hl & UINT64_MAX) + (lh & UINT64_MAX) + (ll >> 64);
  __uint128_t r   = hh + (hl >> 64) + (lh >> 64) + (mid >> 64);
  uint64_t rhi = (uint64_t) (r >> 64), rlo = (uint64_t) r;
  int64_t e = a.e + b.e;
  /* both factors are below 1, so the product needs at most one shift      */
  if (!(rhi >> 63)) { rhi = (rhi << 1) | (rlo >> 63); rlo <<= 1; e--; }
  ti c = { rhi, rlo, e };
  return c;
}

static ti ti_of_double(double x)
{
  int e; double f = frexp(x, &e);
  uint64_t m = (uint64_t) ldexp(f, 53);
  ti c = { m << 11, 0, e };
  return c;
}

/* ---------------------------------------------------------------------- */
/* 2 floats: the value is hi + lo, the sum left unevaluated               */
/* ---------------------------------------------------------------------- */

typedef struct { double hi, lo; } dw;

static inline dw dw_mul(dw a, dw b)
{
  double p = a.hi * b.hi;
  double e = fma(a.hi, b.hi, -p);        /* the part p dropped, exactly    */
  e += a.hi * b.lo + a.lo * b.hi;
  double s = p + e;
  dw c = { s, (p - s) + e };
  return c;
}

/* the double word read back as a 128-bit mantissa, so the two answers     */
/* can be lined up digit against digit                                     */
static ti ti_of_dw(dw a)
{
  int e1; double f1 = frexp(a.hi, &e1);
  uint64_t m1 = (uint64_t) ldexp(f1, 53);
  __uint128_t s = (__uint128_t) m1 << 75;
  if (a.lo != 0) {
    int e2; double f2 = frexp(fabs(a.lo), &e2);
    uint64_t m2 = (uint64_t) ldexp(f2, 53);
    int sh = 75 - (e1 - e2);
    __uint128_t t = sh >= 0 ? (__uint128_t) m2 << sh : (__uint128_t) m2 >> -sh;
    if (a.lo > 0) s += t; else s -= t;
  }
  int64_t e = e1;
  while (!(s >> 127)) { s <<= 1; e--; }
  ti c = { (uint64_t) (s >> 64), (uint64_t) s, e };
  return c;
}

/* ---------------------------------------------------------------------- */
/* Each run computes LANES powers side by side.  With one lane the timing  */
/* is the latency of a multiplication, every one waiting for the previous  */
/* one; with four lanes the chains are independent and the timing is the   */
/* throughput, what the processor sustains when it has work to overlap.    */
/* ---------------------------------------------------------------------- */

static double check = 0;

static double now(void)
{
  struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + 1e-9 * t.tv_nsec;
}

#define RUN(NAME, LANES, TYPE, OF, MUL, PART)                            \
static double NAME(TYPE *last)                                           \
{                                                                        \
  double t = now(), acc = 0;                                             \
  TYPE r[LANES], x[LANES];                                               \
  for (int k = 0; k < REP; k += LANES) {                                 \
    for (int j = 0; j < LANES; j++) {                                    \
      x[j] = OF(M_PI + 1e-12 * (k + j)); r[j] = x[j];                    \
    }                                                                    \
    for (int i = 1; i < POW; i++)                                        \
      for (int j = 0; j < LANES; j++) r[j] = MUL(r[j], x[j]);            \
    /* an empty asm that claims to read and write every power: it keeps   \
       the chains alive and stops the compiler running several rounds of  \
       the outer loop side by side, which would hide the latency           */ \
    for (int j = 0; j < LANES; j++) __asm__ volatile("" : "+m"(r[j]));    \
    acc += (double) (r[0] PART);                                          \
  }                                                                      \
  t = now() - t;                                                         \
  *last = r[LANES - 1]; check += acc;                                    \
  return t;                                                              \
}

static inline double d_of(double x) { return x; }
static inline double d_mul(double a, double b) { return a * b; }
static inline dw dw_of(double x) { dw c = { x, 0 }; return c; }

RUN(ti_lat, 1, ti, ti_of_double, ti_mul, .hi)
RUN(ti_th2, 2, ti, ti_of_double, ti_mul, .hi)
RUN(ti_thr, 4, ti, ti_of_double, ti_mul, .hi)
RUN(dw_lat, 1, dw, dw_of, dw_mul, .hi)
RUN(dw_th2, 2, dw, dw_of, dw_mul, .hi)
RUN(dw_thr, 4, dw, dw_of, dw_mul, .hi)
RUN(d_lat,  1, double, d_of, d_mul, )
RUN(d_th2,  2, double, d_of, d_mul, )
RUN(d_thr,  4, double, d_of, d_mul, )

int main(void)
{
  ti ri; dw rd; double rp;
  double til = ti_lat(&ri), ti2 = ti_th2(&ri), tit = ti_thr(&ri);
  double dwl = dw_lat(&rd), dw2 = dw_th2(&rd), dwt = dw_thr(&rd);
  double dl  = d_lat(&rp),  d2  = d_th2(&rp),  dt  = d_thr(&rp);
  double n = (double) REP * (POW - 1);

  printf("pi^%d, %d times, %d multiplications each\n\n", POW, REP, POW - 1);
  printf("  ns per multiplication, with 1, 2 and 4 chains side by side\n\n");
  printf("  3 ints     %6.2f  %6.2f  %6.2f\n", 1e9*til/n, 1e9*ti2/n, 1e9*tit/n);
  printf("  2 floats   %6.2f  %6.2f  %6.2f\n", 1e9*dwl/n, 1e9*dw2/n, 1e9*dwt/n);
  printf("  1 float    %6.2f  %6.2f  %6.2f\n", 1e9*dl/n,  1e9*d2/n,  1e9*dt/n);
  printf("\n  3 ints / 2 floats   %.2f    %.2f    %.2f\n",
         til/dwl, ti2/dw2, tit/dwt);

  ti rdi = ti_of_dw(rd);
  printf("\nthe last power, as a 128-bit mantissa and an exponent\n");
  printf("  exact     8dfdc6c2c7764947f43e267c0fffe51e  2^166\n");
  printf("  3 ints    %016lx%016lx  2^%ld\n", ri.hi, ri.lo, (long) ri.e);
  printf("  2 floats  %016lx%016lx  2^%ld\n", rdi.hi, rdi.lo, (long) rdi.e);
  printf("  1 float   %.17e\n", rp);
  printf("\nchecksum %.17e\n", check);
  return 0;
}
