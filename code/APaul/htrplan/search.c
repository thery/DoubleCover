// Program 2, the generic search: the search of htr.c, line for line,
// with dd_exp replaced by eval_seed, ref_exp by eval_low, and check by
// a check written here on top of eval_check.

#include <stdlib.h>
#include <assert.h>
#include <math.h>
#include "search.h"

// given x, -1 < x < 1, return the 64-bit value corresponding
// to the fractional part of x
static uint64_t
get_uint64 (double x)
{
  assert (-1 < x && x < 1);
  x = ldexp (x, 64);
  if (x >= 0) return x;
  uint64_t ret = (uint64_t) (-x);
  return ~ret + (uint64_t) 1;
}

// is x hard to round at level m: 1 yes, 0 no, 2 undecided.  e is the
// exponent of exp(x).  F is the fractional part of exp(x) 2^(54-e), times
// 2^64, read from l and s as A is; d is its distance to the nearest
// integer; F is within CHECK_ERR of the exact value (E1, E2).
static int
check (check_t eval_check, int e, double x, int m)
{
  double h, l, s;
  eval_check (&h, &l, &s, x);
  l = ldexp (l, 54 - e);
  if (l >= 1.0) l -= 1.0;
  while (l < 0) l += 1.0;
  s = ldexp (s, 54 - e);
  uint64_t F = get_uint64 (l) + get_uint64 (s);
  uint64_t d = F < -F ? F : -F;
  uint64_t T = 1ul << (64 - m);
  if (d + CHECK_ERR < T) return 1;
  if (d >= T + CHECK_ERR) return 0;
  return 2;
}

// add the candidate x with its verdict v to the array r
static void
report (struct cands *r, unsigned long *size, double x, int v)
{
  if (r->n == *size) {
    *size = *size ? 2 * *size : 1024;
    r->a = realloc (r->a, *size * sizeof (struct cand));
    assert (r->a != NULL);
  }
  r->a[r->n].x = x;
  r->a[r->n].v = v;
  r->n ++;
}

// search hard-to-round cases of exp in [x0,x1)
// with at least m identical bits after round bit
struct cands
search (seed_t eval_seed, low_t eval_low, check_t eval_check,
        double x0, double x1, int m)
{
  struct cands r = { NULL, 0 };
  unsigned long size = 0;
  uint64_t n = 1ul << 20;
  int e, e0, e1;

  // check ulp(x0) = ulp(nextbelow(x1))
  frexp (x0, &e0);
  frexp (nextafter (x1, x0), &e1);
  assert (e0 == e1);

  double ux = ldexp (1.0, e0 - 53); // ux = ulp(x)

  // check exp(x) lies in the same binade in [x0, x1)
  frexp (eval_low (x0), &e);
  frexp (eval_low (nextafter (x1, x0)), &e1);
  assert (e == e1);

  double h, l, s;
  double x = x0;
  while (x < x1) {
    eval_seed (&h, &l, &s, x);
    double dh = h * ux, dl = l * ux; // 1st derivative, multiplied by ux
    double dd = h * ux * ux; // 2nd derivative, multiplied by ux^2

    // prepare loop
    // A is the bits of h+l after the round bit
    h = ldexp (h, 54 - e); // now ulp(h) = 2
    l = ldexp (l, 54 - e);
    // we now have -2 < l < 2
    if (l >= 1.0) l -= 1.0;
    while (l < 0) l += 1.0;
    assert (0 <= l && l < 1);
    s = ldexp (s, 54 - e);
    uint64_t lu = get_uint64 (l), su = get_uint64 (s);
    uint64_t A = lu + su;
    // scale the derivatives too
    dh = ldexp (dh, 54 - e);
    dl = ldexp (dl, 54 - e);
    dd = ldexp (dd, 54 - e);
    uint64_t B = get_uint64 (dh) + get_uint64 (dl);
    // the maximal error is bounded by dd/2*n^2
    dd = dd / 2.0 * n * n;
    // hard-to-round cases are at distance < 2^-(m+1) ulp(h)
    uint64_t E = get_uint64 (dd) + (1ul << (64 - m));
    // we want to find values of A in [-E, E]
    A += E; // shift A
    // now we want to find values of A in [0,2*E]
    for (uint64_t i = 0; i < n; i++) {
      if (__builtin_expect (A < 2*E, 0)) { // found potential hard-to-round case
        double xi = x + i * ux;
        report (&r, &size, xi, check (eval_check, e, xi, m));
      }
      A += B;
    }
    x += n * ux;
    if (x > x1)
      n = (x1 - x) / ux;
  }
  return r;
}
