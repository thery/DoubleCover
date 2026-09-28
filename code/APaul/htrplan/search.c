// Program 2: the search of htr.c, line for line, with dd_exp replaced by
// eval, ref_exp by expo, and check by report.

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

// search hard-to-round cases of exp in [x0,x1)
// with at least m identical bits after round bit
void
search (eval_t eval, expo_t expo, report_t report,
        double x0, double x1, int m)
{
  uint64_t n = 1ul << 20;
  int e, e0, e1;

  // check ulp(x0) = ulp(nextbelow(x1))
  frexp (x0, &e0);
  frexp (nextafter (x1, x0), &e1);
  assert (e0 == e1);

  double ux = ldexp (1.0, e0 - 53); // ux = ulp(x)

  // check exp(x) lies in the same binade in [x0, x1)
  e = expo (x0);
  e1 = expo (nextafter (x1, x0));
  assert (e == e1);

  double h, l, s;
  double x = x0;
  while (x < x1) {
    eval (&h, &l, &s, x);
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
        report (xi, m);
      }
      A += B;
    }
    x += n * ux;
    if (x > x1)
      n = (x1 - x) / ux;
  }
}
