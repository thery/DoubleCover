// search hard-to-round cases of exp in [0.25,0.5)
// with at least 43 identical bits after round bit

#include <stdio.h>
#include <stdint.h>
#include <mpfr.h>
#include <assert.h>
#include <math.h>

// reference code using MPFR, with RNDZ
double
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

// put in h+l+s a triple-double approximation of exp(x)
static void
dd_exp (double *h, double *l, double *s, double x)
{
  mpfr_t t;
  mpfr_init2 (t, 3*53+2);
  mpfr_set_d (t, x, MPFR_RNDN);
  mpfr_exp (t, t, MPFR_RNDN);
  *h = mpfr_get_d (t, MPFR_RNDN);
  mpfr_sub_d (t, t, *h, MPFR_RNDN);
  *l = mpfr_get_d (t, MPFR_RNDN);
  mpfr_sub_d (t, t, *l, MPFR_RNDN);
  *s = mpfr_get_d (t, MPFR_RNDN);
  mpfr_clear (t);
}

unsigned long checks = 0, found = 0;

static void
check (double x, int m)
{
  // printf ("check x=%la\n", x);
  checks ++;
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
// with at least m0 identical bits after round bit
static void
search (double x0, double x1, int m)
{
  uint64_t n = 1ul << 20;
  int e, e0, e1;

  // check ulp(x0) = ulp(nextbelow(x1))
  frexp (x0, &e0);
  frexp (nextafter (x1, x0), &e1);
  assert (e0 == e1);

  double ux = ldexp (1.0, e0 - 53); // ux = ulp(x)

  // check exp(x) lies in the same binade in [x0, x1)
  double y0 = ref_exp (x0);
  double y1 = ref_exp (nextafter (x1, x0));
  frexp (y0, &e);
  frexp (y1, &e1);
  assert (e == e1);
  double uh = ldexp (1.0, e - 53); // uh = ulp(exp(x))

  double h, l, s;
  double x = x0;
  while (x < x1) {
    dd_exp (&h, &l, &s, x);
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
    // scale the derivative too
    dh = ldexp (dh, 54 - e);
    dl = ldexp (dl, 54 - e);
    uint64_t B = get_uint64 (dh) + get_uint64 (dl);
    // the maximal error is bounded by dd/2*n^2
    dd = dd / 2.0 * n * n;
    // hard-to-round cases are at distance < 2^-(m+1) ulp(h)
    uint64_t E = (uint64_t) ldexp (dd, 64) + (1ul << (64 - m));
    // we want to find values of A in [-E, E]
    A += E; // shift A
    // now we want to find values of A in [0,2*E]
    for (uint64_t i = 0; i < n; i++) {
      if (__builtin_expect (A < 2*E, 0)) { // found potential hard-to-round case
        double xi = x + i * ux;
        check (xi, m);
      }
      A += B;
    }
    x += n * ux;
    if (x > x1)
      n = (x1 - x) / ux;
  }
}

/* With x0 = 0.25, x1 = 0.25001, m = 30
on thym.loria.fr (Intel(R) Core(TM) Ultra 7 265) with gcc 15.3.0
(-O3 -march=native):

0x1.00006b1501522p-2
0x1.0000f35300644p-2
322 checks, found 2 hard-to-round

real    0m34.928s
user    0m34.915s
sys     0m0.005s
*/   
int main()
{
  double x0 = 0.25, x1 = 0.25001;
  int m = 30;
  search (x0, x1, m);
  printf ("%lu checks, found %lu hard-to-round\n", checks, found);

}
