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
        check (xi, m);
      }
      A += B;
    }
    x += n * ux;
    if (x > x1)
      n = (x1 - x) / ux;
  }
}

/* With x0 = 0.25, x1 = 0.25001, m = 35
on thym.loria.fr (Intel(R) Core(TM) Ultra 7 265) with gcc 15.3.0
(-O3 -march=native):

0x1.00002385331bep-2
0x1.0000561fc7e06p-2
0x1.0001cd08ef3d4p-2
0x1.00026c769e211p-2
0x1.00028a78a7303p-2
7056503 checks, found 5 hard-to-round

real	0m39.080s
user	0m39.032s
sys	0m0.008s

BaCSeL:
make GMP=$GMP MPFR=$MPFR FPLLL=$FPLLL DEFSAL="-DEXP -DBASIS=2 -DAUTOMATIC"
zimmerma@thym:~/svn/bacsel$ ./bacsel -rnd_mode all -prec 128 -n 53 -nn 53 -m 36 -t 18 -t0 4503599627370496 -t1 4503779771355591 -d 2 -alpha 2 -e_in -2 -nthreads 4
zimmerma@thym:~/svn/bacsel$ ./bacsel -rnd_mode all -prec 128 -n 53 -nn 53 -m 36 -t 18 -t0 4503599627370496 -t1 4503779771355591 -d 2 -alpha 2 -e_in -1 -nthreads 4
./bacsel -rnd_mode all -prec 128 -n 53 -nn 53 -m 36 -t 18 -t0 4503599627370496 -t1 4503779771355591 -d 2 -alpha 2 -e_in -1 -nthreads 4 
Welcome to BaCSeL version 4.0, using 4 thread(s)
Compilation flags: -DBASIS=2 -DEXP -DAUTOMATIC
LLL parameters: delta=0.999 eta=0.501
Parameters for AUTOMATIC: FAILURE_LOWERBOUND=2.0 FAILURE_UPPERBOUND=4.0
*** x=0x4.0001587f1f818p-4, distance is: 1.059463030e-11 0x1.0000561fc7e06p-2
*** x=0x4.00008e14cc6f8p-4, distance is: 1.055287224e-11 0x1.00002385331bep-2
*** x=0x4.00073423bcf5p-4, distance is: 2.577853443e-12 0x1.0001cd08ef3d4p-2
*** x=0x4.000a29e29cc0cp-4, distance is: 7.860279955e-12 0x1.00028a78a7303p-2
*** x=0x4.0009b1da78844p-4, distance is: 7.913797859e-12 0x1.00026c769e211p-2
*/   
int main()
{
  double x0 = 0.25, x1 = 0.25001;
  int m = 35;
  search (x0, x1, m);
  printf ("%lu checks, found %lu hard-to-round\n", checks, found);
}
