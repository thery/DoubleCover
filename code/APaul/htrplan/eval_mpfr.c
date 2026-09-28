// The evaluator of Program 1 (htr.c): exp with MPFR, trusted.
// Also check, which decides a candidate; it is not part of the superset.

#include <stdio.h>
#include <mpfr.h>
#include "eval.h"

// the exponent of exp(x): htr.c's ref_exp rounds toward zero, so that the
// result never rounds up to the next power of 2
int
expo_mpfr (double x)
{
  mpfr_t y;
  mpfr_exp_t emin = mpfr_get_emin ();
  mpfr_set_emin (-1073);
  mpfr_init2 (y, 53);
  mpfr_set_d (y, x, MPFR_RNDN);
  int inex = mpfr_exp (y, y, MPFR_RNDZ);
  mpfr_subnormalize (y, inex, MPFR_RNDZ);
  int e;
  frexp (mpfr_get_d (y, MPFR_RNDN), &e);
  mpfr_clear (y);
  mpfr_set_emin (emin);
  return e;
}

// htr.c's dd_exp: exp(x) at 161 bits, split into three doubles
void
eval_mpfr (double *h, double *l, double *s, double x)
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

// htr.c's check: is x hard to round at level m
int
check_mpfr (double x, int m)
{
  mpfr_t y, z;
  mpfr_init2 (y, 54);
  mpfr_init2 (z, 53 + m);
  mpfr_set_d (y, x, MPFR_RNDN);
  mpfr_exp (z, y, MPFR_RNDN);
  mpfr_set (y, z, MPFR_RNDN);
  int hard = mpfr_cmp (y, z) == 0;
  mpfr_clear (y);
  mpfr_clear (z);
  return hard;
}
