// The evaluators of the initial program (htr.c): exp with MPFR, trusted.

#include <stdio.h>
#include <mpfr.h>
#include "eval.h"

// htr.c's ref_exp: exp(x) rounded toward zero, which meets E3
double
low_mpfr (double x)
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
