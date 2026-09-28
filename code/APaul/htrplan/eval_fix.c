// Program 3, the proved evaluator: exp with integers only (GMP's mpz).
// Tang's scheme:
//   x = N ln2/256 + r, N = 256 k + j, 0 <= j < 256, |r| <= 2^-9.5
//   exp(x) = 2^k * 2^(j/256) * exp(r)
// A fixed-point number is an integer X standing for X / 2^FIX_P.
// Designed error (not yet proved): 2^-169 on y, 2^-158 after the split.

#include <assert.h>
#include "fix.h"
#include "eval.h"
#include "fix_table.h"

static mpz_t T[FIX_TAB];      // 2^(j/256), rounded to nearest
static mpz_t ln2;             // ln2/256, with FIX_LG extra bits
static mpz_t C[FIX_DEG + 1];  // 1/i!, rounded down
static mpz_t rmax;            // bound on |r|: 181/256 2^-9 < 2^-9.5
static mpz_t err;             // bound on the error of y: 2^-160

void
fix_init (void)
{
  for (int j = 0; j < FIX_TAB; j++)
    mpz_init_set_str (T[j], fix_T[j], 16);
  mpz_init_set_str (ln2, fix_ln2, 16);
  mpz_t f;
  mpz_init_set_ui (f, 1);
  for (int i = 0; i <= FIX_DEG; i++) {
    if (i > 0) mpz_mul_ui (f, f, i);
    mpz_init (C[i]);
    mpz_setbit (C[i], FIX_P);
    mpz_fdiv_q (C[i], C[i], f);
  }
  mpz_clear (f);
  mpz_init_set_ui (rmax, 181);
  mpz_mul_2exp (rmax, rmax, FIX_P - 17);
  mpz_init (err);
  mpz_setbit (err, FIX_P - 160);
}

// exp(x) = y / 2^FIX_P * 2^k; returns k
static long
fix_exp (mpz_t y, double x)
{
  mpz_t X, r, t;
  mpz_inits (X, r, t, NULL);
  // X = x 2^FIX_P, exactly
  int ex;
  double mx = frexp (x, &ex);
  long sh = ex - 53 + FIX_P;
  assert (sh >= 0);
  mpz_set_si (X, (long) ldexp (mx, 53));
  mpz_mul_2exp (X, X, sh);
  // r = x - N ln2/256, checked small
  long N = (long) nearbyint (x * (FIX_TAB / M_LN2));
  mpz_mul_si (t, ln2, N);
  mpz_fdiv_q_2exp (t, t, FIX_LG);
  mpz_sub (r, X, t);
  mpz_abs (t, r);
  assert (mpz_cmp (t, rmax) < 0);
  // exp(r) by Horner's rule, one truncation per product
  mpz_set (y, C[FIX_DEG]);
  for (int i = FIX_DEG - 1; i >= 0; i--) {
    mpz_mul (y, y, r);
    mpz_fdiv_q_2exp (y, y, FIX_P);
    mpz_add (y, y, C[i]);
  }
  // times 2^(j/256)
  long j = ((N % FIX_TAB) + FIX_TAB) % FIX_TAB;
  mpz_mul (y, y, T[j]);
  mpz_fdiv_q_2exp (y, y, FIX_P);
  // y is not within err of a power of 2, so its exponent is that of exp(x)
  mpz_sub (t, y, err);
  size_t nb = mpz_sizeinbase (t, 2);
  mpz_add (t, y, err);
  assert (mpz_sizeinbase (t, 2) == nb);
  mpz_clears (X, r, t, NULL);
  return (N - j) / FIX_TAB;
}

int
expo_fix (double x)
{
  mpz_t y;
  mpz_init (y);
  long k = fix_exp (y, x);
  int e = (int) mpz_sizeinbase (y, 2) - FIX_P + k;
  mpz_clear (y);
  return e;
}

// the top 53 bits of y, as a double scaled by 2^sc; y keeps the rest
static double
top53 (mpz_t y, long sc)
{
  if (mpz_sgn (y) == 0) return 0.0;
  long sh = (long) mpz_sizeinbase (y, 2) - 53;
  if (sh < 0) sh = 0;
  mpz_t hi;
  mpz_init (hi);
  mpz_fdiv_q_2exp (hi, y, sh);
  double d = ldexp (mpz_get_d (hi), sh + sc);
  mpz_mul_2exp (hi, hi, sh);
  mpz_sub (y, y, hi);
  mpz_clear (hi);
  return d;
}

void
eval_fix (double *h, double *l, double *s, double x)
{
  mpz_t y;
  mpz_init (y);
  long k = fix_exp (y, x);
  *h = top53 (y, k - FIX_P);
  *l = top53 (y, k - FIX_P);
  *s = top53 (y, k - FIX_P);
  mpz_clear (y);
}

// Is x hard to round at level m: is exp(x) 2^(54-e) within 2^-m of an
// integer?  y has nb bits; its top 54 are the integer part, the other
// nb - 54 bits the fraction.  Returns 1 (hard), 0 (not hard), or 2 when
// the error of y does not allow to decide; a caller that builds a
// superset keeps the undecided ones.
int
check_fix (double x, int m)
{
  mpz_t y, low, d, t;
  mpz_inits (y, low, d, t, NULL);
  fix_exp (y, x);
  long f = (long) mpz_sizeinbase (y, 2) - 54;   // bits of the fraction
  mpz_fdiv_r_2exp (low, y, f);                 // the fraction, times 2^f
  mpz_set_ui (d, 0);
  mpz_setbit (d, f);
  mpz_sub (d, d, low);                         // distance to the next integer
  if (mpz_cmp (low, d) < 0) mpz_set (d, low);  // d = the distance, times 2^f
  mpz_set_ui (t, 0);
  mpz_setbit (t, f - m);                       // the threshold 2^-m, times 2^f
  int r;
  mpz_add (low, d, err);
  if (mpz_cmp (low, t) < 0) r = 1;
  else {
    mpz_sub (low, d, err);
    r = mpz_cmp (low, t) >= 0 ? 0 : 2;
  }
  mpz_clears (y, low, d, t, NULL);
  return r;
}
