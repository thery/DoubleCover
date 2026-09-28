// Program 2, the generic search: htr.c with the evaluators as parameters.
//
// x is hard to round at level m when dist (exp(x) 2^(54-e), Z) < 2^-m,
// where e is the exponent of exp(x): 2^(e-1) <= exp(x) < 2^e.
// The theorem:
//   (S) for every double x in [x0, x1) hard to round at level m,
//       search calls report (x, m, v) with v != 0,
// provided the three evaluators meet their specifications below.

#include <stdint.h>

// An evaluator of exp(x) as three doubles h + l + s, with
//   (E1) |h + l + s - exp(x)| <= 2^-kappa * exp(x)
//   (E2) |l| < 2^(e-53) and |s| < 2^(e-54)
// E2 lets the search read the bits after the round bit from l and s alone.
typedef void (*eval_t) (double *h, double *l, double *s, double x);

// An evaluator of exp(x) from below, as one double d, with
//   (E3) d <= exp(x) < d + ulp(d)
// so that d and exp(x) have the same exponent.
typedef double (*low_t) (double x);

// eval_seed gives the line at each chunk start: kappa is fixed by the
// proof of the window, about 118 is enough (computed, not proved).
// eval_check decides each candidate: it must meet E1 and E2 with
// kappa >= KAPPA_CHECK.  Its error is then at most one unit of 2^-64 on
// the fractional part of exp(x) 2^(54-e), and the conversion to 64 bits
// adds two more: CHECK_ERR.  KAPPA_CHECK is a choice that keeps the proof
// simple: about 95 bits would do for m = 35, with a larger CHECK_ERR.
#define KAPPA_CHECK 118
#define CHECK_ERR 3

// report (x, m, v) is called on every candidate x, with the verdict v of
// the check: 1 hard, 0 not hard, 2 undecided.
typedef void (*report_t) (double x, int m, int v);

void search (eval_t eval_seed, low_t eval_low, eval_t eval_check,
             report_t report, double x0, double x1, int m);
