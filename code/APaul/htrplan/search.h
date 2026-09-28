// Program 2, the generic search: htr.c with the evaluator as a parameter.
//
// x is hard to round at level m when dist (exp(x) 2^(54-e), Z) < 2^-m,
// where e is the exponent of exp(x) (as frexp gives it).  The theorem:
//   (S) for every double x in [x0, x1) hard to round at level m,
//       search calls report (x, m),
// provided eval and expo meet E1 to E3 below.

#include <stdint.h>

// eval (&h, &l, &s, x) approximates exp(x) by h + l + s:
//   (E1) |h + l + s - exp(x)| <= 2^-kappa * exp(x)
//   (E2) |l| < 2^(e-53) and |s| < 2^(e-54)
// kappa is the accuracy the evaluator must reach.  Its value is fixed by
// the proof of the window: about 118 is enough (computed, not proved).
// E2 lets the search read the bits after the round bit from l and s alone.
typedef void (*eval_t) (double *h, double *l, double *s, double x);

// expo (x) returns e, the exponent of exp(x):
//   (E3) 2^(expo(x) - 1) <= exp(x) < 2^expo(x)
// The search scales h, l, s by 2^(54-e), and checks that e is the same
// at both ends of [x0, x1).
typedef int (*expo_t) (double x);

// report (x, m) is called on every candidate x.  S is about these calls.
// A report that filters the candidates with a check (x, m), returning 0
// to reject, must keep every hard x:
//   (E4) dist (exp(x) 2^(54-e), Z) < 2^-m  =>  check (x, m) != 0
typedef void (*report_t) (double x, int m);

void search (eval_t eval, expo_t expo, report_t report,
             double x0, double x1, int m);
