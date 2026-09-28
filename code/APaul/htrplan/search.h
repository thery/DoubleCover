// Program 2: the search of htr.c with the evaluator as a parameter.

#include <stdint.h>

// eval (&h, &l, &s, x) approximates exp(x) by h + l + s.  Let e be the
// exponent of exp(x) (as frexp gives it).  The contract is:
//   (C1) |h + l + s - exp(x)| <= 2^-kappa * exp(x)
//   (C2) |l| < 2^(e-53) and |s| < 2^(e-54)
// C2 is what the search needs to read the bits after the round bit from
// l and s alone.  kappa is what the proof of the window asks for.
typedef void (*eval_t) (double *h, double *l, double *s, double x);

// expo (x) returns e, the exponent of exp(x), exactly.
typedef int (*expo_t) (double x);

// report (x) is called on every candidate.  The theorem to prove is that
// every double of [x0, x1) that is hard to round at level m is reported.
typedef void (*report_t) (double x, int m);

void search (eval_t eval, expo_t expo, report_t report,
             double x0, double x1, int m);
