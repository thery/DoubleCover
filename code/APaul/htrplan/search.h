// Program 2, the generic search: htr.c with the evaluators as parameters.
//
// x is hard to round at level m when dist (exp(x) 2^(54-e), Z) < 2^-m,
// where e is the exponent of exp(x): 2^(e-1) <= exp(x) < 2^e.
// The theorem:
//   (S) for every double x in [x0, x1) hard to round at level m,
//       if search returns nc <= cap, a[0..nc) holds (x, v) with v != 0,
// provided the three evaluators meet their specifications below.  They
// are the only external functions: the exponent and the check are built
// on top of them in search.c.

#include <stdint.h>

// eval_seed (&h, &l, &s, x) gives the line at each chunk start, as three
// doubles h + l + s, with
//   (E1) |h + l + s - exp(x)| <= 2^-kappa * exp(x)
//   (E2) |l| < 2^(e-53) and |s| < 2^(e-54)
// kappa is fixed by the proof of the window: about 118 is enough
// (computed, not proved).  E2 lets the search read the bits after the
// round bit from l and s alone.
typedef void (*seed_t) (double *h, double *l, double *s, double x);

// eval_low (x) gives exp(x) from below, as one double d, with
//   (E3) d <= exp(x) < d + ulp(d)
// so that d and exp(x) have the same exponent.
typedef double (*low_t) (double x);

// eval_check (&h, &l, &s, x) decides each candidate.  It must meet E1 and
// E2 with kappa >= KAPPA_CHECK.  Its error is then at most one unit of
// 2^-64 on the fractional part of exp(x) 2^(54-e), and the conversion to
// 64 bits adds two more: CHECK_ERR.  KAPPA_CHECK is a choice that keeps
// the proof simple: about 95 bits would do for m = 35, with a larger
// CHECK_ERR.
typedef void (*check_t) (double *h, double *l, double *s, double x);
#define KAPPA_CHECK 118
#define CHECK_ERR 3

// A candidate x with the verdict v of the check: 1 hard, 0 not hard,
// 2 undecided.
struct cand { double x; int v; };

// search stores the candidates, in increasing order, in the caller's array
// a of capacity cap, and returns their number nc.  When nc > cap, only the
// first cap are stored, and the caller must call again with a larger a.
unsigned long search (seed_t eval_seed, low_t eval_low, check_t eval_check,
                      double x0, double x1, int m,
                      struct cand *a, unsigned long cap);
