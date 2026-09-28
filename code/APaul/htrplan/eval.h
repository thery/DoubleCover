// The evaluators that can be given to search.

#include <math.h>

// Program 1: MPFR, trusted
int expo_mpfr (double x);
void eval_mpfr (double *h, double *l, double *s, double x);
int check_mpfr (double x, int m);

// Program 3: integers only, to be proved
void fix_init (void);
int expo_fix (double x);
void eval_fix (double *h, double *l, double *s, double x);
