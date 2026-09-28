// The evaluators that can be given to search.

// the initial program: MPFR, trusted
double low_mpfr (double x);
void eval_mpfr (double *h, double *l, double *s, double x);

// Program 3, the proved evaluator: integers only, to be proved
void fix_init (void);
double low_fix (double x);
void eval_fix (double *h, double *l, double *s, double x);
