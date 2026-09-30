// search hard-to-round cases of exp(x)

// gcc -O3 -march=native htr.c -lgmp -fopenmp -lm

// ./a.out in
// where in contains one line per subrange to check
// x0 n B0 B1 ... B7
// where each Bj is represented by l=5 64-bit numbers (lower word first)
// thus we have:
// x0 n B00 B01 ... B04 B10 ... B14 B20 ... B24 ...
// where B0 = B00+2^64*B01+...+2^(64*4)*B04, ...

// Example of input file with one subrange only:
// 0x1.62a3f395a6517p+9 7412951889 0x753f84509685094d 0x822ff4cbc833e3e5 0x9c99347075121f73 0xe5ae3e4e121c49ca 0x4c57313668df383a 0xabccd3de231c7e53 0x6e1c6dbd99c099f5 0xd53bc0e9e8e3c289 0x2d7c716584677711 0x2ff203469426fcce 0xcb1bfce1dd8c8bbf 0xfc434fc6668fb466 0x534d4ed9fe2de648 0xb759bd3cbebfbedd 0x138cd5575a6b34bb 0xe7f25b84be80e191 0xa5da268ebf6b00b5 0x27ad946830951714 0x835981622c6d6446 0xf727a768bbabe003 0x2bb1c0cf297fc691 0x398dc1be5f1dc7ad 0x5509b0c4859f1a1c 0x918f1d6438b8acd1 0xdac2797ab7e8fea5 0xc02b164383c4e2bf 0xfc984906def18d93 0xcfdc2c27da312709 0xe20df0d14ee9e06f 0xbe5d4b8d4f2290a1 0x393aeb524bab0a63 0xcbe0fff5a0cef5bb 0x7e6cf7d4300e21af 0x74e95b37da49497e 0xa1f81da0815895f8 0x7516a12ba8176fad 0x3d25b98cef02caa0 0x38d16e14fb54d3b4 0x4a34bc26461f34c6 0x8592efb44e8b0ea9

#include <stdio.h>
#include <stdint.h>
#include <assert.h>
#include <gmp.h>
#include <math.h>
#include <omp.h>

// {a,n} += {b,n} mod B^n
static void
add (uint64_t *a, uint64_t *b, int n) {
  uint64_t cy = 0;
  for (int i = 0; i < n; i++) {
    uint64_t t = b[i] + cy;
    a[i] += t;
    cy = (t < cy) || (a[i] < t); // at most one condition can hold
  }
}

// {a,n} -= {b,n} mod B^n
static void
sub (uint64_t *a, uint64_t *b, int n) {
  uint64_t cy = 0;
  for (int i = 0; i < n; i++) {
    uint64_t t = b[i] + cy;
    cy = (t < cy) || (a[i] < t); // at most one condition can hold
    a[i] -= t;
  }
}

static void
check (double x) {
#pragma omp critical
  {
    printf ("%la\n", x);
    fflush (stdout);
  }
}

int k = 8; // number of polynomial coefficients (last has degree k-1)
int l = 5; // number of 64-bit words for each coefficient

// return non-zero in case of error
static int
read_params (FILE *fp, double *x0, uint64_t *N, uint64_t B[8][5]) {
  int ret = fscanf (fp, "%la", x0);
  if (ret != 1) return 1;
  ret = fscanf (fp, "%lu", N);
  if (ret != 1) return 1;
  for (int i = 0; i < k; i++)
    for (int j = 0; j < l; j++) {
      ret = fscanf (fp, "%lx", &(B[i][j]));
      if (ret != 1) return 1;
    }
  // read end of line
  getc (fp);
  return 0;
}

// return non-zero in case of end of file
static int
doit (FILE *fp)
{
  double x0, u;
  uint64_t N;
  uint64_t B[8][5];
  int e, ret;
#pragma omp critical
  ret = read_params (fp, &x0, &N, B);
  if (ret != 0)
    return ret;
  frexp (x0, &e); // x0 = f*2^e with 1/2 <= |f| < 1
  u = ldexp (1.0, e - 53);
  /* initialize table-of-differences: initially we have, with all computations
     modulo 2^(64*l):
     B[0] = A[0]
     B[1] = A[0]+A[1]+...+A[k-1]
     ...
     B[k-1] = A[0]+(k-1)*A[1]+...+(k-1)^(k-1)*A[k-1] */
  /* for k=3, we have B0=A0, B1=A0+A1+A2, B2=A0+2*A1+4*A2 */
  for (int i = 1; i < k; i++) {
    for (int j = k-1; j >= i; j--)
      // B[j] <- B[j] - B[j-1]
      sub (B[j], B[j-1], l);
    /* for k=3, after i=1 we have B0=A0, B1=A1+A2, B2=A1+3*A2,
       and after i=2 we have B0=A0, B1=A1+A2, B2=2*A2 */
  }
  static uint64_t ERR = 0x400001; // ceil(2^64*(2^-43+2^-43+2^-90))
  B[0][l-1] += ERR;
  for (unsigned long i = 0; i <= N; i++) {
    if (B[0][l-1] <= 2*ERR)
      check (x0 + i * u);
    for (int j = 0; j < k-1; j++)
      // add (B[j], B[j+1], l);
      mpn_add_n (B[j], B[j], B[j+1], l); // GMP's mpn_add_n is faster
    /* for k=3, if i=1 at the next loop, we now have B0=A0+A1+A2,
       B1=A1+3*A2, B2=2*A2, and if i=2 at the next loop, we now have
       B0=A0+2*A1+4*A2, B1=A1+5*A2, B2=2*A2 */
  }
  return 0;
}

static void
doloop (FILE *fp) {
  while (1) {
    int ret = doit (fp);
    if (ret != 0)
      return;
  }
}

int
main (int argc, char *argv[])
{
  int nthreads;
#pragma omp parallel
  nthreads = omp_get_num_threads ();
  FILE *fp = fopen (argv[1], "r");
#pragma omp parallel for
  for (int i = 0; i < nthreads; i++)
    doloop (fp);
  fclose (fp);
  return 0;
}
