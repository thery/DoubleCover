// search hard-to-round cases of exp(x)

// gcc -O3 -march=native htr.c -lgmp -fopenmp -lm

// ./a.out in
// where in contains one line per subrange to check
// x0 N B0 B1 ... Bk-1
// where each Bj is represented by l 64-bit numbers (lower word first)
// thus we have:
// x0 N B00 B01 ... B0l-1 B10 ... B1l-1 B20 ... B2l-1 ...
// where B0 = B00+2^64*B01+...+2^(64*(l-1))*B0l-1, ...

// Example of input file with one subrange only:
// 0x1.62a3f395a6517p+9 20778149367 0x7ffb221d0e62f2f3 0x753f84509685094d 0x822ff4cbc833e3e5 0x9c99347075121f73 0xe5ae3e4e121c49ca 0x4c57313668df383a 0xf8ab82c672d0237c 0xabccd3de231cbd4c 0x6e1c6dbd99c099f5 0xd53bc0e9e8e3c289 0x2d7c716584677711 0x2ff203469426fcce 0x4cb780997bcdd32f 0xcb1bfce1ddcb860e 0xfc434fc6668fb466 0x534d4ed9fe2de648 0xb759bd3cbebfbedd 0x138cd5575a6b34bb 0x33eca19556d30f6a 0xe7f25b84c4cef108 0xa5da268ebf6b00b5 0x27ad946830951714 0x835981622c6d6446 0xf727a768bbabe003 0x3b05ee7cdd34a7d3 0x2bb1c0cf687a3537 0x398dc1be5f1dc7ad 0x5509b0c4859f1a1c 0x918f1d6438b8acd1 0xdac2797ab7e8fea5 0xc5040444fdd27b48 0xc02b1644fb262aef 0xfc984906def18d93 0xcfdc2c27da312709 0xe20df0d14ee9e06f 0xbe5d4b8d4f2290a1 0x916575ee8efc9fbf 0x393aeb5899bc02e6 0xcbe0fff5a0cef5bb 0x7e6cf7d4300e21af 0x74e95b37da49497e 0xa1f81da0815895f8 0x4aaf07d07b94df46 0x7516a1414bea0418 0x3d25b98cef02caa0 0x38d16e14fb54d3b4 0x4a34bc26461f34c6 0x8592efb44e8b0ea9 0x31323ba395a28553 0xec30e9b161d0b50f 0xc02dfba451a72bd5 0xc8ec523f6ffe263f 0x6203732afdb3f17b 0x692dc1c8b6b9fab4

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

#define K 13
#define L 8

// return non-zero in case of error
static int
read_params (FILE *fp, double *x0, uint64_t *N, int *k, int *l, uint64_t B[K][L]) {
  int ret = fscanf (fp, "%la", x0);
  if (ret != 1) return 1;
  ret = fscanf (fp, "%lu", N);
  if (ret != 1) return 1;
  ret = fscanf (fp, "%d", k);
  if (ret != 1) return 1;
  assert (1 <= *k && *k <= K);
  ret = fscanf (fp, "%d", l);
  if (ret != 1) return 1;
  assert (1 <= *l && *l <= L);
  for (int i = 0; i < *k; i++)
    for (int j = 0; j < *l; j++) {
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
  uint64_t B[K][L];
  int e, ret, k, l;
#pragma omp critical
  ret = read_params (fp, &x0, &N, &k, &l, B);
  if (ret != 0)
    return ret;
  frexp (x0, &e); // x0 = f*2^e with 1/2 <= |f| < 1
  assert (e >= -1021); // ensure no subnormal input
  u = ldexp (1.0, e - 53);
  /* initialize table-of-differences */
  for (int i = 1; i < k; i++) {
    for (int j = k-1; j >= i; j--)
      // B[j] <- B[j] - B[j-1]
      sub (B[j], B[j-1], l);
  }
  static uint64_t ERR = 0x600000; // ceil(2^64*(3*2^-43))
  B[0][l-1] += ERR;
  for (unsigned long i = 0; i < N; i++) {
    if (B[0][l-1] <= 2*ERR)
      check (x0 + i * u);
    for (int j = 0; j < k-1; j++)
      // add (B[j], B[j+1], l);
      mpn_add_n (B[j], B[j], B[j+1], l); // GMP's mpn_add_n is faster
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
  printf ("Processing file %s\n", argv[1]);
  fflush (stdout);
  FILE *fp = fopen (argv[1], "r");
#pragma omp parallel for
  for (int i = 0; i < nthreads; i++)
    doloop (fp);
  fclose (fp);
  printf ("Done\n");
  fflush (stdout);
  return 0;
}
