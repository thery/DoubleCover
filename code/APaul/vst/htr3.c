// The search of htr.c for one line of a table, in plain C for VST.
//
// B holds the k coefficients B_0 .. B_(k-1) of the line, l words each, the
// least significant first: B_i is B[i*l .. i*l + l).  On entry
// B_i = P(i) mod 2^(64 l); search turns them into the table of
// differences, adds err to the top word of B_0, and walks j = 0 .. n-1:
// j is a candidate when the top word of B_0 is at most 2 err.  The first
// cap candidates are written in out; the result is their total number.
// The cut is that of ../capla/htr3/run/htr3.b.

#include <stdint.h>

// B_ia += B_ib mod 2^(64 l): htr.c's add (ADD 2, with _addcarry_u64), on
// one array at two offsets.  gcc compiles _addcarry_u64 to adc; clightgen
// (CompCert, which defines __COMPCERT__) cannot read <immintrin.h> and sees
// a prototype instead: for VST, _addcarry_u64 is an external function whose
// specification (Spec_add.v, addcarry_spec) is assumed.
#ifdef __COMPCERT__
unsigned char _addcarry_u64(unsigned char c, unsigned long long a,
                            unsigned long long b, unsigned long long *out);
#else
#include <immintrin.h>
#endif
static void add(uint64_t *B, uint64_t ia, uint64_t ib, uint64_t l) {
  unsigned char cy = 0;
  for (uint64_t i = 0; i < l; i++)
    cy = _addcarry_u64(cy, B[ia + i], B[ib + i],
                       (unsigned long long *) &B[ia + i]);
}

// B_ia -= B_ib mod 2^(64 l): htr.c's sub, on one array at two offsets.
static void sub(uint64_t *B, uint64_t ia, uint64_t ib, uint64_t l) {
  uint64_t cy = 0;
  for (uint64_t i = 0; i < l; i++) {
    uint64_t t = B[ib + i] + cy;
    cy = (t < cy) || (B[ia + i] < t); // at most one condition can hold
    B[ia + i] -= t;
  }
}

// The table of differences: for i = 1 .. k-1, for j = k-1 down to i,
// B_j -= B_(j-1).
static void difftab(uint64_t *B, uint64_t k, uint64_t l) {
  for (uint64_t i = 1; i < k; i++)
    for (uint64_t j = k - 1; j >= i; j--)
      sub(B, j * l, (j - 1) * l, l);
}

// One step of the table with add: for t = 0 .. k-2, B_t += B_(t+1).  For
// l > 10, where tstep_load does not apply.
static void tstep_add(uint64_t *B, uint64_t k, uint64_t l) {
  for (uint64_t t = 0; t + 1 < k; t++)
    add(B, t * l, (t + 1) * l, l);
}

// One step of the table: for t = 0 .. k-2, B_t += B_(t+1), the old B_(t+1)
// each time, each word read once (as htr_load.c of exp-full-proof): a holds
// the old B_t, b the old B_(t+1), loaded once; B_t = a + b is stored, and b
// becomes a.  l <= 10 (the size of a and b).  The pragmas ask gcc to unroll
// the loops when k and l are constants: without them it stops at the larger
// pairs and the step is slower (clightgen ignores them).
static void tstep_load(uint64_t *B, uint64_t k, uint64_t l) {
  uint64_t a[10], b[10];
#pragma GCC unroll 16
  for (uint64_t i = 0; i < l; i++)
    a[i] = B[i];
#pragma GCC unroll 16
  for (uint64_t t = 0; t + 1 < k; t++) {
#pragma GCC unroll 16
    for (uint64_t i = 0; i < l; i++)
      b[i] = B[(t + 1) * l + i];
    unsigned char cy = 0;
#pragma GCC unroll 16
    for (uint64_t i = 0; i < l; i++)
      cy = _addcarry_u64(cy, a[i], b[i], (unsigned long long *) &B[t * l + i]);
#pragma GCC unroll 16
    for (uint64_t i = 0; i < l; i++)
      a[i] = b[i];
  }
}

// The step with k and l written as constants for the pairs (k, l) of the
// table files, with l alone for other l <= 10, so that gcc unrolls
// tstep_load and keeps a and b in registers.  The switches are on ints (VST
// has no rule for a switch on a 64-bit value): kl is 16 k + l when k <= 13
// and l <= 10, else 0, which is no case; s is l when l <= 10, else 0.
static void tstep(uint64_t *B, uint64_t k, uint64_t l) {
  int kl = k <= 13 && l <= 10 ? (int) (16 * k + l) : 0;
  switch (kl) {
  case 34: tstep_load(B, 2, 2); break;
  case 50: tstep_load(B, 3, 2); break;
  case 67: tstep_load(B, 4, 3); break;
  case 84: tstep_load(B, 5, 4); break;
  case 100: tstep_load(B, 6, 4); break;
  case 117: tstep_load(B, 7, 5); break;
  case 133: tstep_load(B, 8, 5); break;
  case 150: tstep_load(B, 9, 6); break;
  case 167: tstep_load(B, 10, 7); break;
  case 183: tstep_load(B, 11, 7); break;
  case 200: tstep_load(B, 12, 8); break;
  case 216: tstep_load(B, 13, 8); break;
  default:
    {
      int s = l <= 10 ? (int) l : 0;
      switch (s) {
      case 1: tstep_load(B, k, 1); break;
      case 2: tstep_load(B, k, 2); break;
      case 3: tstep_load(B, k, 3); break;
      case 4: tstep_load(B, k, 4); break;
      case 5: tstep_load(B, k, 5); break;
      case 6: tstep_load(B, k, 6); break;
      case 7: tstep_load(B, k, 7); break;
      case 8: tstep_load(B, k, 8); break;
      case 9: tstep_load(B, k, 9); break;
      case 10: tstep_load(B, k, 10); break;
      default: tstep_add(B, k, l); break;
      }
    }
    break;
  }
}

// The search of one line; m = k l is the length of B.
uint64_t search(uint64_t *B, uint64_t m, uint64_t k, uint64_t l, uint64_t n,
                uint64_t err, uint64_t *out, uint64_t cap) {
  uint64_t count = 0;
  difftab(B, k, l);
  B[l - 1] += err;                      // the window
  for (uint64_t j = 0; j < n; j++) {
    if (B[l - 1] <= 2 * err) {
      if (count < cap)
        out[count] = j;
      count++;
    }
    tstep(B, k, l);
  }
  return count;
}
