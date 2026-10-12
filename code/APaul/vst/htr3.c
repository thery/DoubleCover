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

// B_ia += B_ib mod 2^(64 l): htr.c's add (ADD 1, with ADD_LIMB), on one
// array at two offsets.  The two words are read first, so that gcc need
// not read B[ib + i] again after writing B[ia + i].
#define ADD_LIMB(u,v,c) ((u) += (v), (c) = (u) < (v))
static void add(uint64_t *B, uint64_t ia, uint64_t ib, uint64_t l) {
  uint64_t cy = 0, c, d;
  for (uint64_t i = 0; i < l; i++) {
    uint64_t a = B[ia + i], b = B[ib + i];
    ADD_LIMB(a, cy, c);
    ADD_LIMB(a, b, d);
    B[ia + i] = a;
    cy = c + d;
  }
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

// One step of the table: for t = 0 .. k-2, B_t += B_(t+1).
static void tstep_l(uint64_t *B, uint64_t k, uint64_t l) {
  for (uint64_t t = 0; t + 1 < k; t++)
    add(B, t * l, (t + 1) * l, l);
}

// The same, with l written as a constant in each case (htr_patch.c's step),
// so that the compiler unrolls add and chains the carries; other values of
// l take the loop above.  The switch is on an int (VST has no rule for a
// switch on a 64-bit value): s is l when l <= 10, else 0, which is no case.
static void tstep(uint64_t *B, uint64_t k, uint64_t l) {
  int s = l <= 10 ? (int) l : 0;
  switch (s) {
  case 1: tstep_l(B, k, 1); break;
  case 2: tstep_l(B, k, 2); break;
  case 3: tstep_l(B, k, 3); break;
  case 4: tstep_l(B, k, 4); break;
  case 5: tstep_l(B, k, 5); break;
  case 6: tstep_l(B, k, 6); break;
  case 7: tstep_l(B, k, 7); break;
  case 8: tstep_l(B, k, 8); break;
  case 9: tstep_l(B, k, 9); break;
  case 10: tstep_l(B, k, 10); break;
  default: tstep_l(B, k, l); break;
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
