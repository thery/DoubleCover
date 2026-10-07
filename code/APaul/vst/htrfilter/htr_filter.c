// The search of one line (htr3.c, htr.c without GMP) followed by the filter
// of exp100.c on each candidate, for VST.
//
// x0 is the double of the line, xb0 its bits, neg its sign (non-zero when
// x0 < 0).  The inputs x0 + j u of the line keep the exponent of x0, so the
// bits of x0 + j u are xb0 + j (x0 > 0) or xb0 - j (x0 < 0).  search writes
// the first cap candidates j in out; search_filter keeps, in order and at
// the start of out, those for which maybe_hard_bits answers 1 (maybe hard),
// and returns their number.

#include "../htr3.c"
#include "../../exp100/exp100.c"

uint64_t search_filter(uint64_t *B, uint64_t m, uint64_t k, uint64_t l,
                       uint64_t n, uint64_t err, uint64_t *out, uint64_t cap,
                       uint64_t xb0, int neg) {
  uint64_t count = search(B, m, k, l, n, err, out, cap);
  uint64_t c = count;
  if (cap < c) c = cap;                 // the candidates written in out
  uint64_t kept = 0;
  for (uint64_t i = 0; i < c; i++) {
    uint64_t j = out[i];
    uint64_t xb;
    if (neg) xb = xb0 - j; else xb = xb0 + j;
    int r = maybe_hard_bits(xb);
    if (r == 1) {
      out[kept] = j;
      kept++;
    }
  }
  return kept;
}
