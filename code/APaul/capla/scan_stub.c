/* scan_stub.c -- scan.b written back in C, so test_scan.c can be linked
 * by gcc alone.  This is the baseline: the same driver built by gcc
 * measures the loop without the Capla toolchain, which is what the ccomp
 * timings are read against.  It is not used when ccomp compiles scan.b.
 */

#include <stdint.h>

uint64_t scan_count (uint64_t a, uint64_t b, uint64_t twoE, uint64_t n)
{
  uint64_t cnt = 0, x = a, i;
  for (i = 0; i < n; i++)
    {
      if (x < twoE)
        cnt++;
      x = x + b;
    }
  return cnt;
}

void scan_last (uint64_t a, uint64_t b, uint64_t twoE, uint64_t n,
                uint64_t *res)
{
  uint64_t cnt = 0, x = a, i;
  for (i = 0; i < n; i++)
    {
      if (x < twoE)
        cnt++;
      x = x + b;
    }
  res[0] = cnt;
  res[1] = x;
}
