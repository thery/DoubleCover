/* scan.b -- the Lefevre inner loop of htr_plain.c, in Capla.
 *
 * The C being ported is the body of main's chunk loop:
 *
 *   for (i = 0; i < n; i++) {
 *     if (A < twoE) { candidates++; ... }
 *     A = A + B;                     // wraps mod 2^64
 *   }
 *
 * Here the "..." (the exact is_hard test) is dropped: this function only
 * counts the candidates, so it is a pure u64 kernel with no arrays.
 */

fun scan_count(a b twoE: u64, n: u64) -> u64 {
  let cnt: u64 = 0;
  let x: u64 = a;

  for i: u64 = 0 .. n {
    if x < twoE {
      cnt = cnt + 1;
    }
    x = x + b;
  }

  return cnt;
}

/* Same loop, but also reporting the running value of A, so the caller can
 * chain chunks and check the wrap-around against the C reference. */
fun scan_last(a b twoE: u64, n: u64, res: mut [u64; 2]) {
  let cnt: u64 = 0;
  let x: u64 = a;

  for i: u64 = 0 .. n {
    if x < twoE {
      cnt = cnt + 1;
    }
    x = x + b;
  }

  res[0] = cnt;
  res[1] = x;
}
