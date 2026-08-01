/* htr.b -- the whole hard-to-round search of htr_plain.c, in Capla.
 *
 * Capla has no input/output, so where the C prints each case this
 * returns them: htr_search fills the caller's array with the X it finds
 * and returns how many there were.  Everything else is htr_plain.c's
 * main and is_hard, on top of the big_* layer of poly.b.
 */

include! poly

macro! MHRC   { 35u64 }           /* identical bits after the round bit    */
macro! LOG2N  { 20u64 }           /* chunk size n = 2^LOG2N                */
macro! ESHIFT { 550u64 }          /* VDEN - DDEXP - 64                     */
macro! ASHIFT { 481u64 }          /* PBITS - 64                            */
macro! BSHIFT { 535u64 }          /* VDEN + 1 - 64                         */
macro! TOPBIT { 510u64 }          /* PBITS - MHRC                          */
macro! CCNUM  { 4503689699363044i64 }      /* expansion centre c * 2^XDEN  */

/* Is x = X / 2^XDEN a hard-to-round case: are the MHRC bits following the
 * round bit of P(x) all equal?  V and t are scratch the caller owns. */
fun is_hard(X: i64, CO: [[u32; n]; 8], V: mut [u32; n], t: mut [u32; n],
            n: u64) -> bool {
  let mask: u64 = (1u64 << (u32) MHRC!) - 1u64;

  poly_eval(X - CCNUM!, V, CO, t, n);
  let top: u64 = big_bits64(V, TOPBIT!, n) & mask;
  if top == 0 {
    return true;
  }
  if top == mask {
    return big_low_nonzero(V, TOPBIT!, n);
  }
  return false;
}

/* The search over [x0, x1).  Each case found is written to out, up to cap
 * of them; the return value counts them all, so a caller whose array was
 * too small can tell.  stats gets the candidate and the found counts.
 *
 * CO is the coefficient table, filled here by init_coeffs but allocated
 * by the caller: alloc takes only primitive element types, so an
 * [[u32; n]; 8] cannot be allocated inside Capla. */
fun htr_search(x0 x1: i64, CO: mut [[u32; n]; 8],
               out: mut [i64; cap], cap: u64,
               stats: mut [u64; 2], n: u64) -> u64 {
  let V = alloc u32, n;
  let V2 = alloc u32, n;
  let t = alloc u32, n;

  init_coeffs(CO, n);

  let cand: u64 = 0;
  let found: u64 = 0;
  let X: i64 = x0;
  let m: u64 = 1u64 << (u32) LOG2N!;

  while X < x1 {
    poly_eval(X - CCNUM!, V, CO, t, n);
    let E: u64 = big_bits64(V, ESHIFT!, n)
               + (1u64 << (u32) (64 - MHRC!));
    let A: u64 = big_bits64(V, ASHIFT!, n) + E;    /* wraps mod 2^64 */
    let B: u64 = big_bits64(V, BSHIFT!, n);
    let twoE: u64 = 2 * E;

    for i: u64 = 0 .. m {
      if A < twoE {
        cand = cand + 1;
        if is_hard(X + (i64) i, CO, V2, t, n) {
          if found < cap {
            out[found] = X + (i64) i;
          }
          found = found + 1;
        }
      }
      A = A + B;                                   /* wraps mod 2^64 */
    }
    X = X + (i64) m;
  }

  stats[0] = cand;
  stats[1] = found;

  free V;
  free V2;
  free t;
  return found;
}

/* The same search, as a checker rather than a producer: want is prefilled
 * by an oracle with the hard cases, in increasing order, and this only
 * verifies that the search finds exactly those.  There is no output array
 * to size and no case where the answer is truncated, which is why this is
 * the variant to state a specification about.
 *
 * The search visits X in increasing order, so one index into want is
 * enough: each case found must be the next one expected, and every entry
 * of want must be consumed by the end. */
fun htr_check(x0 x1: i64, CO: mut [[u32; n]; 8],
              want: [i64; k], k: u64,
              stats: mut [u64; 2], n: u64) -> bool {
  let V = alloc u32, n;
  let V2 = alloc u32, n;
  let t = alloc u32, n;

  init_coeffs(CO, n);

  let cand: u64 = 0;
  let found: u64 = 0;
  let j: u64 = 0;
  let ok: bool = true;
  let X: i64 = x0;
  let m: u64 = 1u64 << (u32) LOG2N!;

  while X < x1 {
    poly_eval(X - CCNUM!, V, CO, t, n);
    let E: u64 = big_bits64(V, ESHIFT!, n)
               + (1u64 << (u32) (64 - MHRC!));
    let A: u64 = big_bits64(V, ASHIFT!, n) + E;    /* wraps mod 2^64 */
    let B: u64 = big_bits64(V, BSHIFT!, n);
    let twoE: u64 = 2 * E;

    for i: u64 = 0 .. m {
      if A < twoE {
        cand = cand + 1;
        if is_hard(X + (i64) i, CO, V2, t, n) {
          found = found + 1;
          if j < k {
            if want[j] != X + (i64) i {
              ok = false;                  /* not the case expected here */
            }
            j = j + 1;
          } else {
            ok = false;                    /* more cases than the oracle */
          }
        }
      }
      A = A + B;                                   /* wraps mod 2^64 */
    }
    X = X + (i64) m;
  }

  if j != k {
    ok = false;                            /* oracle entries never found */
  }

  stats[0] = cand;
  stats[1] = found;

  free V;
  free V2;
  free t;
  return ok;
}
