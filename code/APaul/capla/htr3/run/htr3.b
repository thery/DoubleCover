// The search of htr3.c for one line of a table, in Capla.
//
// B holds the k coefficients B_0 .. B_(k-1) of the line, l words each, the
// least significant first: B_i is B[i*l .. i*l + l).  On entry
// B_i = P(i) mod 2^(64 l); search turns them into the table of
// differences, adds err to the top word of B_0, and walks j = 0 .. n-1 (the
// half-open [x0, x1) of htr3_new.c): j is a candidate when the top word of
// B_0 is at most 2 err.  The first cap
// candidates are written in out; the result is their total number.

// B_ia += B_ib mod 2^(64 l): htr3.c's add.
fun addw(B: mut [u64; m], m: u64, ia: u64, ib: u64, l: u64) {
  let cy: u64 = 0;
  let t: u64;
  for i: u64 = 0 .. l {
    t = B[ib + i] + cy;
    B[ia + i] = B[ia + i] + t;
    cy = (u64) ((t < cy) || (B[ia + i] < t));
  }
}

// B_ia -= B_ib mod 2^(64 l): htr3.c's sub.
fun subw(B: mut [u64; m], m: u64, ia: u64, ib: u64, l: u64) {
  let cy: u64 = 0;
  let t: u64;
  for i: u64 = 0 .. l {
    t = B[ib + i] + cy;
    cy = (u64) ((t < cy) || (B[ia + i] < t));
    B[ia + i] = B[ia + i] - t;
  }
}

// The table of differences: for i = 1 .. k-1, for j = k-1 down to i,
// B_j -= B_(j-1).
fun difftab(B: mut [u64; m], m: u64, k: u64, l: u64) {
  let j: u64;
  for i: u64 = 1 .. k {
    j = k - 1;
    while (j >= i) {
      subw(B, m, j * l, (j - 1) * l, l);
      j = j - 1;
    }
  }
}

// One step of the table: for t = 0 .. k-2, B_t += B_(t+1).
fun tstep(B: mut [u64; m], m: u64, k: u64, l: u64) {
  for t: u64 = 0 .. k - 1 {
    addw(B, m, t * l, (t + 1) * l, l);
  }
}

fun search(B: mut [u64; m], m: u64, k: u64, l: u64, n: u64, err: u64,
           out: mut [u64; cap], cap: u64) -> u64 {
  let count: u64 = 0;
  difftab(B, m, k, l);
  // the window: err on the top word of B_0
  B[l - 1] = B[l - 1] + err;
  // the main loop, j = 0 .. n-1
  for j: u64 = 0 .. n {
    if (B[l - 1] <= 2 * err) {
      if (count < cap) {
        out[count] = j;
      }
      count = count + 1;
    }
    tstep(B, m, k, l);
  }
  return count;
}
