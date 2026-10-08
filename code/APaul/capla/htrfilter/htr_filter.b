// The search of one line (htr3.c, as ../htr3/run/htr3.b) followed by the
// filter of exp100 on each candidate, in Capla; the Capla version of
// ../../vst/htrfilter/htr_filter.c.  The filter maybe_hard_bits is external:
// it is the C function of ../../exp100/exp100.c, linked with this program.
//
// B holds the k coefficients B_0 .. B_(k-1) of the line, l words each, the
// least significant first: B_i is B[i*l .. i*l + l).  On entry
// B_i = P(i) mod 2^(64 l); search turns them into the table of
// differences, adds err to the top word of B_0, and walks j = 0 .. n-1:
// j is a candidate when the top word of B_0 is at most 2 err.  The first
// cap candidates are written in out; the result is their total number.
// search_filter keeps, in order and at the start of out, the candidates
// for which maybe_hard_bits answers 1, and returns their number.

// B_ia += B_ib mod 2^(64 l): htr.c's add, on one array at two offsets.
fun add(B: mut [u64; m], m: u64, ia: u64, ib: u64, l: u64) {
  let cy: u64 = 0;
  let t: u64;
  for i: u64 = 0 .. l {
    t = B[ib + i] + cy;
    B[ia + i] = B[ia + i] + t;
    cy = (u64) ((t < cy) || (B[ia + i] < t));
  }
}

// B_ia -= B_ib mod 2^(64 l): htr.c's sub, on one array at two offsets.
fun sub(B: mut [u64; m], m: u64, ia: u64, ib: u64, l: u64) {
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
      sub(B, m, j * l, (j - 1) * l, l);
      j = j - 1;
    }
  }
}

// One step of the table: for t = 0 .. k-2, B_t += B_(t+1).
fun tstep(B: mut [u64; m], m: u64, k: u64, l: u64) {
  for t: u64 = 0 .. k - 1 {
    add(B, m, t * l, (t + 1) * l, l);
  }
}

// The search of one line; m = k l is the length of B.
fun search(B: mut [u64; m], m: u64, k: u64, l: u64, n: u64, err: u64,
           out: mut [u64; cap], cap: u64) -> u64 {
  let count: u64 = 0;
  difftab(B, m, k, l);
  // the window: err on the top word of B_0
  B[l - 1] = B[l - 1] + err;
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

// 0 only if x (of bits xb) is surely not hard: exp100's filter, in C.
extern fun maybe_hard_bits(xb: u64) -> u64

// The search, then the filter on the candidates written in out.  x0 is the
// double of the line, xb0 its bits, neg its sign (non-zero when x0 < 0):
// the bits of x0 + j u are xb0 + j (x0 > 0) or xb0 - j (x0 < 0).
fun search_filter(B: mut [u64; m], m: u64, k: u64, l: u64, n: u64,
                  err: u64, out: mut [u64; cap], cap: u64, xb0: u64,
                  neg: u64) -> u64 {
  let count: u64 = search(B, m, k, l, n, err, out, cap);
  let c: u64 = count;
  if cap < c { c = cap; }
  let kept: u64 = 0;
  for i: u64 = 0 .. c {
    let j: u64 = out[i];
    let xb: u64 = xb0 + j;
    if neg != 0 { xb = xb0 - j; }
    let r: u64 = maybe_hard_bits(xb);
    if r == 1 {
      out[kept] = j;
      kept = kept + 1;
    }
  }
  return kept;
}
