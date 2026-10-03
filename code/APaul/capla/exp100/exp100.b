// exp100.c in Capla: the enclosure of exp(x) to about 156 bits and the
// filter maybe_hard.  A probe for the plan doc/exp100-capla-plan.typ.
//
// The differences with exp100.c (code/APaul/exp100):
// - Capla has no global variables: the tables T, C, LN2, RMAX are
//   parameters, filled by the caller (in C) from exp100_table.h;
// - no hexadecimal literals: constants are written in decimal;
// - a number is a [u64; 6] (6 limbs of 32 bits, least significant first);
//   a row of T or C is passed as T[j], C[i];
// - the scratch arrays of num_mulshr, mul_ln2, guess_n are allocated
//   (alloc fills them with zeros) and freed; those of exp_core come from
//   maybe_hard_bits and exp_encl_bits, which allocate them;
// - loops that go down are written as loops that go up, i = 5 - k;
// - num_lt returns a bool, num_bitlen a u64; b, f, be are u64, s and the
//   exponents e, ve are i64.

// a = 0
fun num_zero(a: mut [u64; 6]) {
  for i: u64 = 0 .. 6 {
    a[i] = 0u64;
  }
}

// a = b
fun num_copy(a: mut [u64; 6], b: [u64; 6]) {
  for i: u64 = 0 .. 6 {
    a[i] = b[i];
  }
}

// a = a + b; the sum must fit in 6 limbs
fun num_add(a: mut [u64; 6], b: [u64; 6]) {
  let c: u64 = 0;
  for i: u64 = 0 .. 6 {
    c = c + a[i] + b[i];
    a[i] = c & 4294967295u64;
    c = c >> 32u32;
  }
}

// a = a - b, for a >= b
fun num_sub(a: mut [u64; 6], b: [u64; 6]) {
  let c: u64 = 0;
  for i: u64 = 0 .. 6 {
    let t: u64 = b[i] + c;
    if a[i] >= t {
      a[i] = a[i] - t;
      c = 0u64;
    } else {
      a[i] = a[i] + 4294967296u64 - t;
      c = 1u64;
    }
  }
}

// a < b
fun num_lt(a: [u64; 6], b: [u64; 6]) -> bool {
  for k: u64 = 0 .. 6 {
    let i: u64 = 5 - k;
    if a[i] < b[i] { return true; }
    if a[i] > b[i] { return false; }
  }
  return false;
}

// p = a w on 7 limbs, for w < 2^32
fun num_mul_small(p: mut [u64; 7], a: [u64; 6], w: u64) {
  let c: u64 = 0;
  for i: u64 = 0 .. 6 {
    c = a[i] * w + c;
    p[i] = c & 4294967295u64;
    c = c >> 32u32;
  }
  p[6] = c;
}

// r = floor(a b / 2^160); the quotient must fit in 6 limbs
fun num_mulshr(r: mut [u64; 6], a: [u64; 6], b: [u64; 6]) {
  let p = alloc u64, 12;
  for i: u64 = 0 .. 6 {
    let c: u64 = 0;
    for j: u64 = 0 .. 6 {
      c = a[i] * b[j] + p[i + j] + c;
      p[i + j] = c & 4294967295u64;
      c = c >> 32u32;
    }
    p[i + 6] = c;
  }
  for i: u64 = 0 .. 6 {
    r[i] = p[i + 5];
  }
  free p;
}

// the number of bits of a
fun num_bitlen(a: [u64; 6]) -> u64 {
  let b: u64 = 0;
  for i: u64 = 0 .. 6 {
    for k: u64 = 0 .. 32 {
      if ((a[i] >> (u32) k) & 1u64) == 1u64 {
        b = 32 * i + k + 1;
      }
    }
  }
  return b;
}

// a = 2^f, for f < 192
fun num_pow2(a: mut [u64; 6], f: u64) {
  num_zero(a);
  a[f / 32] = 1u64 << (u32) (f % 32);
}

// a = b mod 2^f, for f < 192
fun num_low(a: mut [u64; 6], b: [u64; 6], f: u64) {
  for i: u64 = 0 .. 6 {
    if i < f / 32 {
      a[i] = b[i];
    } else {
      if i == f / 32 {
        a[i] = b[i] & ((1u64 << (u32) (f % 32)) - 1u64);
      } else {
        a[i] = 0u64;
      }
    }
  }
}

// a = floor(v 2^e), for v < 2^53 and e <= 138
fun num_scale(a: mut [u64; 6], v: u64, e: i64) {
  num_zero(a);
  if e < 0i64 {
    let w: u64 = 0;
    if e > -64i64 {
      w = v >> (u32) (-e);
    }
    a[0] = w & 4294967295u64;
    a[1] = w >> 32u32;
  } else {
    let q: u64 = (u64) e / 32;
    let b: u64 = (u64) e % 32;
    let lo: u64 = (v & 4294967295u64) << (u32) b;
    let hi: u64 = (v >> 32u32) << (u32) b;
    a[q] = lo & 4294967295u64;
    hi = hi + (lo >> 32u32);
    a[q + 1] = hi & 4294967295u64;
    a[q + 2] = hi >> 32u32;
  }
}

// q = floor(n LN2 / 2^32), for n < 2^32
fun mul_ln2(q: mut [u64; 6], n: u64, LN2: [u64; 6]) {
  let p = alloc u64, 7;
  num_mul_small(p, LN2, n);
  for i: u64 = 0 .. 6 {
    q[i] = p[i + 1];
  }
  free p;
}

// the first guess of n: floor(X INV / 2^185), INV = 64/ln2 2^25
fun guess_n(X: [u64; 6]) -> u64 {
  let p = alloc u64, 7;
  num_mul_small(p, X, 3098164009u64);
  let g: u64 = (p[5] >> 25u32) | (p[6] << 7u32);
  free p;
  return g;
}

// The core: y and hs[0] = hN with |exp(x) - y 2^(hN-160)| <= 16 2^(hN-160).
// Returns 0 on success.  X q q1 r h t are scratch.
fun exp_core(xb: u64, y: mut [u64; 6], hs: mut [i64; 1],
             X q q1 r h t: mut [u64; 6],
             T: [[u64; 6]; 64], C: [[u64; 6]; 17],
             LN2 RMAX: [u64; 6]) -> u64 {
  let neg: u64 = xb >> 63u32;
  let be: u64 = (xb >> 52u32) & 2047u64;
  let mx: u64 = xb & 4503599627370495u64;
  if be >= 1033 { return 1u64; }
  if be == 0 {
    be = 1u64;
  } else {
    mx = mx | 4503599627370496u64;
  }
  num_scale(X, mx, (i64) be - 915i64);
  let n: u64 = guess_n(X);
  mul_ln2(q, n, LN2);
  let lt: bool = num_lt(X, q);
  if lt { if n > 0 { n = n - 1; } }
  mul_ln2(q1, n + 1, LN2);
  lt = num_lt(X, q1);
  if !lt { n = n + 1; }
  mul_ln2(q, n, LN2);
  mul_ln2(q1, n + 1, LN2);
  lt = num_lt(X, q);
  if lt { return 2u64; }
  lt = num_lt(X, q1);
  if !lt { return 2u64; }
  let nu: u64 = 0;
  if neg == 1 {
    num_copy(r, q1);
    num_sub(r, X);
    nu = 131072u64 - (n + 1);
  } else {
    num_copy(r, X);
    num_sub(r, q);
    nu = 131072u64 + n;
  }
  lt = num_lt(r, RMAX);
  if !lt { return 3u64; }
  num_copy(h, C[16]);
  for k: u64 = 0 .. 16 {
    let i: u64 = 15 - k;
    num_mulshr(t, h, r);
    num_add(t, C[i]);
    num_copy(h, t);
  }
  let j: u64 = nu & 63u64;
  num_mulshr(y, T[j], h);
  hs[0] = (i64) (nu >> 6u32) - 2048i64;
  return 0u64;
}

// M (3 words of 64 bits) and s[0] with |exp(x) - M 2^s| <= 16 2^s.
fun exp_encl_bits(xb: u64, M: mut [u64; 3], s: mut [i64; 1],
                  T: [[u64; 6]; 64], C: [[u64; 6]; 17],
                  LN2 RMAX: [u64; 6]) -> u64 {
  let y = alloc u64, 6;
  let X = alloc u64, 6;
  let q = alloc u64, 6;
  let q1 = alloc u64, 6;
  let r = alloc u64, 6;
  let h = alloc u64, 6;
  let t = alloc u64, 6;
  let hs = alloc i64, 1;
  let rc: u64 = exp_core(xb, y, hs, X, q, q1, r, h, t, T, C, LN2, RMAX);
  if rc == 0 {
    for i: u64 = 0 .. 3 {
      M[i] = y[2 * i] | (y[2 * i + 1] << 32u32);
    }
    s[0] = hs[0] - 160i64;
  }
  free y; free X; free q; free q1; free r; free h; free t; free hs;
  return rc;
}

// The decision, on the enclosure of exp_core; y lo hi d t are scratch.
fun decide(y: [u64; 6], hN: i64, lo hi d t: mut [u64; 6]) -> u64 {
  num_zero(d);
  d[0] = 16u64;
  num_copy(lo, y);
  num_sub(lo, d);
  num_copy(hi, y);
  num_add(hi, d);
  let b: u64 = num_bitlen(y);
  let bl: u64 = num_bitlen(lo);
  let bh: u64 = num_bitlen(hi);
  if bl != b { return 1u64; }
  if bh != b { return 1u64; }
  let e: i64 = hN - 160i64 + (i64) b - 1i64;
  let ve: i64 = e;
  if e <= -1022i64 { ve = -1022i64; }
  ve = ve - 53i64;
  let fs: i64 = ve - (hN - 160i64);
  if fs < 64i64 { return 1u64; }
  if fs > 184i64 { return 1u64; }
  let f: u64 = (u64) fs;
  num_low(lo, y, f);
  num_pow2(hi, f);
  num_sub(hi, lo);
  let lt: bool = num_lt(lo, hi);
  if lt { num_copy(d, lo); } else { num_copy(d, hi); }
  num_pow2(t, f - 43);
  num_zero(hi);
  hi[0] = 16u64;
  num_add(t, hi);
  lt = num_lt(t, d);
  if lt { return 0u64; }
  return 1u64;
}

// 0 only if x (of bits xb) is surely not hard.
fun maybe_hard_bits(xb: u64, T: [[u64; 6]; 64], C: [[u64; 6]; 17],
                    LN2 RMAX: [u64; 6]) -> u64 {
  let y = alloc u64, 6;
  let X = alloc u64, 6;
  let q = alloc u64, 6;
  let q1 = alloc u64, 6;
  let r = alloc u64, 6;
  let h = alloc u64, 6;
  let t = alloc u64, 6;
  let hs = alloc i64, 1;
  let res: u64 = 1;
  let rc: u64 = exp_core(xb, y, hs, X, q, q1, r, h, t, T, C, LN2, RMAX);
  if rc == 0 {
    res = decide(y, hs[0], X, q, q1, r);
  }
  free y; free X; free q; free q1; free r; free h; free t; free hs;
  return res;
}
