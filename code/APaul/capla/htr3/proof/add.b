// {a,n} += {b,n} mod 2^(64 n): htr3.c's add, line for line.
fun add(a: mut [u64; n], b: [u64; n], n: u64) {
  let cy: u64 = 0;
  let t: u64;
  for i: u64 = 0 .. n {
    t = b[i] + cy;
    a[i] = a[i] + t;
    cy = (u64) ((t < cy) || (a[i] < t));
  }
}
