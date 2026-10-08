fun zero2(a: mut [u64; 2]) {
  for i: u64 = 0 .. 2 {
    a[i] = 0u64;
  }
}

fun g(b: mut [u64; 3]) {
  for j: u64 = 0 .. 3 {
    b[j] = 1u64;
  }
}
