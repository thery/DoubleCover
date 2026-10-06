// enter_loop fails when the function has a local variable named X.
fun f(M: mut [u64; 3]) {
  let X: [u64; 6] = { 0, 0, 0, 0, 0, 0 };
  for i: u64 = 0 .. 3 {
    M[i] = 0u64;
  }
}
