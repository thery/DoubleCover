// A probe of the call mechanism with a row of a table (Sletref on T[j]),
// as exp_core passes T[j] and C[i]; proved in RowCall.v.

// a = b
fun num_copy(a: mut [u64; 6], b: [u64; 6]) {
  for i: u64 = 0 .. 6 {
    a[i] = b[i];
  }
}

// a = T[j], through a call with the row T[j]
fun row_copy(a: mut [u64; 6], T: [[u64; 6]; 64], j: u64) {
  num_copy(a, T[j]);
}
