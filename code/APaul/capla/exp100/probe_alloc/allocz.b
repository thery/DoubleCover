// alloc then read: the semantics gives 0
fun allocz() -> u64 {
  let a = alloc u64, 1;
  let x = a[0];
  free a;
  return x;
}
