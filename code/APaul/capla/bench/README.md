# ccomp vs gcc on `htr_plain.c` — the measurement and the assembly

Everything here was produced on 2026-09-18 on one machine, so that the
`ccomp` and `gcc` numbers can be read against each other.

## Machine and compilers

| | |
|---|---|
| CPU | Intel Core Ultra 7 165U (Meteor Lake, 14 threads) |
| OS | Fedora 43, Linux 7.1.9 |
| gcc | 15.3.1 20260722 (Red Hat 15.3.1-1) |
| ccomp | the Capla fork of CompCert, built 2026-08-01 |

## Build commands

```sh
gcc -O2 -Wall htr_plain.c -o htr_gcc          # ../htr_plain.c
ccomp        htr_plain.c -o htr_ccomp         # same source
ccomp htr.b test_htr.c   -o test_htr          # the Capla port
```

## Timings, full range [0.25, 0.25001)

All three print the same five hard-to-round values and the same
`7056503 candidates, found 5 hard-to-round`.

| build | time | vs gcc | iterations/s |
|---|---|---|---|
| `htr_plain.c`, gcc -O2 | 1 m 56.24 s | — | 1.550e9 |
| `htr_plain.c`, ccomp | 2 m 06.84 s | 1.091× | 1.420e9 |
| `htr.b`, ccomp | 2 m 05.43 s | 1.079× | 1.436e9 |

## Why the gap is only 9%

The run is 171799 chunks of 2^20, i.e. **180 144 308 224** iterations of
the inner loop, and only **7 056 503** of them are candidates — 0.0039%.
`poly_eval` and the whole 21-limb layer therefore run once per 2^20
iterations. Over 99.99% of the time is spent in the body of

```c
for (i = 0; i < n; i++)
  {
    if (A < twoE) { candidates++; if (is_hard (X + (int64_t) i)) ... }
    A = A + B;                           /* wraps mod 2^64 */
  }
```

and that body costs six instructions under either compiler:

```
gcc, main+0x1e3            ccomp, main+0x1f0
  add  $1,%r14               cmp  %r14,%r13
  add  %r12,%rbx             jae  <inc>
  cmp  %r13,%r14             lea  (%r13,%r12,1),%r13
  je   <out>                 lea  1(%rbp),%rbp
  cmp  %rbp,%rbx             cmp  $0x100000,%rbp
  jae  <top>                 jb   <top>
```

Neither unrolls it, neither makes it branchless. The visible difference is
that ccomp takes two branches per iteration (forward `jae`, backward `jb`)
where gcc takes one, which is about the size of the measured gap.

The Capla build, whose loop is inside `htr_search` rather than `main`, adds
two stack reloads — `twoE` and `B` do not stay in registers — and is still
level with ccomp on the C:

```
ccomp, htr_search+0x1f4
  mov  0x68(%rsp),%r9        ; twoE
  cmp  %r9,%r12              ; A < twoE ?
  jae  <inc>
  ...
  mov  0x78(%rsp),%rdx       ; B
  lea  (%r12,%rdx,1),%r12    ; A = A + B
  lea  1(%rbx),%rbx
  cmp  $0x100000,%rbx
  jb   <top>
```

## The files

| file | what |
|---|---|
| `gcc-main.s` | `main` of `htr_plain.c`, gcc -O2 |
| `ccomp-main.s` | `main` of `htr_plain.c`, ccomp |
| `gcc-poly_eval.s` | `poly_eval`, gcc -O2 |
| `ccomp-poly_eval.s` | `poly_eval`, ccomp |
| `caplab-main.s` | `main` of `test_htr.c`, ccomp |
| `caplab-htr_search.s` | `htr_search` from `htr.b`, ccomp |

Each was produced with `objdump -d --no-show-raw-insn`.

## Slicing the run

`test_htr` takes the bounds, so the Capla side slices without an edit:

```sh
./test_htr 4503599627370496 4503620598890496    # 20000 chunks, ~14 s
```

For the C, override `X1NUM` with the same value. A 20000-chunk slice gives
the same ratios in a seventh of the time.
