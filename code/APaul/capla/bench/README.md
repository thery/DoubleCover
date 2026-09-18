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

## The ratio is a property of the core, not of the code — 2026-09-18

A Capla developer rebuilt this exact gcc from the Fedora packages, got
assembly identical to the files here, and still measured 55 s against
ccomp's 2 m 30 s. Same instructions, a 2.7x gap on his machine and 1.09x
on ours.

The explanation is that this CPU is **hybrid**, and the two core types do
not run these two loops the same way. Pinning the *same binaries* with
`taskset` (20000-chunk slice, 2-3 passes each, medians):

| core | gcc -O2 | ccomp | ccomp/gcc | Capla | Capla/gcc |
|---|---|---|---|---|---|
| cpu0, P-core (Redwood Cove) | 14.39 s | 15.03 s | **1.04x** | 15.67 s | 1.09x |
| cpu6, E-core (Crestmont) | 16.55 s | 35.12 s | **2.12x** | 43.66 s | 2.64x |
| cpu12, LP E-core | 20.61 s | 44.92 s | **2.18x** | — | — |

Nothing else changed: same files, same machine, same run. The gap is 1.04x
or 2.18x depending only on which core the kernel picked. Our unpinned runs
landed on P-cores; the developer's machine is in the same regime as our
E-cores, and his 2.72x / 2.77x sit next to our 2.12x / 2.64x.

The mechanism is in the branch layout, and it is visible in the assembly
above. Per iteration of the hot loop:

- **gcc takes one branch**: the backward `jae <top>`, with the `je <out>`
  falling through. The common case — not a candidate, 99.996% of the time
  — is the taken backward branch, and nothing else.
- **ccomp takes two**: the forward `jae <inc>` to reach the increment, then
  the backward `jb <top>`. It puts the common case on a taken *forward*
  branch instead of letting it fall through.

A core that retires one taken branch per cycle therefore needs at least two
cycles per iteration for the ccomp loop and one for the gcc loop — a
ceiling of 2x, which is what the E-cores show. The wide P-core absorbs the
second taken branch and the two come out level.

**So this is not a codegen-quality difference in the usual sense.** Both
compilers emit six instructions doing the same work. What separates them is
which side of the branch the hot path sits on, and that only costs anything
on a narrow front end. If CompCert laid the common case out as fall-through
the gap would close on every core.

## The files

| file | what |
|---|---|
| `gcc-main.s` | `main` of `htr_plain.c`, gcc -O2 |
| `ccomp-main.s` | `main` of `htr_plain.c`, ccomp |
| `gcc-poly_eval.s` | `poly_eval`, gcc -O2 |
| `ccomp-poly_eval.s` | `poly_eval`, ccomp |
| `caplab-main.s` | `main` of `test_htr.c`, ccomp |
| `caplab-htr_search.s` | `htr_search` from `htr.b`, ccomp |

The pinned runs above are reproducible with
`taskset -c <cpu> ./test_htr 4503599627370496 4503620598890496`;
`lscpu -e` says which cpu is which core type.

Each was produced with `objdump -d --no-show-raw-insn`.

## Slicing the run

`test_htr` takes the bounds, so the Capla side slices without an edit:

```sh
./test_htr 4503599627370496 4503620598890496    # 20000 chunks, ~14 s
```

For the C, override `X1NUM` with the same value. A 20000-chunk slice gives
the same ratios in a seventh of the time.
