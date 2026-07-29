(** * Native-compute variant of the benchmarks (run: [make bench-native])

    Identical workloads to [Bench.v] but evaluated with [native_compute]
    instead of [vm_compute].  On a build where the native compiler is
    enabled this should be markedly faster (especially BENCH 2, the raw
    PrimInt63 recurrence); on a build without it, Coq prints
    "native_compute disabled ... falling back to vm_compute" and you get
    the [vm_compute] numbers instead.

    Same extrapolation factors as [Bench.v]:
      BENCH 1  full ~= T1 * 3439.6      (50 chunks, filter only)
      BENCH 2  full ~= T2 * 10748       (2^24 scan steps)
      BENCH 3  full ~= T3 * 172.0       (1000 poly entries)
      BENCH 4  full ~= T4 * 3439.6      (50 chunks, filter + screen)
    Read the "...u" (user CPU) seconds from each [Time] line. *)

From APaulRocq Require Import Search Check.
From APaulRocq Require Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Open Scope Z_scope.

(** Number of chunks used by BENCH 1 and BENCH 4 (as in [Bench.v]). *)
Definition bench_chunks : nat := 50.

(** BENCH 1 — filter only: 50 chunks (polynomial entry + Int63 scan). *)
Time Eval native_compute in List.length (search63 x_start bench_chunks).

(** BENCH 2 — pure Int63 recurrence: 2^24 scan steps. *)
Time Eval native_compute in Lefevre63.bench 0 2654435761 1000000 (2 ^ 24).

(** BENCH 3 — pure polynomial evaluation: 1000 chunk entries. *)
Time Eval native_compute in
  List.fold_left (fun a k => Z.add a (polyV x_start k)) (List.seq 0 1000) 0%Z.

(** BENCH 4 — filter + screen over the same 50 chunks. *)
Time Eval native_compute in hrc63 x_start bench_chunks.
