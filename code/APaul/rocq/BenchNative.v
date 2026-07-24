(** * Native-compute variant of the benchmarks (run: [make bench-native])

    Identical workloads to [Bench.v] but evaluated with [native_compute]
    instead of [vm_compute].  On a build where the native compiler is
    enabled this should be markedly faster (especially BENCH 2, the raw
    PrimInt63 recurrence); on a build without it, Coq prints
    "native_compute disabled ... falling back to vm_compute" and you get
    the [vm_compute] numbers instead.

    Same extrapolation factors as [Bench.v]:
      BENCH 1  full ~= T1 * 3439.6      (50 chunks)
      BENCH 2  full ~= T2 * 10748       (2^24 scan steps)
      BENCH 3  full ~= T3 * 172.0       (1000 poly entries)
    Read the "...u" (user CPU) seconds from each [Time] line. *)

From APaulRocq Require Import Search.
From APaulRocq Require Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Open Scope Z_scope.

(** BENCH 1 — full search: 50 chunks (polynomial entry + Int63 scan). *)
Time Eval native_compute in List.length (search63 4503599627370496 50).

(** BENCH 2 — pure Int63 recurrence: 2^24 scan steps. *)
Time Eval native_compute in Lefevre63.bench 0 2654435761 1000000 (2 ^ 24).

(** BENCH 3 — pure polynomial evaluation: 1000 chunk entries. *)
Time Eval native_compute in
  List.fold_left (fun a k => Z.add a (polyV x_start k)) (List.seq 0 1000) 0%Z.
