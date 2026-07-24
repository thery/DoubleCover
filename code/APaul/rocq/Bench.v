(** * Cross-machine benchmarks for the Int63 search

    Run [make bench] (which compiles this file with [coqc]) and read the
    [Time] lines it prints.  Each is a Coq [Time] measurement; use the CPU
    figure — the "...u" (user) seconds, e.g. "19.342u" — which is
    machine-comparable (independent of wall-clock noise).

    The full al.c interval [[0.25, 0.25001)] is
      FULL_CHUNKS = (x1num - x0num) / 2^20 = 180143985095 / 2^20 = 171981
    chunks of 2^20 grid points  (= 2^24 * 10748 points).

    Three benches, with their extrapolation to the full interval:

      BENCH 1  full search: 50 chunks (poly entry + Int63 list-scan)
               full ~= T1 * (171981 / 50)   = T1 * 3439.6
      BENCH 2  pure Int63 scan: 2^24 recurrence steps (counter, no list)
               full ~= T2 * (171981*2^20 / 2^24) = T2 * 10748
      BENCH 3  pure polynomial evaluation: 1000 chunk entries
               full ~= T3 * (171981 / 1000)  = T3 * 172.0

    ** Reference (this machine, vm_compute, native_compute disabled):
       BENCH 1 : ~18.0 s   -> full ~= 17.2 h   (the real per-chunk cost)
       BENCH 2 : ~2.08 s   -> ~6.2 h  (~124 ns/point, counter only)
       BENCH 3 : ~21.0 s   -> ~1.0 h  (~21 ms/eval)

    ** What this says: the polynomial evaluation (BENCH 3, ~0.021 s/chunk)
    is NOT the bottleneck; the search cost is dominated by the list-scan
    used in [search63] (~0.34 s/chunk), which is heavier than the bare
    recurrence of BENCH 2 (~0.13 s/chunk) because it tracks a [Z] index and
    builds the candidate list.  So the biggest win is switching that index
    to a primitive int (and/or enabling native_compute), not speeding up
    the polynomial. *)

From APaulRocq Require Import Search.
From APaulRocq Require Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Open Scope Z_scope.

(** BENCH 1 — full search: 50 chunks of (polynomial entry + Int63 list-scan)
    from 0.25.  Deterministic (no HRC in the first 50 chunks). *)
Time Eval vm_compute in List.length (search63 4503599627370496 50).

(** BENCH 2 — pure Int63 recurrence: 2^24 scan steps (advance + compare). *)
Time Eval vm_compute in Lefevre63.bench 0 2654435761 1000000 (2 ^ 24).

(** BENCH 3 — pure polynomial evaluation: 1000 chunk entries (no scan). *)
Time Eval vm_compute in
  List.fold_left (fun a k => Z.add a (polyV x_start k)) (List.seq 0 1000) 0%Z.
