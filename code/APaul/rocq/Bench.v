(** * Cross-machine benchmarks for the Int63 search

    Run [make bench] (which compiles this file with [coqc]) and read the
    [Time] lines it prints.  Each is a Coq [Time] measurement; use the CPU
    figure — the "...u" (user) seconds, e.g. "19.342u" — which is
    machine-comparable (independent of wall-clock noise).

    The full search interval [[0.25, 0.25001)] is
      FULL_CHUNKS = (x1num - x0num) / 2^20 = 180143985095 / 2^20 = 171981
    chunks of 2^20 grid points  (= 2^24 * 10748 points).

    Four benches, with their extrapolation to the full interval:

      BENCH 1  filter only: 50 chunks (poly entry + Int63 scan)
               full ~= T1 * (171981 / 50)   = T1 * 3439.6
      BENCH 2  pure Int63 scan: 2^24 recurrence steps (counter, no list)
               full ~= T2 * (171981*2^20 / 2^24) = T2 * 10748
      BENCH 3  pure polynomial evaluation: 1000 chunk entries
               full ~= T3 * (171981 / 1000)  = T3 * 172.0
      BENCH 4  filter + screen: the same 50 chunks through [Check.hrc63]
               full ~= T4 * 3439.6

    BENCH 4 minus BENCH 1 is the cost of screening: with htr.c's corrected
    window the filter flags ~41 candidates per chunk (BENCH 1 returns
    ~2050 over the 50 chunks), and each is re-evaluated by the polynomial.

    ** Reference (this machine, user CPU seconds):
       [make bench]        (vm_compute):
         B1 10.95 (0.219 s/chunk)   B2 2.14   B3 4.16   B4 15.96 -> full ~15.2 h
       [make bench-native] (native_compute):
         B1  2.79 (0.056 s/chunk)   B2 0.26   B3 2.08   B4  4.25 -> full  ~4.1 h

    ** What this says: the filter (B1) is ~2/3 of the work and the screen
    ~1/3.  [Lefevre63.scan] carries a primitive-int index (no [Z.succ] per
    step) and conses only flagged candidates, so it stays close to the bare
    recurrence of BENCH 2.  Both the polynomial (B3) and the screen were
    dominated by avoidable [Z] costs — [Z.pow] is linear in its exponent
    and [Z.modulo] on a ~600-bit [V] is a long division — hence the named
    scaled coefficients [Search.C0]..[C6] and the [Z.land]/[Z.shiftr] forms
    in [Search.wA] and [Check.dist_to_grid]: together they took B4 from
    ~15 s to ~4.2 s under native_compute.  Use [make bench-native] if your
    build has the native compiler. *)

From APaulRocq Require Import Search Check.
From APaulRocq Require Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Open Scope Z_scope.

(** Number of chunks used by BENCH 1 and BENCH 4. *)
Definition bench_chunks : nat := 50.

(** BENCH 1 — filter only: 50 chunks of (polynomial entry + Int63 scan)
    from 0.25.  Deterministic: ~41 candidates per chunk. *)
Time Eval vm_compute in List.length (search63 x_start bench_chunks).

(** BENCH 2 — pure Int63 recurrence: 2^24 scan steps (advance + compare). *)
Time Eval vm_compute in Lefevre63.bench 0 2654435761 1000000 (2 ^ 24).

(** BENCH 3 — pure polynomial evaluation: 1000 chunk entries (no scan). *)
Time Eval vm_compute in
  List.fold_left (fun a k => Z.add a (polyV x_start k)) (List.seq 0 1000) 0%Z.

(** BENCH 4 — filter + screen over the same 50 chunks (no HRC there, so
    the result is the empty list). *)
Time Eval vm_compute in hrc63 x_start bench_chunks.
