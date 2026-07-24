(** * Cross-machine benchmark for the Int63 search

    A fixed, deterministic workload: run [make bench] (which compiles this
    file with [coqc]) and read the two [Time] lines it prints.  Then
    extrapolate to the full al.c interval.

    The full interval [[0.25, 0.25001)] is
      FULL_CHUNKS = (x1num - x0num) / 2^20 = 180143985095 / 2^20 = 171981
    chunks of 2^20 grid points.

    ** Reference (this machine, vm_compute, native_compute disabled):
       - full pipeline, 50 chunks : ~18.0 s   -> full ~= 17.2 h
       - pure Int63 scan, 2^24    : ~2.08 s    -> ~124 ns / point

    ** How to extrapolate:
       If BENCH 1 (below) prints T1 seconds for [BENCH_CHUNKS = 50] chunks,
       the full interval takes about
         T1 * (171981 / 50) = T1 * 3439.6   seconds.
       (18.0 s here -> ~61900 s ~= 17.2 h.)

    Note: in [search63] the degree-7 polynomial entry evaluation dominates
    (~0.23 s/chunk here) over the Int63 scan (~0.13 s/chunk, = 2^20*124 ns).
    BENCH 2 isolates the raw scan so you can see which part your machine
    accelerates.  A machine with native_compute enabled should be markedly
    faster on both. *)

From APaulRocq Require Import Search.
From APaulRocq Require Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Open Scope Z_scope.

(** BENCH 1 — full pipeline: 50 chunks of (polynomial entry + Int63 scan),
    starting at 0.25.  Deterministic result (no HRC in the first 50 chunks). *)
Time Eval vm_compute in List.length (search63 4503599627370496 50).

(** BENCH 2 — pure Int63 recurrence: 2^24 scan steps (advance + compare). *)
Time Eval vm_compute in Lefevre63.bench 0 2654435761 1000000 (2 ^ 24).
