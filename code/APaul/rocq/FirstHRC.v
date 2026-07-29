(** * Long bench — compute the first hard case starting from 0.25

    Runs the Int63 search from [x = 0.25 = x_start / 2^54] across every
    chunk up to and including the first hard-to-round case of [htr.c]
    (parameter [m = 35]), [0x1.00002385331bep-2], which lies at chunk
    9093, fine index 209342, i.e. global grid position
      9093 * 2^20 + 209342 = 9534910910.

    With [htr.c]'s corrected window (see [Search.wE]) the *filter* flags
    ~41 positions per chunk — ~373000 over these 9094 chunks — so the
    candidates must be screened chunk by chunk rather than accumulated:
    [Check.hrc63] fuses the two, re-evaluating the polynomial at each
    candidate and keeping only the genuine hard cases (htr.c's check(),
    via Cheb instead of MPFR).  Over chunks 0..9093 exactly one survives:
      hrc63 x_start 9094 = [9534910910].

    ** THIS IS A LONG RUN — 9094 chunks of 2^20 points (~5% of the full
    htr.c interval).  Measured:
       native_compute : ~13 min (~0.085 s/chunk)  -> full interval ~4.1 h
       vm_compute     : ~4x slower
    Run on demand only; read the "...u" CPU seconds from the Time line. *)

From APaulRocq Require Import Search Check.
From Stdlib Require Import ZArith List.
Open Scope Z_scope.

(** Number of chunks up to and including the one holding the first case. *)
Definition n_chunks_first : nat := 9094.

(** Filter then check, fused per chunk:
      = [9534910910]   (0x1.00002385331bep-2) *)
Time Eval native_compute in hrc63 x_start n_chunks_first.
