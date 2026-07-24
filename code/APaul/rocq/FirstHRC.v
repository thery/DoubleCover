(** * Long bench — compute the first hard case starting from 0.25

    Runs the Int63 search from [x = 0.25 = x_start / 2^54] across every
    chunk up to and including the first hard-to-round case,
    [0x1.00006b1501522p-2], which lies at chunk 27413, fine index 5410,
    i.e. global grid position
      27413 * 2^20 + 5410 = 28744619298.

    [search63 x_start 27414] scans chunks 0..27413 (each 2^20 points) and
    returns the filter's *candidate* positions ("possible HRC"), NOT the
    confirmed ones.  There are ~53 of them here (the flag probability per
    point is 2E/2^63 = 2^-29, so ~27413*2^20*2^-29 ~= 53, matching al.c's
    density of ~322 over the whole interval).  Most are false positives
    that al.c's check() (an MPFR oracle, not run in Rocq) rejects; only the
    two documented hard cases survive over all of [0.25,0.25001).

    In the returned list:
      - the first CANDIDATE is 301099550 (chunk 287) — reached in seconds;
      - the first CONFIRMED hard case, 0x1.00006b1501522p-2, is at global
        position 27413*2^20 + 5410 = 28744619298 (further down the list).
    Distinguishing the confirmed one requires check(); the Rocq search only
    produces the candidate list.

    ** THIS IS A LONG RUN — ~27413 chunks of 2^20 points (~16% of the full
    al.c interval).  Measured:
       native_compute : ~15.5 min (~0.034 s/chunk)  -> full interval ~1.6 h
       vm_compute      : several x slower
    Run on demand only.  Read the "...u" CPU seconds from the Time line. *)

From APaulRocq Require Import Search.
From Stdlib Require Import ZArith List.
Open Scope Z_scope.

Time Eval native_compute in search63 x_start 27414.
