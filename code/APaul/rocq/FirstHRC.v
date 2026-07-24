(** * Long bench — compute the first hard case starting from 0.25

    Runs the Int63 search from [x = 0.25 = x_start / 2^54] across every
    chunk up to and including the first hard-to-round case,
    [0x1.00006b1501522p-2], which lies at chunk 27413, fine index 5410,
    i.e. global grid position
      27413 * 2^20 + 5410 = 28744619298.

    [search63 x_start 27414] (the filter) produces ~53 *candidate* positions
    over these chunks (flag probability 2E/2^63 = 2^-29, so
    ~27413*2^20*2^-29 ~= 53, matching al.c's density of ~322 over the whole
    interval).  Most are false positives; [Check.screen] re-evaluates the
    polynomial at each and keeps only the genuine hard cases (al.c's
    check(), via Cheb instead of MPFR).  The second al.c hard case is at
    chunk 62291 (> 27413), so over chunks 0..27413 exactly one survives:
      screen x_start (search63 x_start 27414) = [28744619298].

    ** THIS IS A LONG RUN — ~27413 chunks of 2^20 points (~16% of the full
    al.c interval).  Measured:
       native_compute : ~15.5 min (~0.034 s/chunk)  -> full interval ~1.6 h
       vm_compute      : several x slower
    Run on demand only.  Read the "...u" CPU seconds from the Time line. *)

From APaulRocq Require Import Search Check.
From Stdlib Require Import ZArith List.
Open Scope Z_scope.

(** Filter then check: [search63] produces the ~53 candidates and [screen]
    keeps only the genuine hard cases (via the polynomial, no MPFR).  The
    second al.c hard case is at chunk 62291 (> 27413), so over these chunks
    exactly one survives:
      = [28744619298]   (0x1.00006b1501522p-2)
    The screen adds only ~1 s on top of the ~15.5 min filter. *)
Time Eval native_compute in screen x_start (search63 x_start 27414).
