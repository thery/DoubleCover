(** * Long bench — compute the first hard case starting from 0.25

    Runs the Int63 search from [x = 0.25 = x_start / 2^54] across every
    chunk up to and including the first hard-to-round case,
    [0x1.00006b1501522p-2], which lies at chunk 27413, fine index 5410,
    i.e. global grid position
      27413 * 2^20 + 5410 = 28744619298.

    [search63 x_start 27414] scans chunks 0..27413 (each 2^20 points) and
    returns the filter's candidate positions.  The confirmed first hard
    case is [28744619298]; in the two chunks straddling it the filter flags
    only that point (checked separately), so the result list is expected to
    be short:
      Eval ... in search63 x_start 27414.   (* = [28744619298] (+ maybe a
                                                  few earlier candidates) *)

    ** THIS IS A LONG RUN — ~27413 chunks of 2^20 points (~16% of the full
    al.c interval).  Reference (this machine):
       native_compute : ~31 min     (make first-hrc; native compiler)
       vm_compute      : ~1.7 h      (change native_compute -> vm_compute)
    Run on demand only.  Read the "...u" CPU seconds from the Time line. *)

From APaulRocq Require Import Search.
From Stdlib Require Import ZArith List.
Open Scope Z_scope.

Time Eval native_compute in search63 x_start 27414.
