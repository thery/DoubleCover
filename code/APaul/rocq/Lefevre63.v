(** * Lefèvre's search loop over primitive 63-bit integers (fast variant)

    Experimental [PrimInt63] port of [Lefevre.scan].  Coq's primitive
    integers are real machine words under [vm_compute], so the inner loop
    runs ~120x faster than the [Z]/bignum version:

      - one [2^20]-point chunk: ~0.14 s here  (vs ~16.4 s over [Z]);
      - ~130 ns / point           (vs ~15.6 us / point over [Z]).

    ** The 63-vs-64-bit point.
    [al.c]/[htr.c] use [uint64] (wraparound mod [2^64]) only because that
    is the hardware word.  [PrimInt63] wraps mod [2^63], so we run the
    fixed-point one bit coarser (63-bit fractions): [A + B] and [2*E] wrap
    natively, [<?] is native.  This costs no correctness: the
    hard-to-round test only needs the fractional distance to ~[2^-m] ulp
    with [m = 35], and a 63-bit fraction resolves to [2^-63] — a ~28-bit
    margin.  The extra per-step coarsening is [<= 2^-63]; over a [2^20]
    chunk it accumulates to [<= 2^-43], far inside the window [E]
    (~[2^-14.6] since [htr.c] widened it to cover the chunk drift), so
    widening [E] by a negligible margin keeps the filter sound (no hard
    case missed).

    This file provides the computation; the soundness proof (via the
    [Uint63] theory / [to_Z]) is future work. *)

From Stdlib Require Import Uint63 ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** ** The search (over [int = PrimInt63]) *)

(** flag test: running value below the doubled window threshold. *)
Definition is_candidate (A twoE : int) : bool := (A <? twoE)%uint63.

(** one step: test [A], then advance [A += B] with native mod-[2^63] wrap.
    The grid index [i] is a primitive int too, so the loop carries no [Z]
    (the [Z.succ] every step was the main cost); only the flagged indices
    are kept, and they are converted to [Z] once, at the end. *)
Definition scan_step (B twoE : int) (st : int * int * list int) : int * int * list int :=
  let '(A, i, acc) := st in
  ( (A + B)%uint63,
    (i + 1)%uint63,
    if is_candidate A twoE then i :: acc else acc ).

(** scan [n] points from running value [A] at index [i0]. *)
Definition scan_from (A B twoE i0 : int) (n : N) : list Z :=
  let '(_, _, acc) := N.iter n (scan_step B twoE) (A, i0, @nil int) in
  List.map Uint63.to_Z (List.rev acc).

(** scan a chunk of [n] points from index [0]. *)
Definition scan (A B twoE : int) (n : N) : list Z := scan_from A B twoE 0%uint63 n.

(** window width factor [2*E]. *)
Definition window_factor : int := 2.

(** per-chunk search matching the C code's [A += E] shift and [2*E] threshold,
    both wrapping mod [2^63] natively. *)
Definition lefevre_chunk (Alu B E : int) (n : N) : list Z :=
  scan (Alu + E)%uint63 B (window_factor * E)%uint63 n.

(** ** Sanity checks *)

Example scan_basic : scan 0 1 3 10 = [0; 1; 2].
Proof. vm_compute. reflexivity. Qed.

(** wraparound is at [2^63] now: starting two below [max_int]. *)
Example scan_wraps : scan (Uint63.sub Uint63.max_int 1) 1 3 5 = [2; 3; 4].
Proof. vm_compute. reflexivity. Qed.

Example chunk_demo : lefevre_chunk 0 1 2 8 = [0; 1].
Proof. vm_compute. reflexivity. Qed.

(** ** Micro-benchmark

    Count the flags over [n] points; used to measure the raw recurrence
    speed.  [Eval vm_compute in bench 0 2654435761 1000000 (2^20)] returns
    in ~0.14 s (vs ~16.4 s for the [Z] version of the same scan). *)
Definition bench (A B twoE : int) (n : N) : int :=
  snd (N.iter n
        (fun st => let '(a, cnt) := st in
           ((a + B)%uint63, if (a <? twoE)%uint63 then (cnt + 1)%uint63 else cnt))
        (A, 0%uint63)).
