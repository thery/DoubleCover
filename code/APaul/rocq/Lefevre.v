(** * Lefèvre's search loop, in Rocq over [Z]

    This is the "integer half" of the MPFR/Rocq split: the inner loop of
    [al.c]'s [search], written with [Z] arithmetic.  [al.c] runs it on
    [uint64]s; we model the 64-bit wraparound explicitly with [mod 2^64],
    so the Rocq function computes exactly what the C loop computes.

    Recall the C inner loop (per chunk):
    {[
        A += E;                              // shift by the half-window
        for (uint64_t i = 0; i < n; i++) {
          if (A < 2*E) check (x + i*ux, m);  // flag a candidate
          A += B;                            // advance (wraps mod 2^64)
        }
    ]}
    Here [A] is the distance of [exp] to the round-bit grid (as a 64-bit
    fraction), [B] the per-step increment (scaled first derivative), and
    [E] the error-plus-window bound.  The loop flags every grid index [i]
    whose running value [A] lands in the window [[0, 2E)].

    This file only *defines* the search (and its closed form); soundness
    against the reals — that every genuine hard-to-round case is flagged —
    comes later, bridging to the CoqInterval side. *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** ** 64-bit modular arithmetic *)

(** The [uint64] wraparound modulus. *)
Definition two64 : Z := 2 ^ 64.

(** Reduce a [Z] to its [uint64] representative in [[0, 2^64)]. *)
Definition uwrap (a : Z) : Z := a mod two64.

(** ** The search *)

(** The flag test of the inner loop: the running value is inside the
    window, i.e. below the doubled threshold [twoE = 2*E]. *)
Definition is_candidate (A twoE : Z) : bool := A <? twoE.

(** The loop carries a state [(A, i, acc)]: the running value [A], the
    current grid index [i], and the flagged indices so far (in reverse).
    [B] (per-step increment) and [twoE] are the fixed chunk parameters.
    One step tests the current index, then advances [A] with [uint64]
    wraparound. *)
Definition scan_step (B twoE : Z) (st : Z * Z * list Z) : Z * Z * list Z :=
  let '(A, i, acc) := st in
  ( uwrap (A + B),
    Z.succ i,
    if is_candidate A twoE then i :: acc else acc ).

(** One chunk of Lefèvre's search: run [scan_step] for [n] grid points,
    starting from running value [A] at index [i0].

    Counting with [N] and indexing with [Z] keeps the whole loop on
    binary numbers, so [vm_compute] runs a full [2^20]-point chunk almost
    instantly — a unary-[nat] fuel would blow up here.

    Returns the flagged indices (candidates) in increasing order. *)
Definition scan_from (A B twoE i0 : Z) (n : N) : list Z :=
  let '(_, _, acc) := N.iter n (scan_step B twoE) (A, i0, @nil Z) in
  rev acc.

(** Scan a chunk of [n] points starting at grid index [0]. *)
Definition scan (A B twoE : Z) (n : N) : list Z := scan_from A B twoE 0 n.

(** The window has width [2*E]; we name the doubling factor rather than
    writing a bare literal. *)
Definition window_factor : Z := 2.

(** Top-level per-chunk search, matching [al.c] after its [get_uint64]
    conversions:
    - [Alu] = [lu + su]        (bits of [h+l+s] after the round bit),
    - [B]   = [dh + dl]        (scaled first derivative),
    - [E]   = error + window,  [n] = number of grid points.

    We reproduce [al.c]'s [A += E] shift and its [2*E] threshold, both
    reduced mod [2^64]. *)
Definition lefevre_chunk (Alu B E : Z) (n : N) : list Z :=
  scan (uwrap (Alu + E)) B (uwrap (window_factor * E)) n.

(** ** Sanity checks (computed by [vm_compute])

    [vm_compute] runs a full [2^20]-point chunk in ~16 s here
    ([native_compute] is disabled in this build).  That is fine for
    spot-validating single chunks against [al.c]; the full 170k-chunk
    search is far too large to execute in Rocq, so soundness will instead
    use the closed form of the running value ([uwrap (A + i*B)]). *)

(** A rising run [A = i] flags the indices with [i < 2E = 3]. *)
Example scan_basic : scan 0 1 3 10 = [0; 1; 2].
Proof. vm_compute. reflexivity. Qed.

(** The running value wraps at [2^64]: starting two below, the window is
    hit only after the wrap, at indices 2, 3, 4. *)
Example scan_wraps : scan (two64 - 2) 1 3 5 = [2; 3; 4].
Proof. vm_compute. reflexivity. Qed.

(** [lefevre_chunk] applies the [A += E] shift and the [2*E] threshold:
    with [E = 2] the window is [[0,4)] and [A] starts at [2]. *)
Example chunk_demo : lefevre_chunk 0 1 2 8 = [0; 1].
Proof. vm_compute. reflexivity. Qed.
