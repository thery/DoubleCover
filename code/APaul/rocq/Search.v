(** * Full search driver: Chebyshev polynomial entries + Lefèvre scan

    Starting from a value [v = num/2^54], iterate [n] chunks; each chunk

      - takes its entry data [(A0, B, E)] from the degree-7 Chebyshev
        polynomial [Cheb] evaluated at the chunk start (no MPFR at runtime),
      - runs one Lefèvre inner scan over its [2^20] grid points,

    collecting the global positions of the candidate hard-to-round cases.

    [Cheb] is certified ([Cheb.cheb_valid]) over the *whole* al.c interval
    [[0.25, 0.25001)], so — unlike the local degree-5 [Poly] — the same
    polynomial drives the search across the entire interval.

    Two versions: [search_Z] uses [Lefevre.scan] (Z, mod 2^64) and
    [search63] uses [Lefevre63.scan] (PrimInt63, mod 2^63, ~120x faster). *)

From APaulRocq Require Import Cheb.
From APaulRocq Require Lefevre Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Import ListNotations.
Open Scope Z_scope.

(** ** Entry data from the polynomial

    [Cheb] gives [P(x) = (sum A_k (x-c)^k)/2^cden].  Written over the grid,
    the value is [V = P(x_k)*2^vden] with [vden = cden + 7*xden].  al.c's
    per-chunk integers, validated against al.c's own output, are

      A0 = frac(exp x * 2^53) * 2^w  +  E    (running distance to the grid)
      B  = frac(exp x / 2)    * 2^w          (per-step increment)
      E  = 2^(w - m_hrc)                     (window; the Taylor term is 0)

    for word size [w] (64 for Z, 63 for PrimInt63).  From [V] these are
    integer shifts; the round-bit fraction begins at bit [Pbits = vden-53]. *)

Definition m_hrc : Z := 30.                 (* identical bits after the round bit *)
Definition vden  : Z := cden + 7 * xden.    (* value scale, = 598 *)
Definition Pbits : Z := vden - 53.          (* round-bit-fraction position, = 545 *)

(** value [V = P(x_k)*2^vden] at chunk [k] from start [v]. *)
Definition polyV (v : Z) (k : nat) : Z :=
  let d := (v + Z.of_nat k * 2 ^ 20) - Cc in
    A0 * 2 ^ (xden * 7) + A1 * d     * 2 ^ (xden * 6) + A2 * d ^ 2 * 2 ^ (xden * 5)
  + A3 * d ^ 3 * 2 ^ (xden * 4) + A4 * d ^ 4 * 2 ^ (xden * 3) + A5 * d ^ 5 * 2 ^ (xden * 2)
  + A6 * d ^ 6 * 2 ^ xden       + A7 * d ^ 7.

(** 64-bit seeds (for the [Z] scan). *)
Definition seedA (V : Z) : Z := ((V mod 2 ^ Pbits) / 2 ^ (Pbits - 64) + 2 ^ (64 - m_hrc)) mod 2 ^ 64.
Definition seedB (V : Z) : Z := (V / 2 ^ (vden + 1 - 64)) mod 2 ^ 64.
Definition twoE  : Z := 2 ^ (64 + 1 - m_hrc).

(** 63-bit seeds (for the [PrimInt63] scan). *)
Definition seedA63 (V : Z) : int := Uint63.of_Z (((V mod 2 ^ Pbits) / 2 ^ (Pbits - 63) + 2 ^ (63 - m_hrc)) mod 2 ^ 63).
Definition seedB63 (V : Z) : int := Uint63.of_Z ((V / 2 ^ (vden + 1 - 63)) mod 2 ^ 63).
Definition twoE63  : int := Uint63.of_Z (2 ^ (63 + 1 - m_hrc)).

(** chunk size (one al.c chunk = 2^20 grid points). *)
Definition chunkN : N := (2 ^ 20)%N.

(** ** The two drivers: iterate [n] chunks from [v], global candidate positions *)

Definition search_Z (v : Z) (n : nat) : list Z :=
  concat (map (fun k => let V := polyV v k in
     map (fun loc => Z.of_nat k * 2 ^ 20 + loc)
         (Lefevre.scan (seedA V) (seedB V) twoE chunkN))
     (seq 0 n)).

Definition search63 (v : Z) (n : nat) : list Z :=
  concat (map (fun k => let V := polyV v k in
     map (fun loc => Z.of_nat k * 2 ^ 20 + loc)
         (Lefevre63.scan (seedA63 V) (seedB63 V) twoE63 chunkN))
     (seq 0 n)).

(** ** Example — reproduces al.c's first hard case from the polynomial

    [0.25 = x_start / 2^54].  The first hard case [0x1.00006b1501522p-2]
    lies at chunk 27413, fine index 5410.  Starting the driver at that
    chunk finds it in one iteration (verified by [vm_compute], ~0.4 s):

      Eval vm_compute in search63 4503628371984384 1.   (* = [5410] *)

    Starting from [0.25] itself, the same hard case appears at global
    position [27413*2^20 + 5410 = 28744619298]:

      Eval vm_compute in search63 x_start 27414.   (* = [28744619298] *)

    but that is ~27413 chunks (~2.5 h with search63; ~42 days with
    search_Z), so only the single-chunk form above is run at build time. *)
Definition x_start : Z := 4503599627370496.   (* 0.25 = 2^52 / 2^54 *)

(** ** Cost of the FULL al.c interval [0.25, 0.25001) in Coq

    The interval spans [x1num - x0num = 180143985095] grid points, i.e.
    [~171981] chunks of [2^20].  At the measured per-chunk rates under
    [vm_compute] (Z: ~132.7 s/chunk; PrimInt63: ~0.34 s/chunk, polynomial
    entry evaluation included):

      - search_Z  : ~171981 * 132.7 s  ~= 2.28e7 s  ~= 264 days (~8.7 months)
      - search63  : ~171981 * 0.22 s   ~= 3.8e4 s   ~= 10.5 hours  (vm_compute)
        (~0.22 s/chunk with the int-indexed Lefevre63.scan; the polynomial
         entry is only ~0.021 s of that, the rest is the 2^20-point scan)

    With native_compute (a native-compiler-enabled build; see
    [make bench-native]) search63 is ~3.5x faster, ~0.065 s/chunk, so the
    full interval is ~3.2 h.  For reference, al.c in C sweeps the whole
    interval in ~35 s; the residual gap is per-operation overhead. *)
