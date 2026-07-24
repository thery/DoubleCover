(** * Full search driver: polynomial entries + Lefèvre scan (Z and Int63)

    Starting from a value [v = num/2^54], iterate [n] chunks; each chunk

      - takes its entry data [(A0, B, E)] from the (degree-5) polynomial of
        [Poly] evaluated at the chunk start (no MPFR at runtime), and
      - runs one Lefèvre inner scan over its [2^20] grid points,

    collecting the global positions of the candidate hard-to-round cases.

    Two versions: [search_Z] uses [Lefevre.scan] (Z, mod 2^64) and
    [search63] uses [Lefevre63.scan] (PrimInt63, mod 2^63) — the latter is
    ~120x faster under [vm_compute].

    The polynomial here is [Poly] (valid over the shifted 100-chunk region,
    where the hard case sits at chunk 50); for the true al.c interval
    [[0.25,0.25001)] one would swap in [Cheb]'s degree-7 polynomial. *)

From APaulRocq Require Import Poly.
From APaulRocq Require Lefevre Lefevre63.
From Stdlib Require Import ZArith Uint63 List.
Import ListNotations.
Open Scope Z_scope.

(** ** Entry data from the polynomial

    The polynomial value is [V = P(x)*2^vden].  al.c's per-chunk integers
    are (validated against al.c's own output):

      A0 = frac(exp x * 2^53) * 2^w  +  E     (running distance to the grid)
      B  = frac(exp x / 2)    * 2^w           (per-step increment)
      E  = 2^(w - m_hrc)                      (window; the Taylor term is 0 here)

    with word size [w] (64 for Z, 63 for PrimInt63).  From [V] these are
    integer shifts: the round-bit fraction begins at bit [Pbits = vden-53]. *)

Definition Pbits : Z := vden - 53.        (* = 427 *)
Definition polyV (v : Z) (k : nat) : Z :=
  let d := (v + Z.of_nat k * 2 ^ 20) - Cc in
    A0 * 2 ^ (xden * 5) + A1 * d     * 2 ^ (xden * 4) + A2 * d ^ 2 * 2 ^ (xden * 3)
  + A3 * d ^ 3 * 2 ^ (xden * 2) + A4 * d ^ 4 * 2 ^ xden + A5 * d ^ 5.

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

(** ** The two drivers *)

(** iterate [n] chunks from [v], returning global candidate positions. *)
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

(** ** Example (the [Poly] region: hard case at chunk 50)

    With [v = x0_num] (the shifted start), the driver finds the hard case
    at global position [50*2^20 = 52428800] once [n] reaches 51 — i.e. at
    the 51st iteration.  Verified by [vm_compute] (not run at build time to
    keep compilation fast):

      Eval vm_compute in search63 x0_num 40.   (*  = []          (~14 s) *)
      Eval vm_compute in search63 x0_num 51.   (*  = [52428800]  (~17 s) *)

    [search_Z] gives the identical result but ~132 s per chunk (mod-2^64
    bignum arithmetic), so ~1.9 h for 51 chunks — hence [search63]. *)
