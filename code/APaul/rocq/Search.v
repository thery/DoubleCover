(** * Full search driver: Chebyshev polynomial entries + Lefèvre scan

    Starting from a value [v = num/2^54], iterate [n] chunks; each chunk

      - takes its entry data [(A0, B, E)] from the degree-7 Chebyshev
        polynomial [Cheb] evaluated at the chunk start (no MPFR at runtime),
        following [htr.c] — the fixed version of [al.c], whose window [E]
        now includes the second-order drift over the chunk,
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
    the value is [V = P(x_k)*2^vden] with [vden = cden + 7*xden].  The
    per-chunk integers, validated against [htr.c]'s own per-chunk dump, are

      A0 = frac(exp x * 2^53) * 2^w  +  E    (running distance to the grid)
      B  = frac(exp x / 2)    * 2^w          (per-step increment)
      E  = drift + 2^(w - m_hrc)             (window: model error + target)

    for word size [w] (64 for Z, 63 for PrimInt63).  From [V] these are
    integer shifts; the round-bit fraction begins at bit [Pbits = vden-53]. *)

Definition m_hrc : Z := 35.                 (* identical bits after the round bit *)
Definition vden  : Z := cden + 7 * xden.    (* value scale, = 598 *)
Definition Pbits : Z := vden - 53.          (* round-bit-fraction position, = 545 *)

(** ** The chunk and the drift term — [htr.c]'s correction to [al.c]

    The scan replaces the true phase by the affine model [A + i*B] over a
    whole chunk of [n = 2^log2N] points.  The model error at index [i] is
    the Taylor remainder [(i^2/2)*phi''], [phi = exp*2^53] read on the
    grid, so over a chunk it is at most [(n^2/2)*phi'']; the window [E]
    must absorb it or a genuine hard case can be stepped over.  In the
    word scale that term is [floor (exp x * 2^(w + ddexp))] with

      ddexp = 2*(e_x - 53) + (54 - e_y) - 1 + 2*log2N     (= -16 here)

    ([2*(e_x-53)]: the two factors [ux = 2^(e_x-53)] of the second
    derivative; [54 - e_y]: the scaling that puts [ulp] of the value at 2;
    [-1]: the [/2] of the Taylor term; [2*log2N]: the [n^2]).

    [al.c] omitted the [54 - e_y] factor, so its drift term was
    under-scaled by [2^53], underflowed to [0], and left [E = 2^(w-m)]:
    the filter could miss a real hard case sitting at a large [i] (see
    [al_miss.c]).  [htr.c] adds the missing [ldexp (dd, 54 - e)], which is
    the [wE] below, and is what this file now computes. *)

Definition log2N : Z := 20.                    (* chunk exponent: n = 2^log2N     *)
Definition e_x   : Z := -1.                    (* frexp exponent of x on [0.25,0.5) *)
Definition e_y   : Z := 1.                     (* frexp exponent of exp x there     *)
Definition ddexp : Z := 2 * (e_x - 53) + (54 - e_y) - 1 + 2 * log2N.   (* = -16 *)

(** chunk size (one chunk = [2^log2N] grid points). *)
Definition chunkN : N := (2 ^ Z.to_N log2N)%N.

(** ** The polynomial, evaluated by Horner

    [V = P(x)*2^vden] as a function of [d = x*2^54 - Cc].  The scaled
    coefficients are named constants rather than inline
    [A_k * 2 ^ (xden * (7-k))] products: Rocq's [Z] is a binary [positive],
    so a 220x378-bit product is ~80000 elementary steps, and re-doing the
    seven of them on every call costs 4x the rest of the evaluation.
    Naming them cuts a [polyHorner] call from ~6 ms to ~2 ms — and with
    htr.c's window this runs once per candidate, ~41 per chunk. *)

Definition C0 : Z := A0 * 2 ^ (xden * 7).
Definition C1 : Z := A1 * 2 ^ (xden * 6).
Definition C2 : Z := A2 * 2 ^ (xden * 5).
Definition C3 : Z := A3 * 2 ^ (xden * 4).
Definition C4 : Z := A4 * 2 ^ (xden * 3).
Definition C5 : Z := A5 * 2 ^ (xden * 2).
Definition C6 : Z := A6 * 2 ^ xden.

Definition polyHorner (d : Z) : Z :=
  ((((((A7 * d + C6) * d + C5) * d + C4) * d + C3) * d + C2) * d + C1) * d + C0.

Definition polyV (v : Z) (k : nat) : Z :=
  polyHorner ((v + Z.of_nat k * 2 ^ log2N) - Cc).

(** ** Seeds, at an arbitrary word size [w]

    [V] is positive, so the [/ 2^k] and [mod 2^k] of the derivation are
    written as [Z.shiftr] and [Z.land]: on Rocq's binary [positive] a
    division is quadratic in the operand sizes while a shift or a mask is
    linear, and [V] is ~600 bits wide. *)

(** low-[n]-bits mask, i.e. [x mod 2^n = Z.land x (mask n)] for [x >= 0]. *)
Definition mask (n : Z) : Z := 2 ^ n - 1.

(** window: model drift over the chunk, plus the [2^-m_hrc] target. *)
Definition wE (w V : Z) : Z := Z.shiftr V (vden - ddexp - w) + 2 ^ (w - m_hrc).

(** running value at index 0, already shifted by [E] as [al.c] does. *)
Definition wA (w V : Z) : Z :=
  Z.land (Z.shiftr (Z.land V (mask Pbits)) (Pbits - w) + wE w V) (mask w).

(** per-step increment (scaled first derivative). *)
Definition wB (w V : Z) : Z := Z.land (Z.shiftr V (vden + 1 - w)) (mask w).

Definition w64 : Z := 64.    (* word size of the [Z] scan (al.c's uint64) *)
Definition w63 : Z := 63.    (* word size of the [PrimInt63] scan          *)

(** 64-bit seeds (for the [Z] scan). *)
Definition seedA (V : Z) : Z := wA w64 V.
Definition seedB (V : Z) : Z := wB w64 V.
Definition twoE  (V : Z) : Z := Lefevre.window_factor * wE w64 V.

(** 63-bit seeds (for the [PrimInt63] scan). *)
Definition seedA63 (V : Z) : int := Uint63.of_Z (wA w63 V).
Definition seedB63 (V : Z) : int := Uint63.of_Z (wB w63 V).
Definition twoE63  (V : Z) : int := Uint63.of_Z (Lefevre.window_factor * wE w63 V).

(** ** The two drivers: iterate [n] chunks from [v], global candidate positions *)

Definition search_Z (v : Z) (n : nat) : list Z :=
  concat (map (fun k => let V := polyV v k in
     map (fun loc => Z.of_nat k * 2 ^ log2N + loc)
         (Lefevre.scan (seedA V) (seedB V) (twoE V) chunkN))
     (seq 0 n)).

(** The [PrimInt63] driver takes a per-chunk post-processing [post], so a
    caller can screen each chunk's candidates as they are produced instead
    of accumulating them all: with the corrected [E] the filter flags
    ~[2*E/2^w * 2^log2N ~= 41] positions *per chunk*, so a long run would
    otherwise build a list of hundreds of thousands of elements.  See
    [Check.hrc63]. *)
Definition search63_with (post : list Z -> list Z) (v : Z) (n : nat) : list Z :=
  concat (map (fun k => let V := polyV v k in
     post (map (fun loc => Z.of_nat k * 2 ^ log2N + loc)
               (Lefevre63.scan (seedA63 V) (seedB63 V) (twoE63 V) chunkN)))
     (seq 0 n)).

Definition search63 : Z -> nat -> list Z := search63_with (fun l => l).

(** ** Example — reproduces htr.c's first hard case from the polynomial

    [0.25 = x_start / 2^54].  With [m = 35], [htr.c] reports five hard
    cases on [[0.25, 0.25001)]; the first is [0x1.00002385331bep-2], at
    chunk 9093, fine index 209342, i.e. global position
    [9093*2^20 + 209342 = 9534910910].

    The filter alone flags 41 positions in that chunk (the window is now
    [2E ~= 2^49.4] instead of al.c's [2^35]), so the single-chunk example
    lives in [Check.v], where the polynomial screen cuts those 41 down to
    the one genuine case:

      Eval vm_compute in screen v (search63 v 1) = [209342]   (v = chunk 9093)

    Over the whole interval [htr.c] flags 7056503 positions (~41 per
    chunk) and keeps 5. *)
Definition x_start : Z := 4503599627370496.   (* 0.25 = 2^52 / 2^54 *)

(** ** Cost of the FULL al.c interval [0.25, 0.25001) in Coq

    The interval spans [x1num - x0num = 180143985095] grid points, i.e.
    [~171981] chunks of [2^20].  Measured per-chunk rates (see [Bench.v]),
    polynomial entry evaluation included:

                            vm_compute        native_compute
      search63 (filter)     0.219 s/chunk     0.056 s/chunk  -> full ~2.7 h
      hrc63 (+ screen)      0.319 s/chunk     0.085 s/chunk  -> full ~4.1 h
      search_Z              ~132.7 s/chunk                   -> ~264 days

    For reference, htr.c in C sweeps the whole interval in ~39 s; the
    residual gap is per-operation overhead.

    Note the corrected window costs ~41 candidates per chunk (al.c's
    unsound one flagged ~0.002), so a long run must screen per chunk —
    that is what [search63_with] is for. *)
