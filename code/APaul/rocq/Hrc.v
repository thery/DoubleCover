(** * Finding hard-to-round cases in the recorded table, in pure [Z]

    This is the piece that was missing: a Rocq function that takes the
    table [dd_data] and returns the indices of all hard-to-round cases,
    computing entirely with [Z] arithmetic on the recorded integers — no
    reals, no MPFR, no CoqInterval in the search itself.

    It is possible precisely because each row stores [h, l, s] as *exact*
    integers.  The recorded value is
      [vR = h*2^-sh + l*2^-sl + s*2^-ss],
    so, in the binade [1,2) (round-bit grid spacing [2^-53]),
      [vR * 2^53 = W / 2^(ss-53)]   with
      [W = h*2^(ss-sh) + l*2^(ss-sl) + s].
    The row is a hard-to-round case (toward a machine number / midpoint)
    exactly when [W] is within [2^(ss-53-m)] of a multiple of [2^(ss-53)],
    i.e. [vR*2^53] is within [2^-m] of an integer.

    (The test inspects the recorded value [vR]; since [Certif.table_correct]
    proves [|vR - exp x| < 2^-160] while the window here is [2^-30], the
    result also identifies the true hard-to-round cases of [exp].  Assumes
    [ss] is the largest scale, [ss >= sl >= sh >= 53], as produced by the
    recorder.) *)

From Stdlib Require Import ZArith List.
From APaulRocq Require Import Data.
Import ListNotations.
Open Scope Z_scope.

(** binary64 significand width. *)
Definition prec53 : Z := 53.

(** Required number of identical bits after the round bit (the [m] of
    [al.c]).  A row is hard-to-round when [exp x] agrees with a grid point
    to within [2^-m_hrc]. *)
Definition m_hrc : Z := 30.

(** Distance (in [[0, 2^P / 2]]) from [W] to the nearest multiple of [2^P]. *)
Definition dist_to_grid (W P : Z) : Z :=
  let r := W mod 2 ^ P in Z.min r (2 ^ P - r).

(** Pure-[Z] hard-to-round test on a recorded row. *)
Definition is_hrc (r : entry) : bool :=
  let W := h r * 2 ^ (ss - sh) + l r * 2 ^ (ss - sl) + s r in
  let P := ss - prec53 in
  Z.ltb (dist_to_grid W P) (2 ^ (P - m_hrc)).

(** Indices of all hard-to-round cases in a table. *)
Definition find_hrc (t : list entry) : list nat :=
  map fst (filter (fun p => is_hrc (snd p))
                  (combine (seq 0 (length t)) t)).

(** Running the detector on the recorded table finds exactly row 50 — the
    hard case [0x1.00006b1501522p-2] — with no prior knowledge of where it
    is.  (Row 50 was placed there by the recorder; this theorem *rediscovers*
    it by computation.) *)
Theorem found_hrc : find_hrc dd_data = [50%nat].
Proof. vm_compute. reflexivity. Qed.
