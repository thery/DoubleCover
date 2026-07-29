(** * Screening filter candidates with the polynomial (htr.c's check(), in Rocq)

    [Search.search63] is only the *filter*: it returns candidate positions
    ("possible HRC"), most of which are false positives.  With [htr.c]'s
    corrected window it flags ~41 positions per chunk (7056503 over the
    whole interval, matching [htr.c]'s own count).  [htr.c] then runs
    [check()] — an MPFR re-evaluation of [exp] at each candidate, keeping
    only those genuinely within [2^-m] of the round-bit grid.

    Here we do that check with the degree-7 [Cheb] polynomial instead of
    MPFR: at a candidate we evaluate [P(x)] *exactly* (rational) and test
    the true distance to the grid.  Since [Cheb.cheb_valid] certifies
    [|exp x - P x| <= 2^-160] over the whole interval while the window is
    [2^-35], the polynomial verdict equals the true [exp] verdict.  So the
    whole worst-case search — filter then check — runs in Rocq with no
    MPFR, on a certified polynomial. *)

From APaulRocq Require Import Search Cheb.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

(** [P(x) * 2^vden] at fine grid offset [g] from start [v]: [x = (v+g)/2^54]. *)
Definition polyV_fine (v g : Z) : Z := polyHorner ((v + g) - Cc).

(** Named once, for the same reason as [Search.C0]..[Search.C6]: [Z.pow] is
    linear in its exponent, and these would otherwise be recomputed — three
    times — at every candidate.  The reduction below the round bit is a
    mask, not a [mod]: [Z.modulo] on a ~600-bit [V] is a long division. *)
Definition two_Pbits : Z := 2 ^ Pbits.               (* round-bit grid step *)
Definition mask_Pbits : Z := mask Pbits.             (* its low-bits mask    *)
Definition win_Pbits : Z := 2 ^ (Pbits - m_hrc).     (* half-window          *)

Definition dist_to_grid (V : Z) : Z :=
  let r := Z.land V mask_Pbits in Z.min r (two_Pbits - r).

(** The polynomial check: is [exp x] genuinely within [2^-m_hrc] of the
    round-bit grid at fine position [g] (start [v])?  This is [htr.c]'s
    [check()], via [Cheb] rather than MPFR. *)
Definition check_poly (v g : Z) : bool :=
  Z.ltb (dist_to_grid (polyV_fine v g)) win_Pbits.

(** Screen a candidate list down to the genuine hard-to-round cases. *)
Definition screen (v : Z) (cands : list Z) : list Z :=
  List.filter (check_poly v) cands.

(** Filter and check fused: each chunk's ~41 candidates are screened as
    soon as they are produced, so a long run never accumulates them. *)
Definition hrc63 (v : Z) (n : nat) : list Z :=
  search63_with (screen v) v n.

(** ** Examples

    Chunk 9093 from [0.25] holds [htr.c]'s first hard case
    [0x1.00002385331bep-2] at fine index 209342.  The filter flags 41
    positions there; the screen keeps exactly one. *)

Definition chunk_first : Z := 9093.               (* chunk of the 1st htr.c case  *)
Definition v_first : Z := x_start + chunk_first * 2 ^ log2N.

Example first_case_chunk : hrc63 v_first 1 = [209342].
Proof. vm_compute. reflexivity. Qed.

Example first_case_filter_size : List.length (search63 v_first 1) = 41%nat.
Proof. vm_compute. reflexivity. Qed.

(** The same run from [0.25] puts it at the global position
    [9093*2^20 + 209342 = 9534910910]. *)
Example first_case_global : check_poly x_start 9534910910 = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The [al.c] case that used to be "the first one"

    [0x1.00006b1501522p-2] (chunk 27413, fine index 5410) is hard to only
    30 bits, so at [m = 35] it is a false positive: the corrected filter
    still flags it — the window is much wider now — but the screen
    rejects it. *)

Definition chunk_al : Z := 27413.
Definition v_al : Z := x_start + chunk_al * 2 ^ log2N.

Example al_case_is_flagged : List.existsb (Z.eqb 5410) (search63 v_al 1) = true.
Proof. vm_compute. reflexivity. Qed.

Example al_case_rejected_at_35 : hrc63 v_al 1 = [].
Proof. vm_compute. reflexivity. Qed.

(** A false positive of the filter fails the check. *)
Example false_positive_fails : check_poly v_first 9466 = false.
Proof. vm_compute. reflexivity. Qed.
