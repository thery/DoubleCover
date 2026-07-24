(** * Screening filter candidates with the polynomial (al.c's check(), in Rocq)

    [Search.search63] is only the *filter*: it returns candidate positions
    ("possible HRC", ~322 over the whole al.c interval), most of which are
    false positives.  al.c then runs [check()] — an MPFR re-evaluation of
    [exp] at each candidate, keeping only those genuinely within [2^-m] of
    the round-bit grid.

    Here we do that check with the degree-7 [Cheb] polynomial instead of
    MPFR: at a candidate we evaluate [P(x)] *exactly* (rational) and test
    the true distance to the grid.  Since [Cheb.cheb_valid] certifies
    [|exp x - P x| <= 2^-160] over the whole interval while the window is
    [2^-30], the polynomial verdict equals the true [exp] verdict.  So the
    whole worst-case search — filter then check — runs in Rocq with no
    MPFR, on a certified polynomial. *)

From APaulRocq Require Import Search Cheb.
From Stdlib Require Import ZArith List.
Import ListNotations.
Open Scope Z_scope.

Definition vden  : Z := cden + 7 * xden.   (* value scale of P(x_k), = 598 *)
Definition Pbits : Z := vden - 53.         (* round-bit-fraction position, = 545 *)
Definition m_hrc : Z := 30.                (* identical bits after the round bit *)

(** [P(x) * 2^vden] at fine grid offset [g] from start [v]: [x = (v+g)/2^54]. *)
Definition polyV_fine (v g : Z) : Z :=
  let d := (v + g) - Cc in
    A0 * 2 ^ (xden * 7) + A1 * d     * 2 ^ (xden * 6) + A2 * d ^ 2 * 2 ^ (xden * 5)
  + A3 * d ^ 3 * 2 ^ (xden * 4) + A4 * d ^ 4 * 2 ^ (xden * 3) + A5 * d ^ 5 * 2 ^ (xden * 2)
  + A6 * d ^ 6 * 2 ^ xden       + A7 * d ^ 7.

Definition dist_to_grid (V P : Z) : Z :=
  let r := V mod 2 ^ P in Z.min r (2 ^ P - r).

(** The polynomial check: is [exp x] genuinely within [2^-m_hrc] of the
    round-bit grid at fine position [g] (start [v])?  This is al.c's
    [check()], via [Cheb] rather than MPFR. *)
Definition check_poly (v g : Z) : bool :=
  Z.ltb (dist_to_grid (polyV_fine v g) Pbits) (2 ^ (Pbits - m_hrc)).

(** Screen a candidate list down to the genuine hard-to-round cases. *)
Definition screen (v : Z) (cands : list Z) : list Z :=
  List.filter (check_poly v) cands.

(** Example: the real hard case survives; the false positives (the first
    filter candidates from the [0.25] run) are rejected. *)
Example screen_example :
  screen x_start [301099550; 801032799; 945509024; 28744619298]
  = [28744619298].
Proof. vm_compute. reflexivity. Qed.

(** The real hard case passes the check; a false positive fails. *)
Example real_passes : check_poly x_start 28744619298 = true.
Proof. vm_compute. reflexivity. Qed.

Example false_positive_fails : check_poly x_start 301099550 = false.
Proof. vm_compute. reflexivity. Qed.
