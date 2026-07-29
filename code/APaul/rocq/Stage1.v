(** * Stage 1 — certifying the hard-to-round cases found by [htr.c]

    [htr.c] (the corrected [al.c]: its per-chunk window now covers the
    second-order drift, see [al_miss.c] and [Search.wE]) searches for
    hard-to-round cases of the exponential over binary64 arguments.  On
    the interval [0.25, 0.25001) with parameter [m = 35] it reports
    exactly five inputs:

        0x1.00002385331bep-2   0x1.0000561fc7e06p-2   0x1.0001cd08ef3d4p-2
        0x1.00026c769e211p-2   0x1.00028a78a7303p-2

    (independently confirmed by BaCSeL, see the comment in [htr.c]).

    What [htr.c]'s [check()] tests is proximity to the *round-bit grid* of
    spacing [2^-53] on the binade [1,2) — it rounds [exp x] to 54 bits and
    asks whether that is already the [53+m]-bit value.  Grid points with an
    even significand are machine numbers, those with an odd significand are
    the midpoints between two consecutive ones; both are worst cases (the
    first for the directed roundings, the second for round-to-nearest).
    Four of the five below sit next to a machine number, one
    ([0x1.00026c769e211p-2]) next to a midpoint.

    For each of them [exp x] lies within [2^-88] of its grid point — i.e.
    35 identical bits follow the round bit.  Here we certify this
    rigorously with CoqInterval.  Everything below is proved from the
    reals; no floating-point model is assumed yet (that comes in Stages 2
    and 3). *)

From Stdlib Require Import Reals ZArith Lia Lra.
From Interval Require Import Tactic.
Open Scope R_scope.

(** ** Specification *)

(** A real [G] is a point of the round-bit grid on the binade [1,2):
    [G = k / 2^53] with [2^53 <= k < 2^54].  [k] even means [G] is a
    representable binary64 number; [k] odd means [G] is a midpoint. *)
Definition is_grid_1_2 (G : R) : Prop :=
  exists k : Z, (2 ^ 53 <= k < 2 ^ 54)%Z /\ G = IZR k / 2 ^ 53.

(** A representable binary64 number in the binade [1,2): [D = n / 2^52]
    with [2^52 <= n < 2^53] (the ulp on this binade is [2^-52]). *)
Definition is_double_1_2 (D : R) : Prop :=
  exists n : Z, (2 ^ 52 <= n < 2 ^ 53)%Z /\ D = IZR n / 2 ^ 52.

(** [x] is a hard-to-round case with [N] extra identical bits: [exp x] is
    within [2^-(53+N)] of a grid point, equivalently within [2^-N] of the
    round-bit position.  (53 significand bits + N bits below the round
    bit.) *)
Definition htr_toward_grid (x : R) (N : nat) : Prop :=
  exists G : R, is_grid_1_2 G /\ Rabs (exp x - G) < / 2 ^ (53 + N).

(** ** The five reported inputs, as exact rationals [M / 2^54] *)

Definition x1 : R := 4503609162281406 / 2 ^ 54.   (* 0x1.00002385331bep-2 *)
Definition x2 : R := 4503622746144262 / 2 ^ 54.   (* 0x1.0000561fc7e06p-2 *)
Definition x3 : R := 4503723385484244 / 2 ^ 54.   (* 0x1.0001cd08ef3d4p-2 *)
Definition x4 : R := 4503766181732881 / 2 ^ 54.   (* 0x1.00026c769e211p-2 *)
Definition x5 : R := 4503774236930819 / 2 ^ 54.   (* 0x1.00028a78a7303p-2 *)

(** The nearby grid points [G = k / 2^53]. *)

Definition G1 : R := 11565478897793914 / 2 ^ 53.  (* k even -> a double   *)
Definition G2 : R := 11565487618814400 / 2 ^ 53.  (* k even -> a double   *)
Definition G3 : R := 11565552230813028 / 2 ^ 53.  (* k even -> a double   *)
Definition G4 : R := 11565579706769917 / 2 ^ 53.  (* k ODD  -> a midpoint *)
Definition G5 : R := 11565584878358332 / 2 ^ 53.  (* k even -> a double   *)

Lemma G1_grid : is_grid_1_2 G1.
Proof. exists 11565478897793914%Z. split; [lia | reflexivity]. Qed.

Lemma G2_grid : is_grid_1_2 G2.
Proof. exists 11565487618814400%Z. split; [lia | reflexivity]. Qed.

Lemma G3_grid : is_grid_1_2 G3.
Proof. exists 11565552230813028%Z. split; [lia | reflexivity]. Qed.

Lemma G4_grid : is_grid_1_2 G4.
Proof. exists 11565579706769917%Z. split; [lia | reflexivity]. Qed.

Lemma G5_grid : is_grid_1_2 G5.
Proof. exists 11565584878358332%Z. split; [lia | reflexivity]. Qed.

(** ** Rigorous enclosures (the numeric heart of Stage 1)

    Each says [exp x] is within [2^-88] of the corresponding grid point.
    The true distances are [2^-35.5 .. 2^-37.5] half-ulps, so the margin
    on the weakest one is only ~0.46 bit: the enclosures are computed at
    [i_prec 120]. *)

Lemma exp_x1_near_G1 : Rabs (exp x1 - G1) < / 2 ^ 88.
Proof. unfold x1, G1. interval with (i_prec 120). Qed.

Lemma exp_x2_near_G2 : Rabs (exp x2 - G2) < / 2 ^ 88.
Proof. unfold x2, G2. interval with (i_prec 120). Qed.

Lemma exp_x3_near_G3 : Rabs (exp x3 - G3) < / 2 ^ 88.
Proof. unfold x3, G3. interval with (i_prec 120). Qed.

Lemma exp_x4_near_G4 : Rabs (exp x4 - G4) < / 2 ^ 88.
Proof. unfold x4, G4. interval with (i_prec 120). Qed.

Lemma exp_x5_near_G5 : Rabs (exp x5 - G5) < / 2 ^ 88.
Proof. unfold x5, G5. interval with (i_prec 120). Qed.

(** ** Main results

    All five reported inputs are genuine hard-to-round cases with 35
    identical bits after the round bit ([53 + 35 = 88]). *)

Theorem case1_hard : htr_toward_grid x1 35.
Proof. exists G1. split; [exact G1_grid | exact exp_x1_near_G1]. Qed.

Theorem case2_hard : htr_toward_grid x2 35.
Proof. exists G2. split; [exact G2_grid | exact exp_x2_near_G2]. Qed.

Theorem case3_hard : htr_toward_grid x3 35.
Proof. exists G3. split; [exact G3_grid | exact exp_x3_near_G3]. Qed.

Theorem case4_hard : htr_toward_grid x4 35.
Proof. exists G4. split; [exact G4_grid | exact exp_x4_near_G4]. Qed.

Theorem case5_hard : htr_toward_grid x5 35.
Proof. exists G5. split; [exact G5_grid | exact exp_x5_near_G5]. Qed.

(** ** The two cases [al.c] used to report

    With the unsound window, [al.c] ran at [m = 30] and reported
    [0x1.00006b1501522p-2] and [0x1.0000f35300644p-2].  Those are genuine
    30-bit hard cases (and near machine numbers), just not 35-bit ones, so
    they do not appear in [htr.c]'s list.  Kept here because Stages 2/3
    and [Check.v] use them as reference points. *)

Definition xa : R := 4503628371989794 / 2 ^ 54.   (* 0x1.00006b1501522p-2 *)
Definition xb : R := 4503664944219716 / 2 ^ 54.   (* 0x1.0000f35300644p-2 *)

Definition Ga : R := 11565491230683926 / 2 ^ 53.  (* k even -> a double *)
Definition Gb : R := 11565514710581608 / 2 ^ 53.  (* k even -> a double *)

Lemma Ga_grid : is_grid_1_2 Ga.
Proof. exists 11565491230683926%Z. split; [lia | reflexivity]. Qed.

Lemma Gb_grid : is_grid_1_2 Gb.
Proof. exists 11565514710581608%Z. split; [lia | reflexivity]. Qed.

Lemma exp_xa_near_Ga : Rabs (exp xa - Ga) < / 2 ^ 83.
Proof. unfold xa, Ga. interval with (i_prec 100). Qed.

Lemma exp_xb_near_Gb : Rabs (exp xb - Gb) < / 2 ^ 83.
Proof. unfold xb, Gb. interval with (i_prec 100). Qed.

Theorem caseA_hard_30 : htr_toward_grid xa 30.
Proof. exists Ga. split; [exact Ga_grid | exact exp_xa_near_Ga]. Qed.

Theorem caseB_hard_30 : htr_toward_grid xb 30.
Proof. exists Gb. split; [exact Gb_grid | exact exp_xb_near_Gb]. Qed.

(** Grid points with an even significand are exactly the machine numbers
    of the binade; this is the link with [is_double_1_2]. *)
Lemma double_is_grid : forall D : R, is_double_1_2 D -> is_grid_1_2 D.
Proof.
  intros D [n [Hn ->]].
  exists (2 * n)%Z. split; [lia | ].
  replace ((2:R) ^ 53) with (2 * 2 ^ 52) by reflexivity.
  rewrite mult_IZR. field.
Qed.
