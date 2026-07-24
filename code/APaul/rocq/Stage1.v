(** * Stage 1 — certifying the hard-to-round cases found by [al.c]

    [al.c] searches for hard-to-round cases of the exponential over
    binary64 arguments.  On the interval [0.25, 0.25001) with parameter
    [m = 30] it reports exactly two inputs:

        0x1.00006b1501522p-2   and   0x1.0000f35300644p-2

    For each of them, [exp x] turns out to lie within [2^-83] of a
    representable binary64 number [D] living in the binade [1,2) — i.e.
    within [2^-30] of a "round-bit" grid point that is in fact a machine
    number.  Concretely: 30 identical (zero) bits follow the round bit,
    so these are genuine worst cases for the directed rounding modes.

    Here we certify this rigorously with CoqInterval.  Everything below
    is proved from the reals; no floating-point model is assumed yet
    (that comes in Stages 2 and 3). *)

From Stdlib Require Import Reals ZArith Lia.
From Interval Require Import Tactic.
Open Scope R_scope.

(** ** Specification *)

(** A real [D] is a representable binary64 number in the binade [1,2):
    its integer significand [n] satisfies [2^52 <= n < 2^53] and
    [D = n / 2^52]  (the ulp on this binade is [2^-52]). *)
Definition is_double_1_2 (D : R) : Prop :=
  exists n : Z, (2 ^ 52 <= n < 2 ^ 53)%Z /\ D = IZR n / 2 ^ 52.

(** [x] is a hard-to-round case *toward a machine number* with [N] extra
    identical bits: [exp x] is within [2^-(53+N)] of a representable
    double, equivalently within [2^-N] half-ulp of a machine number.
    (53 mantissa bits + N bits below the round bit.) *)
Definition htr_toward_double (x : R) (N : nat) : Prop :=
  exists D : R, is_double_1_2 D /\ Rabs (exp x - D) < / 2 ^ (53 + N).

(** ** The two reported inputs, as exact rationals [M / 2^54] *)

Definition x1 : R := 4503628371989794 / 2 ^ 54.   (* 0x1.00006b1501522p-2 *)
Definition x2 : R := 4503664944219716 / 2 ^ 54.   (* 0x1.0000f35300644p-2 *)

(** The nearby doubles [D = n / 2^52]. *)
Definition D1 : R := 5782745615341963 / 2 ^ 52.
Definition D2 : R := 5782757355290804 / 2 ^ 52.

Lemma D1_double : is_double_1_2 D1.
Proof. exists 5782745615341963%Z. split; [lia | reflexivity]. Qed.

Lemma D2_double : is_double_1_2 D2.
Proof. exists 5782757355290804%Z. split; [lia | reflexivity]. Qed.

(** ** Rigorous enclosures (the numeric heart of Stage 1)

    Each says [exp x] is within [2^-83] of the corresponding double. *)

Lemma exp_x1_near_D1 : Rabs (exp x1 - D1) < / 2 ^ 83.
Proof. unfold x1, D1. interval with (i_prec 100). Qed.

Lemma exp_x2_near_D2 : Rabs (exp x2 - D2) < / 2 ^ 83.
Proof. unfold x2, D2. interval with (i_prec 100). Qed.

(** ** Main results

    Both reported inputs are genuine hard-to-round cases with 30
    identical bits after the round bit ([53 + 30 = 83]). *)

Theorem case1_hard : htr_toward_double x1 30.
Proof. exists D1. split; [exact D1_double | exact exp_x1_near_D1]. Qed.

Theorem case2_hard : htr_toward_double x2 30.
Proof. exists D2. split; [exact D2_double | exact exp_x2_near_D2]. Qed.
