(** * Certifying recorded [dd_exp] values against [exp]

    [Data.v] stores, as plain integers, the first 100 triple-double values
    [h + l + s] that [al.c]'s [dd_exp] computes for [exp] (via MPFR).  Here
    we reconnect that data to the actual exponential: we give each entry a
    real interpretation and prove, with CoqInterval, that the recorded
    value approximates [exp x] to the triple-double accuracy.

    This is the Rocq end of the "MPFR computes / Rocq certifies" split:
    MPFR produced the integers, but nothing MPFR-specific is trusted —
    the bound below is checked entirely inside Rocq.

    Everything is written parametrically in the entry index [start], so
    checking a different line (or, after regenerating [Data.v], a different
    region) is a one-line change. *)

From Stdlib Require Import Reals ZArith List.
From Interval Require Import Tactic.
From APaulRocq Require Import Data.
Import ListNotations.
Open Scope R_scope.

(** ** Certification parameters

    Named once, so nothing below hardcodes a bare literal. *)

(** Working precision, in bits, used by CoqInterval to discharge each
    bound.  Ample for the triple-double accuracy of the recorded data. *)
Definition work_prec : positive := 200.

(** Accuracy we certify: every recorded value is proven within
    [2^- target_prec] of the true exponential.  The measured error is
    about [2^-161.8], so [160] holds with margin. *)
Definition target_prec : nat := 160.

(** ** Real interpretation of an entry *)

(** Using the fixed per-field scales [sx, sh, sl, ss] declared in [Data.v]. *)

(** The recorded input [x]. *)
Definition xR (e : entry) : R := IZR (x e) * powerRZ 2 (- sx).

(** The recorded value of [exp x], i.e. the triple-double [h + l + s]. *)
Definition vR (e : entry) : R :=
    IZR (h e) * powerRZ 2 (- sh)
  + IZR (l e) * powerRZ 2 (- sl)
  + IZR (s e) * powerRZ 2 (- ss).

(** Entry [e] is correct to [p] bits: its recorded value is within
    [2^-p] of the true exponential at the recorded input. *)
Definition entry_correct (e : entry) (p : nat) : Prop :=
  Rabs (vR e - exp (xR e)) < / 2 ^ p.

(** ** Parametric access to the array *)

Definition default_entry : entry := {| x := 0; h := 0; l := 0; s := 0 |}.

(** The [k]-th recorded entry. *)
Definition nth_entry (k : nat) : entry := nth k dd_data default_entry.

(** Reduce a single [entry_correct _ _] goal to concrete integers and
    discharge it with CoqInterval at [work_prec] bits.  Works whether the
    entry is a record literal or an [nth_entry k] / list-element
    expression: [cbn] performs all the projection/[nth] reduction. *)
Ltac check_entry :=
  unfold entry_correct, xR, vR;
  cbn -[powerRZ pow];
  interval with (i_prec work_prec).

(** Prove a [Forall (fun e => entry_correct e p) l] goal where [l] is a
    concrete prefix ([firstn n dd_data]) or the whole [dd_data]: unfold
    the list, then certify each element with [check_entry]. *)
Ltac check_table :=
  cbn [firstn dd_data];
  repeat (apply Forall_cons; [ check_entry | ]);
  try apply Forall_nil.

(** ** Checking one line

    Change [start] to certify a different line.  Row 50 is the hard-to-round
    case 0x1.00006b1501522p-2 (its [h] is the nearby machine number, [l] the
    ~2^-84 residual). *)
Definition start : nat := 50.

Theorem line_correct : entry_correct (nth_entry start) target_prec.
Proof. unfold start. check_entry. Qed.

(** ** Checking the first [n] lines

    Change [n_check] to certify a different prefix.  Timing is linear:
    ~0.06 s/entry (n = 20 ~ 1 s, n = 100 ~ 6 s). *)
Definition n_check : nat := 100.

Theorem first_n_correct :
  Forall (fun e => entry_correct e target_prec) (firstn n_check dd_data).
Proof. unfold n_check. check_table. Qed.

(** ** The whole table

    Every recorded triple-double value is a correct [target_prec]-bit
    approximation of [exp] at its input. *)
Theorem table_correct :
  Forall (fun e => entry_correct e target_prec) dd_data.
Proof. check_table. Qed.
