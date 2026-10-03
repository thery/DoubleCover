(** The check of one test of ExpModel.v against exp100.c: the return code,
    M and s of [exp_encl_bits], and the result of [maybe_hard_bits]. *)

From Stdlib Require Import ZArith.
From Exp100 Require Import ExpModel.

Open Scope Z_scope.

(** (xb, rc, M, s, maybe_hard) as printed by gen_tests.c; M = s = 0 when
    rc <> 0. *)
Definition test : Type := Z * Z * Z * Z * Z.

Definition ok (t : test) : bool :=
  let '(xb, rc, M, s, mh) := t in
  match exp_encl_Z xb with
  | inl c => (c =? rc) && (M =? 0) && (s =? 0)
  | inr (M', s') => (rc =? 0) && (M' =? M) && (s' =? s)
  end && (maybe_hard_Z xb =? mh).
