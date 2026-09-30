(** * Checking one line of htr3.c's input: the example line of the file

    A line gives [x0], [N] and the values [B_j = P(j) mod 2^320],
    [j = 0 .. 7], of the polynomial [P(j) = A_0 + A_1 j + ... + A_7 j^7],
    where [A_i] is [2^320 frac(a_i)] rounded to nearest, with
    [a_i = exp(x0) u^i / (i! v)], [u = 2^-43] and [v = 2^970].

    The check:
    - [encl]: [exp(x0) / v] is in [[lo, lo + 1] / 2^340] (coq-interval);
    - [binade]: [exp] stays in [[2^1023, 2^1024)] on the subrange, so [v]
      is the right unit there (coq-interval);
    - [line_ok]: from [lo] and [lo + 1], the rounding of every [A_i] is
      decided, the resulting [B_j] are the file's, and [N] is small enough
      for the Taylor remainder and for [ERR] (exact computation on [Z]). *)

From Stdlib Require Import ZArith Reals List.
From Interval Require Import Tactic.
Import ListNotations.

Open Scope Z_scope.

(** ** The line *)

(** [x0 = 0x1.62a3f395a6517p+9 = m0 / 2^43]. *)
Definition m0 : Z := 0x162a3f395a6517.
Definition N : Z := 7412951889.

(** The file's [B_j], five words of 64 bits each, lowest first. *)
Definition Bwords : list (list Z) := [
  [0x753f84509685094d; 0x822ff4cbc833e3e5; 0x9c99347075121f73;
   0xe5ae3e4e121c49ca; 0x4c57313668df383a];
  [0xabccd3de231c7e53; 0x6e1c6dbd99c099f5; 0xd53bc0e9e8e3c289;
   0x2d7c716584677711; 0x2ff203469426fcce];
  [0xcb1bfce1dd8c8bbf; 0xfc434fc6668fb466; 0x534d4ed9fe2de648;
   0xb759bd3cbebfbedd; 0x138cd5575a6b34bb];
  [0xe7f25b84be80e191; 0xa5da268ebf6b00b5; 0x27ad946830951714;
   0x835981622c6d6446; 0xf727a768bbabe003];
  [0x2bb1c0cf297fc691; 0x398dc1be5f1dc7ad; 0x5509b0c4859f1a1c;
   0x918f1d6438b8acd1; 0xdac2797ab7e8fea5];
  [0xc02b164383c4e2bf; 0xfc984906def18d93; 0xcfdc2c27da312709;
   0xe20df0d14ee9e06f; 0xbe5d4b8d4f2290a1];
  [0x393aeb524bab0a63; 0xcbe0fff5a0cef5bb; 0x7e6cf7d4300e21af;
   0x74e95b37da49497e; 0xa1f81da0815895f8];
  [0x7516a12ba8176fad; 0x3d25b98cef02caa0; 0x38d16e14fb54d3b4;
   0x4a34bc26461f34c6; 0x8592efb44e8b0ea9]].

(** [htr3.c]'s window, on the top word: [E = ERR 2^256]. *)
Definition ERR : Z := 0x400001.

(** ** The enclosure of [exp(x0) / v], proposed by MPFR, proved here *)

Definition Pe : Z := 340.
Definition lo : Z :=
  0x26bf1cd6907eee4c57313668df383ae5ae3e4e121c49ca9c99347075121f73822ff4cbc833e3e5753f84509685094d7ffb2.

Open Scope R_scope.

Definition x0 : R := IZR m0 / 2 ^ 43.

Lemma encl :
  IZR lo / 2 ^ 340 <= exp x0 / 2 ^ 970 <= IZR (lo + 1) / 2 ^ 340.
Proof.
unfold x0, m0, lo; split; interval with (i_prec 500).
Qed.

(** [exp] stays in one binade on [[x0, x0 + N u]]. *)
Lemma binade :
  2 ^ 1023 <= exp x0 /\ exp (x0 + IZR N / 2 ^ 43) < 2 ^ 1024.
Proof.
unfold x0, m0, N; split; interval with (i_prec 100).
Qed.

Close Scope R_scope.

(** ** The exact part *)

(** [2^320 a_i = 2^320 exp(x0) u^i / (i! v)] is [Y 2^340 / (2^(20 + 43 i) i!)]
    with [Y = exp(x0) / v]; its nearest integer from a value [y] of
    [Y 2^340] is [floor((2 y + d) / (2 d))] with [d = 2^(20 + 43 i) i!]. *)
Definition den (i : nat) : Z := 2 ^ (20 + 43 * Z.of_nat i) * Z.of_nat (fact i).
Definition near (y : Z) (i : nat) : Z := (2 * y + den i) / (2 * den i).

Definition Mw : Z := 2 ^ 320.

(** The rounding of [A_i] is decided when [lo] and [lo + 1] round alike. *)
Definition decided (i : nat) : bool := near lo i =? near (lo + 1) i.

Definition A (i : nat) : Z := near lo i mod Mw.

(** [B_j = sum_i A_i j^i mod 2^320], by Horner's rule. *)
Definition Bval (j : Z) : Z :=
  fold_right (fun a acc => a + j * acc) 0 (map A (seq 0 8)) mod Mw.

Definition of_words (w : list Z) : Z :=
  fold_right (fun x acc => x + 2 ^ 64 * acc) 0 w.

(** The Taylor remainder [2^54 (N u)^8 / 8!] is at most [2^-43]; the
    rounding of the [A_i], at most [1 + N + ... + N^7], and the target
    [2^-43] fit in the window [ERR 2^256]. *)
Definition taylor_ok : bool := N ^ 8 * 2 ^ (54 + 43) <=? Z.of_nat (fact 8) * 2 ^ 344.
Definition sumN : Z := fold_right (fun k acc => N ^ k + acc) 0 (map Z.of_nat (seq 0 8)).
Definition window_ok : bool :=
  Mw / 2 ^ 43 + Mw / 2 ^ 43 + sumN <=? ERR * 2 ^ 256.

Definition line_ok_b : bool :=
  forallb decided (seq 0 8)
  && forallb (fun j => Bval (Z.of_nat j) =? of_words (nth j Bwords []))
       (seq 0 8)
  && taylor_ok && window_ok.

Lemma line_ok : line_ok_b = true.
Proof. vm_compute. reflexivity. Qed.
