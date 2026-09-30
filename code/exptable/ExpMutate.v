(** * Changing one bit of a line makes the check fail

    A test of the checker, not a proof about the table: on the first lines
    of [in_lt], which pass, one bit of one coefficient [B_i] is changed, or
    [x0] is moved, and [check_line] must then answer [false].  The bits
    changed in each [B_i] are the lowest, one in the middle and the
    highest; [x0] is moved by one ulp each way and has three bits of its
    significand changed. *)

From Stdlib Require Import ZArith List Bool.
From ExpTable Require Import ExpCheck ExpData.
Import ListNotations.

Open Scope Z_scope.

(** [x] with bit [b] changed. *)
Definition flip (b x : Z) : Z := Z.lxor x (2 ^ b).

(** [B] with bit [b] of [B_i] changed. *)
Definition flipB (B : list Z) (i : nat) (b : Z) : list Z :=
  firstn i B ++ flip b (nth i B 0) :: skipn (S i) B.

(** The bits changed in a coefficient, and in the significand of [x0]. *)
Definition bitsB : list Z := [0; lbits / 2; lbits - 1].
Definition bitsM : list Z := [0; 20; 51].

(** Every change of the line makes [check_line] answer [false]. *)
Definition all_fail (M0 n : Z) (B : list Z) : bool :=
  forallb (fun i => forallb (fun b => negb (check_line M0 n (flipB B i b)))
                            bitsB) (seq 0 k) &&
  negb (check_line (M0 + 1) n B) && negb (check_line (M0 - 1) n B) &&
  forallb (fun b => negb (check_line (flip b M0) n B)) bitsM.

(** The line passes, and every change of it fails. *)
Definition mutate_ok (r : Z * Z * list Z) : bool :=
  match r with (M0, n, B) => check_line M0 n B && all_fail M0 n B end.

(** The first three lines of the table. *)
Example mutate_lines : forallb mutate_ok (firstn 3 ExpData.table) = true.
Proof. native_cast_no_check (eq_refl true). Qed.
