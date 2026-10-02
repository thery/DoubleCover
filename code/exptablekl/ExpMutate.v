(** * Changing one bit of a line makes the check fail

    A test of the checker, not a proof about the table: on lines that
    pass, one bit of one coefficient [B_i] is changed, or [x0] is moved,
    and [check_line] must then answer [false].  The bits changed in each
    [B_i] are the lowest, one in the middle and the highest; [x0] is moved
    by one ulp each way and has three bits of its significand changed. *)

From Stdlib Require Import ZArith List Bool.
From ExpTableKL Require Import ExpCheck ExpParse MutData.
Import ListNotations.

Open Scope Z_scope.

(** [x] with bit [b] changed. *)
Definition flip (b x : Z) : Z := Z.lxor x (2 ^ b).

(** [B] with bit [b] of [B_i] changed. *)
Definition flipB (B : list Z) (i : nat) (b : Z) : list Z :=
  firstn i B ++ flip b (nth i B 0) :: skipn (S i) B.

(** The bits changed in a coefficient of [l] words, and in the
    significand of [x0]. *)
Definition bitsB (l : Z) : list Z := [0; lbits l / 2; lbits l - 1].
Definition bitsS : list Z := [0; 20; 51].

(** Every change of the line makes [check_line] answer [false]. *)
Definition all_fail (S0 ex n : Z) (k : nat) (l : Z) (B : list Z) : bool :=
  forallb (fun i => forallb (fun b =>
             negb (check_line S0 ex n k l (flipB B i b))) (bitsB l))
          (seq 0 k) &&
  negb (check_line (S0 + 1) ex n k l B) &&
  negb (check_line (S0 - 1) ex n k l B) &&
  forallb (fun b => negb (check_line (flip b S0) ex n k l B)) bitsS.

(** The line passes, and every change of it fails. *)
Definition mutate_ok (s : PrimString.string) : bool :=
  match parse s with
  | Some (S0, ex, n, k, l, B) =>
    check_line S0 ex n k l B && all_fail S0 ex n k l B
  | None => false
  end.

Example mutate_lines : forallb mutate_ok MutData.lines = true.
Proof. native_cast_no_check (eq_refl true). Qed.
