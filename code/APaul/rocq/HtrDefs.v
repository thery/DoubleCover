(** * What the search of htr3.c computes, on integers

    The search of [code/APaul/htr3.c] (and of its Capla version,
    [code/APaul/capla/htr3/htr3.b]) for one line of a table: the line gives
    [k] coefficients [b_0 .. b_(k-1)] of [l] words each, the values
    [P(0) .. P(k-1)] of a polynomial modulo [beta^l]; the search turns them
    into the table of differences, adds the window [err] to the top word of
    the first coefficient, and walks [j = 0 .. n-1] (the half-open
    [[x0, x1)] of [htr3_new.c]), keeping [j] when the top word of the first
    coefficient is at most [2 err].

    This file only says what is computed, with plain integers, and needs
    nothing but the standard library: it is shared by the proofs on the
    Capla program and by those on the search of [doc/htr.md]. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.

Open Scope Z_scope.

(** ** Words and coefficients *)

Definition wbits : Z := 64.            (* bits of a word *)

(** [beta^l], the modulus of a coefficient of [l] words. *)
Definition baseZ (l : Z) : Z := 2 ^ (wbits * l).

(** The top word of [b] seen as [l] words: [(b mod beta^l) / beta^(l-1)]. *)
Definition top (l b : Z) : Z := (b mod baseZ l) / 2 ^ (wbits * (l - 1)).

(** ** The table of differences *)

(** [C(n, t)]. *)
Fixpoint binom (n t : nat) : Z :=
  match n, t with
  | _, O => 1
  | O, S _ => 0
  | S n', S t' => binom n' t' + binom n' t
  end.

(** The [j]-th forward difference at 0 of the sequence [ds]:
    [sum_(t <= j) (-1)^(j - t) C(j, t) ds_t]. *)
Definition fdiff (ds : list Z) (j : nat) : Z :=
  fold_right Z.add 0
    (map (fun t => (-1) ^ Z.of_nat (j - t) * binom j t * nth t ds 0)
         (seq 0 (S j))).

(** One step of the table: [d_t + d_(t+1)], the last one unchanged. *)
Fixpoint tstepZ (ds : list Z) : list Z :=
  match ds with
  | a :: (b :: _) as r => (a + b) :: tstepZ r
  | _ => ds
  end.

(** ** The search *)

(** The window: [err] added to the top word of the first coefficient. *)
Definition window (l err : Z) (ds : list Z) : list Z :=
  match ds with
  | a :: r => (a + err * 2 ^ (wbits * (l - 1))) :: r
  | [] => []
  end.

(** The table after [j] steps, from the values [ds = P(0) .. P(k-1)]. *)
Definition table (l err : Z) (ds : list Z) (j : nat) : list Z :=
  Nat.iter j tstepZ (window l err (map (fdiff ds) (seq 0 (length ds)))).

(** [j] is a candidate: the top word of the first coefficient is at most
    [2 err]. *)
Definition cand (l err : Z) (ds : list Z) (j : nat) : bool :=
  top l (nth 0 (table l err ds j) 0) <=? 2 * err.

(** The candidates [j = 0 .. n-1], in increasing order. *)
Definition cands (l err : Z) (ds : list Z) (n : nat) : list nat :=
  filter (cand l err ds) (seq 0 n).

(** ** The polynomial

    [polyZ A j = A_0 + A_1 j + ... + A_(k-1) j^(k-1)], [k] the length of
    [A]: the polynomial whose values the line holds. *)
Definition polyZ (A : list Z) (j : Z) : Z :=
  fold_right Z.add 0
    (map (fun t => nth t A 0 * j ^ Z.of_nat t) (seq 0 (length A))).
