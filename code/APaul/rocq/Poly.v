(** * Finding the hard-to-round case from a polynomial, without the table

    Over the tiny interval spanned by the 100 chunk starts (width ~2^-27),
    [exp] is reproduced to ~2^-179 by a single degree-5 Taylor polynomial
    [P] about the dyadic midpoint [c].  So we can *simulate* the recorded
    table: instead of 100 MPFR values, generate 100 values by evaluating
    [P], then run the same hard-to-round search on them.

    Two parts:
    - integer side: [P] evaluated exactly (rational) at each grid point,
      giving a value-table on which a pure-[Z] HRC test finds row 50;
    - real side: one CoqInterval call bounds [|exp x - P x|] over the whole
      interval, certifying that the polynomial-based search sees the same
      hard-to-round cases as the true exponential. *)

From Stdlib Require Import Reals ZArith List.
From Interval Require Import Tactic.
Import ListNotations.

(** ** Shared constants *)

Open Scope Z_scope.

(** The polynomial is [P(x) = (sum_{j=0}^5 A_j (x-c)^j) / 2^cden], the
    degree-5 Taylor expansion of [exp] about [c = Cc / 2^xden], with
    coefficients [A_j = round(exp(c)/j! * 2^cden)]. *)
Definition xden : Z := 54.    (* grid scale: x = num / 2^xden                *)
Definition cden : Z := 210.   (* coefficient denominator: a_j = A_j / 2^cden *)
Definition prec53 : Z := 53.  (* binary64 significand width                   *)
Definition m_hrc : Z := 30.   (* required identical bits after the round bit  *)

Definition A0 : Z := 2112873046211101960745487299836695701278643019779725570912266820.
Definition A1 : Z := 2112873046211101960745487299836695701278643019779725570912266820.
Definition A2 : Z := 1056436523105550980372743649918347850639321509889862785456133410.
Definition A3 : Z := 352145507701850326790914549972782616879773836629954261818711137.
Definition A4 : Z := 88036376925462581697728637493195654219943459157488565454677784.
Definition A5 : Z := 17607275385092516339545727498639130843988691831497713090935557.

Definition x0_num : Z := 4503628319560994.   (* x0  = x0_num  / 2^xden *)
Definition Cc     : Z := 4503628371465506.   (* c   = Cc      / 2^xden *)

(** ** Integer side: simulate the table by evaluating [P] *)

(** grid point [k]: [x_k = Xk k / 2^xden], stride [2^20] (one al.c chunk). *)
Definition Xk (k : nat) : Z := x0_num + Z.of_nat k * 2 ^ 20.
Definition delta (k : nat) : Z := Xk k - Cc.                (* (x_k - c) * 2^xden *)

(** value denominator: [P(x_k) = Pnum k / 2^vden]. *)
Definition vden : Z := cden + 5 * xden.

(** one "call" to the polynomial: exact numerator of [P(x_k)] over [2^vden]. *)
Definition poly_val (k : nat) : Z :=
    A0 * 2 ^ (xden * 5) + A1 * delta k     * 2 ^ (xden * 4)
  + A2 * (delta k) ^ 2 * 2 ^ (xden * 3) + A3 * (delta k) ^ 3 * 2 ^ (xden * 2)
  + A4 * (delta k) ^ 4 * 2 ^ xden       + A5 * (delta k) ^ 5.

(** the simulated table: 100 polynomial evaluations replacing the rows. *)
Definition poly_table : list Z := map poly_val (seq 0 100).

(** distance of [V] to the nearest multiple of [2^P]. *)
Definition dist_to_grid (V P : Z) : Z :=
  let r := V mod 2 ^ P in Z.min r (2 ^ P - r).

(** HRC test on a generated value [V = P(x_k) * 2^vden]: [P(x_k) * 2^53] is
    within [2^-m_hrc] of an integer. *)
Definition Pbits : Z := vden - prec53.
Definition is_hrc_v (V : Z) : bool :=
  Z.ltb (dist_to_grid V Pbits) (2 ^ (Pbits - m_hrc)).

(** indices of the hard-to-round cases in a value-table. *)
Definition find_hrc_table (t : list Z) : list nat :=
  map fst (filter (fun p => is_hrc_v (snd p))
                  (combine (seq 0 (length t)) t)).

(** Running the search on the polynomial-generated table finds exactly
    row 50 — the hard case — with no recorded table at all. *)
Theorem found_hrc_poly : find_hrc_table poly_table = [50%nat].
Proof. vm_compute. reflexivity. Qed.

(** ** Direct search: no intermediate value-table

    Evaluate [P] at each grid point on the fly and test, accumulating the
    hard-to-round indices — [poly_table] is never built. *)

Definition is_hrc_at (k : nat) : bool := is_hrc_v (poly_val k).

Fixpoint scan_aux (k fuel : nat) (acc : list nat) : list nat :=
  match fuel with
  | O => rev acc
  | S f => scan_aux (S k) f (if is_hrc_at k then k :: acc else acc)
  end.

(** Scan the first [n] grid points directly. *)
Definition find_hrc_direct (n : nat) : list nat := scan_aux 0 n [].

Theorem found_hrc_direct : find_hrc_direct 100 = [50%nat].
Proof. vm_compute. reflexivity. Qed.

(** The direct scan and the table-based search agree. *)
Theorem direct_eq_table : find_hrc_direct 100 = find_hrc_table poly_table.
Proof. vm_compute. reflexivity. Qed.

(** ** Real side: the polynomial really is [exp] on this interval *)

Open Scope R_scope.

Definition c_R   : R := IZR Cc / 2 ^ 54.
Definition x0_R  : R := IZR x0_num / 2 ^ 54.
Definition x99_R : R := IZR (x0_num + 99 * 2 ^ 20) / 2 ^ 54.

Definition P_R (x : R) : R :=
  (IZR A0
 + IZR A1 * (x - c_R)
 + IZR A2 * (x - c_R) ^ 2
 + IZR A3 * (x - c_R) ^ 3
 + IZR A4 * (x - c_R) ^ 4
 + IZR A5 * (x - c_R) ^ 5) / 2 ^ 210.

(** One CoqInterval call: the degree-5 polynomial approximates [exp] to
    [2^-170] over the entire interval [[x0, x99]] — the single place where
    [exp] is evaluated.  Since the HRC window is [2^-30 >> 2^-170], the
    polynomial-based search above sees exactly the hard-to-round cases of
    the true exponential. *)
Theorem poly_close_to_exp :
  forall x : R, x0_R <= x <= x99_R -> Rabs (exp x - P_R x) <= / 2 ^ 170.
Proof.
  intros x Hx.
  unfold x0_R, x99_R in Hx.
  unfold P_R, c_R, A0, A1, A2, A3, A4, A5, Cc, x0_num in *.
  interval with (i_bisect x, i_taylor x, i_degree 8, i_prec 260).
Qed.
