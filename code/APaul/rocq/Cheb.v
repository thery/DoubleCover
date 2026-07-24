(** * A degree-7 polynomial approximation of exp on the al.c interval

    [al.c]'s [main] searches [exp] over the interval
      [[0.25, 0.25001)] = [[x0num/2^54, x1num/2^54)].
    Over this interval a single degree-7 polynomial reproduces [exp] to
    better than [2^-160].  We use a *near-minimax* polynomial (Chebyshev
    interpolation at the 8 Chebyshev nodes) rather than a Taylor
    expansion: on this interval Taylor needs degree 8 (degree-7 Taylor
    only reaches ~2^-155.8), whereas degree-7 Chebyshev reaches ~2^-162.8,
    saving one degree.

    The coefficients below are produced by [cheb.c]; here we only carry
    them and let CoqInterval certify, in a single call, that the resulting
    polynomial is within [2^-160] of [exp] over the whole al.c interval. *)

From Stdlib Require Import Reals ZArith.
From Interval Require Import Tactic.

Open Scope Z_scope.

(** ** Parameters *)

(** [P(x) = (sum_{k=0}^7 A_k (x-c)^k) / 2^cden], with [c = Cc / 2^54]. *)
Definition xden : Z := 54.     (* binade scale: values are n / 2^54          *)
Definition cden : Z := 220.    (* coefficient denominator: b_k = A_k / 2^cden *)
Definition tprec : Z := 160.   (* certified accuracy: |exp - P| <= 2^-tprec   *)

(** al.c search interval [[x0num/2^54, x1num/2^54)] = [[0.25, 0.25001)]. *)
Definition x0num : Z := 4503599627370496.   (* 0.25    *)
Definition x1num : Z := 4503779771355591.   (* 0.25001 (as a double) *)

(** Expansion centre [c = Cc / 2^54] (a dyadic near the interval midpoint). *)
Definition Cc : Z := 4503689699363044.

(** Degree-7 near-minimax coefficients (from [cheb.c]). *)
Definition A0 : Z := 2163589364992741933118445721196378216934906269757062429882016697139.
Definition A1 : Z := 2163589364992741933118445721196378216934906269757207993170105654204.
Definition A2 : Z := 1081794682496370966559222860598189108677064269726287542097608990680.
Definition A3 : Z := 360598227498790322186407620199396369512441171053721432073608518278.
Definition A4 : Z := 90149556874697580546601863127622122923215211978685306865410548378.
Definition A5 : Z := 18029911374939516109320376351944599647206281390364150137105444866.
Definition A6 : Z := 3004985229159269040746102559036977637496749560112241178749261625.
Definition A7 : Z := 429283604165524687645441962100556428820723774627516109662437926.

(** ** The approximation and its certificate *)

Open Scope R_scope.

Definition x_lo : R := IZR x0num / 2 ^ 54.
Definition x_hi : R := IZR x1num / 2 ^ 54.
Definition c_R  : R := IZR Cc / 2 ^ 54.

Definition P_R (x : R) : R :=
  (IZR A0
 + IZR A1 * (x - c_R)
 + IZR A2 * (x - c_R) ^ 2
 + IZR A3 * (x - c_R) ^ 3
 + IZR A4 * (x - c_R) ^ 4
 + IZR A5 * (x - c_R) ^ 5
 + IZR A6 * (x - c_R) ^ 6
 + IZR A7 * (x - c_R) ^ 7) / 2 ^ 220.

(** One CoqInterval call certifies the degree-7 polynomial is within
    [2^-160] of [exp] over the entire al.c interval [[0.25, 0.25001)]. *)
Theorem cheb_valid :
  forall x : R, x_lo <= x <= x_hi -> Rabs (exp x - P_R x) <= / 2 ^ 160.
Proof.
  intros x Hx.
  unfold x_lo, x_hi in Hx.
  unfold P_R, c_R, x0num, x1num, Cc, A0, A1, A2, A3, A4, A5, A6, A7 in *.
  interval with (i_bisect x, i_taylor x, i_degree 10, i_prec 300).
Qed.
