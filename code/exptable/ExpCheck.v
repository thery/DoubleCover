(** * Checking a table for the hard-to-round search of exp, by reflection

    The search is the one of [doc/htr.md] (Paul Zimmermann), whose
    notation we keep.  The input range is cut into subranges
    [[x0, x1]] with [x1 = x0 + n u], [u = ulp x] and [v = ulp(exp x) / 2]
    constant on each.  With [a_i = exp x0 u^i / i!], each [A_i] is an
    integer with [0 <= A_i < beta^l] and [|A_i - beta^l frac(a_i/v)| < 1],
    and [P(j) = A_0 + A_1 j + ... + A_(k-1) j^(k-1)].

    A line of the table is [(x0, n, B)] with [B_i = P(i) mod beta^l] for
    [i < k], the output of step 3 of the search.  [line_ok] states the
    six conditions under which the search on that line misses no hard
    case; [check_table] tests them all with one boolean function, and
    [check_tableP] proves that a [true] answer gives [table_ok]. *)

From Stdlib Require Import ZArith Reals Lia Lra List.
From Flocq Require Import Core.
From Bignums Require Import BigZ.
From Interval Require Import Xreal Basic Specific_bigint Specific_ops.
From Interval Require Import Float_full.
Import ListNotations.

(** ** Parameters

    The table and the search are described here and nowhere else, in the
    notation of [doc/htr.md]. *)

Open Scope Z_scope.

Definition beta : Z := 2 ^ 64.    (* the machine word basis            *)
Definition l : Z := 5.            (* words of an A_i or a B_i          *)
Definition k : nat := 8.          (* terms of the Taylor polynomial    *)
Definition m : Z := 43.           (* identical bits after the round bit *)
Definition E : Z := 2 ^ 278.      (* the window of the search (a guess) *)
Definition xbin : Z := 9.         (* x ranges over [2^xbin, 2^(xbin+1)) *)
Definition guard : Z := 64.       (* extra bits in the exp enclosure   *)

(** ** Derived constants

    [beta^l = 2^lbits], [u = 2^uexp], [v = 2^(e - vsh)] for [exp x] in
    [[2^e, 2^(e+1))], and the precision at which [exp] is enclosed. *)

Module SFBI2 := SpecificFloat BigIntRadix2.
Module I := FloatIntervalFull SFBI2.

Definition beta_l : Z := beta ^ l.
Definition lbits : Z := Z.log2 beta * l.
Definition uexp : Z := xbin - 52.
Definition vsh : Z := 53.
Definition prec : SFBI2.precision :=
  SFBI2.PtoP (Z.to_pos (lbits + vsh + guard)).

(** ** The conditions *)

Open Scope R_scope.

Definition bp (e : Z) : R := bpow radix2 e.
Definition u : R := bp uexp.
Definition fracR (r : R) : R := r - IZR (Zfloor r).

(** [a_i = exp x0 u^i / i!]. *)
Definition a (x0 : R) (i : nat) : R := exp x0 * u ^ i / INR (fact i).

(** [f 0 + ... + f (N-1)]. *)
Fixpoint sumR (f : nat -> R) (N : nat) : R :=
  match N with O => 0 | S N' => sumR f N' + f N' end.

(** [P(j) = A_0 + A_1 j + ... + A_(k-1) j^(k-1)], in integers. *)
Definition Pz (A : list Z) (j : Z) : Z :=
  fold_right Z.add 0%Z (map (fun i => (nth i A 0 * j ^ Z.of_nat i)%Z) (seq 0 k)).

(** The six conditions on a line [(x0, n, B)], [x0 = M0 u]. *)
Definition line_ok (M0 n : Z) (B : list Z) : Prop :=
  let x0 := IZR M0 * u in
  let x1 := IZR (M0 + n) * u in
  exists e : Z,
  let v := bp (e - vsh) in
  let rho := exp x1 * (IZR n * u) ^ k / (INR (fact k) * v) in
  (* 1. u is constant on [x0, x1] *)
  (0 <= n)%Z /\ bp xbin <= x0 /\ x1 < bp (xbin + 1) /\
  (* 2. v is constant on [x0, x1] *)
  bp e <= exp x0 /\ exp x1 < bp (e + 1) /\
  (* 3. (H_A), and the table holds P(0) .. P(k-1) *)
  (exists A : list Z, length A = k /\ length B = k /\
    (forall i, (i < k)%nat ->
       (0 <= nth i A 0%Z < beta_l)%Z /\
       Rabs (IZR (nth i A 0%Z) - IZR beta_l * fracR (a x0 i / v)) < 1) /\
    (forall i, (i < k)%nat ->
       nth i B 0%Z = (Pz A (Z.of_nat i) mod beta_l)%Z)) /\
  (* 4. (H_T), the Taylor remainder *)
  (forall j, (0 <= j <= n)%Z ->
     Rabs (exp (x0 + IZR j * u) / v - sumR (fun i => a x0 i / v * IZR j ^ i) k)
       <= rho) /\
  (* 5. (H_E), the window *)
  IZR beta_l * (bp (- m) + rho) + sumR (fun i => IZR n ^ i) k <= IZR E.

(** Condition 6, [2 E < beta^l], is on the search, not on a line. *)
Definition table_ok (t : list (Z * Z * list Z)) : Prop :=
  (2 * E < beta_l)%Z /\
  forall M0 n B, In (M0, n, B) t -> line_ok M0 n B.

Close Scope R_scope.

(** ** The checker *)

Open Scope bool_scope.

(** The float [N u]. *)
Definition xpt (N : Z) : SFBI2.type :=
  Specific_ops.Float (BigZ.of_Z N) (BigZ.of_Z uexp).

(** A positive float as its significand and exponent. *)
Definition getF (f : SFBI2.type) : option (positive * Z) :=
  match SFBI2.toF f with Basic.Float false p e => Some (p, e) | _ => None end.

(** An enclosure [[mL 2^fL, mU 2^fU]] of [exp (N u)]. *)
Definition encl (N : Z) : option (Z * Z * Z * Z) :=
  if SFBI2.valid_lb (xpt N) && SFBI2.valid_ub (xpt N) &&
     match getF (xpt N) with
     | Some (p, e) => Z.eqb (Z.pos p) N && Z.eqb e uexp
     | None => false
     end
  then
    match I.exp prec (Float.Ibnd (xpt N) (xpt N)) with
    | Float.Ibnd lo up =>
      if SFBI2.valid_lb lo && SFBI2.valid_ub up then
        match getF lo, getF up with
        | Some (pL, fL), Some (pU, fU) => Some (Z.pos pL, fL, Z.pos pU, fU)
        | _, _ => None
        end
      else None
    | Float.Inan => None
    end
  else None.

(** [floor (p 2^g / fk + h / 2)], in integers. *)
Definition flr (p g fk h : Z) : Z :=
  if Z.leb 0 g then (2 * p * 2 ^ g + h * fk) / (2 * fk)
  else (2 * p + h * fk * 2 ^ (- g)) / (2 * fk * 2 ^ (- g)).

(** [p 2^f < 2^g], for [p >= 1]. *)
Definition lt2 (p f g : Z) : bool :=
  if Z.leb g f then false else Z.ltb p (2 ^ (g - f)).

(** [A_i], from the enclosure of [exp x0]: [beta^l a_i / v] is
    [p 2^(f + gi) / i!], its nearest integer [R] and its integer part
    [q] (in units of [beta^l]) must be the same at both ends. *)
Definition coefA (mL fL mU fU e : Z) (i : nat) (fk : Z) : option Z :=
  let gi := lbits + uexp * Z.of_nat i - (e - vsh) in
  let R := flr mL (fL + gi) fk 1 in
  let q := flr mL (fL + gi - lbits) fk 0 in
  let Ai := R - q * beta_l in
  if Z.eqb R (flr mU (fU + gi) fk 1) &&
     Z.eqb q (flr mU (fU + gi - lbits) fk 0) &&
     Z.leb 0 Ai && Z.ltb Ai beta_l
  then Some Ai else None.

(** [A_i .. A_(i+c-1)], [fk] being [i!]. *)
Fixpoint coefs (mL fL mU fU e : Z) (i : nat) (fk : Z) (c : nat)
  : option (list Z) :=
  match c with
  | O => Some nil
  | S c' =>
    match coefA mL fL mU fU e i fk,
          coefs mL fL mU fU e (S i) (fk * Z.of_nat (S i)) c' with
    | Some Ai, Some As => Some (Ai :: As)
    | _, _ => None
    end
  end.

(** [1 + n + ... + n^(k-1)]. *)
Definition sumn (n : Z) : Z :=
  fold_right Z.add 0 (map (fun i => n ^ Z.of_nat i) (seq 0 k)).

(** (H_E) with [exp x1 <= mU 2^fU]:
    [beta^l (2^-m + mU 2^fU (n u)^k / (k! v)) + sumn n <= E]. *)
Definition window_ok (mU fU e n : Z) : bool :=
  let X := mU * n ^ Z.of_nat k in
  let g := fU + lbits + uexp * Z.of_nat k - (e - vsh) in
  let C := 2 ^ (lbits - m) + sumn n in
  let kf := Z.of_nat (fact k) in
  if Z.leb 0 g then Z.leb (X * 2 ^ g + C * kf) (E * kf)
  else Z.leb (X + C * kf * 2 ^ (- g)) (E * kf * 2 ^ (- g)).

Definition check_line (M0 n : Z) (B : list Z) : bool :=
  Z.leb 0 n && Z.leb (2 ^ 52) M0 && Z.ltb (M0 + n) (2 ^ 53) &&
  Nat.eqb (length B) k &&
  match encl M0, encl (M0 + n) with
  | Some (mL0, fL0, mU0, fU0), Some (mL1, fL1, mU1, fU1) =>
    let e := Z.log2 mL0 + fL0 in
    lt2 mU1 fU1 (e + 1) && window_ok mU1 fU1 e n &&
    match coefs mL0 fL0 mU0 fU0 e 0 1 k with
    | Some A =>
      forallb (fun i => Z.eqb (nth i B 0) (Pz A (Z.of_nat i) mod beta_l))
              (seq 0 k)
    | None => false
    end
  | _, _ => false
  end.

Definition check_table (t : list (Z * Z * list Z)) : bool :=
  Z.ltb (2 * E) beta_l && Z.leb m lbits &&
  forallb (fun r => match r with (M0, n, B) => check_line M0 n B end) t.

(** ** Correctness *)

Theorem check_lineP M0 n B : check_line M0 n B = true -> line_ok M0 n B.
Proof.
Admitted.

Theorem check_tableP t : check_table t = true -> table_ok t.
Proof.
Admitted.
