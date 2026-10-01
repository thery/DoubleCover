(** * Checking a table for the hard-to-round search of exp, by reflection

    The search is the one of [doc/htr.md] (Paul Zimmermann), whose
    notation we keep.  The inputs are cut into subranges from [x0] to
    [x1 = x0 + n u], with [u = ulp x] and [v = ulp(exp x) / 2] constant on
    each.  With [a_i = exp x0 u^i / i!], each [A_i] is an integer with
    [0 <= A_i < beta^l] and [|A_i - beta^l frac(a_i/v)| < 1], and
    [P(j) = A_0 + A_1 j + ... + A_(k-1) j^(k-1)].

    A line of the table is [(x0, n, B)] with [B_i = P(i) mod beta^l] for
    [i < k].  Here [x0] is any normal double, positive or negative, and
    [exp x0] may be subnormal.  [x0] is written [S0 2^(ex - 52)], [S0] an
    integer with [2^52 <= |S0| < 2^53]; then [u = 2^(ex - 52)] and the
    inputs are [x0 + j u = (S0 + j) 2^(ex - 52)]: [j = 0 .. n] if the
    parameter [closed] is [true] (the subrange is [[x0, x1]]), [j = 0 ..
    n - 1] if it is [false] (the subrange is [[x0, x1)]).  The last input
    is [x_last = SL 2^(ex - 52)], [SL = S0 + n - drop].

    [line_ok] states the six conditions under which the search on a line
    misses no hard case; [check_line] tests them.  This file holds the
    definitions only; [ExpProof] proves the checker correct. *)

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
Definition l : Z := 6.            (* words of an A_i or a B_i          *)
Definition k : nat := 9.          (* terms of the Taylor polynomial    *)
Definition m : Z := 43.           (* identical bits after the round bit *)
Definition E : Z := 0x600000 * 2 ^ 320.  (* the window (inferred) *)
Definition guard : Z := 64.       (* extra bits in the exp enclosure   *)
Definition closed : bool := true. (* true: j = 0..n; false: j = 0..n-1 *)

(** ** Derived constants and the binary64 format

    [beta^l = 2^lbits]; a double has [prec] bits, the smallest normal
    exponent is [emin]: if [2^e <= y < 2^(e+1)], the doubles near [y] are
    multiples of [2^(max e emin - prec + 1)], so [v] is
    [2^(max e emin - prec)]. *)

Module SFBI2 := SpecificFloat BigIntRadix2.
Module I := FloatIntervalFull SFBI2.

Definition beta_l : Z := beta ^ l.
Definition lbits : Z := Z.log2 beta * l.
Definition prec : Z := 53.        (* bits of a double                  *)
Definition emin : Z := -1022.     (* smallest normal exponent          *)
Definition iprec : SFBI2.precision :=
  SFBI2.PtoP (Z.to_pos (lbits + prec + guard)).

(** The inputs of a line are [x0 + j u], [j = 0 .. n - drop]. *)
Definition drop : Z := if closed then 0 else 1.

(** [u = 2^uexp ex] for [x0] in [[2^ex, 2^(ex+1))]. *)
Definition uexp (ex : Z) : Z := ex - (prec - 1).

(** [v = 2^vexp e] for [exp x] in [[2^e, 2^(e+1))], or below [2^emin]. *)
Definition vexp (e : Z) : Z := Z.max e emin - prec.

(** ** The conditions *)

Open Scope R_scope.

Definition bp (e : Z) : R := bpow radix2 e.
Definition fracR (r : R) : R := r - IZR (Zfloor r).

(** [a_i = exp x0 u^i / i!]. *)
Definition a (x0 u : R) (i : nat) : R := exp x0 * u ^ i / INR (fact i).

(** [f 0 + ... + f (N-1)]. *)
Fixpoint sumR (f : nat -> R) (N : nat) : R :=
  match N with O => 0 | S N' => sumR f N' + f N' end.

(** [P(j) = A_0 + A_1 j + ... + A_(k-1) j^(k-1)], in integers. *)
Definition Pz (A : list Z) (j : Z) : Z :=
  fold_right Z.add 0%Z
    (map (fun i => (nth i A 0 * j ^ Z.of_nat i)%Z) (seq 0 k)).

(** The six conditions on a line [(x0, n, B)], [x0 = S0 2^(ex - 52)],
    whose last input is [xl = SL 2^(ex - 52)]. *)
Definition line_ok (S0 ex n : Z) (B : list Z) : Prop :=
  let u := bp (uexp ex) in
  let SL := (S0 + n - drop)%Z in
  let x0 := IZR S0 * u in
  let xl := IZR SL * u in
  exists e : Z,
  let v := bp (vexp e) in
  let rho := exp xl * (IZR n * u) ^ k / (INR (fact k) * v) in
  (* 1. u is constant: every S0 + j, j = 0 .. n - drop, has 53 bits *)
  (drop <= n)%Z /\ (2 ^ 52 <= Z.abs S0 < 2 ^ 53)%Z /\
  (2 ^ 52 <= Z.abs SL < 2 ^ 53)%Z /\ (0 < S0 * SL)%Z /\
  (* 2. v is constant on [exp x0, exp xl] *)
  bp e <= exp x0 /\ exp xl < bp (Z.max e emin + 1) /\
  (* 3. (H_A), and the table holds P(0) .. P(k-1) *)
  (exists A : list Z, length A = k /\ length B = k /\
    (forall i, (i < k)%nat ->
       (0 <= nth i A 0%Z < beta_l)%Z /\
       Rabs (IZR (nth i A 0%Z) - IZR beta_l * fracR (a x0 u i / v)) < 1) /\
    (forall i, (i < k)%nat ->
       nth i B 0%Z = (Pz A (Z.of_nat i) mod beta_l)%Z)) /\
  (* 4. (H_T), the Taylor remainder *)
  (forall j, (0 <= j <= n - drop)%Z ->
     Rabs (exp (x0 + IZR j * u) / v -
           sumR (fun i => a x0 u i / v * IZR j ^ i) k) <= rho) /\
  (* 5. (H_E), the window *)
  IZR beta_l * (bp (- m) + rho) + sumR (fun i => IZR n ^ i) k <= IZR E.

Close Scope R_scope.

(** ** The checker *)

Open Scope bool_scope.

(** The float [N 2^ue]. *)
Definition xpt (N ue : Z) : SFBI2.type :=
  Specific_ops.Float (BigZ.of_Z N) (BigZ.of_Z ue).

(** A float as its signed significand and exponent. *)
Definition getS (f : SFBI2.type) : option (Z * Z) :=
  match SFBI2.toF f with
  | Basic.Float s p e => Some (if s then Z.neg p else Z.pos p, e)
  | _ => None
  end.

(** A positive float as its significand and exponent. *)
Definition getF (f : SFBI2.type) : option (positive * Z) :=
  match SFBI2.toF f with Basic.Float false p e => Some (p, e) | _ => None end.

(** An enclosure [[mL 2^fL, mU 2^fU]] of [exp (N 2^ue)]. *)
Definition encl (N ue : Z) : option (Z * Z * Z * Z) :=
  if SFBI2.valid_lb (xpt N ue) && SFBI2.valid_ub (xpt N ue) &&
     match getS (xpt N ue) with
     | Some (p, e) => Z.eqb p N && Z.eqb e ue
     | None => false
     end
  then
    match I.exp iprec (Float.Ibnd (xpt N ue) (xpt N ue)) with
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
    [p 2^(f + gi) / i!]; its nearest integer [R] and its integer part
    [q] (in units of [beta^l]) must be the same at both ends. *)
Definition coefA (mL fL mU fU ve ue : Z) (i : nat) (fk : Z) : option Z :=
  let gi := lbits + ue * Z.of_nat i - ve in
  let R := flr mL (fL + gi) fk 1 in
  let q := flr mL (fL + gi - lbits) fk 0 in
  let Ai := R - q * beta_l in
  if Z.eqb R (flr mU (fU + gi) fk 1) &&
     Z.eqb q (flr mU (fU + gi - lbits) fk 0) &&
     Z.leb 0 Ai && Z.ltb Ai beta_l
  then Some Ai else None.

(** [A_i .. A_(i+c-1)], [fk] being [i!]. *)
Fixpoint coefs (mL fL mU fU ve ue : Z) (i : nat) (fk : Z) (c : nat)
  : option (list Z) :=
  match c with
  | O => Some nil
  | S c' =>
    match coefA mL fL mU fU ve ue i fk,
          coefs mL fL mU fU ve ue (S i) (fk * Z.of_nat (S i)) c' with
    | Some Ai, Some As => Some (Ai :: As)
    | _, _ => None
    end
  end.

(** [1 + n + ... + n^(k-1)]. *)
Definition sumn (n : Z) : Z :=
  fold_right Z.add 0 (map (fun i => n ^ Z.of_nat i) (seq 0 k)).

(** (H_E) with [exp xl <= mU 2^fU]:
    [beta^l (2^-m + mU 2^fU (n u)^k / (k! v)) + sumn n <= E]. *)
Definition window_ok (mU fU ve ue n : Z) : bool :=
  let X := mU * n ^ Z.of_nat k in
  let g := fU + lbits + ue * Z.of_nat k - ve in
  let C := 2 ^ (lbits - m) + sumn n in
  let kf := Z.of_nat (fact k) in
  if Z.leb 0 g then Z.leb (X * 2 ^ g + C * kf) (E * kf)
  else Z.leb (X + C * kf * 2 ^ (- g)) (E * kf * 2 ^ (- g)).

Definition check_line (S0 ex n : Z) (B : list Z) : bool :=
  let SL := S0 + n - drop in
  let ue := uexp ex in
  Z.leb drop n && Z.leb (2 ^ 52) (Z.abs S0) && Z.ltb (Z.abs S0) (2 ^ 53) &&
  Z.leb (2 ^ 52) (Z.abs SL) && Z.ltb (Z.abs SL) (2 ^ 53) &&
  Z.ltb 0 (S0 * SL) && Nat.eqb (length B) k &&
  match encl S0 ue, encl SL ue with
  | Some (mL0, fL0, mU0, fU0), Some (mL1, fL1, mU1, fU1) =>
    let e := Z.log2 mL0 + fL0 in
    let ve := vexp e in
    lt2 mU1 fU1 (Z.max e emin + 1) && window_ok mU1 fU1 ve ue n &&
    match coefs mL0 fL0 mU0 fU0 ve ue 0 1 k with
    | Some A =>
      forallb (fun i => Z.eqb (nth i B 0) (Pz A (Z.of_nat i) mod beta_l))
              (seq 0 k)
    | None => false
    end
  | _, _ => false
  end.
