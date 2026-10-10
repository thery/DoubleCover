(* Domain.v — mirrors numbers.elpi: domains of numbers, for the evaluators.

   A domain is the record of its operations on its numbers, of some type N:
   how a literal reads, and how the unary and binary operations and the
   comparisons compute. The evaluators take a domain as an argument and are
   polymorphic in N. As an Elpi predicate may fail (no clause for an unknown
   operator), an operation returns an option. A comparison is decided by an
   `if` in Elpi, which never fails; here it returns an option too, so that a
   domain may refuse to compare two equal numbers: the partial semantics of
   Abadi and Plotkin (Smooth.v). The reals and the dual numbers never refuse.

   The domain of Elpi's floats becomes the domain of the reals of Rocq: a
   literal is read exactly (as a rational number), and the operations are those
   of R. Dual numbers are over any domain, as in Elpi. *)

From Stdlib Require Import String Ascii ZArith List QArith Qreals Reals
  DecimalString.
From ElpiDiff Require Import Syntax.

Import ListNotations.
Open Scope R_scope.

Record domain (N : Type) : Type := Domain {
  dom_lit : string -> option N;                   (* a real literal,
    spelled as in the source: "2", "0.9" *)
  dom_op1 : unary -> N -> option N;               (* a unary operation *)
  dom_op2 : binary -> N -> N -> option N;
    (* a binary arithmetic operation *)
  dom_cmp : binary -> N -> N -> option bool       (* a comparison *)
}.

Arguments Domain {N}.  Arguments dom_lit {N}.  Arguments dom_op1 {N}.
Arguments dom_op2 {N}.  Arguments dom_cmp {N}.

(* --- reading a literal ------------------------------------------------------
   string_to_real of Elpi, on the literals of the source: an optional sign,
   digits, an optional fractional part, an optional exponent; read exactly,
   as a rational number. *)

Definition digit (c : ascii) : option Z :=
  let n := nat_of_ascii c in
  if (48 <=? n)%nat && (n <=? 57)%nat then Some (Z.of_nat (n - 48)) else None.

(* read_digits l m k: the digits at the head of l appended to m, with their
   number added to k, and the rest of l. *)
Fixpoint read_digits (l : list ascii) (m : Z) (k : nat) : Z * nat * list ascii
  :=
  match l with
  | c :: l' => match digit c with
               | Some d => read_digits l' (m * 10 + d)%Z (S k)
               | None => (m, k, l)
               end
  | [] => (m, k, [])
  end.

Definition read_sign (l : list ascii) : Z * list ascii :=
  match l with
  | "-"%char :: l' => ((-1)%Z, l')
  | "+"%char :: l' => (1%Z, l')
  | _ => (1%Z, l)
  end.

(* A decimal number: m * 10^e, with m the digits before and after the point. *)
Definition read_decimal (l : list ascii) : option Q :=
  let '(sg, l0) := read_sign l in
  let '(m1, k1, l1) := read_digits l0 0 0 in
  let '(m2, k2, l2) := match l1 with
                       | "."%char :: l' => read_digits l' m1 0
                       | _ => (m1, 0%nat, l1)
                       end in
  let '(ex, l3) := match l2 with
                   | c :: l' => if (c =? "e")%char || (c =? "E")%char then
                                  let '(se, l'') := read_sign l' in
                                  let '(x, kx, l4) := read_digits l'' 0 0 in
                                  if (kx =? 0)%nat then (0%Z, l2) else
                                    ((se * x)%Z, l4)
                                else (0%Z, l2)
                   | [] => (0%Z, [])
                   end in
  if ((k1 + k2 =? 0)%nat || negb (match l3 with [] => true | _ =>
    false end))%bool then None
  else Some (inject_Z (sg * m2) * Qpower (inject_Z 10) (ex - Z.of_nat k2))%Q.

Definition strip (l : list ascii) : list ascii :=
  let fix drop l := match l with " "%char :: l' => drop l' | _ => l end in
  rev (drop (rev (drop l))).

(* A literal is a number, or the quotient of two numbers ("13.0 / 12.0"), a
   constant expression of C++: float-lit in numbers.elpi. *)
Definition read_literal (s : string) : option Q :=
  let l := list_ascii_of_string s in
  let fix split (l acc : list ascii) : option (list ascii * list ascii) :=
    match l with
    | "/"%char :: l' => Some (rev acc, l')
    | c :: l' => split l' (c :: acc)
    | [] => None
    end in
  match split l [] with
  | Some (a, b) => match read_decimal (strip a), read_decimal (strip b) with
                   | Some x, Some y => Some (x / y)%Q
                   | _, _ => None
                   end
  | None => read_decimal (strip l)
  end.

(* --- the reals
   ----------------------------------------------------------------
   The domain of floats of Elpi, with the reals of Rocq. *)

Definition real_lit (s : string) : option R :=
  match read_literal s with Some q => Some (Q2R q) | None => None end.

Definition real_op1 (f : unary) (x : R) : option R :=
  match f with
  | Neg => Some (- x)
  | Sin => Some (sin x)
  | Cos => Some (cos x)
  | Exp => Some (exp x)
  | Log => Some (ln x)
  | Sqrt => Some (sqrt x)
  | Pow k => Some (powerRZ x k)
  | Unknown1 _ => None
  end.

Definition real_op2 (f : binary) (x y : R) : option R :=
  match f with
  | Add => Some (x + y)
  | Sub => Some (x - y)
  | Mul => Some (x * y)
  | Divide => Some (x / y)
  | _ => None
  end.

(* A comparison of reals always answers. *)
Definition real_cmp (f : binary) (x y : R) : option bool :=
  match f with
  | Lt => Some (if Rlt_dec x y then true else false)
  | Le => Some (if Rle_dec x y then true else false)
  | Gt => Some (if Rgt_dec x y then true else false)
  | Ge => Some (if Rge_dec x y then true else false)
  | _ => Some false
  end.

Definition reals : domain R := Domain real_lit real_op1 real_op2 real_cmp.

(* --- dual numbers
   --------------------------------------------------------------
   `Dual x dx`: a value and its tangent, over any domain B. An operation
   computes its value in B and its tangent by the chain rule, with the partial
   derivatives of operations.elpi computed in B. *)

Inductive dual (N : Type) : Type := Dual (x dx : N).
Arguments Dual {N}.

Section Duals.
Variable N : Type.
Variable B : domain N.

Local Notation "'let*' x := a 'in' b" :=
  (match a with Some x => b | None => None end)
  (at level 200, x name, b at level 200).

(* A literal is a constant: its tangent is zero. *)
Definition dual_lit (s : string) : option (dual N) :=
  let* x := dom_lit B s in let* z := dom_lit B "0" in Some (Dual x z).

(* dual_partial1 f x y: the derivative of f at x, where y = f x. *)
Definition dual_partial1 (f : unary) (x y : N) : option N :=
  match f with
  | Neg => dom_lit B "-1"
  | Sin => dom_op1 B Cos x
  | Cos => let* s := dom_op1 B Sin x in dom_op1 B Neg s
  | Exp => Some y
  | Log => let* o := dom_lit B "1" in dom_op2 B Divide o x
  | Sqrt => let* o := dom_lit B "1" in let* t := dom_lit B "2" in
            let* t2 := dom_op2 B Mul t y in dom_op2 B Divide o t2
  | Pow 0 => dom_lit B "0"
  | Pow k => let* q := dom_op1 B (Pow (k - 1)) x in
             let* kb := dom_lit B (NilZero.string_of_int (Z.to_int k)) in
               dom_op2 B Mul kb q
  | Unknown1 _ => None
  end.

(* op1 f (Dual x dx) is (f x, f'(x) dx). *)
Definition dual_op1 (f : unary) (a : dual N) : option (dual N) :=
  let 'Dual x dx := a in
  let* y := dom_op1 B f x in let* p := dual_partial1 f x y in
  let* dy := dom_op2 B Mul p dx in Some (Dual y dy).

(* op2 f: the value, and the tangent by the partial derivatives. *)
Definition dual_op2 (f : binary) (a b : dual N) : option (dual N) :=
  let 'Dual x dx := a in let 'Dual y dy := b in
  match f with
  | Add => let* z := dom_op2 B Add x y in let* dz :=
    dom_op2 B Add dx dy in Some (Dual z dz)
  | Sub => let* z := dom_op2 B Sub x y in let* dz :=
    dom_op2 B Sub dx dy in Some (Dual z dz)
  | Mul => let* z := dom_op2 B Mul x y in
    (* d(xy) = y dx + x dy *)
           let* u := dom_op2 B Mul y dx in let* w := dom_op2 B Mul x dy in
           let* dz := dom_op2 B Add u w in Some (Dual z dz)
  | Divide => let* z := dom_op2 B Divide x y in
    (* d(x/y) = (dx - (x/y) dy) / y *)
              let* u := dom_op2 B Mul z dy in let* w := dom_op2 B Sub dx u in
              let* dz := dom_op2 B Divide w y in Some (Dual z dz)
  | _ => None
  end.

(* A comparison compares the values, in B: it answers when B answers. *)
Definition dual_cmp (f : binary) (a b : dual N) : option bool :=
  let 'Dual x _ := a in let 'Dual y _ := b in dom_cmp B f x y.

Definition duals : domain (dual N) := Domain dual_lit dual_op1 dual_op2
  dual_cmp.

End Duals.

Arguments duals {N}.
