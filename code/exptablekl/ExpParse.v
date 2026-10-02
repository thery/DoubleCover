(** * Reading the lines of the table from their text

    A line of a table file is kept verbatim as a primitive string:

      -0x1.62e42fefa39efp+0 183286408249 6 4 0xca7ee542549487ee ...

    that is [x0] in hexadecimal ([-]? [0x1], then [.F] with at most 13
    digits or nothing, then [p], a sign and the exponent in decimal), [n],
    [k] and [l] in decimal, then [k * l] words in hexadecimal, each [B_i]
    being [l] words, the least significant first.  [parse] turns such a
    line into [(S0, ex, n, k, l, B)] with [x0 = S0 2^(ex - 52)]; a line of
    another shape, or with [k] or [l] out of [[1, kmax]] or [[1, lmax]],
    gives [None], and [check_raw] then answers [false]. *)

From Stdlib Require Import ZArith List PrimString PrimStringAxioms Uint63.
From ExpTableKL Require Import ExpCheck.
Import ListNotations.

Open Scope Z_scope.

(** ** Characters *)

Definition c_space : int := 32%uint63.   (* ' ' *)
Definition c_0 : int := 48%uint63.       (* '0' *)
Definition c_9 : int := 57%uint63.       (* '9' *)
Definition c_a : int := 97%uint63.       (* 'a' *)
Definition c_f : int := 102%uint63.      (* 'f' *)
Definition c_x : int := 120%uint63.      (* 'x' *)
Definition c_dot : int := 46%uint63.     (* '.' *)
Definition c_p : int := 112%uint63.      (* 'p' *)
Definition c_plus : int := 43%uint63.    (* '+' *)
Definition c_1 : int := 49%uint63.       (* '1' *)
Definition c_minus : int := 45%uint63.   (* '-' *)

(** The value of a hexadecimal digit, or [None]. *)
Definition hexd (c : int) : option Z :=
  if (c_0 <=? c)%uint63 && (c <=? c_9)%uint63 then Some (to_Z (c - c_0))
  else if (c_a <=? c)%uint63 && (c <=? c_f)%uint63
  then Some (to_Z (c - c_a) + 10)
  else None.

(** The value of a decimal digit, or [None]. *)
Definition decd (c : int) : option Z :=
  if (c_0 <=? c)%uint63 && (c <=? c_9)%uint63 then Some (to_Z (c - c_0))
  else None.

(** ** Numbers *)

(** The number written with the digits [cs] in base [b], most
    significant first; [None] if a character is not a digit. *)
Fixpoint digits (d : int -> option Z) (b acc : Z) (cs : list int)
  : option Z :=
  match cs with
  | [] => Some acc
  | c :: cs' =>
    match d c with
    | Some v => digits d b (acc * b + v) cs'
    | None => None
    end
  end.

Definition hexv (cs : list int) : option Z :=
  match cs with [] => None | _ => digits hexd 16 0 cs end.

Definition decv (cs : list int) : option Z :=
  match cs with [] => None | _ => digits decd 10 0 cs end.

(** A word [0xhh...h]. *)
Definition wordv (cs : list int) : option Z :=
  match cs with
  | c0 :: cx :: cs' =>
    if (c0 =? c_0)%uint63 && (cx =? c_x)%uint63 then hexv cs' else None
  | _ => None
  end.

(** The characters before the first [p], and those after it. *)
Fixpoint split_p (cs : list int) : list int * list int :=
  match cs with
  | [] => ([], [])
  | c :: cs' =>
    if (c =? c_p)%uint63 then ([], cs')
    else let (a, b) := split_p cs' in (c :: a, b)
  end.

(** A signed exponent [+d...d] or [-d...d]. *)
Definition expv (cs : list int) : option Z :=
  match cs with
  | c :: cs' =>
    if (c =? c_plus)%uint63 then decv cs'
    else if (c =? c_minus)%uint63 then
      match decv cs' with Some e => Some (- e) | None => None end
    else None
  | [] => None
  end.

(** The fraction digits [F] of [0x1.F] and the exponent: [.F] may be
    absent, and [F] has at most 13 digits (trailing zeros may be left
    out); the significand is [16^13 + F 16^(13 - |F|)]. *)
Definition fracv (cs : list int) : option (Z * Z) :=
  let (fr, ex) := split_p cs in
  match fr with
  | [] => match expv ex with Some e => Some (16 ^ 13, e) | None => None end
  | cd :: fr' =>
    if (cd =? c_dot)%uint63 && Nat.leb (List.length fr') 13 then
      match digits hexd 16 1 fr', expv ex with
      | Some f, Some e => Some (f * 16 ^ Z.of_nat (13 - List.length fr'), e)
      | _, _ => None
      end
    else None
  end.

(** [x0 = [-]0x1.Fp+-E]: its signed significand [S0] and its exponent,
    [x0 = S0 2^(E - 52)]. *)
Definition x0v (cs : list int) : option (Z * Z) :=
  let (sg, cs1) :=
    match cs with
    | c :: cs' => if (c =? c_minus)%uint63 then (true, cs') else (false, cs)
    | [] => (false, cs)
    end in
  match cs1 with
  | c0 :: cx :: c1 :: cs' =>
    if (c0 =? c_0)%uint63 && (cx =? c_x)%uint63 && (c1 =? c_1)%uint63 then
      match fracv cs' with
      | Some (M, e) => Some (if sg then - M else M, e)
      | None => None
      end
    else None
  | _ => None
  end.

(** ** Lines *)

(** The fields of a line, separated by single spaces. *)
Fixpoint fields (cur : list int) (cs : list int) : list (list int) :=
  match cs with
  | [] => [rev cur]
  | c :: cs' =>
    if (c =? c_space)%uint63 then rev cur :: fields [] cs'
    else fields (c :: cur) cs'
  end.

(** [w_0 + w_1 beta + ... ], the words least significant first. *)
Definition wsum (ws : list Z) : Z := fold_right (fun w a => w + beta * a) 0 ws.

(** The [c] numbers [B_i], each of [lw] words, from the list of all
    words. *)
Fixpoint group (c lw : nat) (ws : list Z) : list Z :=
  match c with
  | O => []
  | S c' => wsum (firstn lw ws) :: group c' lw (skipn lw ws)
  end.

(** All the words, or [None] if one is not a word. *)
Fixpoint wordsv (fs : list (list int)) : option (list Z) :=
  match fs with
  | [] => Some []
  | f :: fs' =>
    match wordv f, wordsv fs' with
    | Some w, Some ws => Some (w :: ws)
    | _, _ => None
    end
  end.

(** [k] and [l] are checked before they are used as sizes. *)
Definition parse (s : string) : option (Z * Z * Z * nat * Z * list Z) :=
  match fields [] (to_list s) with
  | fx :: fn :: fk :: fl :: fw =>
    match x0v fx, decv fn, decv fk, decv fl with
    | Some (S0, ex), Some n, Some k, Some l =>
      if Z.leb 1 k && Z.leb k (Z.of_nat kmax) && Z.leb 1 l &&
         Z.leb l lmax &&
         Nat.eqb (List.length fw) (Z.to_nat k * Z.to_nat l) then
        match wordsv fw with
        | Some ws =>
          Some (S0, ex, n, Z.to_nat k, l,
                group (Z.to_nat k) (Z.to_nat l) ws)
        | None => None
        end
      else None
    | _, _, _, _ => None
    end
  | _ => None
  end.

(** ** The check on the text *)

Definition check_raw (ls : list string) : bool :=
  forallb (fun s => match parse s with
                    | Some (S0, ex, n, k, l, B) => check_line S0 ex n k l B
                    | None => false
                    end) ls.
