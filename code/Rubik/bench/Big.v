(* Can the kernel hold a table the size of the real one?

   b.[i / n].[i mod n] = i  with n = 2^k, so n*n entries.
   n = 1024  ->      1 048 576   (smoke test)
   n = 16384 ->    268 435 456   (2.1 GB of int63)

   For scale: the phase-1 pruning table is 2 217 093 120 values in 0..10, so
   nibble packed it is 1.5e8 int63 -- SMALLER than the 2.68e8 tested here. *)

From Stdlib Require Import Uint63 PArray.
Open Scope uint63_scope.

Fixpoint mkrows (r : nat) (n c : int) (b : array (array int))
                : array (array int) :=
  match r with
  | O => b
  | S r' => mkrows r' n (c + 1) (PArray.set b c (PArray.make n 0))
  end.

Definition empty (n : int) (r : nat) : array (array int) :=
  mkrows r n 0 (PArray.make n (PArray.make 1 0)).

(* fill a row completely, then one outer set *)
Fixpoint fillrow (r : nat) (n c j : int) (row : array int) : array int :=
  match r with
  | O => row
  | S r' => fillrow r' n c (j + 1) (PArray.set row j (c * n + j))
  end.

Fixpoint fillB (r : nat) (rin : nat) (n c : int) (b : array (array int))
               : array (array int) :=
  match r with
  | O => b
  | S r' => fillB r' rin n (c + 1)
              (PArray.set b c (fillrow rin n c 0 (PArray.get b c)))
  end.

Fixpoint maxrow (r : nat) (j m : int) (row : array int) : int :=
  match r with
  | O => m
  | S r' =>
      let v := PArray.get row j in
      maxrow r' (j + 1) (if m <? v then v else m) row
  end.

Fixpoint maxall (r : nat) (rin : nat) (c m : int) (b : array (array int))
                : int :=
  match r with
  | O => m
  | S r' => maxall r' rin (c + 1) (maxrow rin 0 m (PArray.get b c)) b
  end.

Definition build_max (n : int) (r : nat) : int :=
  maxall r r 0 0 (fillB r r n 0 (empty n r)).
