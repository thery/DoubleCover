From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63 Tabi Moves Coordfs Coordfsi Fstab FsTable
        Searchr Redun Searchir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* V0 .. V4 : bare skeleton -> the real search shape, one ingredient at a
   time, at the SAME depth throughout.  Each returns the node count, which
   must agree with the OCaml half or the comparison is void.

   The heuristic is synthetic -- h x = x land 3 -- so that it is provably the
   same function on both sides and cheap enough not to distort the cost of the
   ingredient being added.  It still prunes, so V4 really is a different tree
   from V3.                                                                *)

Definition allow (p : nat) : seq nat :=
  [seq k <- iota 0 18 | okfc0 nfcube oppf p (fcpos k)].

Definition hsyn (x : int) : nat := to_nat (x land 3)%uint63.

(* V0 : the skeleton -- recursion and the move rule, no state at all *)
Fixpoint V0 (d : nat) (p : nat) : int :=
  if d is d'.+1 then
    (fix go (l : seq nat) (acc : int) : int :=
       if l is k :: l' then go l' (acc + V0 d' (fcpos k))%uint63 else acc)
      (allow p) 1%uint63
  else 1%uint63.

(* V1 : + carry the cube and compose it at every node *)
Fixpoint V1 (d : nat) (a : arr) (p : nat) : int :=
  if d is d'.+1 then
    (fix go (l : seq nat) (acc : int) : int :=
       if l is k :: l' then
         go l' (acc + V1 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                            (fcpos k))%uint63
       else acc) (allow p) 1%uint63
  else 1%uint63.

(* V2 : + the goal test *)
Fixpoint V2 (d : nat) (a : arr) (p : nat) : int :=
  if eq_tabi 47 a (id_tabi 47) then 1%uint63
  else if d is d'.+1 then
    (fix go (l : seq nat) (acc : int) : int :=
       if l is k :: l' then
         go l' (acc + V2 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                            (fcpos k))%uint63
       else acc) (allow p) 1%uint63
  else 1%uint63.

(* V3 : + compute the coordinate and the heuristic (computed, NOT used) *)
Fixpoint V3 (d : nat) (a : arr) (p : nat) : int :=
  if eq_tabi 47 a (id_tabi 47) then 1%uint63
  else if d is d'.+1 then
    (fix go (l : seq nat) (acc : int) : int :=
       if l is k :: l' then
         go l' ((if (of_nat (hsyn (coordi a)) <? 0)%uint63 then 1 else 0) + acc +
                V3 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                      (fcpos k))%uint63
       else acc) (allow p) 1%uint63
  else 1%uint63.

(* V4 : + prune on it -- the real search shape *)
Fixpoint V4 (d : nat) (a : arr) (p : nat) : int :=
  if hsyn (coordi a) <= d then
    if eq_tabi 47 a (id_tabi 47) then 1%uint63
    else if d is d'.+1 then
      (fix go (l : seq nat) (acc : int) : int :=
         if l is k :: l' then
           go l' (acc + V4 d' (comp_tabi 47 a (nth (id_tabi 47) mtis k))
                              (fcpos k))%uint63
         else acc) (allow p) 1%uint63
    else 1%uint63
  else 1%uint63.

Definition D := 5.

Time Eval native_compute in V0 D nfcube.
Time Eval native_compute in V1 D sfti nfcube.
Time Eval native_compute in V2 D sfti nfcube.
Time Eval native_compute in V3 D sfti nfcube.
Time Eval native_compute in V4 D sfti nfcube.
