(* =========================================================================  *)
(*  Tabi.v                                                                    *)
(*                                                                            *)
(*  The tables of Table.v, on int63 and PArray, and the bridge back.          *)
(*                                                                            *)
(*  WHY A BRIDGE.  Rewriting Table.v itself in PArray means rebuilding the    *)
(*  list library first -- uniq, index, nth, map -- since tab_ok is stated     *)
(*  with them.  Instead every array operation is only asked to AGREE with     *)
(*  the list one it mirrors:                                                  *)
(*                                                                            *)
(*      ti2t (comp_tabi a b) = comp_tab (ti2t a) (ti2t b)                     *)
(*                                                                            *)
(*  and the reasoning stays on the list side, where mathcomp already has      *)
(*  everything.  Well-formedness is not even restated: tabi_ok is tab_ok      *)
(*  read through the bridge, so tab_ok_comp and friends apply unchanged.      *)
(*                                                                            *)
(*  ti2t is never executed.  The search runs on arrays; the lists exist only  *)
(*  inside proofs, and tabi_ok only in statements -- it is paid once for the  *)
(*  eighteen move tables and the start table, then carried by tab_ok_comp.    *)
(*                                                                            *)
(*  NOTHING BELOW IS PROVED YET.  This is the skeleton: the operations, the   *)
(*  search, and what each has to satisfy.                                     *)
(* =========================================================================  *)
(* Uint63 first and mathcomp after, so mathcomp wins the names they share     *)
(* (size).  PArray is Required but not Imported: its .[ ] notation would      *)
(* clash with mathcomp's.                                                     *)
From Stdlib Require Import Uint63.
From Stdlib Require PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Search Tsearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Section Tabi.

(* tables have size n.+1, as in Table.v                                       *)
Variable n : nat.

Notation arr := (PArray.array int).

(* ---- 0. nat and int63 ---------------------------------------------------- *)

(* Uint63 gives to_nat and of_nat directly; neither ever runs, since ti2t     *)
(* lives only inside proofs.                                                  *)

Lemma to_natK k : (k < n.+1)%nat -> to_nat (of_nat k) = k.
Proof.
Admitted.

Lemma of_natK x : (to_nat x < n.+1)%nat -> of_nat (to_nat x) = x.
Proof.
Admitted.

(* ---- 1. The bridge ------------------------------------------------------- *)

Definition ti2t (a : arr) : seq nat :=
  [seq to_nat (PArray.get a (of_nat k)) | k <- iota 0 n.+1].

(* Well-formedness is NOT restated: it is tab_ok, read through the bridge.    *)
Definition tabi_ok (a : arr) := tab_ok n (ti2t a).

Lemma size_ti2t a : size (ti2t a) = n.+1.
Proof.
Admitted.

(* ---- 2. The operations --------------------------------------------------- *)

(* a bounded loop; the fuel is n.+1, which is a variable, not a literal       *)

Fixpoint foldi (k : nat) (i : int) (f : int -> arr -> arr) (a : arr) : arr :=
  match k with
  | O => a
  | S k' => foldi k' (i + 1) f (f i a)
  end.

Definition id_tabi : arr :=
  foldi n.+1 0 (fun i a => PArray.set a i i) (PArray.make (of_nat n.+1) 0).

(* (a then b): the entry at i is b at a's entry at i.  It fills a FRESH       *)
(* array rather than overwriting a: the search composes the same a with all   *)
(* eighteen moves in a row, and PArray being persistent, an in place fold     *)
(* would leave a behind a chain of n.+1 diffs that every sibling then has to  *)
(* re-root through.                                                           *)
Definition comp_tabi (a b : arr) : arr :=
  foldi n.+1 0 (fun i c => PArray.set c i (PArray.get b (PArray.get a i)))
        (PArray.make (of_nat n.+1) 0).

Definition inv_tabi (a : arr) : arr :=
  foldi n.+1 0 (fun i c => PArray.set c (PArray.get a i) i)
        (PArray.make (of_nat n.+1) 0).

Fixpoint exp_tabi (a : arr) (m : nat) : arr :=
  if m is m1.+1 then comp_tabi a (exp_tabi a m1) else id_tabi.

Fixpoint eqi (k : nat) (i : int) (a b : arr) : bool :=
  match k with
  | O => true
  | S k' => (PArray.get a i =? PArray.get b i) && eqi k' (i + 1) a b
  end.

Definition eq_tabi (a b : arr) : bool := eqi n.+1 0 a b.

(* ---- 3. What the operations have to satisfy ------------------------------ *)

Lemma ti2t_id : ti2t id_tabi = id_tab n.
Proof.
Admitted.

Lemma ti2t_comp a b :
  tabi_ok a -> tabi_ok b -> ti2t (comp_tabi a b) = comp_tab (ti2t a) (ti2t b).
Proof.
Admitted.

Lemma ti2t_inv a : tabi_ok a -> ti2t (inv_tabi a) = inv_tab n (ti2t a).
Proof.
Admitted.

Lemma ti2t_exp a m : tabi_ok a -> ti2t (exp_tabi a m) = exp_tab n (ti2t a) m.
Proof.
Admitted.

Lemma eq_tabiE a b :
  tabi_ok a -> tabi_ok b -> eq_tabi a b = (ti2t a == ti2t b).
Proof.
Admitted.

(* the ones the search needs, in the form it needs them                       *)
Lemma tabi_ok_comp a b : tabi_ok a -> tabi_ok b -> tabi_ok (comp_tabi a b).
Proof.
Admitted.

Lemma eq_tabi_id a : tabi_ok a -> eq_tabi a id_tabi = (ti2t a == id_tab n).
Proof.
Admitted.

(* ---- 4. The search, on arrays -------------------------------------------- *)

(* the moves, as arrays                                                       *)
Variable mtis : seq (arr).
Hypothesis mtis_ok : all tabi_ok mtis.

(* the heuristic, read on arrays, and the list-side one it mirrors            *)
Variable Dti : arr -> nat.
Variable Dt : seq nat -> nat.
Hypothesis DtiE : forall a, tabi_ok a -> Dti a = Dt (ti2t a).

Fixpoint searchi (d : nat) (a : arr) : bool :=
  (Dti a <= d) &&
  (eq_tabi a id_tabi ||
   (if d is d'.+1 then has (fun mt => searchi d' (comp_tabi a mt)) mtis
    else false)).

(* THE BRIDGE FOR THE SEARCH: what runs and what is proved sound agree.       *)
Lemma searchiE d a :
  tabi_ok a -> searchi d a = searcht n [seq ti2t mt | mt <- mtis] Dt d (ti2t a).
Proof.
Admitted.

(* and hence, composing with searchtE of Tsearch.v and searchN of Search.v,   *)
(* a false answer from the array search is a membership fact.                 *)
Corollary searchiN d a :
  tabi_ok a -> searchi d a = false ->
  searcht n [seq ti2t mt | mt <- mtis] Dt d (ti2t a) = false.
Proof. by move=> aok; rewrite searchiE. Qed.

End Tabi.
