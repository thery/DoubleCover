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
(* PArray is imported without its notations -- ssrint63.v does the same and   *)
(* redeclares the ones it needs -- and ssrint63.v brings the int63 toolbox:   *)
(* of_natK, to_natK, to_nat_incr, to_nat_bounded, the reflect views, and int  *)
(* as an eqType.                                                              *)
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
(* the name avoids mathcomp's ssrint, which would win the short name          *)
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

Section Tabi.

(* tables have size n.+1, as in Table.v                                       *)
Variable n : nat.

Notation arr := (PArray.array int).

(* the tables are indexed by int63, so n.+1 has to fit in one.  For the cube  *)
(* n is 47.                                                                   *)
Hypothesis n_small : n.+1 < nwB.

(* ---- 0. The array axioms, instantiated ----------------------------------- *)

(* PrimArray.get is universe polymorphic and the axioms about it are not, so  *)
(* neither apply nor rewrite can guess their type argument.  Instantiating    *)
(* them once at int makes them usable by plain rewrite everywhere below.      *)

Lemma get_setE (t : arr) (i v : int) :
  (i <? PArray.length t)%uint63 = true -> PArray.get (PArray.set t i v) i = v.
Proof. exact: (@PArray.get_set_same int t i v). Qed.

Lemma get_set_otherE (t : arr) (i j v : int) :
  i <> j -> PArray.get (PArray.set t i v) j = PArray.get t j.
Proof. exact: (@PArray.get_set_other int t i j v). Qed.

Lemma get_makeE (v i sz : int) : PArray.get (PArray.make sz v) i = v.
Proof. exact: (@PArray.get_make int v sz i). Qed.

(* ---- 0. nat and int63 ---------------------------------------------------- *)

(* to_nat and of_nat, of_natK, to_natK, to_nat_incr, to_nat_bounded and the   *)
(* reflect views all come from ssrint63.v.  Nothing here ever runs: ti2t      *)
(* only inside proofs.                                                        *)

Lemma to_of_natK k : k < n.+1 -> to_nat (of_nat k) = k.
Proof. by move=> kn; apply: of_natK; exact: leq_trans kn (ltnW n_small). Qed.

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

(* successor, and the two shapes of fold the operations use: an index below   *)
(* the start is untouched, an index in range gets what the fold writes.       *)

Lemma to_nat_add1 i : (to_nat i).+1 <= n.+1 -> to_nat (i + 1) = (to_nat i).+1.
Proof. by move=> h; apply: to_nat_incr; apply: leq_ltn_trans h n_small. Qed.

Lemma get_foldi_lt (g : int -> int) m i0 j a :
  to_nat i0 + m <= n.+1 -> to_nat j < to_nat i0 ->
  PArray.get (foldi m i0 (fun i c => PArray.set c i (g i)) a) j =
  PArray.get a j.
Proof.
elim: m i0 a => [|m IH] i0 a //= hb hj.
have h1 : (to_nat i0).+1 <= n.+1.
  by rewrite (leq_trans _ hb) // addnS ltnS leq_addr.
rewrite IH.
- by rewrite get_set_otherE // => e; rewrite e ltnn in hj.
- by rewrite to_nat_add1 // addSn -addnS.
by rewrite to_nat_add1 // ltnS ltnW.
Qed.

Lemma get_foldi_in (g : int -> int) m i0 j a :
  to_nat i0 + m <= n.+1 -> to_nat i0 <= to_nat j < to_nat i0 + m ->
  PArray.get (foldi m i0 (fun i c => PArray.set c i (g i)) a) j = g j.
Proof.
Admitted.


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
