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

(* and the arrays must be allocatable                                         *)
Hypothesis n_len : (of_nat n.+1 <=? PArray.max_length)%uint63.

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

(* simpl must not unfold it: the search proofs use /= and would otherwise     *)
(* turn ti2t a into its map and shred the goal.                               *)
Arguments ti2t : simpl never.

(* Well-formedness is NOT restated: it is tab_ok, read through the bridge.    *)
Definition tabi_ok (a : arr) := tab_ok n (ti2t a).

Lemma size_ti2t a : size (ti2t a) = n.+1.
Proof. by rewrite size_map size_iota. Qed.

(* ---- 2. The operations --------------------------------------------------- *)

(* a bounded loop; the fuel is n.+1, which is a variable, not a literal       *)

Fixpoint foldi (k : nat) (i : int) (f : int -> arr -> arr) (a : arr) : arr :=
  match k with
  | O => a
  | S k' => foldi k' (i + 1) f (f i a)
  end.

(* successor, and the two shapes of fold the operations use: an index below   *)
(* the start is untouched, an index in range gets what the fold writes.       *)

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

(* ---- 3. What the operations compute, index by index ---------------------  *)

(* Everything below is read through these four: the bridge is a map over      *)
(* iota, so each ti2t equation reduces to one index, and each operation is    *)
(* a fold, so each index reduces to one get.                                  *)

(* the defining property of the bridge                                        *)
Lemma nth_ti2t a i :
  i < n.+1 -> nth 0%N (ti2t a) i = to_nat (get a (of_nat i)).
Proof.
move=> iL; rewrite /ti2t.
rewrite (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota // add0n.
Qed.

(* a well formed table holds indices, which is what makes the composite       *)
(* lookups land in range                                                      *)
Lemma tabi_lt a i :
  tabi_ok a -> i < n.+1 -> to_nat (get a (of_nat i)) < n.+1.
Proof.
move=> aok iL; rewrite -nth_ti2t //.
have /and3P[_ /allP hall _] := aok.
by apply: hall; rewrite mem_nth // size_ti2t.
Qed.

Lemma get_id_tabi i : i < n.+1 -> get id_tabi (of_nat i) = of_nat i.
Proof.
move=> iL.
rewrite /id_tabi
  (@get_foldi_in (fun j => j) n.+1 0 (of_nat i) (make (of_nat n.+1) 0)).
- by [].
- by rewrite to_nat_0 add0n.
- by rewrite to_nat_0 add0n length_makeE n_len of_natK.
by rewrite to_nat_0 add0n to_of_natK //= iL.
Qed.

Lemma get_comp_tabi a b i :
  i < n.+1 -> get (comp_tabi a b) (of_nat i) = get b (get a (of_nat i)).
Proof.
move=> iL.
rewrite /comp_tabi
  (@get_foldi_in (fun j => get b (get a j)) n.+1 0 (of_nat i)
     (make (of_nat n.+1) 0)).
- by [].
- by rewrite to_nat_0 add0n.
- by rewrite to_nat_0 add0n length_makeE n_len of_natK.
by rewrite to_nat_0 add0n to_of_natK //= iL.
Qed.


(* ---- 4. What the operations have to satisfy ------------------------------ *)

Lemma ti2t_id : ti2t id_tabi = id_tab n.
Proof.
apply: (@eq_from_nth _ 0%N) => [|k];
  first by rewrite size_ti2t /id_tab size_iota.
rewrite size_ti2t => kL.
by rewrite nth_ti2t // get_id_tabi // to_of_natK // /id_tab nth_iota.
Qed.

Lemma ti2t_comp a b :
  tabi_ok a -> tabi_ok b -> ti2t (comp_tabi a b) = comp_tab (ti2t a) (ti2t b).
Proof.
move=> aok bok.
apply: (@eq_from_nth _ 0%N) => [|k].
  by rewrite size_ti2t /comp_tab size_map size_ti2t.
rewrite size_ti2t => kL.
rewrite nth_ti2t // get_comp_tabi // /comp_tab (nth_map 0%N) ?size_ti2t //.
by rewrite !nth_ti2t ?to_natK //; exact: tabi_lt.
Qed.

(* The inverse fold is the odd one out: it writes the index i at position     *)
(* get a i, so what survives at a position is decided by injectivity of the   *)
(* table rather than by the order of the writes.                              *)
(* the entries of a well formed table are pairwise distinct, so reading it    *)
(* is injective on indices -- this is what makes the inverse well defined.    *)
Lemma get_tabi_inj a x y :
  tabi_ok a -> to_nat x < n.+1 -> to_nat y < n.+1 ->
  get a x = get a y -> x = y.
Proof.
move=> aok hx hy hxy.
have /and3P[/eqP sE _ aU] := aok.
(* to_nat (get a x) is nth (ti2t a) (to_nat x) by nth_ti2t and to_natK, and   *)
(* ti2t a is uniq, so index_uniq turns equal entries into equal indices.      *)
have e : nth 0%N (ti2t a) (to_nat x) = nth 0%N (ti2t a) (to_nat y).
  by rewrite !nth_ti2t ?hx ?hy; first by rewrite !to_natK ?hxy.
apply: to_nat_inj.
rewrite -(index_uniq 0%N (i := to_nat x) (s := ti2t a)) ?sE //.
by rewrite e index_uniq // sE.
Qed.

Lemma get_inv_tabi a j :
  tabi_ok a -> j < n.+1 ->
  to_nat (get (inv_tabi a) (of_nat j)) = index j (ti2t a).
Proof.
move=> aok jL.
have /and3P[/eqP asz _ auniq] := aok.
have jin : j \in ti2t a by apply: (tab_memE aok).
set i := index j (ti2t a).
have iL : i < n.+1 by rewrite -asz index_mem.
have hnth : to_nat (get a (of_nat i)) = j by rewrite -nth_ti2t // nth_index.
have hgj : get a (of_nat i) = of_nat j.
  by apply: to_nat_inj; rewrite hnth to_of_natK.
rewrite -hgj /inv_tabi
  (@get_foldi_wr (get a) n.+1 0 (of_nat i) (make (of_nat n.+1) 0)).
- by rewrite to_of_natK.
- by rewrite to_nat_0 add0n.
- move=> x; rewrite to_nat_0 add0n => /andP[_ hx].
  apply/nltbP; rewrite length_makeE n_len of_natK //.
  by rewrite -[x]to_natK tabi_lt.
- move=> x y; rewrite to_nat_0 add0n => /andP[_ hx] /andP[_ hy].
  exact: get_tabi_inj.
by rewrite to_nat_0 add0n to_of_natK //= iL.
Qed.

Lemma ti2t_inv a : tabi_ok a -> ti2t (inv_tabi a) = inv_tab n (ti2t a).
Proof.
move=> aok.
apply: (@eq_from_nth _ 0%N) => [|k].
  by rewrite size_ti2t /inv_tab size_map size_iota.
rewrite size_ti2t => kL.
rewrite nth_ti2t // get_inv_tabi // /inv_tab (nth_map 0%N) ?size_iota //.
by rewrite nth_iota // add0n.
Qed.

Lemma ti2t_exp a m : tabi_ok a -> ti2t (exp_tabi a m) = exp_tab n (ti2t a) m.
Proof.
move=> aok; elim: m => [|m IH] /=; first exact: ti2t_id.
have eok : tabi_ok (exp_tabi a m).
  by rewrite /tabi_ok IH; apply: tab_ok_exp.
by rewrite ti2t_comp // IH.
Qed.

(* eqi compares the m entries from i0 on, one by one                          *)
Lemma eqiE m i0 a b :
  to_nat i0 + m < nwB ->
  eqi m i0 a b =
  all (fun k => get a (of_nat k) == get b (of_nat k)) (iota (to_nat i0) m).
Proof.
elim: m i0 => [|m IH] i0 //= hb.
rewrite -[(i0 + 1)%uint63]/(incr _).
have hi : (to_nat i0).+1 < nwB.
  by apply: leq_ltn_trans hb; rewrite addnS ltnS leq_addr.
rewrite IH; last by rewrite to_nat_incr // addSn -addnS.
by rewrite to_nat_incr // eqb_eqb to_natK.
Qed.

Lemma eq_tabiE a b :
  tabi_ok a -> tabi_ok b -> eq_tabi a b = (ti2t a == ti2t b).
Proof.
move=> aok bok.
rewrite /eq_tabi eqiE ?to_nat_0 ?add0n //.
apply/allP/eqP => [hall|e].
  apply: (@eq_from_nth _ 0%N) => [|k]; first by rewrite !size_ti2t.
  rewrite size_ti2t => kL.
  rewrite !nth_ti2t //; congr (to_nat _); apply/eqP.
  by apply: hall; rewrite mem_iota add0n.
move=> k; rewrite mem_iota add0n => /andP[_ kL].
apply/eqP; apply: to_nat_inj.
by rewrite -!nth_ti2t // e.
Qed.

(* the ones the search needs, in the form it needs them                       *)
Lemma tabi_ok_comp a b : tabi_ok a -> tabi_ok b -> tabi_ok (comp_tabi a b).
Proof.
by move=> aok bok; rewrite /tabi_ok ti2t_comp //; apply: tab_ok_comp.
Qed.

Lemma eq_tabi_id a : tabi_ok a -> eq_tabi a id_tabi = (ti2t a == id_tab n).
Proof.
move=> aok.
have iok : tabi_ok id_tabi by rewrite /tabi_ok ti2t_id; apply: tab_ok_id.
by rewrite eq_tabiE // ti2t_id.
Qed.

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
(* the same shape as searchtE in Tsearch.v: induction on d, DtiE for the cut,*)
(* eq_tabi_id for the solved test, has_map and ti2t_comp for the recursive    *)
(* call.  This script gets every step but the eq_in_has, which will not       *)
(* apply here although the identical one does in Tsearch.v:                   *)
(*                                                                            *)
(*   elim: d a => [|d IH] a aok.                                              *)
(*     by rewrite /searchi /searcht DtiE // eq_tabi_id //.                    *)
(*   rewrite {1}/searchi -/searchi {1}/searcht -/searcht DtiE //              *)
(*           eq_tabi_id //.                                                   *)
(*   congr (_ && (_ || _)).                                                   *)
(*   rewrite has_map; apply: eq_in_has => mt mtM.                             *)
(*   have mtok : tabi_ok mt by apply: (allP mtis_ok).                         *)
(*   by rewrite -ti2t_comp // IH // tabi_ok_comp.                             *)
(*                                                                            *)
(* Beware /= here: it unfolds ti2t and comp_tab and shreds the goal.          *)
Admitted.

(* and hence, composing with searchtE of Tsearch.v and searchN of Search.v,   *)
(* a false answer from the array search is a membership fact.                 *)
Corollary searchiN d a :
  tabi_ok a -> searchi d a = false ->
  searcht n [seq ti2t mt | mt <- mtis] Dt d (ti2t a) = false.
Proof. by move=> aok; rewrite searchiE. Qed.

End Tabi.
