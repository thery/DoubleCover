(* =========================================================================  *)
(*  Cyc.v                                                                     *)
(*                                                                            *)
(*  Cyclic permutations of a finite type, presented by a list of the points   *)
(*  they cycle.  `cyc [:: a0; a1; ...; ak]` is the permutation                *)
(*     a0 -> a1 -> ... -> ak -> a0,  fixing everything else.                  *)
(*  It is built as a product of transpositions, so it carries no injectivity  *)
(*  proof obligation.  The three lemmas characterise it fully on a `uniq`     *)
(*  list -- purely by rewriting, never by evaluating a permutation.           *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma in_rcons (T : eqType) y s (x : T) :
  (x \in rcons s y) = (x == y) || (x \in s).
Proof. by elim: s => //= z s IH;  rewrite !inE IH orbCA. Qed.

Section Cyc.

Variable A : finType.

Definition cyc (s : seq A) : {perm A} :=
  if s is a0 :: rest then \prod_(a <- rest) tperm a0 a else 1%g.

Lemma cyc1 a : cyc [:: a] = 1.
Proof. by rewrite [LHS]big_nil. Qed.

Lemma cyc_notin a l : a \notin l -> cyc l a = a.
Proof.
case: l => [|b] /=; first by rewrite permE.
elim => [|c l IH aL]; rewrite !(big_cons, big_nil, mulg1, permE) //=.
rewrite tpermD ?IH //; move: aL; rewrite !inE !negb_or.
- by case/and3P => ->.
- by case/and3P => ? _ _; rewrite eq_sym.
by case/and3P => _ ? _; rewrite eq_sym.
Qed.

Lemma cyc_succ a b l1 l2 :
  uniq (l1 ++ a :: b :: l2) -> cyc (l1 ++ a :: b :: l2) a = b.
Proof.
case: l1 => [|c l1].
  rewrite cat0s /cyc !(big_cons, big_nil, mulg1, permE) /= tpermL.
  rewrite !inE !negb_or => /and3P[/andP[? ?] ? ?].
  by rewrite [LHS](@cyc_notin b (a :: l2)) // !inE !negb_or; apply/andP;
     split; rewrite 1?eq_sym.
elim: l1 => [|d l1 IH] /=.
  rewrite !inE !negb_or => /and3P[/and3P[? ? ?] /andP[? ?] /andP[? ?]].
  rewrite !(big_cons, big_nil, mulg1, permE) /= tpermR permE /= tpermL //.
  rewrite [LHS](@cyc_notin b (c :: l2)) //.
  by rewrite inE negb_or; apply/andP; rewrite 1?eq_sym.
rewrite !inE !negb_or => /and3P[/andP[H1 H2] H3 H4].
rewrite big_cons !permE /= tpermD ?IH //=.
- by apply/andP; split.
- by rewrite mem_cat negb_or inE negb_or in H2; case/and3P: H2.
by rewrite mem_cat negb_or inE negb_or in H3; case/and3P: H3.
Qed.

Lemma cyc_tail a b l :
  uniq (a :: rcons l b) -> cyc (a :: rcons l b) b = a.
Proof.
rewrite /=.
elim: l => [|c l IH] /=; rewrite !(big_cons, big_nil, mulg1, permE) /=.
  by rewrite tpermR permE.
rewrite !inE !in_rcons !negb_or => /and3P[/andP[? /andP[? ?]] /andP[? ?] ?].
rewrite permE /= ifN; last by rewrite eq_sym.
rewrite ifN ?IH ?in_rcons ?negb_or //; last by rewrite eq_sym.
by rewrite -andbA; apply/and3P; split.
Qed.

Lemma cyc_nth a i l :
  uniq l -> i < size l -> cyc l (nth a l i) = nth a l (i.+1 %% (size l)).
Proof.
move=> Hu iLl.
move: iLl; case: (ltngtP i.+1) => // [i1Ll|iEl] _; last first.
  rewrite iEl modnn.
  case/lastP : l Hu iEl => // l b Hu.
  rewrite size_rcons => [] [->].
  rewrite nth_rcons ltnn eqxx.
  case: l Hu => [|c l Hu]; first by rewrite [rcons _ _]/= cyc1 permE.
  by rewrite [RHS]/= cyc_tail.
rewrite modn_small //.
suff lE : l = take i l ++ (nth a l i) :: nth a l i.+1 :: drop i.+2 l.
  by rewrite [X in cyc X]lE cyc_succ // -lE.
rewrite -{1 3 4}(@cat_take_drop  i _ l); congr (_ ++ _).
rewrite nth_cat size_take.
have iLl : i < size l by apply: leq_ltn_trans i1Ll.
rewrite iLl ltnn subnn nth_cat size_take iLl ifN; last by rewrite -leqNgt.
have -> : i.+1 - i = 1%N by rewrite subSn // subnn.
rewrite [in LHS](drop_nth a) // [in LHS](drop_nth a) //.
by rewrite nth_drop addn0 nth_drop addn1.
Qed.

Lemma cyc_pow_nth n a i l :
  uniq l -> i < size l -> 
  ((cyc l) ^+ n) (nth a l i) = nth a l ((n + i) %% (size l)).
Proof.
move=> lU iLs.
elim: n => // [|n IH]; first by rewrite permE modn_small.
rewrite expgSr permE /= IH cyc_nth //; last first.
  by rewrite ltn_mod (leq_ltn_trans _ iLs).
by rewrite -addn1 modnDml addnAC addn1.
Qed.

End Cyc.

(* -------------------------------------------------------------------------  *)
(*  Order and commutation of cycles.                                          *)
(*                                                                            *)
(*  These let us reason about a face turn, which is a product of disjoint     *)
(*  4-cycles, without ever evaluating a permutation: an n-cycle has order n,  *)
(*  disjoint cycles commute, and a product of same-length disjoint cycles is  *)
(*  killed by that length.                                                    *)
(* -------------------------------------------------------------------------  *)

(* A cycle only moves the points it lists, so its support lies in that set.   *)
Lemma cyc_on (A : finType) (l : seq A) : perm_on [set x in l] (cyc l).
Proof.
apply/subsetP => x; rewrite !inE.
by move=> H; apply: contraTT H => xnl; rewrite cyc_notin // eqxx.
Qed.

(* Cycles on disjoint sets of points commute.                                 *)
Lemma cyc_comm (A : finType) (l1 l2 : seq A) :
  [disjoint [set x in l1] & [set x in l2]] -> commute (cyc l1) (cyc l2).
Proof. by move=> d; apply: perm_onC d; exact: cyc_on. Qed.

(* Disjointness of the point-sets is disjointness of the underlying lists.    *)
Lemma disjoint_set_seq (A : finType) (s1 s2 : seq A) :
  [disjoint [set x in s1] & [set x in s2]] = ~~ has (mem s1) s2.
Proof.
apply/idP/idP => [d|h].
  apply/hasPn => y ys.
  by move: d => /pred0P/(_ y); rewrite !inE ys andbT => ->.
apply/pred0P => y; rewrite !inE.
apply/negbTE; rewrite negb_and orbC -implybE; apply/implyP => ys2.
by move/hasPn: h => /(_ y ys2).
Qed.

(* Two commuting elements, each of exponent n, have a product of exponent n.  *)
Lemma expgMn1 (gT : finGroupType) (s t : gT) n :
  commute s t -> s ^+ n = 1 -> t ^+ n = 1 -> (s * t) ^+ n = 1.
Proof. by move=> c s1 t1; rewrite expgMn // s1 t1 mulg1. Qed.

(* An element commutes with a product once it commutes with each factor.      *)
Lemma commute_prod (gT : finGroupType) (I : eqType) (r : seq I)
    (f : I -> gT) x :
  (forall i, i \in r -> commute x (f i)) -> commute x (\prod_(i <- r) f i).
Proof.
elim: r => [|i r IH] H; first by rewrite big_nil /commute mulg1 mul1g.
rewrite big_cons; apply: commuteM; first by apply: H; rewrite inE eqxx.
by apply: IH => j jr; apply: H; rewrite inE jr orbT.
Qed.

Lemma compE (A B C : Type) (f : A -> B) (g : B -> C) x : (g \o f) x = g (f x).
Proof. by []. Qed.

(* An n-cycle has order n.                                                    *)
Lemma cyc_order (A : finType) (l : seq A) : uniq l -> cyc l ^+ size l = 1.
Proof.
case: l => // a l uL.
apply/permP => x; rewrite permE.
have [xIl|xNIl] := boolP (x \in a :: l); last first.
  elim: size => [|m IH]; first by rewrite expg0 permE.
  by rewrite expgSr permE compE IH cyc_notin.
rewrite -(nth_index a xIl) cyc_pow_nth ?index_mem //.
by rewrite -modnDml modnn modn_small // index_mem.
Qed.

(* A product of pairwise-disjoint cycles, all of length n, has n-th power the *)
(* identity: the factors commute and each is killed by the n-th power.  The   *)
(* disjointness hypothesis is packaged as uniqueness of the concatenation.    *)
Lemma cyc_prod_expn (A : finType) (ll : seq (seq A)) (n : nat) :
  uniq (flatten ll) -> (forall l, l \in ll -> size l = n) ->
  (\prod_(l <- ll) cyc l) ^+ n = 1.
Proof.
elim: ll => [|l0 ll IH] Uf Sz; first by rewrite big_nil expg1n.
move: (Uf) => /=; rewrite cat_uniq => /and3P[Ul0 nh Uf'].
rewrite big_cons; apply: expgMn1.
- apply: commute_prod => l lin; apply: cyc_comm.
  rewrite disjoint_set_seq; apply/hasPn => y yl.
  by move/hasPn: nh; apply; apply/flattenP; exists l.
- by rewrite -(Sz l0 (mem_head l0 ll)) (@cyc_order _ l0 Ul0).
- by apply: IH => // l lin; apply: Sz; rewrite inE lin orbT.
Qed.
