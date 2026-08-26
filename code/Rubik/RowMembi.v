(* =========================================================================  *)
(*  RowMembi.v -- where a position stands, without leaving int63.             *)
(* =========================================================================  *)

(* WHY.  MEASURED at depth eleven, 86 144 answers: the search alone 2.5 s,    *)
(* the same search turning each answer into ranks 12.0, into a place 12.1,    *)
(* and into a bit in the map 12.3.  So RowMemb's tomemb is 110 of the 113     *)
(* microseconds an answer costs, and recording the answers is three quarters  *)
(* of the whole thirteen level run.                                           *)
(*                                                                            *)
(* WHAT IS IN IT.  `ti2t' writes the forty eight entry table out as a LIST OF *)
(* UNARY NUMBERS, one of_nat an entry -- measured elsewhere here at 1.53      *)
(* microseconds for a value of twenty one, against 0.04 for the array read it *)
(* stands in for -- and the two ranks ask for forty more.                     *)
(*                                                                            *)
(* WHAT IS HERE.  The same three ranks with no nat anywhere: the inverse      *)
(* table stays an array, the three lookup tables are arrays, and the rank is  *)
(* the same mixed radix fold on int63.  `tomembiE' at the bottom is the       *)
(* bridge, and it is PROVED.                                                  *)
(*                                                                            *)
(* The one thing it asks for is that the position is a well formed table,     *)
(* which is what the search carries anyway: without it the inverse table      *)
(* holds nothing in particular and neither side means anything.               *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Lehmer RowTabP RowMemb.

Notation arr := (PArray.array int).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* the int63 Lehmer digit and rank, as RowMembi has them *)
Definition lcodei (nn : nat) (f : int -> int) (i : int) : int :=
  ifold nn 0
    (fun j c =>
       if (Uint63.ltb i j) && (Uint63.ltb (f j) (f i))
       then Uint63.add c 1 else c)
    0.

Definition lrankii (nn : nat) (ni : int) (f : int -> int) : int :=
  ifold nn 0
    (fun i r => Uint63.add (Uint63.mul r (Uint63.sub ni i)) (lcodei nn f i))
    0.

(* ---- 1. ifold is a foldl over iota --------------------------------------- *)

Lemma ifoldEg (A : Type) (n : nat) (x : int) (g : int -> A -> A)
      (h : nat -> A -> A) (a : A) :
  (to_nat x + n < nwB)%N ->
  (forall k b, (to_nat x <= to_nat k)%N -> (to_nat k < to_nat x + n)%N ->
               g k b = h (to_nat k) b) ->
  ifold n x g a = foldl (fun b i => h i b) a (iota (to_nat x) n).
Proof.
elim: n x a => [|m ih] x a hb hg; first by [].
rewrite /= hg //; last by rewrite addnS ltnS leq_addr.
have h1 : (to_nat x + to_nat 1 < nwB)%N.
  by rewrite to_nat_1; apply: leq_ltn_trans hb; rewrite leq_add2l.
have hx1 : to_nat (x + 1) = (to_nat x).+1.
  by rewrite to_nat_add // to_nat_1 addn1.
rewrite -hx1; apply: ih; first by rewrite hx1 addSnnS.
move=> k b hk1 hk2; apply: hg; first by rewrite hx1 in hk1; apply: ltnW.
by rewrite hx1 addSnnS in hk2.
Qed.

Lemma ifoldE (A : Type) (n : nat) (g : int -> A -> A) (h : nat -> A -> A)
      (a : A) :
  (n < nwB)%N ->
  (forall k b, (to_nat k < n)%N -> g k b = h (to_nat k) b) ->
  ifold n 0 g a = foldl (fun b i => h i b) a (iota 0 n).
Proof.
move=> hb hg; apply: (ifoldEg (x := 0)); first by [].
by move=> k b _; apply: hg.
Qed.

(* ---- 2. the comparison, read on the nat side ----------------------------- *)

Lemma nltbE (x y : int) : (x <? y) = (to_nat x < to_nat y)%N.
Proof. by apply/idP/idP => /nltbP. Qed.

(* ---- 3. a fold that adds one is a count ---------------------------------- *)

Lemma foldl_count (p : nat -> bool) (s : seq nat) (a : int) :
  (to_nat a + seq.size s < nwB)%N ->
  to_nat (foldl (fun c j => if p j then Uint63.add c 1 else c) a s)
  = (to_nat a + count p s)%N.
Proof.
elim: s a => [|j s ih] a hb /=; first by rewrite addn0.
have hs : (to_nat a + seq.size s < nwB)%N.
  by apply: leq_ltn_trans hb; rewrite leq_add2l; apply: leqnSn.
case: (p j) => /=; last by rewrite (ih _ hs).
have h1 : (to_nat a + to_nat 1 < nwB)%N.
  by rewrite to_nat_1; apply: leq_ltn_trans hb; rewrite leq_add2l.
have ha : to_nat (a + 1) = (to_nat a).+1 by rewrite to_nat_add // to_nat_1 addn1.
have hb1 : (to_nat (a + 1) + seq.size s < nwB)%N by rewrite ha addSn -addnS.
by rewrite (ih _ hb1) ha addSn addnS.
Qed.

(* ---- 4. the digit, walked over all the places ---------------------------- *)

Lemma count_lcode (nn : nat) (f : nat -> nat) (i0 : nat) :
  (i0 < nn)%N ->
  count (fun j => (i0 < j)%N && (f j < f i0)%N) (iota 0 nn) = lcode nn f i0.
Proof.
move=> hi; rewrite /lcode -{1}(subnKC hi) iotaD add0n count_cat.
have -> : count (fun j => (i0 < j)%N && (f j < f i0)%N) (iota 0 i0.+1) = 0%N.
  apply/eqP; rewrite -leqn0 leqNgt -has_count.
  apply/hasPn => j; rewrite mem_iota add0n ltnS => /andP[_ hj].
  by rewrite negb_and ltnNge hj.
rewrite add0n; apply: eq_in_count => j.
by rewrite mem_iota => /andP[hj _]; rewrite hj.
Qed.

Lemma lcodeiE (nn : nat) (g : int -> int) (f : nat -> nat) (i : int) :
  (nn < nwB)%N ->
  (forall p, (to_nat p < nn)%N -> to_nat (g p) = f (to_nat p)) ->
  (to_nat i < nn)%N ->
  to_nat (lcodei nn g i) = lcode nn f (to_nat i).
Proof.
move=> hn hgf hi; rewrite /lcodei.
have h0 : to_nat 0 = 0%N by [].
have -> : ifold nn 0
            (fun j c => if (i <? j) && (g j <? g i) then Uint63.add c 1 else c)
            0
        = foldl (fun c j => if (to_nat i < j)%N && (f j < f (to_nat i))%N
                            then Uint63.add c 1 else c) 0 (iota 0 nn).
  apply: ifoldE; first by exact: hn.
  move=> k c hk.
  have e1 : (i <? k) = (to_nat i < to_nat k)%N by exact: nltbE.
  have e2 : (g k <? g i) = (f (to_nat k) < f (to_nat i))%N.
    by rewrite nltbE -(hgf k hk) -(hgf i hi).
  by rewrite e1 e2.
have hsz : (to_nat 0 + seq.size (iota 0 nn) < nwB)%N.
  by rewrite h0 add0n seq.size_iota; exact: hn.
by rewrite (foldl_count
              (fun j => (to_nat i < j)%N && (f j < f (to_nat i))%N) hsz)
            h0 add0n (count_lcode f hi).
Qed.

(* ---- 5. the rank -------------------------------------------------------- *)

Lemma lrankiiE (nn : nat) (g : int -> int) (f : nat -> nat) :
  (nn < nwB)%N ->
  (forall p, (to_nat p < nn)%N -> to_nat (g p) = f (to_nat p)) ->
  lrankii nn (of_nat nn) g = lranki nn f.
Proof.
move=> hn hgf; rewrite /lrankii /lranki.
apply: ifoldE; first by exact: hn.
move=> k r hk.
have hnn : to_nat (of_nat nn) = nn by exact: (of_natK _ hn).
have h1 : (to_nat k <= to_nat (of_nat nn))%N by rewrite hnn; apply: ltnW.
have h2 : (to_nat (of_nat nn) < nwB)%N by rewrite hnn; exact: hn.
have h3 : (nn - to_nat k < nwB)%N.
  by apply: leq_ltn_trans hn; apply: leq_subr.
have hsub : Uint63.sub (of_nat nn) k = of_nat (nn - to_nat k)%N.
  by apply: to_nat_inj; rewrite (to_nat_sub (of_nat nn) k h1 h2) hnn (of_natK _ h3).
have hc : lcodei nn g k = of_nat (lcode nn f (to_nat k)).
  by rewrite -(lcodeiE hn hgf hk) to_natK.
by rewrite hsub hc.
Qed.

(* ---- and the int63 side -------------------------------------------------- *)

Definition nfacei : int := 48.
Definition ncorni : int := 8.
Definition nmidi  : int := 4.

Definition cposia : arr :=
  Eval vm_compute in mkarrn nfacei [seq of_nat v | v <- cposv].
Definition eposia : arr :=
  Eval vm_compute in mkarrn nfacei [seq of_nat v | v <- eposv].
(* THE EIGHT IS TAKEN OFF IN THE TABLE.  On the nat side the middle place is  *)
(* the edge place less eight, and a nat subtraction stops at nought where an  *)
(* int63 one would wrap.  Stored already taken off, the two agree whatever    *)
(* the facelet, and a subtraction goes from the inner loop.                   *)
Definition emidia : arr :=
  Eval vm_compute in mkarrn nfacei [seq of_nat (v - 8)%N | v <- eposv].
Definition cprimia : arr :=
  Eval vm_compute in mkarrn ncorni [seq of_nat v | v <- cprimp].

Definition rank8i (f : int -> int) : int := lrankii 8 ncorni f.
Definition rank4i (f : int -> int) : int := lrankii 4 nmidi f.

Definition tomembi (a : arr) : memb :=
  let v := inv_tabi flast a in
  (rank8i (fun p => PArray.get cposia (PArray.get v (PArray.get cprimia p))),
   rank8i (fun p => PArray.get eposia (PArray.get v (PArray.get eprimi p))),
   rank4i (fun p => PArray.get emidia
                      (PArray.get v
                         (PArray.get eprimi (Uint63.add ncorni p))))).

(* ---- the tables are the lists, checked ----------------------------------- *)

Lemma n48_lt : (48 < nwB)%N.
Proof. by apply: (@ltn_nwB 6). Qed.

Lemma h0 : to_nat 0 = 0%N.
Proof. by []. Qed.

Definition cposiaok : bool :=
  alli 48 0 (fun i => to_nat (PArray.get cposia i) == cposn (to_nat i)).
Lemma cposiaokE : cposiaok. Proof. by vm_compute. Qed.

Definition eposiaok : bool :=
  alli 48 0 (fun i => to_nat (PArray.get eposia i) == eposn (to_nat i)).
Lemma eposiaokE : eposiaok. Proof. by vm_compute. Qed.

Definition emidiaok : bool :=
  alli 48 0 (fun i => to_nat (PArray.get emidia i) == (eposn (to_nat i) - 8)%N).
Lemma emidiaokE : emidiaok. Proof. by vm_compute. Qed.

Definition cprimiaok : bool :=
  alli 8 0 (fun p => to_nat (PArray.get cprimia p) == nth 0%N cprimp (to_nat p)).
Lemma cprimiaokE : cprimiaok. Proof. by vm_compute. Qed.

Definition eprimiaok : bool :=
  alli 12 0 (fun p => to_nat (PArray.get eprimi p) == nth 0%N eprim (to_nat p)).
Lemma eprimiaokE : eprimiaok. Proof. by vm_compute. Qed.

Lemma alli48 (f : int -> bool) : alli 48 0 f -> forall i, (to_nat i < 48)%N -> f i.
Proof.
have hw : (to_nat 0 + 48 < nwB)%N by rewrite h0 add0n; exact: n48_lt.
rewrite (alliE f hw) h0 => /allP hall i hi.
by rewrite -[i]to_natK; apply: hall; rewrite mem_iota add0n hi.
Qed.

Lemma alli8 (f : int -> bool) : alli 8 0 f -> forall i, (to_nat i < 8)%N -> f i.
Proof.
have hw : (to_nat 0 + 8 < nwB)%N.
  by rewrite h0 add0n; apply: ltn_trans n48_lt.
rewrite (alliE f hw) h0 => /allP hall i hi.
by rewrite -[i]to_natK; apply: hall; rewrite mem_iota add0n hi.
Qed.

Lemma alli12 (f : int -> bool) : alli 12 0 f -> forall i, (to_nat i < 12)%N -> f i.
Proof.
have hw : (to_nat 0 + 12 < nwB)%N.
  by rewrite h0 add0n; apply: ltn_trans n48_lt.
rewrite (alliE f hw) h0 => /allP hall i hi.
by rewrite -[i]to_natK; apply: hall; rewrite mem_iota add0n hi.
Qed.

(* ---- each table read, on the nat side ------------------------------------ *)

Lemma cposiaE i : (to_nat i < 48)%N ->
  to_nat (PArray.get cposia i) = cposn (to_nat i).
Proof.
by move=> hi; apply/eqP; move: cposiaokE; rewrite /cposiaok => h; exact: (@alli48 _ h i hi).
Qed.

Lemma eposiaE i : (to_nat i < 48)%N ->
  to_nat (PArray.get eposia i) = eposn (to_nat i).
Proof.
by move=> hi; apply/eqP; move: eposiaokE; rewrite /eposiaok => h; exact: (@alli48 _ h i hi).
Qed.

Lemma emidiaE i : (to_nat i < 48)%N ->
  to_nat (PArray.get emidia i) = (eposn (to_nat i) - 8)%N.
Proof.
by move=> hi; apply/eqP; move: emidiaokE; rewrite /emidiaok => h; exact: (@alli48 _ h i hi).
Qed.

Lemma cprimiaE p : (to_nat p < 8)%N ->
  PArray.get cprimia p = of_nat (nth 0%N cprimp (to_nat p)).
Proof.
move=> hp; move: cprimiaokE; rewrite /cprimiaok => hok.
have /eqP h := @alli8 _ hok p hp.
by rewrite -[LHS]to_natK h.
Qed.

Lemma eprimiE p : (to_nat p < 12)%N ->
  PArray.get eprimi p = of_nat (nth 0%N eprim (to_nat p)).
Proof.
move=> hp; move: eprimiaokE; rewrite /eprimiaok => hok.
have /eqP h := @alli12 _ hok p hp.
by rewrite -[LHS]to_natK h.
Qed.

(* ---- the two lists hold facelets ----------------------------------------- *)

Lemma cprimp_lt p : (p < 8)%N -> (nth 0%N cprimp p < 48)%N.
Proof.
move=> hp.
have hall : all (fun v => (v < 48)%N) cprimp by vm_compute.
have hsz : seq.size cprimp = 8%N by vm_compute.
by apply: (allP hall); rewrite mem_nth // hsz.
Qed.

Lemma eprim_lt p : (p < 12)%N -> (nth 0%N eprim p < 48)%N.
Proof.
move=> hp.
have hall : all (fun v => (v < 48)%N) eprim by vm_compute.
have hsz : seq.size eprim = 12%N by vm_compute.
by apply: (allP hall); rewrite mem_nth // hsz.
Qed.

(* ---- reading the inverse table ------------------------------------------- *)

Lemma invok a : tabi_ok flast a -> tabi_ok flast (inv_tabi flast a).
Proof.
by move=> aok; rewrite /tabi_ok (ti2t_inv n47_small n47_len aok); apply: tab_ok_inv.
Qed.

Lemma ugetE a j : tabi_ok flast a -> (j < 48)%N ->
  PArray.get (inv_tabi flast a) (of_nat j)
  = of_nat (nth 0%N (ti2t flast (inv_tabi flast a)) j).
Proof. by move=> aok hj; rewrite (@nth_ti2t flast) ?to_natK //. Qed.

Lemma ugetlt a j : tabi_ok flast a -> (j < 48)%N ->
  (nth 0%N (ti2t flast (inv_tabi flast a)) j < 48)%N.
Proof.
move=> aok hj; rewrite (@nth_ti2t flast) //.
by apply: (tabi_lt (invok aok)).
Qed.

Lemma readE (T : arr) (tf : nat -> nat) (a : arr) (j : nat) :
  (forall i, (to_nat i < 48)%N -> to_nat (PArray.get T i) = tf (to_nat i)) ->
  tabi_ok flast a -> (j < 48)%N ->
  to_nat (PArray.get T (PArray.get (inv_tabi flast a) (of_nat j)))
  = tf (nth 0%N (ti2t flast (inv_tabi flast a)) j).
Proof.
move=> hT aok hj.
have hm : (nth 0%N (ti2t flast (inv_tabi flast a)) j < 48)%N by exact: ugetlt.
have hmw : (nth 0%N (ti2t flast (inv_tabi flast a)) j < nwB)%N.
  by apply: (ltn_trans hm n48_lt).
rewrite (ugetE aok hj).
have hlt : (to_nat (of_nat (nth 0%N (ti2t flast (inv_tabi flast a)) j)) < 48)%N.
  by rewrite (of_natK _ hmw).
by rewrite (hT _ hlt) (of_natK _ hmw).
Qed.

(* ---- the three places ---------------------------------------------------- *)

Lemma n8_lt : (8 < nwB)%N. Proof. by apply: (ltn_trans _ n48_lt). Qed.
Lemma n4_lt : (4 < nwB)%N. Proof. by apply: (ltn_trans _ n48_lt). Qed.
Lemma ncorniE : of_nat 8 = ncorni. Proof. by vm_compute. Qed.
Lemma nmidiE : of_nat 4 = nmidi. Proof. by vm_compute. Qed.
Lemma to_nat_ncorni : to_nat ncorni = 8%N. Proof. by vm_compute. Qed.

Lemma tomembiE a : tabi_ok flast a -> tomembi a = tomemb a.
Proof.
move=> aok; rewrite /tomembi /tomemb /rank8i /rank4i /rank8 /rank4.
congr (_, _, _).
- rewrite -ncorniE; apply: (lrankiiE n8_lt) => p hp.
  rewrite (cprimiaE hp).
  by apply: (readE cposiaE aok (cprimp_lt hp)).
- rewrite -ncorniE; apply: (lrankiiE n8_lt) => p hp.
  have hp12 : (to_nat p < 12)%N by apply: (ltn_trans hp).
  rewrite (eprimiE hp12).
  by apply: (readE eposiaE aok (eprim_lt hp12)).
rewrite -nmidiE; apply: (lrankiiE n4_lt) => p hp.
have hj12 : (8 + to_nat p < 12)%N by rewrite ltn_add2l.
have hnw : (12 < nwB)%N by apply: (ltn_trans _ n48_lt).
have hpw : (to_nat ncorni + to_nat p < nwB)%N.
  by rewrite to_nat_ncorni; apply: (ltn_trans hj12 hnw).
have hadd : to_nat (Uint63.add ncorni p) = (8 + to_nat p)%N.
  by rewrite (to_nat_add ncorni p hpw) to_nat_ncorni.
have h12 : (to_nat (Uint63.add ncorni p) < 12)%N by rewrite hadd.
rewrite (eprimiE h12) hadd.
by apply: (readE (tf := fun m => (eposn m - 8)%N) emidiaE aok (eprim_lt hj12)).
Qed.
