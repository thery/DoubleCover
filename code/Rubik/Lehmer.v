(* =========================================================================  *)
(*  Lehmer.v -- ranking a permutation of places, and its sign.                *)
(* =========================================================================  *)

(* NOTHING HERE IS ABOUT THE CUBE.  A permutation of the places 0 to n - 1 is *)
(* a function on nat that is one to one on them, and this file is the two     *)
(* things one wants of such a thing.                                          *)
(*                                                                            *)
(* ITS RANK.  At each place count how many LATER places hold something        *)
(* smaller -- the Lehmer digits, lcode -- and read them as a mixed radix      *)
(* number, digit i below n - i - 1.  lrank is that number, it is below n      *)
(* factorial, and it names the permutation and no other.                      *)
(*                                                                            *)
(* ITS SIGN.  The same digits added up rather than packed are the number of   *)
(* inversions, and the parity of that is the sign.  prmn is that parity.      *)
(*                                                                            *)
(* BOTH ARE ON nat AND BOTH COMPUTE, which is the reason this file exists at  *)
(* all.  mathcomp's sign is odd_perm, counting orbits of a permutation of a   *)
(* finite type, and a permutation of ordinals does not reduce -- so a table   *)
(* walk cannot ask for it.  What is owed in exchange is the bridge between    *)
(* the two, which is prmn_swap and prmn_mul below.                            *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition lrank (n : nat) (f : nat -> nat) : nat :=
  foldl (fun r i =>
           (r * (n - i)
            + count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1)))%N)
        0%N (iota 0 n).

Lemma foldl_eq_in (T : eqType) (R : Type) (F G : R -> T -> R)
  (s : seq T) (r : R) :
  (forall x r', x \in s -> F r' x = G r' x) -> foldl F r s = foldl G r s.
Proof.
elim: s r => [|x s ih] r hFG //=.
rewrite hFG ?mem_head //; apply: ih => y r' hy.
by apply: hFG; rewrite in_cons hy orbT.
Qed.

Lemma fold_mixed n (g : nat -> nat) :
  (forall i, (g i <= n - i.+1)%N) ->
  forall m k r, (k + m = n)%N ->
    (foldl (fun a i => (a * (n - i) + g i)%N) r (iota k m) < (r + 1) * m`!)%N.
Proof.
move=> hg; elim=> [|m ih] k r hkm /=; first by rewrite fact0 muln1 addn1.
have hnk : (n - k = m.+1)%N by rewrite -hkm addKn.
have hnk1 : (n - k.+1 = m)%N by rewrite -hkm -addSnnS addKn.
have hgk : (g k <= m)%N by rewrite -hnk1; apply: hg.
apply: leq_trans (ih k.+1 _ _) _; first by rewrite addSnnS.
have hf : (0 < m`!)%N by apply: fact_gt0.
rewrite factS mulnA leq_pmul2r //.
by rewrite hnk mulnDl mul1n -addnA leq_add2l addn1 ltnS.
Qed.

Lemma fold_mixed_ge n (g : nat -> nat) :
  forall m k r, (k + m = n)%N ->
    (r * m`! <= foldl (fun a i => (a * (n - i) + g i)%N) r (iota k m))%N.
Proof.
elim=> [|m ih] k r hkm /=; first by rewrite fact0 muln1.
have hnk : (n - k = m.+1)%N by rewrite -hkm addKn.
apply: leq_trans (ih k.+1 _ _) => //; last by rewrite addSnnS.
by rewrite factS mulnA leq_pmul2r ?fact_gt0 // hnk leq_addr.
Qed.

Lemma fold_mixed_div n (g : nat -> nat) m k r :
  (forall i, (g i <= n - i.+1)%N) -> (k + m = n)%N ->
  (foldl (fun a i => (a * (n - i) + g i)%N) r (iota k m)) %/ m`! = r.
Proof.
move=> hg hkm.
have hf : (0 < m`!)%N by apply: fact_gt0.
have hlo := @fold_mixed_ge n g m k r hkm.
have hhi := @fold_mixed n g hg m k r hkm.
rewrite -{1}(subnKC hlo) divnMDl // divn_small ?addn0 //.
rewrite ltn_subLR //.
by apply: leq_trans hhi _; rewrite mulnDl mul1n addnC.
Qed.

Lemma lrank_lt n f : (lrank n f < n`!)%N.
Proof.
have hg i : (count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1))
             <= n - i.+1)%N.
  by rewrite -{2}(size_iota i.+1 (n - i.+1)); apply: count_size.
by move: (fold_mixed hg 0%N (add0n n)); rewrite add0n mul1n /lrank.
Qed.

Lemma lrank_eq n (f g : nat -> nat) :
  (forall p, (p < n)%N -> f p = g p) -> lrank n f = lrank n g.
Proof.
move=> hfg; rewrite /lrank; apply: foldl_eq_in => i r.
rewrite mem_iota add0n => /andP[_ hi]; congr (_ + _)%N.
apply: eq_in_count => j; rewrite mem_iota => /andP[hj1 hj2].
by rewrite !hfg // (leq_trans hj2) // subnKC.
Qed.

(* ---- two facts about a permutation of the places ------------------------- *)

(* it stays inside them                                                       *)
Lemma perm_range n q : perm_eq [seq q p | p <- iota 0 n] (iota 0 n) ->
  forall p, (p < n)%N -> (q p < n)%N.
Proof.
move=> hp p hpn.
have : q p \in [seq q j | j <- iota 0 n].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hp) mem_iota add0n.
Qed.

(* and it is one to one on them                                               *)
Lemma perm_inj n q : perm_eq [seq q p | p <- iota 0 n] (iota 0 n) ->
  forall a b, (a < n)%N -> (b < n)%N -> q a = q b -> a = b.
Proof.
move=> hp a b ha hb hq.
have hu : uniq [seq q p | p <- iota 0 n] by rewrite (perm_uniq hp) iota_uniq.
have hs : size [seq q p | p <- iota 0 n] = n by rewrite size_map size_iota.
have hn c : (c < n)%N -> nth 0%N [seq q p | p <- iota 0 n] c = q c.
  by move=> hc; rewrite (nth_map 0%N) ?size_iota // nth_iota // add0n.
by apply/eqP; rewrite -(nth_uniq 0%N _ _ hu) ?hs // !hn // hq.
Qed.

(* and a composition of two of them is one                                    *)
Lemma perm_comp n (q1 q2 : nat -> nat) :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q1 (q2 p) | p <- iota 0 n] (iota 0 n).
Proof.
move=> h1 h2; rewrite (@eq_map _ _ _ (q1 \o q2)) // map_comp.
by apply: perm_trans h1; apply: perm_map.
Qed.

(* and a one to one map of the places onto themselves is one                  *)
Lemma perm_of_rng n (f : nat -> nat) :
  uniq [seq f p | p <- iota 0 n] ->
  (forall p, (p < n)%N -> (f p < n)%N) ->
  perm_eq [seq f p | p <- iota 0 n] (iota 0 n).
Proof.
move=> hu hr; apply: uniq_perm => //; first exact: iota_uniq.
have hsub : {subset [seq f p | p <- iota 0 n] <= iota 0 n}.
  move=> x /mapP[p]; rewrite mem_iota add0n => /andP[_ hp] ->.
  by rewrite mem_iota add0n hr.
have hs : size [seq f p | p <- iota 0 n] = n by rewrite size_map size_iota.
have hle : (size (iota 0 n) <= size [seq f p | p <- iota 0 n])%N.
  by rewrite hs size_iota.
by have [_ h] := uniq_min_size hu hsub hle; move=> x; rewrite h.
Qed.

(* and the values still to come at a place are all different                  *)
Lemma perm_tail_uniq n q : perm_eq [seq q p | p <- iota 0 n] (iota 0 n) ->
  forall p, (p <= n)%N -> uniq [seq q j | j <- iota p (n - p)].
Proof.
move=> hq p hp.
have hu : uniq [seq q j | j <- iota 0 n] by rewrite (perm_uniq hq) iota_uniq.
by move: hu; rewrite -{1}(subnKC hp) iotaD add0n map_cat cat_uniq => /and3P[].
Qed.

Definition lcode (n : nat) (q : nat -> nat) (i : nat) : nat :=
  count (fun j => (q j < q i)%N) (iota i.+1 (n - i.+1)).

(* a digit is below its radix                                                 *)
Lemma lcode_bd n q i : (lcode n q i <= n - i.+1)%N.
Proof.
by rewrite /lcode -{2}(size_iota i.+1 (n - i.+1)); apply: count_size.
Qed.

(* PEEL ONE DIGIT AND REPEAT.  fold_mixed_div reads the fold's starting value *)
(* back, so from two equal folds the two starts are equal; that value is      *)
(* r * (n - k) + the digit at k, and since the digit is below n - k a         *)
(* division and a remainder separate the two.  Then the tails are equal folds *)
(* again and the induction carries on.                                        *)
Lemma lrank_code_gen n q1 q2 m k r1 r2 : (k + m = n)%N ->
  foldl (fun a i => (a * (n - i) + lcode n q1 i)%N) r1 (iota k m)
  = foldl (fun a i => (a * (n - i) + lcode n q2 i)%N) r2 (iota k m) ->
  r1 = r2 /\ forall i, (k <= i)%N -> (i < n)%N ->
    lcode n q1 i = lcode n q2 i.
Proof.
elim: m k r1 r2 => [|m ih] k r1 r2 /= hkm.
  move=> ->; split=> // i hi hin.
  by move: hkm; rewrite addn0 => hk; rewrite -hk ltnNge hi in hin.
have hnk : (n - k = m.+1)%N by rewrite -hkm addKn.
have hnk1 : (n - k.+1 = m)%N by rewrite -hkm -addSnnS addKn.
have hd1 : (lcode n q1 k < n - k)%N by rewrite hnk -hnk1; apply: lcode_bd.
have hd2 : (lcode n q2 k < n - k)%N by rewrite hnk -hnk1; apply: lcode_bd.
have hc : (0 < n - k)%N by rewrite hnk.
move=> he.
have [heq htl] := ih k.+1 _ _ (etrans (addSnnS k m) hkm) he.
have hk12 : lcode n q1 k = lcode n q2 k.
  by move: (congr1 (fun x => x %% (n - k))%N heq); rewrite !modnMDl !modn_small.
have hr : r1 = r2.
  move: (congr1 (fun x => x %/ (n - k))%N heq).
  by rewrite !divnMDl // !divn_small // !addn0.
split=> // i hi hin.
move: hi; rewrite leq_eqVlt => /orP[/eqP<-|hi]; first by [].
by apply: htl.
Qed.

Lemma lrank_code n (q1 q2 : nat -> nat) :
  lrank n q1 = lrank n q2 ->
  forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i.
Proof.
move=> h i hi.
by have [_ hd] := @lrank_code_gen n q1 q2 n 0%N 0%N 0%N (add0n n) h; apply: hd.
Qed.

(* THE DIGIT COUNTS VALUES, not places: how many of the values still to come  *)
(* are below the one taken here.                                              *)
Lemma lcodeE n q p : lcode n q p
  = count (fun v => (v < q p)%N) [seq q j | j <- iota p.+1 (n - p.+1)].
Proof. by rewrite /lcode count_map. Qed.

(* one member of a set of naturals has a given number of members below it     *)
(* raising the bar past a member of the list counts one more                  *)
Lemma count_lt_strict (s : seq nat) v w : (v < w)%N -> v \in s ->
  (count (fun x => (x < v)%N) s < count (fun x => (x < w)%N) s)%N.
Proof.
move=> hvw; elim: s => [|x t ih] //=; rewrite inE => /orP[/eqP hx|hv].
  rewrite -hx ltnn hvw /= add0n add1n ltnS.
  by apply: sub_count => y h; apply: (ltn_trans h hvw).
apply: (@leq_ltn_trans ((x < w)%N + count (fun x0 => (x0 < v)%N) t)).
  by rewrite leq_add2r; case: (ltnP x v) => h; rewrite ?(ltn_trans h hvw).
by rewrite ltn_add2l; apply: ih.
Qed.

Lemma count_below_inj (s : seq nat) (v w : nat) :
  uniq s -> v \in s -> w \in s ->
  count (fun x => (x < v)%N) s = count (fun x => (x < w)%N) s -> v = w.
Proof.
move=> hu hv hw h; case: (ltngtP v w) => // hlt.
  by move: (count_lt_strict hlt hv); rewrite h ltnn.
by move: (count_lt_strict hlt hw); rewrite h ltnn.
Qed.

(* THE CODE DETERMINES THE PERMUTATION, and the induction is on the place.    *)
(* Which values are still to come at place p is settled by the places before  *)
(* p; the digit then says how many of them are below the one taken at p,      *)
(* which picks it out of them, because a set of naturals has one member with  *)
(* a given number of members below it.                                        *)
Lemma code_tails n q1 q2 :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  (forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i) ->
  forall p, (p <= n)%N ->
    perm_eq [seq q1 j | j <- iota p (n - p)] [seq q2 j | j <- iota p (n - p)].
Proof.
move=> h1 h2 hcode.
elim=> [|p ih] hp.
  by rewrite subn0; apply: perm_trans h1 _; rewrite perm_sym.
have hpn : (p < n)%N by [].
have hip := ih (ltnW hp).
have hsp : (n - p)%N = (n - p.+1).+1 by rewrite subnS prednK // subn_gt0.
move: hip; rewrite hsp /=.
set t1 := [seq q1 j | j <- iota p.+1 (n - p.+1)].
set t2 := [seq q2 j | j <- iota p.+1 (n - p.+1)].
move=> hip.
have hus : uniq (q1 p :: t1).
  by move: (perm_tail_uniq h1 (ltnW hp)); rewrite hsp /=.
have hm2 : q2 p \in q1 p :: t1 by rewrite (perm_mem hip) mem_head.
have e1 : count (fun x => (x < q1 p)%N) (q1 p :: t1) = lcode n q1 p.
  by rewrite lcodeE /= ltnn add0n.
have e2 : count (fun x => (x < q2 p)%N) (q1 p :: t1) = lcode n q2 p.
  by rewrite (permP hip) lcodeE /= ltnn add0n.
have hq : q1 p = q2 p.
  apply: (count_below_inj hus (mem_head _ _) hm2).
  by rewrite e1 e2 (hcode p hpn).
by move: hip; rewrite hq perm_cons.
Qed.

Lemma code_perm n (q1 q2 : nat -> nat) :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  (forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i) ->
  forall p, (p < n)%N -> q1 p = q2 p.
Proof.
move=> h1 h2 hcode p hpn.
have hT := code_tails h1 h2 hcode.
have hsp : (n - p)%N = (n - p.+1).+1 by rewrite subnS prednK // subn_gt0.
have hit := hT p.+1 hpn.
have hus := perm_tail_uniq h1 (ltnW hpn).
have hip := hT p (ltnW hpn).
move: hus hip; rewrite hsp /= => /andP[hnotin _] hip.
apply/eqP; apply/negPn/negP => hne.
have : q1 p \in [seq q2 j | j <- iota p.+1 (n - p.+1)].
  move: (perm_mem hip (q1 p)); rewrite mem_head in_cons (negbTE hne) /=.
  by move=> <-.
by rewrite -(perm_mem hit) (negbTE hnotin).
Qed.

Lemma lrank_inj n (q1 q2 : nat -> nat) :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  lrank n q1 = lrank n q2 -> forall p, (p < n)%N -> q1 p = q2 p.
Proof.
move=> h1 h2 hr; apply: code_perm => //.
exact: lrank_code hr.
Qed.

Definition prmn (n : nat) (q : nat -> nat) : bool :=
  odd (sumn [seq count (fun j => (q j < q i)%N) (iota i.+1 (n - i.+1))
            | i <- iota 0 n]).

Lemma prmn_id n : prmn n id = false.
Proof.
rewrite /prmn; suff -> : [seq count (fun j => (j < i)%N) (iota i.+1 (n - i.+1))
                         | i <- iota 0 n]
                       = [seq 0%N | i <- iota 0 n].
  by elim: (iota 0 n) => //= _ l ih; rewrite ih.
apply/eq_in_map => i _; apply/eqP; rewrite -leqn0 leqNgt -has_count.
apply/negP => /hasP[j]; rewrite mem_iota => /andP[hj _] /= hji.
by move: hj; rewrite ltnNge (ltnW hji).
Qed.

Lemma prmn_eq n (f g : nat -> nat) :
  (forall p, (p < n)%N -> f p = g p) -> prmn n f = prmn n g.
Proof.
move=> hfg; rewrite /prmn; congr odd; congr sumn.
apply/eq_in_map => i; rewrite mem_iota add0n => /andP[_ hi].
rewrite hfg //; apply: eq_in_count => j.
rewrite mem_iota => /andP[hj1 hj2].
by rewrite hfg // (leq_trans hj2) // subnKC.
Qed.

(* one place off the end of a range                                           *)
Lemma subn_step n k : (k < n)%N -> (n - k)%N = (n - k.+1).+1.
Proof. by move=> hk; rewrite subnS prednK // subn_gt0. Qed.

Definition swp (i p : nat) : nat :=
  if p == i then i.+1 else if p == i.+1 then i else p.

Lemma swpK i : involutive (swp i).
Proof.
move=> p; rewrite /swp; case: (p =P i) => [->|hi].
  by rewrite ifN ?eqxx // -[i.+1 == i]/(i.+1 == i) neq_ltn ltnSn orbT.
case: (p =P i.+1) => [->|hi1]; first by rewrite eqxx.
by rewrite ifN ?ifN //; apply/eqP.
Qed.

(* the exchange sends the places after k to the places after k: either both   *)
(* i and i + 1 are among them, and it swaps two of them, or neither is and it *)
(* does nothing                                                               *)
Lemma swp_mem n i k j : (i.+1 < n)%N -> k != i -> k != i.+1 ->
  (k.+1 <= j)%N -> (j < n)%N -> (k.+1 <= swp i j)%N && (swp i j < n)%N.
Proof.
move=> hi hki hki1 hj1 hj2.
have [hlt|hge] := ltnP k i.
  rewrite /swp; case: eqP => [_|_].
    by rewrite hi andbT (leq_trans hlt (leqnSn i)).
  case: eqP => [_|_]; last by rewrite hj1 hj2.
  by rewrite hlt (ltnW hi).
have hgt : (i.+1 < k)%N.
  rewrite ltn_neqAle eq_sym hki1 /=.
  by move: hge; rewrite leq_eqVlt eq_sym (negbTE hki).
have hik : (i < k)%N := ltn_trans (ltnSn i) hgt.
have hn1 : j != i by rewrite gtn_eqF // (ltn_trans hik hj1).
have hn2 : j != i.+1 by rewrite gtn_eqF // (ltn_trans hgt hj1).
by rewrite /swp ifN ?ifN ?hj1 ?hj2.
Qed.

(* so it is itself a permutation of the places                                *)
Lemma swp_perm n i : (i.+1 < n)%N ->
  perm_eq [seq swp i p | p <- iota 0 n] (iota 0 n).
Proof.
move=> hi; apply: uniq_perm.
- by rewrite map_inj_uniq ?iota_uniq //; apply: can_inj (swpK i).
- exact: iota_uniq.
have hb j : (j < n)%N -> (swp i j < n)%N.
  move=> hj; rewrite /swp; case: eqP => [_|_] //.
  by case: eqP => [_|_] //; apply: ltn_trans (ltnSn i) hi.
move=> j; rewrite mem_iota add0n; apply/mapP/idP => [[j' hj' ->]|hj].
  by apply: hb; move: hj'; rewrite mem_iota add0n => /andP[_ ->].
by exists (swp i j); [rewrite mem_iota add0n hb | rewrite swpK].
Qed.

Lemma prmn_swap_out n q i k : (k < n)%N -> (i.+1 < n)%N ->
  k != i -> k != i.+1 ->
  count (fun j => (q (swp i j) < q (swp i k))%N) (iota k.+1 (n - k.+1))
  = count (fun j => (q j < q k)%N) (iota k.+1 (n - k.+1)).
Proof.
move=> hk hi hki hki1.
have hsk : swp i k = k by rewrite /swp ifN ?ifN.
rewrite hsk.
transitivity (count (fun x => (q x < q k)%N)
                    [seq swp i j | j <- iota k.+1 (n - k.+1)]).
  by rewrite count_map.
have hperm : perm_eq [seq swp i j | j <- iota k.+1 (n - k.+1)]
                     (iota k.+1 (n - k.+1)).
  apply: uniq_perm.
  - by rewrite map_inj_uniq ?iota_uniq //; apply: can_inj (swpK i).
  - exact: iota_uniq.
  move=> j; rewrite mem_iota subnKC //; apply/mapP/idP => [[j' hj' ->]|hj].
    move: hj'; rewrite mem_iota subnKC // => /andP[h1 h2].
    by have /andP[-> ->] := swp_mem hi hki hki1 h1 h2.
  exists (swp i j); last by rewrite swpK.
  move: hj => /andP[h1 h2]; rewrite mem_iota subnKC //.
  by have /andP[-> ->] := swp_mem hi hki hki1 h1 h2.
by rewrite (permP hperm).
Qed.

Lemma prmn_swap_mid n q i : (i.+1 < n)%N -> q i != q i.+1 ->
  odd (count (fun j => (q (swp i j) < q (swp i i))%N) (iota i.+1 (n - i.+1))
       + count (fun j => (q (swp i j) < q (swp i i.+1))%N)
               (iota i.+2 (n - i.+2)))
  = ~~ odd (count (fun j => (q j < q i)%N) (iota i.+1 (n - i.+1))
            + count (fun j => (q j < q i.+1)%N) (iota i.+2 (n - i.+2))).
Proof.
move=> hi hne.
have hsp : (n - i.+1)%N = (n - i.+2).+1 := subn_step hi.
have hsi : swp i i = i.+1 by rewrite /swp eqxx.
have hsi1 : swp i i.+1 = i by rewrite /swp gtn_eqF ?ltnSn // eqxx.
have htail r : count (fun j => (q (swp i j) < r)%N) (iota i.+2 (n - i.+2))
             = count (fun j => (q j < r)%N) (iota i.+2 (n - i.+2)).
  apply: eq_in_count => j; rewrite mem_iota => /andP[hj _].
  have hn1 : j != i by rewrite gtn_eqF // (leq_trans (leqnSn _) hj).
  have hn2 : j != i.+1 by rewrite gtn_eqF.
  by rewrite /swp ifN ?ifN.
have hb : (q i.+1 < q i)%N = ~~ (q i < q i.+1)%N by case: ltngtP hne.
rewrite hsi hsp /= hsi1 !htail hb.
set C0 := count (fun j => (q j < q i)%N) (iota i.+2 (n - i.+2)).
set C1 := count (fun j => (q j < q i.+1)%N) (iota i.+2 (n - i.+2)).
by case: (q i < q i.+1)%N; rewrite !oddD /=; case: (odd C0); case: (odd C1).
Qed.

(* two of a row of four turn over, so the row turns over                      *)
Lemma addb_mid (A a b B c d : bool) : a (+) b = ~~ (c (+) d) ->
  A (+) (a (+) (b (+) B)) = ~~ (A (+) (c (+) (d (+) B))).
Proof.
by move=> h; case: A; case: B; move: h; case: a; case: b; case: c; case: d.
Qed.

Lemma prmn_swap n q i : (i.+1 < n)%N -> q i != q i.+1 ->
  prmn n (fun p => q (swp i p)) = ~~ prmn n q.
Proof.
move=> hi hne.
have hin : (i <= n)%N by apply: ltnW; apply: ltnW.
have hin1 : (i < n)%N by apply: ltn_trans (ltnSn i) hi.
have hni : (n - i)%N = (n - i.+2).+2.
  by rewrite (subn_step hin1) (subn_step hi).
have hcat : iota 0 n = iota 0 i ++ [:: i, i.+1 & iota i.+2 (n - i.+2)].
  by rewrite -{1}(subnKC hin) iotaD add0n hni.
have hA : sumn [seq count (fun j => (q (swp i j) < q (swp i k))%N)
                         (iota k.+1 (n - k.+1)) | k <- iota 0 i]
        = sumn [seq count (fun j => (q j < q k)%N) (iota k.+1 (n - k.+1))
               | k <- iota 0 i].
  congr sumn; apply/eq_in_map => k; rewrite mem_iota add0n => /andP[_ hk].
  apply: prmn_swap_out => //.
  - by apply: ltn_trans hk _; apply: ltn_trans (ltnSn i) hi.
  - by rewrite ltn_eqF.
  by rewrite ltn_eqF // (ltn_trans hk (ltnSn i)).
have hB : sumn [seq count (fun j => (q (swp i j) < q (swp i k))%N)
                         (iota k.+1 (n - k.+1)) | k <- iota i.+2 (n - i.+2)]
        = sumn [seq count (fun j => (q j < q k)%N) (iota k.+1 (n - k.+1))
               | k <- iota i.+2 (n - i.+2)].
  congr sumn; apply/eq_in_map => k; rewrite mem_iota => /andP[hk1 hk2].
  rewrite subnKC // in hk2.
  apply: prmn_swap_out => //.
  - by rewrite gtn_eqF // (ltn_trans (ltnSn i) hk1).
  by rewrite gtn_eqF.
rewrite /prmn hcat !map_cat !sumn_cat /= hA hB.
rewrite !oddD; apply: addb_mid.
by rewrite -!oddD; apply: prmn_swap_mid.
Qed.

(* the number of inversions, of which prmn is the parity                      *)
Definition invn (n : nat) (q : nat -> nat) : nat :=
  sumn [seq lcode n q i | i <- iota 0 n].

Lemma prmnI n q : prmn n q = odd (invn n q).
Proof. by []. Qed.

(* BUBBLE SORT, in three pieces.  A permutation with no inversions is the     *)
(* identity; one that is not the identity has two neighbouring places out of  *)
(* order; and exchanging there loses exactly one inversion.  So the induction *)
(* runs on the number of inversions and each step is prmn_swap.               *)

(* a permutation of the places that never goes down is the identity on them   *)
Lemma nondec_id n q : perm_eq [seq q p | p <- iota 0 n] (iota 0 n) ->
  (forall i j, (i < j)%N -> (j < n)%N -> (q i <= q j)%N) ->
  forall p, (p < n)%N -> q p = p.
Proof.
move=> hp hnd p hpn.
have hs1 : sorted leq [seq q i | i <- iota 0 n].
  rewrite sorted_pairwise; last exact: leq_trans.
  rewrite pairwise_map; apply/(pairwiseP 0%N) => i j.
  rewrite !inE !size_iota => hi hj hij.
  by rewrite !nth_iota // !add0n; apply: hnd.
have hs2 : sorted leq (iota 0 n).
  by rewrite -[leq]/(fun m k => (m <= k)%N); apply: iota_sorted.
have he : [seq q i | i <- iota 0 n] = iota 0 n.
  by apply: (sorted_eq leq_trans anti_leq hs1 hs2 hp).
have := congr1 (fun l => nth 0%N l p) he.
by rewrite (nth_map 0%N) ?size_iota // !nth_iota // !add0n.
Qed.

Lemma invn0_id n q : perm_eq [seq q p | p <- iota 0 n] (iota 0 n) ->
  invn n q = 0%N -> forall p, (p < n)%N -> q p = p.
Proof.
move=> hp h0; apply: nondec_id => // i j hij hjn.
have hin : (i < n)%N by apply: ltn_trans hij hjn.
have hd : lcode n q i = 0%N.
  apply/eqP; rewrite -leqn0 -h0 /invn.
  have : lcode n q i \in [seq lcode n q k | k <- iota 0 n].
    by apply/mapP; exists i => //; rewrite mem_iota.
  by elim: [seq _ _ _ | _ <- _] => //= x l ih; rewrite inE
     => /orP[/eqP->|/ih hl]; [apply: leq_addr | apply: leq_trans hl _;
     apply: leq_addl].
move: hd; rewrite /lcode => /eqP; rewrite -leqn0 leqNgt -has_count.
move/negP => hh; rewrite leqNgt; apply/negP => hlt; apply: hh; apply/hasP.
by exists j => //; rewrite mem_iota hij subnKC.
Qed.

(* never going down between neighbours is never going down at all             *)
Lemma adj_nondec n q : (forall i, (i.+1 < n)%N -> (q i <= q i.+1)%N) ->
  forall i j, (i < j)%N -> (j < n)%N -> (q i <= q j)%N.
Proof.
move=> h i j; elim: j => [|j ih] //.
rewrite ltnS leq_eqVlt => /orP[/eqP->|hij] hjn; first exact: h.
exact: leq_trans (ih hij (ltnW hjn)) (h j hjn).
Qed.

Lemma has_descent n q : (0 < invn n q)%N ->
  exists i, (i.+1 < n)%N /\ (q i.+1 < q i)%N.
Proof.
move=> hpos.
case: (boolP (has (fun i => (i.+1 < n)%N && (q i.+1 < q i)%N) (iota 0 n))).
  by move=> /hasP[i _ /andP[h1 h2]]; exists i.
move=> /hasPn hno; exfalso.
have hnd : forall i j, (i < j)%N -> (j < n)%N -> (q i <= q j)%N.
  apply: adj_nondec => i hi.
  have hin : i \in iota 0 n.
    by rewrite mem_iota add0n (ltn_trans (ltnSn i) hi).
  by move: (hno i hin); rewrite hi /= -leqNgt.
have h0 : invn n q = 0%N.
  rewrite /invn.
  suff -> : [seq lcode n q i | i <- iota 0 n] = [seq 0%N | i <- iota 0 n].
    by elim: (iota 0 n) => //= _ l ih; rewrite ih.
  apply/eq_in_map => i; rewrite mem_iota add0n => /andP[_ hi].
  apply/eqP; rewrite /lcode -leqn0 leqNgt -has_count; apply/negP => /hasP[j].
  rewrite mem_iota subnKC // => /andP[hj1 hj2] /=.
  by rewrite ltnNge (hnd i j hj1 hj2).
by rewrite h0 ltnn in hpos.
Qed.

Lemma invn_swap n q i : (i.+1 < n)%N -> (q i.+1 < q i)%N ->
  (invn n (fun p => q (swp i p)) < invn n q)%N.
Proof.
move=> hi hdesc.
have hin1 : (i < n)%N := ltn_trans (ltnSn i) hi.
have hin : (i <= n)%N by apply: ltnW.
have hni : (n - i)%N = (n - i.+2).+2.
  by rewrite (subn_step hin1) (subn_step hi).
have hcat : iota 0 n = iota 0 i ++ [:: i, i.+1 & iota i.+2 (n - i.+2)].
  by rewrite -{1}(subnKC hin) iotaD add0n hni.
rewrite /invn hcat !map_cat !sumn_cat /=.
have hA : sumn [seq lcode n (fun p => q (swp i p)) k | k <- iota 0 i]
        = sumn [seq lcode n q k | k <- iota 0 i].
  congr sumn; apply/eq_in_map => k; rewrite mem_iota add0n => /andP[_ hk].
  rewrite /lcode; apply: prmn_swap_out => //.
  - by apply: ltn_trans hk _.
  - by rewrite ltn_eqF.
  by rewrite ltn_eqF // (ltn_trans hk (ltnSn i)).
have hB : sumn [seq lcode n (fun p => q (swp i p)) k
               | k <- iota i.+2 (n - i.+2)]
        = sumn [seq lcode n q k | k <- iota i.+2 (n - i.+2)].
  congr sumn; apply/eq_in_map => k; rewrite mem_iota => /andP[hk1 hk2].
  rewrite subnKC // in hk2.
  rewrite /lcode; apply: prmn_swap_out => //.
  - by rewrite gtn_eqF // (ltn_trans (ltnSn i) hk1).
  by rewrite gtn_eqF.
rewrite hA hB ltn_add2l !addnA ltn_add2r.
have hsp : (n - i.+1)%N = (n - i.+2).+1 := subn_step hi.
have hsi : swp i i = i.+1 by rewrite /swp eqxx.
have hsi1 : swp i i.+1 = i by rewrite /swp gtn_eqF ?ltnSn // eqxx.
have htail r : count (fun j => (q (swp i j) < r)%N) (iota i.+2 (n - i.+2))
             = count (fun j => (q j < r)%N) (iota i.+2 (n - i.+2)).
  apply: eq_in_count => j; rewrite mem_iota => /andP[hj _].
  have hn1 : j != i by rewrite gtn_eqF // (leq_trans (leqnSn _) hj).
  have hn2 : j != i.+1 by rewrite gtn_eqF.
  by rewrite /swp ifN ?ifN.
have hb0 : (q i < q i.+1)%N = false by apply/negbTE; rewrite -leqNgt ltnW.
rewrite /lcode hsp /= hsi hsi1 !htail ltnNge -ltnS hdesc /=.
by rewrite hb0 add0n add1n addSn addnC ltnn.
Qed.

Lemma prmn_mul n q1 q2 :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  prmn n (fun p => q1 (q2 p)) = prmn n q1 (+) prmn n q2.
Proof.
move=> h1; move: {2}(invn n q2) (leqnn (invn n q2)) => m.
elim: m q2 => [|m ih] q2 hm h2.
  have h0 : invn n q2 = 0%N by apply/eqP; rewrite -leqn0.
  have hid := invn0_id h2 h0.
  rewrite (prmn_eq (fun p hp => congr1 q1 (hid p hp))).
  by rewrite [prmn n q2]prmnI h0 /= addbF.
case: (posnP (invn n q2)) => [h0|hpos].
  have hid := invn0_id h2 h0.
  rewrite (prmn_eq (fun p hp => congr1 q1 (hid p hp))).
  by rewrite [prmn n q2]prmnI h0 /= addbF.
have [i [hi hdesc]] := has_descent hpos.
have hne : q2 i != q2 i.+1 by rewrite gtn_eqF.
have h2' : perm_eq [seq q2 (swp i p) | p <- iota 0 n] (iota 0 n).
  by apply: perm_comp h2 _; apply: swp_perm.
have hle : (invn n (fun p => q2 (swp i p)) <= m)%N.
  by rewrite -ltnS; apply: leq_trans hm; apply: invn_swap.
have hstep := ih _ hle h2'.
have hne1 : q1 (q2 i) != q1 (q2 i.+1).
  apply/eqP => heq; case/eqP: hne.
  by apply: (perm_inj h1) => //; apply: (perm_range h2) => //; apply: ltnW.
have hL : prmn n (fun p => q1 (q2 (swp i p))) = ~~ prmn n (fun p => q1 (q2 p)).
  by apply: (@prmn_swap n (fun p => q1 (q2 p)) i).
have hR : prmn n (fun p => q2 (swp i p)) = ~~ prmn n q2 by apply: prmn_swap.
move: hstep; rewrite hL hR => /(congr1 negb).
by rewrite negbK => ->; case: (prmn n q1); case: (prmn n q2).
Qed.

(* ---- a permutation that keeps to a partition ----------------------------- *)

(* If the first n1 places go among themselves and the last n2 among           *)
(* themselves, a pair of places from different halves is never an inversion,  *)
(* so the count splits and the sign is the exclusive or of the two.           *)
Section Cat.

Variable n1 n2 : nat.
Variable e q1 q2 : nat -> nat.

Hypothesis he1 : forall p, (p < n1)%N -> e p = q1 p.
Hypothesis he2 : forall p, (p < n2)%N -> e (n1 + p)%N = (n1 + q2 p)%N.
Hypothesis h1lt : forall p, (p < n1)%N -> (q1 p < n1)%N.

(* a place of the first block counts only inside the first block: a place of  *)
(* the second holds something at n1 or above, and a place of the first holds  *)
(* something below it                                                         *)
Lemma lcode_cat1 i : (i < n1)%N ->
  lcode (n1 + n2) e i = lcode n1 q1 i.
Proof.
move=> hi; rewrite /lcode.
have hi1 : (i.+1 <= n1)%N by [].
have hs : (n1 + n2 - i.+1)%N = ((n1 - i.+1) + n2)%N.
  by rewrite addnBAC.
rewrite hs iotaD subnKC // count_cat.
have -> : count (fun j => (e j < e i)%N) (iota n1 n2) = 0%N.
  apply/eqP; rewrite -leqn0 leqNgt -has_count; apply/negP => /hasP[j].
  rewrite mem_iota => /andP[hj1 hj2] /=.
  rewrite -(subnKC hj1) he2 ?he1 //; last by rewrite ltn_subLR // addnC.
  move=> h.
  by move: (ltn_trans h (h1lt hi)); rewrite ltnNge leq_addr.
rewrite addn0; apply: eq_in_count => j.
by rewrite mem_iota subnKC // => /andP[hj1 hj2]; rewrite !he1.
Qed.

(* and a place of the second block counts only inside the second, where the   *)
(* comparison is the same one shifted by n1                                   *)
Lemma lcode_cat2 p : (p < n2)%N ->
  lcode (n1 + n2) e (n1 + p)%N = lcode n2 q2 p.
Proof.
move=> hp; rewrite /lcode -addnS.
have -> : (n1 + n2 - (n1 + p.+1))%N = (n2 - p.+1)%N by rewrite subnDl.
rewrite iotaDl count_map; apply: eq_in_count => j.
rewrite mem_iota subnKC // => /andP[_ hj].
by rewrite /= !he2 // ltn_add2l.
Qed.

Lemma prmn_cat : prmn (n1 + n2) e = prmn n1 q1 (+) prmn n2 q2.
Proof.
rewrite /prmn iotaD map_cat sumn_cat oddD; congr (_ (+) _).
  congr odd; congr sumn; apply/eq_in_map => i.
  by rewrite mem_iota add0n => /andP[_ hi]; apply: lcode_cat1.
congr odd; congr sumn.
rewrite add0n -[in LHS](addn0 n1) iotaDl -map_comp addn0.
apply/eq_in_map => p; rewrite mem_iota add0n => /andP[_ hp].
exact: lcode_cat2.
Qed.

End Cat.
