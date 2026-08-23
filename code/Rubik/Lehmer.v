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
Proof. Admitted.

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
Proof. Admitted.

(* one member of a set of naturals has a given number of members below it     *)
Lemma count_below_inj (s : seq nat) (v w : nat) :
  uniq s -> v \in s -> w \in s ->
  count (fun x => (x < v)%N) s = count (fun x => (x < w)%N) s -> v = w.
Proof. Admitted.

Lemma code_perm n (q1 q2 : nat -> nat) :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  (forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i) ->
  forall p, (p < n)%N -> q1 p = q2 p.
Proof. Admitted.

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

Lemma invn0_id n q : perm_eq [seq q p | p <- iota 0 n] (iota 0 n) ->
  invn n q = 0%N -> forall p, (p < n)%N -> q p = p.
Proof. Admitted.

Lemma has_descent n q : (0 < invn n q)%N ->
  {i | (i.+1 < n)%N & (q i.+1 < q i)%N}.
Proof. Admitted.

Lemma invn_swap n q i : (i.+1 < n)%N -> (q i.+1 < q i)%N ->
  (invn n (fun p => q (swp i p)) < invn n q)%N.
Proof. Admitted.

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
have [i hi hdesc] := has_descent hpos.
have hne : q2 i != q2 i.+1 by rewrite gtn_eqF.
Admitted.

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
Proof. Admitted.

(* and a place of the second block counts only inside the second, where the   *)
(* comparison is the same one shifted by n1                                   *)
Lemma lcode_cat2 p : (p < n2)%N ->
  lcode (n1 + n2) e (n1 + p)%N = lcode n2 q2 p.
Proof. Admitted.

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
