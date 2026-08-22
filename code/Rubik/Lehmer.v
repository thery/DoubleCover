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

Lemma lrank_code n (q1 q2 : nat -> nat) :
  lrank n q1 = lrank n q2 ->
  forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i.
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

Definition swp (i p : nat) : nat :=
  if p == i then i.+1 else if p == i.+1 then i else p.

Lemma swpK i : involutive (swp i).
Proof.
move=> p; rewrite /swp; case: (p =P i) => [->|hi].
  by rewrite ifN ?eqxx // -[i.+1 == i]/(i.+1 == i) neq_ltn ltnSn orbT.
case: (p =P i.+1) => [->|hi1]; first by rewrite eqxx.
by rewrite ifN ?ifN //; apply/eqP.
Qed.

Lemma prmn_swap_out n q i k : (k < n)%N -> (i.+1 < n)%N ->
  k != i -> k != i.+1 ->
  count (fun j => (q (swp i j) < q (swp i k))%N) (iota k.+1 (n - k.+1))
  = count (fun j => (q j < q k)%N) (iota k.+1 (n - k.+1)).
Proof. Admitted.

Lemma prmn_swap_mid n q i : (i.+1 < n)%N -> q i != q i.+1 ->
  odd (count (fun j => (q (swp i j) < q (swp i i))%N) (iota i.+1 (n - i.+1))
       + count (fun j => (q (swp i j) < q (swp i i.+1))%N)
               (iota i.+2 (n - i.+2)))
  = ~~ odd (count (fun j => (q j < q i)%N) (iota i.+1 (n - i.+1))
            + count (fun j => (q j < q i.+1)%N) (iota i.+2 (n - i.+2))).
Proof. Admitted.

Lemma prmn_swap n q i : (i.+1 < n)%N -> q i != q i.+1 ->
  prmn n (fun p => q (swp i p)) = ~~ prmn n q.
Proof. Admitted.

Lemma prmn_mul n q1 q2 :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  prmn n (fun p => q1 (q2 p)) = prmn n q1 (+) prmn n q2.
Proof. Admitted.

(* ---- a permutation that keeps to a partition ----------------------------- *)

(* If the first n1 places go among themselves and the last n2 among           *)
(* themselves, a pair of places from different halves is never an inversion,  *)
(* so the count splits and the sign is the exclusive or of the two.           *)
Lemma prmn_cat n1 n2 (e q1 q2 : nat -> nat) :
  (forall p, (p < n1)%N -> e p = q1 p) ->
  (forall p, (p < n2)%N -> e (n1 + p)%N = (n1 + q2 p)%N) ->
  (forall p, (p < n1)%N -> (q1 p < n1)%N) ->
  prmn (n1 + n2) e = prmn n1 q1 (+) prmn n2 q2.
Proof. Admitted.
