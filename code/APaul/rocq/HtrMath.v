(** * T6: the mathematics of the search of htr3.c, no Capla

    Two facts the proof of the Capla htr3 needs (doc/htr3-capla-plan.typ):
    (a) the table the search builds from the values of a polynomial gives
    the polynomial at [j] in its first coefficient, plus the window, modulo
    [beta^l]; (b) the test of [hscan] implies the top-word test of htr3.c.
    The search walks [j = 0 .. n-1], as [TaylorLink.hscan_exp] does. *)

From Stdlib Require Import ZArith Reals Lia List.
From APaulRocq Require Import HtrDefs TaylorReal.
From mathcomp Require Import all_ssreflect all_algebra ssrZ zify.
From APaulRocq Require Import Shift TaylorScan TaylorLink.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

(** ** Helpers: from the lists of HtrDefs.v to sums over [Z] *)

Section Helpers.

Local Open Scope ring_scope.

Lemma foldZE (F : nat -> Z) r :
  fold_right Z.add Z0 (List.map F r) = \sum_(i <- r) F i.
Proof. by elim: r => [|a r IH] /=; rewrite ?big_nil ?big_cons ?IH. Qed.

Lemma seqE m n : List.seq m n = iota m n.
Proof. by elim: n m => //= n IH m; rewrite IH. Qed.

Lemma ListmapE (T U : Type) (F : T -> U) s : List.map F s = map F s.
Proof. by elim: s => //= a s ->. Qed.

Lemma ListnthE (T : Type) (d : T) s i : List.nth i s d = nth d s i.
Proof. by elim: s i => [|a s IH] [|i] //=. Qed.

Lemma lengthE (T : Type) (s : list T) : length s = size s.
Proof. by elim: s => //= a s ->. Qed.

Lemma binomE t s : binom t s = Z.of_nat 'C(t, s).
Proof.
elim: t s => [|t IH] [|s] //=.
by rewrite binS !IH; lia.
Qed.

Lemma powZE (x : Z) n : Z.pow x (Z.of_nat n) = x ^+ n.
Proof.
elim: n => [//|n IH].
by rewrite Nat2Z.inj_succ Z.pow_succ_r ?IH ?exprS //; lia.
Qed.

Lemma mulrnZ (c : Z) n : c *+ n = Z.mul c (Z.of_nat n).
Proof. by elim: n => [|n IH]; rewrite ?mulr0n ?mulrS ?IH; lia. Qed.

Lemma natZ_exp n t : Z.of_nat (n ^ t) = (Z.of_nat n) ^+ t.
Proof. by elim: t => [//|t IH]; rewrite expnS exprS Nat2Z.inj_mul IH. Qed.

(** ** The steps: after [j] steps, [d_i] is [sum_t C(j, t) d_(i+t)] *)

(** Past the end, the list reads as zeros, so the last one is unchanged. *)
Lemma nth_tstepZ ds i : nth 0 (tstepZ ds) i = nth 0 ds i + nth 0 ds i.+1.
Proof. by elim: ds i => [|a [|b r] IH] [|i] //=; lia. Qed.

Lemma nth_iterZ ds j i :
  nth 0 (Nat.iter j tstepZ ds) i =
  \sum_(0 <= t < j.+1) nth 0 ds (i + t) *+ 'C(j, t).
Proof.
elim: j i => [|j IH] i.
  by rewrite big_nat1 addn0 bin0 mulr1n.
rewrite [Nat.iter _ _ _]/= nth_tstepZ !IH.
rewrite [RHS]big_nat_recl //= bin0 mulr1n.
under [in RHS]eq_bigr => t _ do rewrite binS mulrnDr.
rewrite big_split /= addrA; congr (_ + _).
  rewrite [LHS]big_nat_recl //= bin0 mulr1n addn0; congr (_ + _).
  rewrite [RHS]big_nat_recr //= bin_small // mulr0n addr0.
  by apply: eq_bigr => t _; rewrite addnS.
by apply: eq_bigr => t _; rewrite addSnnS.
Qed.

(** ** [fdiff] is the difference of Shift.v *)

(** The coefficient [(-1)^(t - s) C(t, s)]. *)
Definition csgn t s : Z := (-1) ^+ (t - s) *+ 'C(t, s).

Lemma csgnS0 t : csgn t.+1 0 = - csgn t 0.
Proof. by rewrite /csgn !subn0 !bin0 exprS mulN1r mulNrn. Qed.

Lemma csgnSS t s : csgn t.+1 s.+1 = csgn t s - csgn t s.+1.
Proof.
rewrite /csgn subSS binS mulrnDr.
case: (ltngtP s t) => [st|ts|->].
- by rewrite -(subnSK st) exprS mulN1r mulNrn addrC.
- by rewrite !bin_small ?mulr0n ?subr0 ?addr0 // ltnW.
- by rewrite bin_small // !mulr0n subr0 add0r.
Qed.

Lemma diffnE (f : nat -> Z) t n :
  diffn t f n = \sum_(0 <= s < t.+1) csgn t s * f (n + s)%N.
Proof.
elim: t n => [|t IH] n.
  by rewrite big_nat1 /csgn addn0 bin0 mulr1n expr0 mul1r.
rewrite diffnS /diff !IH.
rewrite [RHS]big_nat_recl // csgnS0 addn0.
under [in RHS]eq_bigr => s _ do rewrite csgnSS mulrBl.
rewrite sumrB [in X in _ - X]big_nat_recl // addn0.
have c0 : csgn t t.+1 = 0 by rewrite /csgn bin_small.
rewrite [X in _ = _ + (_ - X)]big_nat_recr //= c0 mul0r addr0.
under eq_bigr => s _ do rewrite addSnnS.
rewrite mulNr.
move: (\sum_(0 <= s < t.+1) _) (\sum_(0 <= i < t) _) (csgn t 0 * f n).
by move=> X Y x; lia.
Qed.

Lemma fdiffE (f : nat -> Z) k t :
  (t < k)%N -> fdiff (List.map f (List.seq 0 k)) t = diffn t f 0.
Proof.
move=> tk; rewrite diffnE /fdiff foldZE seqE /index_iota subn0.
apply: eq_big_seq => s; rewrite mem_iota => /andP[_ st].
rewrite ListnthE ListmapE seqE (nth_map 0%N); last first.
  by rewrite size_iota; apply: leq_trans tk.
rewrite nth_iota; last by apply: leq_trans tk.
by rewrite powZE binomE /csgn mulrnZ add0n.
Qed.

(** ** The head of the table *)

Lemma sum_widen (F : nat -> Z) a b :
  (a <= b)%N -> (forall t, (a <= t)%N -> F t = 0) ->
  \sum_(0 <= t < a) F t = \sum_(0 <= t < b) F t.
Proof.
move=> ab F0; rewrite [RHS](big_cat_nat (leq0n a) ab) /=.
rewrite [X in _ = _ + X]big1_seq ?addr0 // => t; rewrite mem_index_iota.
by move=> /andP[_ /andP[ta _]]; apply: F0.
Qed.

Lemma nth_window L err T t : T <> nil ->
  nth 0 (window L err T) t =
  nth 0 T t + (if t == 0%N then Z.mul err (2 ^ (wbits * (L - 1))) else 0).
Proof. by case: T => [//|a r] _; case: t => [|t] /=; lia. Qed.

(** From the values [f 0 .. f (k-1)], the head after [j] steps is
    [sum_(t < k) C(j, t) diffn t f 0] plus the window. *)
Lemma table_headE (f : nat -> Z) L err k j : (0 < k)%N ->
  List.nth 0 (table L err (List.map f (List.seq 0 k)) j) Z0 =
  \sum_(0 <= t < k) diffn t f 0 *+ 'C(j, t) +
  Z.mul err (2 ^ (wbits * (L - 1))).
Proof.
move=> k0; rewrite /table ListnthE nth_iterZ.
have -> : length (List.map f (List.seq 0 k)) = k.
  by rewrite lengthE ListmapE seqE size_map size_iota.
set T := List.map _ (List.seq 0 k).
have Tn : T <> nil by rewrite /T; case: (k) k0.
under eq_bigr => t _ do rewrite add0n (nth_window _ _ _ Tn) mulrnDl.
rewrite big_split [X in _ + X = _]big_nat_recl // eqxx bin0 mulr1n.
rewrite [X in _ + (_ + X)]big1 ?addr0 => [|t _]; last by rewrite mul0rn.
congr (_ + _).
have nT t : nth 0 T t = if (t < k)%N then diffn t f 0 else 0.
  rewrite /T ListmapE seqE; case: ltnP => tk.
    by rewrite (nth_map 0%N) ?size_iota // nth_iota // add0n fdiffE.
  by rewrite nth_default // size_map size_iota.
have F1 : forall t, (j.+1 <= t)%N -> T`_t *+ 'C(j, t) = 0.
  by move=> t jt; rewrite bin_small ?mulr0n.
have F2 : forall t, (k <= t)%N -> T`_t *+ 'C(j, t) = 0.
  by move=> t kt; rewrite nT ltnNge kt mul0rn.
transitivity (\sum_(0 <= t < j.+1 + k) T`_t *+ 'C(j, t)).
  exact: (sum_widen (leq_addr k j.+1) F1).
transitivity (\sum_(0 <= t < k) T`_t *+ 'C(j, t)).
  by rewrite (sum_widen (leq_addl j.+1 k) F2).
by apply: eq_big_nat => t /andP[_ tk]; rewrite nT tk.
Qed.

(** [polyZ A] has degree less than [k], the length of [A]. *)
Lemma polyZ_diffn A m : (0 < size A)%N ->
  diffn (size A) (fun n => polyZ A (Z.of_nat n)) m = 0.
Proof.
move=> A0; rewrite -(prednK A0); move: m; apply/is_polyCbP/is_poly_UC.
exists A => n; rewrite (prednK A0) /polyZ foldZE seqE lengthE.
rewrite -(big_mkord xpredT (fun i => A`_i *+ U_basis i n)).
rewrite /index_iota subn0; apply: eq_bigr => i _.
by rewrite /U_basis mulrnZ natZ_exp powZE ListnthE.
Qed.

End Helpers.

(** (a) From the values [P(0) .. P(k-1)] modulo [beta^l], [k >= 1] the
    number of coefficients of [P], the table after [j] steps holds
    [P(j) + err beta^(l-1)] in its first coefficient, modulo [beta^l]. *)
Lemma table_head (A : list Z) (L err : Z) (j : nat) :
  (0 < length A)%N -> Z.le 1 L ->
  Z.modulo (List.nth 0 (table L err
              (List.map (fun i => Z.modulo (polyZ A (Z.of_nat i)) (baseZ L))
                        (List.seq 0 (List.length A))) j) Z0) (baseZ L) =
  Z.modulo (Z.add (polyZ A (Z.of_nat j))
                  (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1)))))
           (baseZ L).
Proof.
rewrite lengthE => A0 L1; rewrite table_headE //.
set M := baseZ L; set w := Z.mul err _.
pose P n := polyZ A (Z.of_nat n); pose q n := (- Z.div (P n) M)%R.
have M0 : M <> Z0.
  by have := Z.pow_pos_nonneg 2 (wbits * L); rewrite /M /baseZ /wbits; lia.
have dE t : diffn t (fun i => Z.modulo (P i) M) 0 =
            (diffn t P 0 + M * diffn t q 0)%R.
  rewrite -diffn_scale -diffn_add; apply: diffn_ext => m.
  by rewrite /q (Z.mod_eq _ _ M0); lia.
under eq_bigr => t _ do rewrite dE mulrnDl -mulrnAr.
rewrite big_split /= -mulr_sumr.
have -> : (\sum_(0 <= t < size A) diffn t P 0 *+ 'C(j, t))%R = P j.
  rewrite big_mkord -(prednK A0) -newton // => m.
  by rewrite (prednK A0); apply: polyZ_diffn.
rewrite -/(P j).
set X := (\sum_(0 <= t < size A) _)%R.
have -> : (P j + M * X + w)%R = Z.add (Z.add (P j) w) (Z.mul X M).
  by rewrite /=; lia.
exact: Z_mod_plus_full.
Qed.


(** (b) The test of [hscan], [(b + E) mod beta^l <= 2 E] with
    [E = err beta^(l-1)], implies the top-word test of htr3.c. *)
Lemma top_hit (L err b : Z) :
  Z.le 1 L -> Z.le 0 err ->
  Z.le (Z.modulo (Z.add b (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1)))))
                 (baseZ L))
       (Z.mul 2 (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1))))) ->
  Z.le (top L (Z.add b (Z.mul err (Z.pow 2 (Z.mul wbits (Z.sub L 1))))))
       (Z.mul 2 err).
Proof.
move=> L1 err0 h; rewrite /top.
have D0 : Z.lt 0 (Z.pow 2 (Z.mul wbits (Z.sub L 1))).
  by apply: Z.pow_pos_nonneg; rewrite /wbits; lia.
by apply: Z.div_le_upper_bound => //; lia.
Qed.
