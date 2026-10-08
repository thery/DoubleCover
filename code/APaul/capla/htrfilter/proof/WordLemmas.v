(** * Lemmas on the words of an array (HtrWords.v), shared by the proofs *)

From APaulRocq Require Import HtrDefs.
From compcert Require Import CaplaProof.
From mathcomp Require Import tuple.
Require Import HtrFilterCapla.HtrWords.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Local Open Scope Z_scope.

(** ** Bases *)

Lemma baseZ0 : baseZ (Z.of_nat 0) = 1.
Proof. by []. Qed.

Lemma baseZS (k : nat) : baseZ (Z.of_nat k.+1) = baseZ (Z.of_nat k) * 2 ^ wbits.
Proof.
  rewrite /baseZ /wbits -Z.pow_add_r; try lia; f_equal; lia.
Qed.

Lemma baseZ_pos (k : nat) : 0 < baseZ (Z.of_nat k).
Proof. rewrite /baseZ /wbits; apply: Z.pow_pos_nonneg; lia. Qed.

Lemma baseZ_add (a b : nat) :
  baseZ (Z.of_nat (a + b)) = baseZ (Z.of_nat a) * baseZ (Z.of_nat b).
Proof. rewrite /baseZ /wbits -Z.pow_add_r; try lia; f_equal; lia. Qed.

(** ** Words *)

Section Words.

Context {n : nat}.
Implicit Types B : {ffun 'I_n -> int64}.

Lemma wd_ord B (q : 'I_n) : wd B q = Int64.unsigned (B q).
Proof.
  by rewrite /wd (nth_map Int64.zero) ?size_tuple ?card_ord // nth_fgraph_ord.
Qed.

Lemma wdE B q (H : (q < n)%nat) : wd B q = Int64.unsigned (B (Ordinal H)).
Proof. exact: (wd_ord B (Ordinal H)). Qed.

Lemma wd_out B q : (n <= q)%nat -> wd B q = 0.
Proof.
  move=> H; rewrite /wd nth_default // size_map size_tuple card_ord //.
Qed.

Lemma wd_bound B q : 0 <= wd B q < 2 ^ wbits.
Proof.
  case: (ltnP q n) => H; last by rewrite wd_out //; rewrite /wbits; lia.
  rewrite wdE; have := Int64.unsigned_range (B (Ordinal H)).
  by rewrite /wbits.
Qed.

(* Two arrays that agree on a word. *)
Lemma wd_eq B B' q :
  (forall H : (q < n)%nat, B' (Ordinal H) = B (Ordinal H)) -> wd B' q = wd B q.
Proof.
  move=> E; case: (ltnP q n) => H; last by rewrite !wd_out.
  by rewrite !(wdE _ _ H) E.
Qed.

(* Reading an array just written. *)
Lemma wd_set B k v q : (k < n)%nat ->
  wd (B ↑[k ← v]) q = if q == k then Int64.unsigned v else wd B q.
Proof.
  move=> Hk; case: eqP => [->|Nq].
  - by rewrite (wdE _ _ Hk) (setfE _ _ _ Hk) ffunE eqxx.
  - apply: wd_eq => H; rewrite (setfE _ _ _ Hk) ffunE; case: eqP => // E.
    by case: Nq; move: E => /(f_equal val).
Qed.

(** ** Segments *)

Lemma segv0 B a : segv B a 0 = 0.
Proof. by []. Qed.

(* The l + 1 words from a: the l low ones, then word a + l at its weight. *)
Lemma segvS B a l :
  segv B a l.+1 = segv B a l + baseZ (Z.of_nat l) * wd B (a + l).
Proof.
  elim: l a => [|l IH] a.
    by rewrite baseZ0 addn0; cbn [segv]; lia.
  have E : segv B a l.+2 = wd B a + 2 ^ wbits * segv B a.+1 l.+1 by [].
  have E1 : segv B a l.+1 = wd B a + 2 ^ wbits * segv B a.+1 l by [].
  rewrite E E1 IH baseZS addSnnS; lia.
Qed.

Lemma segv_bound B a l : 0 <= segv B a l < baseZ (Z.of_nat l).
Proof.
  elim: l a => [|l IH] a; first by rewrite baseZ0; cbn [segv]; lia.
  cbn [segv]; have := IH a.+1; have := wd_bound B a; rewrite baseZS; nia.
Qed.

(* The l words from a depend on these words only. *)
Lemma segv_ext B B' a l :
  (forall q, (a <= q < a + l)%nat -> wd B' q = wd B q) ->
  segv B' a l = segv B a l.
Proof.
  elim: l a => [|l IH] a H //; cbn [segv].
  rewrite (H a); [lia | rewrite IH // => q Hq; apply: H; lia].
Qed.

(* The value of the words of a segment that sum up modulo the base. *)
Lemma segv_mod B a l c v :
  segv B a l + c * baseZ (Z.of_nat l) = v ->
  segv B a l = v mod baseZ (Z.of_nat l).
Proof.
  move=> Hv; have := segv_bound B a l => Hb.
  apply: (Z.mod_unique_pos _ _ c); lia.
Qed.

End Words.

(** ** Words of 64 bits *)

(* The index a + i of a loop, below the length of the array, as a natural
   number. *)
Lemma add_nat (a i : int64) (n : nat) :
  (Z.to_nat (Int64.unsigned a) + Z.to_nat (Int64.unsigned i) < n)%nat ->
  Z.of_nat n <= Int64.max_unsigned ->
  Z.to_nat (Int64.unsigned (Int64.add a i)) =
  (Z.to_nat (Int64.unsigned a) + Z.to_nat (Int64.unsigned i))%nat.
Proof.
  move=> H Hn.
  have Ra := Int64.unsigned_range a; have Ri := Int64.unsigned_range i.
  rewrite Int64.add_unsigned Int64.unsigned_repr; lia.
Qed.

(* The carry of one round of add. *)
Lemma add_carry (a b c : int64) : Int64.unsigned c <= 1 ->
  Int64.unsigned (Int64.add a (Int64.add b c)) +
    2 ^ wbits * Int64.unsigned
      (if Int64.ltu (Int64.add b c) c then Int64.one
       else if Int64.ltu (Int64.add a (Int64.add b c)) (Int64.add b c)
            then Int64.one else Int64.zero) =
  Int64.unsigned a + Int64.unsigned b + Int64.unsigned c.
Proof.
  move=> Hc.
  have Ra := Int64.unsigned_range a; have Rb := Int64.unsigned_range b.
  have Rc := Int64.unsigned_range c.
  have Et : Int64.unsigned (Int64.add b c) =
            (Int64.unsigned b + Int64.unsigned c) mod Int64.modulus.
    by rewrite Int64.add_unsigned Int64.unsigned_repr_eq.
  have Es : Int64.unsigned (Int64.add a (Int64.add b c)) =
            (Int64.unsigned a + Int64.unsigned (Int64.add b c)) mod Int64.modulus.
    by rewrite Int64.add_unsigned Int64.unsigned_repr_eq.
  rewrite /Int64.ltu Es Et /wbits.
  change Int64.modulus with 18446744073709551616 in *.
  change (2 ^ 64) with 18446744073709551616.
  case: Coqlib.zlt => H1; last case: Coqlib.zlt => H2.
  all: rewrite ?Int64.unsigned_one ?Int64.unsigned_zero.
  all: lia.
Qed.

(* The borrow of one round of sub. *)
Lemma sub_borrow (a b c : int64) : Int64.unsigned c <= 1 ->
  Int64.unsigned (Int64.sub a (Int64.add b c)) -
    2 ^ wbits * Int64.unsigned
      (if Int64.ltu (Int64.add b c) c then Int64.one
       else if Int64.ltu a (Int64.add b c) then Int64.one else Int64.zero) =
  Int64.unsigned a - Int64.unsigned b - Int64.unsigned c.
Proof.
  move=> Hc.
  have Ra := Int64.unsigned_range a; have Rb := Int64.unsigned_range b.
  have Rc := Int64.unsigned_range c.
  have Et : Int64.unsigned (Int64.add b c) =
            (Int64.unsigned b + Int64.unsigned c) mod Int64.modulus.
    by rewrite Int64.add_unsigned Int64.unsigned_repr_eq.
  have Es : Int64.unsigned (Int64.sub a (Int64.add b c)) =
            (Int64.unsigned a - Int64.unsigned (Int64.add b c)) mod Int64.modulus.
    by rewrite /Int64.sub Int64.unsigned_repr_eq.
  rewrite /Int64.ltu Es Et /wbits.
  change Int64.modulus with 18446744073709551616 in *.
  change (2 ^ 64) with 18446744073709551616.
  case: Coqlib.zlt => H1; last case: Coqlib.zlt => H2.
  all: rewrite ?Int64.unsigned_one ?Int64.unsigned_zero.
  all: lia.
Qed.

(* A product of indices below the length of the array, as a natural
   number. *)
Section Mul.
Transparent Int64.mul.
Lemma mul_nat (a b : int64) (n : nat) :
  (Z.to_nat (Int64.unsigned a) * Z.to_nat (Int64.unsigned b) <= n)%nat ->
  Z.of_nat n <= Int64.max_unsigned ->
  Z.to_nat (Int64.unsigned (Int64.mul a b)) =
  (Z.to_nat (Int64.unsigned a) * Z.to_nat (Int64.unsigned b))%nat.
Proof.
  move=> H Hn.
  have Ra := Int64.unsigned_range a; have Rb := Int64.unsigned_range b.
  rewrite /Int64.mul Int64.unsigned_repr; first lia.
  nia.
Qed.
End Mul.

(* i + 1 below the length of the array, as a natural number. *)
Lemma add1_nat (a : int64) (n : nat) :
  (Z.to_nat (Int64.unsigned a) < n)%nat -> Z.of_nat n <= Int64.max_unsigned ->
  Z.to_nat (Int64.unsigned (Int64.add a (Int64.repr 1))) =
  (Z.to_nat (Int64.unsigned a)).+1.
Proof.
  move=> H Hn; have Ra := Int64.unsigned_range a.
  rewrite Int64.add_unsigned Int64.unsigned_repr; rewrite Int64.unsigned_repr; try lia.
  all: rewrite /Int64.max_unsigned /=; lia.
Qed.

(** ** Coefficients *)

Section Coefs.

Context {n : nat}.
Implicit Types B : {ffun 'I_n -> int64}.

Lemma size_coefsA B L K : size (coefsA B L K) = K.
Proof. by rewrite /coefsA size_map size_iota. Qed.

Lemma nth_coefsA B L K p : (p < K)%nat -> nth 0 (coefsA B L K) p = coefA B L p.
Proof. by move=> H; rewrite /coefsA (nth_map 0%nat) ?size_iota // nth_iota. Qed.

Lemma coefA_bound B L p : 0 <= coefA B L p < baseZ (Z.of_nat L).
Proof. exact: segv_bound. Qed.

(* Two arrays that agree on the words of coefficient p. *)
Lemma coefA_ext B B' L p :
  (forall q : 'I_n, (p * L <= q < p * L + L)%nat -> B' q = B q) ->
  coefA B' L p = coefA B L p.
Proof.
  move=> H; apply: segv_ext => q Hq; apply: wd_eq => Hq'.
  by apply: H.
Qed.

End Coefs.

(** ** tstepZ, element by element *)

Lemma size_tstepZ ds : size (tstepZ ds) = size ds.
Proof.
  elim: ds => [|a r IH] //; case: r IH => [|b r] IH //.
  have -> : tstepZ [:: a, b & r] = (a + b) :: tstepZ (b :: r) by [].
  by rewrite /= IH.
Qed.

Lemma nth_tstepZ ds p : (p.+1 < size ds)%nat ->
  nth 0 (tstepZ ds) p = nth 0 ds p + nth 0 ds p.+1.
Proof.
  elim: ds p => [|a r IH] p //; case: r IH => [|b r] IH H.
    by case: p H.
  case: p H => [|p] H //.
  by rewrite [tstepZ _]/= [nth _ (_ :: _) p.+1]/= IH.
Qed.

Lemma nth_tstepZ_last ds p : p.+1 = size ds -> nth 0 (tstepZ ds) p = nth 0 ds p.
Proof.
  elim: ds p => [|a r IH] p //; case: r IH => [|b r] IH H.
    by case: p H.
  case: p H => [|p] H //.
  have -> : tstepZ [:: a, b & r] = (a + b) :: tstepZ (b :: r) by [].
  have E : p.+1 = size (b :: r) by move: H => /= [->].
  exact: (IH p E).
Qed.

(** ** Comparisons of words as natural numbers *)

Lemma ltu_nat (a b : int64) :
  Int64.ltu a b = (Z.to_nat (Int64.unsigned a) < Z.to_nat (Int64.unsigned b))%nat.
Proof.
  have Ra := Int64.unsigned_range a; have Rb := Int64.unsigned_range b.
  rewrite /Int64.ltu; case: Coqlib.zlt => H; apply/esym.
  - by apply/ltP; lia.
  - by apply/negP => /ltP; lia.
Qed.

Lemma sub1_nat (k : int64) : (0 < Z.to_nat (Int64.unsigned k))%nat ->
  Z.to_nat (Int64.unsigned (Int64.sub k (Int64.repr 1))) =
  (Z.to_nat (Int64.unsigned k)).-1.
Proof.
  move=> H; have Rk := Int64.unsigned_range k.
  rewrite /Int64.sub Int64.unsigned_repr.
  all: change (Int64.unsigned (Int64.repr 1)) with 1%Z; try lia.
  rewrite /Int64.max_unsigned; lia.
Qed.
