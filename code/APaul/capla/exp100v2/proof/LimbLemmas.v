(** * Lemmas shared by the proofs: words of 64 bits holding limbs of 32
    bits, and the value of the low limbs of an array after a write. *)

From compcert Require Import CaplaProof.
From Exp100 Require Import ExpNum ExpLimbs.
Require Import Exp100Capla2.Bridge.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Open Scope capla_scope.

(** ** Words *)

Section Words.
Transparent Int64.modu Int64.repr Int64.unsigned Int.repr Int.unsigned Int.modu.

(* The low limb of a word: c & (2^32 - 1). *)
Lemma and_mask (c : int64) :
  Int64.unsigned (Int64.and c (Int64.repr 4294967295)) =
  (Int64.unsigned c mod 2 ^ 32)%Z.
Proof.
  have -> : Int64.repr 4294967295 =
            Int64.sub (Int64.repr 4294967296) Int64.one by [].
  rewrite -(Int64.modu_and _ _ (Int64.repr 32)) //.
  have E : Int64.unsigned (Int64.repr 4294967296) = (2 ^ 32)%Z by [].
  rewrite /Int64.modu E Int64.unsigned_repr //.
  have := Int64.unsigned_range c.
  have := Z.mod_pos_bound (Int64.unsigned c) (2 ^ 32) ltac:(lia).
  change Int64.max_unsigned with 18446744073709551615%Z; lia.
Qed.

(* The carry of a word: c >> 32. *)
Lemma shru32 (c : int64) :
  Int64.unsigned (Int64.shru' c (Int.modu (Int.repr 32) Int64.iwordsize')) =
  (Int64.unsigned c / 2 ^ 32)%Z.
Proof.
  have -> : Int.modu (Int.repr 32) Int64.iwordsize' = Int.repr 32 by [].
  have E : Int.unsigned (Int.repr 32) = 32%Z by [].
  rewrite /Int64.shru' E Z.shiftr_div_pow2; lia.
Qed.

End Words.

Section Mul.
Transparent Int64.mul.

(* a w + c fits in a word when the three are limbs. *)
Lemma mul_add_word (a w c : int64) :
  (Int64.unsigned a < 2 ^ 32)%Z -> (Int64.unsigned w < 2 ^ 32)%Z ->
  (Int64.unsigned c < 2 ^ 32)%Z ->
  Int64.unsigned (Int64.add (Int64.mul a w) c) =
  (Int64.unsigned a * Int64.unsigned w + Int64.unsigned c)%Z.
Proof.
  move=> Ha Hw Hc.
  have := Int64.unsigned_range a; have := Int64.unsigned_range w;
    have := Int64.unsigned_range c => Rc Rw Ra.
  rewrite Int64.add_unsigned /Int64.mul.
  have Ep : (0 <= Int64.unsigned a * Int64.unsigned w <=
             (2 ^ 32 - 1) * (2 ^ 32 - 1))%Z by nia.
  have M : Int64.max_unsigned = 18446744073709551615%Z by [].
  rewrite (Int64.unsigned_repr (Int64.unsigned a * Int64.unsigned w)) ?M; lia.
Qed.

End Mul.

(** ** Arrays *)

Section Arr.

Context {n : nat}.
Implicit Types f : {ffun 'I_n -> int64}.

(* pvalS on a natural index. *)
Lemma pvalSn f k (H : (k < n)%nat) :
  pval f k.+1 = (pval f k + limb_base k * Int64.unsigned (f (Ordinal H)))%Z.
Proof. exact: (pvalS f (Ordinal H)). Qed.

(* Reading an array just written. *)
Lemma setfP f k v (H : (k < n)%nat) (i : 'I_n) :
  (f ↑[k ← v]) i = if nat_of_ord i == k then v else f i.
Proof.
  by rewrite (setfE _ _ _ H) ffunE.
Qed.

(* Writing limb k changes the k + 1 low limbs and above. *)
Lemma pval_setf f k v (H : (k < n)%nat) m : (m <= n)%nat ->
  pval (f ↑[k ← v]) m =
  (pval f m + if (k < m)%nat then
     (Int64.unsigned v - Int64.unsigned (f (Ordinal H))) * limb_base k
   else 0)%Z.
Proof.
  elim: m => [|m IH] Hm; first by rewrite !pval0.
  rewrite !(pvalSn _ _ Hm) IH ?(ltnW Hm) // (setfP _ _ _ H) /=.
  case: (eqVneq m k) => [Emk|Nmk].
  - subst m; rewrite ltnn ltnSn.
    have -> : Ordinal Hm = Ordinal H by apply: val_inj.
    lia.
  - have -> : (k < m.+1)%nat = (k < m)%nat.
      by rewrite ltnS leq_eqVlt; case: eqP => // E; case/eqP: Nmk.
    lia.
Qed.

(* The low limbs of an array of limbs. *)
Lemma pval_lt f k : limbsA f -> (k <= n)%nat ->
  (0 <= pval f k < limb_base k)%Z.
Proof.
  move=> Hl; elim: k => [|k IH] Hk; first by rewrite pval0 limb_base0; lia.
  have [L0 L1] := Hl (Ordinal Hk).
  rewrite (pvalSn _ _ Hk) limb_baseS; move: L0 L1.
  have := IH (ltnW Hk); have := limb_base_pos k.
  rewrite /limb_bits; nia.
Qed.

End Arr.

(** ** Sums and differences of limbs, from num_add and num_sub *)

Section AddSub.
Local Open Scope Z_scope.

(* The sum of a carry and two limbs does not wrap. *)
Lemma add3_unsigned (c x y : int64) :
  Int64.unsigned c <= 1 -> Int64.unsigned x < 2 ^ 32 ->
  Int64.unsigned y < 2 ^ 32 ->
  Int64.unsigned (Int64.add (Int64.add c x) y) =
  Int64.unsigned c + Int64.unsigned x + Int64.unsigned y.
Proof.
  move=> Hc Hx Hy.
  have := Int64.unsigned_range c; have := Int64.unsigned_range x.
  have := Int64.unsigned_range y => Ry Rx Rc.
  rewrite !Int64.add_unsigned (Int64.unsigned_repr (_ + _)).
  { change Int64.max_unsigned with 18446744073709551615; lia. }
  rewrite Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

(* A limb plus a carry does not wrap. *)
Lemma add2_unsigned (y c : int64) :
  Int64.unsigned y < 2 ^ 32 -> Int64.unsigned c <= 1 ->
  Int64.unsigned (Int64.add y c) = Int64.unsigned y + Int64.unsigned c.
Proof.
  move=> Hy Hc.
  have := Int64.unsigned_range y; have := Int64.unsigned_range c => Rc Ry.
  rewrite Int64.add_unsigned Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

(* x - t, when t <= x. *)
Lemma sub_unsigned (x t : int64) :
  Int64.unsigned t <= Int64.unsigned x ->
  Int64.unsigned (Int64.sub x t) = Int64.unsigned x - Int64.unsigned t.
Proof.
  move=> H.
  have := Int64.unsigned_range x; have := Int64.unsigned_range t => Rt Rx.
  rewrite /Int64.sub Int64.unsigned_repr //.
  change Int64.max_unsigned with 18446744073709551615; lia.
Qed.

(* x + 2^32 - t, when x < t <= 2^32. *)
Lemma borrow_unsigned (x t : int64) :
  Int64.unsigned x < Int64.unsigned t <= 2 ^ 32 ->
  Int64.unsigned (Int64.sub (Int64.add x (Int64.repr 4294967296)) t) =
  Int64.unsigned x + 2 ^ 32 - Int64.unsigned t.
Proof.
  move=> H.
  have := Int64.unsigned_range x; have := Int64.unsigned_range t => Rt Rx.
  have E : Int64.unsigned (Int64.add x (Int64.repr 4294967296)) =
           Int64.unsigned x + 2 ^ 32.
  { rewrite Int64.add_unsigned (Int64.unsigned_repr 4294967296).
    { change Int64.max_unsigned with 18446744073709551615; lia. }
    rewrite Int64.unsigned_repr //.
    change Int64.max_unsigned with 18446744073709551615; lia. }
  rewrite sub_unsigned E //; lia.
Qed.

End AddSub.

(** ** Writes in an array, from num_add and num_sub *)

Section Writes.

Context {n : nat}.
Implicit Types a : {ffun 'I_n -> int64}.

(* Writing limb k leaves the other limbs. *)
Lemma setf_other a k v (j : 'I_n) : (j : nat) <> k -> (a ↑[ k ← v ]) j = a j.
Proof.
  move=> Hj; rewrite /setf; case: insubP => [k' _ Ek|_] //=.
  rewrite ffunE; case: eqP => // Ejk; case: Hj; by rewrite Ejk.
Qed.

(* Limb k is the value written. *)
Lemma setf_at a k v (Hk : (k < n)%nat) : (a ↑[ k ← v ]) (Ordinal Hk) = v.
Proof. by rewrite (setfE _ _ _ Hk) ffunE eqxx. Qed.

(* Writing limb k adds it, at its weight, to the k low limbs. *)
Lemma pval_setf_top a k v : (k < n)%nat ->
  pval (a ↑[ k ← v ]) k.+1 = pval a k + limb_base k * Int64.unsigned v.
Proof.
  move=> Hk.
  rewrite -[k.+1]/((Ordinal Hk).+1) pvalS setf_at.
  congr (_ + _); apply: pval_ext => j Hj; apply: setf_other.
  by move=> E; move: Hj; rewrite E ltnn.
Qed.

(* Writing limb o adds it, at its weight, to the o low limbs. *)
Lemma pval_upd a (o : 'I_n) v :
  pval [ffun j => if j == o then v else a j] o.+1 =
  pval a o + limb_base o * Int64.unsigned v.
Proof.
  rewrite pvalS ffunE eqxx; congr (_ + _).
  apply: pval_ext => j Hj; rewrite ffunE; case: eqP => // Ej.
  by move: Hj; rewrite Ej ltnn.
Qed.

End Writes.
