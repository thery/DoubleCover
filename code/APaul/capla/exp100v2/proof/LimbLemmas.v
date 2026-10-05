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
