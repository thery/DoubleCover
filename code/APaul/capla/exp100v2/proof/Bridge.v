(** * From Capla's arrays to the numbers of the shared model

    Capla passes an array of n words as a function [{ffun 'I_n -> int64}].
    The shared files (ExpNum.v, ExpLimbs.v) hold a number as a list of Z,
    the least significant limb first, standing for [valZ].  The two meet
    through [words], the list of the values of the words of an array:
    [valA a] is [valZ (words a)], and [pval a k] is the number of the k
    low limbs, which the carry loops follow. *)

From compcert Require Import CaplaProof.
From mathcomp Require Import tuple.
From Exp100 Require Import ExpNum ExpLimbs.

Set Bullet Behavior "Strict Subproofs".
Unset SsrOldRewriteGoalsOrder.

Local Open Scope Z_scope.

(** ** Limb bases *)

Lemma limb_base0 : limb_base 0 = 1.
Proof. by []. Qed.

Lemma limb_baseS k : limb_base k.+1 = 2 ^ limb_bits * limb_base k.
Proof.
  rewrite /limb_base Nat2Z.inj_succ Z.mul_succ_r Z.pow_add_r /limb_bits; lia.
Qed.

Lemma limb_base_pos k : 0 < limb_base k.
Proof. rewrite /limb_base /limb_bits; apply: Z.pow_pos_nonneg; lia. Qed.

(** ** The value of a sequence *)

(* A limb written after the last one weighs 2^(32 size). *)
Lemma valZ_rcons s x : valZ (rcons s x) = valZ s + limb_base (size s) * x.
Proof.
  elim: s => [|y s IH]; first by rewrite limb_base0; cbn [rcons valZ]; lia.
  rewrite rcons_cons; cbn [valZ size]; rewrite IH limb_baseS; ring.
Qed.

(* The values of words are not negative. *)
Lemma valZ_unsigned_ge0 (s : list int64) :
  0 <= valZ [seq Int64.unsigned x | x <- s].
Proof.
  elim: s => [|x s IH]; cbn [map valZ]; first lia.
  have := Int64.unsigned_range x; rewrite /limb_bits; lia.
Qed.

(* mathcomp's nth is Stdlib's, the arguments in another order. *)
Lemma nth_List_nth {A : Type} (s : list A) x0 k :
  nth x0 s k = List.nth k s x0.
Proof. by elim: s k => [|y s IH] [|k] //=. Qed.

(** ** Arrays of words *)

Section Arrays.

Context {n : nat}.
Implicit Types a b : {ffun 'I_n -> int64}.

(* The values of the words of an array, the first word first. *)
Definition words a : list Z := [seq Int64.unsigned x | x <- tuple.tval (fgraph a)].

(* The number an array of limbs stands for. *)
Definition valA a : Z := valZ (words a).

(* The number its k low limbs stand for. *)
Definition pval a (k : nat) : Z := valZ (seq.take k (words a)).

(* Every word of the array is a limb. *)
Definition limbsA a : Prop := forall i : 'I_n, limb (Int64.unsigned (a i)).

Lemma size_words a : size (words a) = n.
Proof. by rewrite /words size_map size_tuple card_ord. Qed.

Lemma nth_words a (i : 'I_n) : nth 0 (words a) i = Int64.unsigned (a i).
Proof. by rewrite (nth_map Int64.zero) ?size_tuple ?card_ord // nth_fgraph_ord. Qed.

Lemma pval0 a : pval a 0 = 0.
Proof. by rewrite /pval take0. Qed.

(* One more limb: the low ones, and limb i at its weight. *)
Lemma pvalS a (i : 'I_n) :
  pval a i.+1 = pval a i + limb_base i * Int64.unsigned (a i).
Proof.
  rewrite /pval (take_nth 0) ?size_words // valZ_rcons nth_words.
  by rewrite size_takel // size_words ltnW.
Qed.

(* The low limbs depend on the low words only. *)
Lemma pval_ext a b k :
  (forall i : 'I_n, (i < k)%nat -> a i = b i) -> pval a k = pval b k.
Proof.
  move=> H; rewrite /pval; congr valZ.
  apply: (@eq_from_nth _ 0); first by rewrite !size_take; rewrite !size_words.
  move=> j; rewrite size_take size_words => Hj.
  have Hjn : (j < n)%nat.
    by move: Hj; case: (ltnP k n) => [Hkn Hjk|//]; apply: ltn_trans Hjk Hkn.
  have Hjk : (j < k)%nat.
    by move: Hj; case: (ltnP k n) => [//|Hnk Hj']; apply: leq_trans Hj' Hnk.
  rewrite !nth_take //.
  rewrite -[j]/(nat_of_ord (Ordinal Hjn)).
  rewrite !nth_words.
  by rewrite H.
Qed.

(* All the limbs. *)
Lemma pval_all a : pval a n = valA a.
Proof. by rewrite /pval -{1}(size_words a) take_size. Qed.

Lemma pval_ge0 a k : 0 <= pval a k.
Proof. by rewrite /pval /words -map_take; apply: valZ_unsigned_ge0. Qed.

Lemma valA_ge0 a : 0 <= valA a.
Proof. by rewrite -pval_all; apply: pval_ge0. Qed.

(* The length of the list of words. *)
Lemma length_words a : List.length (words a) = n.
Proof. exact: size_words. Qed.

(* Every word is a limb exactly when every value is a limb. *)
Lemma limbsA_Forall a : limbsA a <-> List.Forall limb (words a).
Proof.
  rewrite List.Forall_nth; split.
  - move=> H j d Hj.
    have Hjn : (j < n)%nat by apply/ltP; rewrite -(length_words a).
    rewrite -nth_List_nth (set_nth_default 0) ?size_words //.
    by rewrite -[j]/(nat_of_ord (Ordinal Hjn)) nth_words; apply: H.
  - move=> H i; have := H i 0 ltac:(rewrite length_words; apply/ltP; done).
    by rewrite -nth_List_nth nth_words.
Qed.

(* The number of an array of limbs is below 2^(32 n). *)
Lemma valA_bound a : limbsA a -> 0 <= valA a < limb_base n.
Proof.
  move/limbsA_Forall/valZ_bounds; rewrite length_words.
  by rewrite /valA.
Qed.

End Arrays.
