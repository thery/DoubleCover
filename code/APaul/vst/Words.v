(** * Words and the numbers they stand for

    A coefficient of the search is [l] words of 64 bits, the least
    significant first.  Here, with plain integers: a word is an integer in
    [0, 2^64), a list of words stands for [valZ], and [baseZ l] is the
    modulus of [l] words (as in [code/APaul/rocq/HtrDefs.v]). *)

From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist.
Import ListNotations.

Open Scope Z_scope.

Definition wbits : Z := 64.            (* bits of a word *)

(** [beta^l], the modulus of a coefficient of [l] words. *)
Definition baseZ (l : Z) : Z := 2 ^ (wbits * l).

(** A word: an integer in [0, 2^64). *)
Definition word (x : Z) : Prop := 0 <= x < 2 ^ wbits.

(** The number a list of words stands for, least significant word first. *)
Fixpoint valZ (ws : list Z) : Z :=
  match ws with
  | [] => 0
  | w :: r => w + 2 ^ wbits * valZ r
  end.

Lemma baseZ0 : baseZ 0 = 1.
Proof. reflexivity. Qed.

Lemma baseZ_pos l : 0 <= l -> 0 < baseZ l.
Proof. intros; unfold baseZ, wbits; apply Z.pow_pos_nonneg; lia. Qed.

Lemma baseZ_succ l : 0 <= l -> baseZ (l + 1) = baseZ l * 2 ^ wbits.
Proof.
  intros; unfold baseZ, wbits; rewrite <- Z.pow_add_r; try lia.
  f_equal; lia.
Qed.

Lemma valZ_app a b : valZ (a ++ b) = valZ a + baseZ (Zlength a) * valZ b.
Proof.
  induction a as [|w a IH]; cbn [app valZ].
  - change (Zlength (@nil Z)) with 0; rewrite baseZ0; lia.
  - rewrite IH, Zlength_cons, <- Z.add_1_r.
    rewrite baseZ_succ by apply Zlength_nonneg.
    ring.
Qed.

Lemma valZ_bound ws : Forall word ws -> 0 <= valZ ws < baseZ (Zlength ws).
Proof.
  induction 1 as [|w ws Hw _ IH]; cbn [valZ].
  - change (Zlength (@nil Z)) with 0; rewrite baseZ0; lia.
  - rewrite Zlength_cons, <- Z.add_1_r.
    rewrite baseZ_succ by apply Zlength_nonneg.
    unfold word in Hw; nia.
Qed.

(** The words [a .. b] are those of [a .. b-1] then word [b]. *)
Lemma valZ_sublist_succ xs a b : 0 <= a <= b -> b < Zlength xs ->
  valZ (sublist a (b + 1) xs) =
  valZ (sublist a b xs) + baseZ (b - a) * Znth b xs.
Proof.
  intros Hab Hb.
  rewrite (sublist_split a b (b + 1)) by lia.
  rewrite valZ_app, sublist_len_1 by lia; simpl valZ.
  rewrite Zlength_sublist by lia; ring.
Qed.

(** [n] words minus a carry times [baseZ n] equal to [v]: the words stand
    for [v mod baseZ n] (the carry is the quotient). *)
Lemma valZ_mod ws n c v : Forall word ws -> Zlength ws = n ->
  valZ ws - c * baseZ n = v -> valZ ws = v mod baseZ n.
Proof.
  intros Hw Hn Hv; subst n.
  pose proof (valZ_bound ws Hw).
  apply (Z.mod_unique_pos _ _ (- c)); lia.
Qed.

(** One step of a loop over the words of [ia .. ia+l): with [s = 1] the
    addition B_ia += B_ib with its carry [c], with [s = -1] the
    subtraction B_ia -= B_ib with its borrow [c].  If the first [i] words of
    [xs'] at [ia] stand for B_ia + s B_ib up to the carry, then writing at
    [ia + i] the word [d] of the next step keeps it for [i + 1] words. *)
Lemma valZ_step s xs xs' ia ib i c c' d :
  0 <= ia -> 0 <= ib -> 0 <= i ->
  ia + i < Zlength xs' -> ia + i < Zlength xs -> ib + i < Zlength xs ->
  valZ (sublist ia (ia + i) xs') + s * c * baseZ i =
    valZ (sublist ia (ia + i) xs) + s * valZ (sublist ib (ib + i) xs) ->
  d + s * 2 ^ wbits * c' = Znth (ia + i) xs + s * Znth (ib + i) xs + s * c ->
  valZ (sublist ia (ia + (i + 1)) (upd_Znth (ia + i) xs' d)) +
    s * c' * baseZ (i + 1) =
  valZ (sublist ia (ia + (i + 1)) xs) +
    s * valZ (sublist ib (ib + (i + 1)) xs).
Proof.
  intros Ha Hb Hi Ha' Ha1 Hb1 Hv Hd.
  rewrite !Z.add_assoc.
  rewrite !valZ_sublist_succ; try lia;
    try (rewrite upd_Znth_Zlength; lia).
  rewrite sublist_upd_Znth_l, upd_Znth_same by lia.
  replace (ia + i - ia) with i by lia.
  replace (ib + i - ib) with i by lia.
  rewrite baseZ_succ by lia.
  assert (Hm : baseZ i * (d + s * 2 ^ wbits * c') =
               baseZ i * (Znth (ia + i) xs + s * Znth (ib + i) xs + s * c))
    by (rewrite Hd; reflexivity).
  lia.
Qed.
