From Stdlib Require Import ZArith List Lia.
From VST.zlist Require Import sublist.
Import ListNotations.
Open Scope Z_scope.
Definition lbits : Z := 32.
Definition limb (x : Z) : Prop := 0 <= x < 2 ^ lbits.
Fixpoint valL (ws : list Z) : Z :=
  match ws with [] => 0 | w :: r => w + 2 ^ lbits * valL r end.
Lemma valL_app a b : valL (a ++ b) = valL a + 2 ^ (lbits * Zlength a) * valL b.
Proof.
  induction a as [|w a IH]; cbn [app valL].
  - change (Zlength (@nil Z)) with 0; rewrite Z.mul_0_r, Z.pow_0_r; lia.
  - rewrite IH, Zlength_cons, <- Z.add_1_r.
    replace (lbits * (Zlength a + 1)) with (lbits * Zlength a + lbits) by lia.
    rewrite Z.pow_add_r by (unfold lbits; pose proof (Zlength_nonneg a); lia).
    ring.
Qed.
Lemma valL_sublist_succ xs b : 0 <= b < Zlength xs ->
  valL (sublist 0 (b + 1) xs) = valL (sublist 0 b xs) + 2 ^ (lbits * b) * Znth b xs.
Proof.
  intros Hb. rewrite (sublist_split 0 b (b + 1)) by lia.
  rewrite valL_app, sublist_len_1 by lia; simpl valL.
  rewrite Zlength_sublist by lia; replace (b - 0) with b by lia; ring.
Qed.
