(** * A [true] answer of the checker gives the six conditions *)

From Stdlib Require Import ZArith Reals Lia Lra List Bool.
From Flocq Require Import Core.
From ExpTableKL Require Import ExpCheck ExpParse ExpTaylor ExpArith ExpEncl.

Open Scope R_scope.

(** One word leaves room for the [2^-m] term of the window. *)
Lemma m_le_lbits l : (1 <= l)%Z -> (m <= lbits l)%Z.
Proof.
intros Hl; unfold m, lbits, beta; change (Z.log2 (2 ^ 64)) with 64%Z; lia.
Qed.

(** With one word or more, the window is less than half the modulus. *)
Lemma E_lt l : (1 <= l)%Z -> (2 * E l < beta_l l)%Z.
Proof.
intros Hl; unfold E, beta_l.
replace l with (1 + (l - 1))%Z at 2 by ring.
rewrite Z.pow_add_r by lia; rewrite Z.pow_1_r, Z.mul_assoc.
apply Z.mul_lt_mono_pos_r; [apply Z.pow_pos_nonneg; [reflexivity|lia]|].
reflexivity.
Qed.

Theorem check_lineP S0 ex n k l B :
  check_line S0 ex n k l B = true -> line_ok S0 ex n k l B.
Proof.
unfold check_line.
set (ue := uexp ex).
destruct (encl l S0 ue) as [[[[mL0 fL0] mU0] fU0]|] eqn:h0;
  [|rewrite !andb_false_r; discriminate].
destruct (encl l (S0 + n - drop) ue) as [[[[mL1 fL1] mU1] fU1]|] eqn:h1;
  [|rewrite !andb_false_r; discriminate].
set (e := (Z.log2 mL0 + fL0)%Z).
destruct (coefs l mL0 fL0 mU0 fU0 (vexp e) ue 0 1 k) as [A|] eqn:hc;
  [|rewrite !andb_false_r; discriminate].
intros h.
apply andb_prop in h as [h hm].
apply andb_prop in hm as [hm hB].
apply andb_prop in hm as [hlt hw].
apply andb_prop in h as [h hlen].
apply andb_prop in h as [h hsg].
apply andb_prop in h as [h h53'].
apply andb_prop in h as [h h52'].
apply andb_prop in h as [h h53].
apply andb_prop in h as [h h52].
apply andb_prop in h as [h hn].
apply andb_prop in h as [h hlu].
apply andb_prop in h as [h hll].
apply andb_prop in h as [hk1 hku].
apply Nat.leb_le in hk1, hku; apply Z.leb_le in hll, hlu.
apply Z.leb_le in hn; apply Z.leb_le in h52; apply Z.ltb_lt in h53.
apply Z.leb_le in h52'; apply Z.ltb_lt in h53'; apply Z.ltb_lt in hsg.
apply Nat.eqb_eq in hlen.
destruct (encl_ok _ _ _ _ _ _ _ h0) as [pL0 [pU0 [lo0 up0]]].
destruct (encl_ok _ _ _ _ _ _ _ h1) as [pL1 [pU1 [lo1 up1]]].
assert (hl0 : (0 <= l)%Z) by lia.
exists e; cbv zeta; fold ue.
assert (hu : 0 < bp ue) by apply bpow_gt_0.
assert (hd : (0 <= drop)%Z) by (unfold drop; destruct closed; lia).
assert (hxl : IZR (S0 + n - drop) * bp ue =
              IZR S0 * bp ue + IZR (n - drop) * bp ue)
  by (rewrite minus_IZR, plus_IZR, minus_IZR; ring).
repeat split.
- (* 1. u is constant *)
  exact hn.
- exact h52.
- exact h53.
- exact h52'.
- exact h53'.
- exact hsg.
- (* 2. v is constant *)
  apply Rle_trans with (IZR mL0 * bp fL0); [apply log2_le; exact pL0|].
  exact lo0.
- apply Rle_lt_trans with (IZR mU1 * bp fU1); [exact up1|].
  apply lt2_ok; [lia|exact hlt].
- (* 3. (H_A), and the table holds P(0) .. P(k-1) *)
  exists A.
  destruct (coefs_ok _ _ _ _ _ _ _ _ _ _ _ _ hl0 eq_refl (conj lo0 up0) hc)
    as [hlA hA].
  split; [exact hlA|]; split; [exact hlen|]; split.
  + intros i hi; destruct (hA i hi) as [hA1 hA2]; split; [exact hA1|].
    exact hA2.
  + intros i hi.
    rewrite forallb_forall in hB.
    apply Z.eqb_eq, hB, in_seq; lia.
- (* 4. (H_T) *)
  intros j hj; rewrite hxl.
  apply HT_ok; [exact hu|apply bpow_gt_0|lia|lia].
- (* 5. (H_E) *)
  apply window_okP with (mU := mU1) (fU := fU1);
    [exact hl0|exact (m_le_lbits l hll)|lia| |exact hw].
  split; [apply Rlt_le, exp_pos|exact up1].
- (* 6. k and l fit the search, the window *)
  exact hk1.
- exact hku.
- exact hll.
- exact hlu.
- exact (E_lt l hll).
Qed.

(** The same on the text of the lines: each one reads as a line that
    satisfies the six conditions. *)
Theorem check_rawP ls : check_raw ls = true ->
  forall s, In s ls -> exists S0 ex n k l B,
    parse s = Some (S0, ex, n, k, l, B) /\ line_ok S0 ex n k l B.
Proof.
unfold check_raw; intros hall s hin.
rewrite forallb_forall in hall.
specialize (hall _ hin).
destruct (parse s) as [[[[[[S0 ex] n] k] l] B]|]; [|discriminate].
exists S0, ex, n, k, l, B; split; [reflexivity|].
apply check_lineP; exact hall.
Qed.
